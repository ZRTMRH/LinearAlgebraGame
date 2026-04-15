FROM node:20

# Install bubblewrap for lean4game security sandboxing in production and sudo for permissions
RUN apt-get update && apt-get install -y bubblewrap sudo git && rm -rf /var/lib/apt/lists/*

# Allow node user to use sudo without password (for development)
RUN echo "node ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers

WORKDIR /

COPY ./lean-toolchain /lean-toolchain

# Switch to node user for elan installation
USER node

# Install elan as node user in their home directory
ENV ELAN_HOME=/home/node/.elan
ENV PATH=/home/node/.elan/bin:$PATH

RUN export LEAN_VERSION="$(cat /lean-toolchain)" && \
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --no-modify-path --default-toolchain $LEAN_VERSION && \
  /home/node/.elan/bin/elan --version && \
  /home/node/.elan/bin/lean --version && \
  /home/node/.elan/bin/leanc --version && \
  /home/node/.elan/bin/lake --version

# Go back to root for copying files
USER root

# Copy the startup script
COPY start-server.sh /home/node/start-server.sh
RUN chmod +x /home/node/start-server.sh && \
    chown node:node /home/node/start-server.sh

USER node
WORKDIR /home/node/game

# Ensure PATH includes elan binaries for node user
ENV PATH="/home/node/.elan/bin:${PATH}"
ENV ELAN_HOME="/home/node/.elan"

# Copy dependency files first for better Docker layer caching
COPY --chown=node:node lakefile.lean lake-manifest.json lean-toolchain ./

# Update dependencies and get cache (this layer will be cached if dependencies don't change)
RUN echo "Updating Lake dependencies..." && lake update -R
RUN echo "Getting mathlib cache (this should speed up build significantly)..." && \
    lake exe cache get --force || echo "Cache get failed, will build from source (slower)"

# Clone lean4game repository (v4.28.0 monorepo - no gitpkg dependencies)
# NOTE (2026-04-15): The v4.28.0 branch has known browser-side regressions tracked in
# leanprover-community/lean4game#451, #445, #485 (missing files-service-override in
# LeanMonaco.start, and an uncaught rejection from updateVSCodeOptions). We patch them
# below. Pinning to the maintainer-cited commit `1eec1eb6` was attempted but fails at
# `npm install` because that commit still has a gitpkg.vercel.app git dep that now
# returns 402 — see memory/docker_gitpkg_issue.md. The v4.28.0 tag is currently the
# only buildable target.
RUN git clone https://github.com/leanprover-community/lean4game.git --branch v4.28.0 /home/node/lean4game && \
    chown -R node:node /home/node/lean4game

# Pre-install npm dependencies during Docker build (npm workspaces: installs client + relay)
RUN echo "Pre-installing npm dependencies for lean4game..." && \
    cd /home/node/lean4game && npm install

# Patch lean4monaco v1.1.9: its LeanMonaco.start() calls vscode/services `initialize(...)`
# without a files service override. The default (read-only) file service then rejects
# `createModelReference(...)` inside LeanMonacoEditor.start() with
# `FileOperationError: Unable to write file '...' (NoPermissions)`. That throw prevents
# the Monaco editor from mounting, so no Lean LSP client ever registers for the URI and
# the infoview is stuck on "No active Lean client" forever.
# Fix: inject `getFilesServiceOverride()` into the initialize() service overrides. The
# override's default in-memory filesystem provider (registered at priority 0) makes
# writes to file:// URIs succeed.
RUN echo "Patching lean4monaco to include files-service-override..." && \
    LM=/home/node/lean4game/node_modules/lean4monaco/dist/leanmonaco.js && \
    grep -q "monaco-vscode-files-service-override" "$LM" || { \
      sed -i "s|^import getModelServiceOverride from '@codingame/monaco-vscode-model-service-override';|&\nimport getFilesServiceOverride from '@codingame/monaco-vscode-files-service-override';|" "$LM" && \
      sed -i "s|\.\.\.getModelServiceOverride()|...getModelServiceOverride(),\n                ...getFilesServiceOverride()|" "$LM" ; \
    } && \
    grep -n "FilesServiceOverride" "$LM"

# Second patch: `updateVSCodeOptions` in lean4monaco calls `workspace.getConfiguration().update(key, value)`
# without a ConfigurationTarget argument. Because `LeanMonaco.start()` sets a workspace
# (`workspaceUri: Uri.file('/workspace.code-workspace')`), this defaults to Workspace scope
# and triggers a write-through to `/workspace.code-workspace`. The codingame in-memory
# ConfigurationEditing path rejects that write with `NoPermissions`, which surfaces as an
# Uncaught promise rejection and prevents the Lean extension from activating — leaving the
# infoview stuck on "No active Lean client". The config value is already applied in-memory
# by the time the write-through runs, so swallowing the rejection is safe.
RUN echo "Patching lean4monaco updateVSCodeOptions to swallow config-write errors..." && \
    LM=/home/node/lean4game/node_modules/lean4monaco/dist/leanmonaco.js && \
    grep -q "update(key, vsCodeOptions\[key\])\.catch" "$LM" || \
      sed -i "s|workspace\.getConfiguration()\.update(key, vsCodeOptions\[key\]);|workspace.getConfiguration().update(key, vsCodeOptions[key]).catch(()=>{});|" "$LM" && \
    grep -n "vsCodeOptions\[key\]" "$LM"

# Now copy the rest of the project
COPY --chown=node:node . .

# Build the project (only this step runs if game files change)
RUN echo "Building Lean project..." && lake build

# Pre-build GameServer.Runner so first level open isn't blocked compiling it.
# `lake serve` (used by lean4game v4.28.0 in fallback mode) elaborates a synthetic
# `import GameServer.Runner` for every didOpen; without this, the browser tab
# freezes ("page not responding") while it compiles on demand.
RUN echo "Pre-building GameServer.Runner..." && lake build GameServer.Runner

# Pre-build lean4game relay and client
RUN echo "Pre-building lean4game relay and client..." && \
    cd /home/node/lean4game && \
    npm run build:relay && \
    VITE_LEAN4GAME_SINGLE=true VITE_LEAN4GAME_OWNER=local VITE_LEAN4GAME_REPO=game npm run build:client

# Create games directory and link our game for lean4game to find it
RUN mkdir -p /home/node/lean4game/games/local && \
    ln -sf /home/node/game /home/node/lean4game/games/local/game && \
    echo "Verifying symlink was created..." && \
    ls -la /home/node/lean4game/games/local/

EXPOSE 3000

CMD ["/home/node/start-server.sh"]
