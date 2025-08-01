FROM node:20

# Install bubblewrap for lean4game security sandboxing in production
RUN apt-get update && apt-get install -y bubblewrap && rm -rf /var/lib/apt/lists/*

WORKDIR /

COPY ./lean-toolchain /lean-toolchain

USER node

WORKDIR /home/node

RUN export LEAN_VERSION="$(cat /lean-toolchain | grep -oE '[^:]+$')" && git clone --depth 1 --branch $LEAN_VERSION https://github.com/leanprover-community/lean4game.git

WORKDIR /

USER root

ENV ELAN_HOME=/usr/local/elan \
  PATH=/usr/local/elan/bin:$PATH

SHELL ["/bin/bash", "-euxo", "pipefail", "-c"]

RUN export LEAN_VERSION="$(cat /lean-toolchain)" && \
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --no-modify-path --default-toolchain $LEAN_VERSION; \
    chmod -R a+w $ELAN_HOME; \
    elan --version; \
    lean --version; \
    leanc --version; \
    lake --version;

# Copy the startup script
COPY start-server.sh /home/node/start-server.sh
RUN chmod +x /home/node/start-server.sh

USER node
WORKDIR /home/node/game

# Copy dependency files first for better Docker layer caching
COPY --chown=node:node lakefile.lean lake-manifest.json lean-toolchain ./

# Update dependencies and get cache (this layer will be cached if dependencies don't change)
RUN echo "Updating Lake dependencies..." && lake update -R
RUN echo "Getting mathlib cache (this should speed up build significantly)..." && \
    lake exe cache get --force || echo "Cache get failed, will build from source (slower)"

# Pre-install npm dependencies during Docker build to avoid runtime timeouts
RUN echo "Pre-installing npm dependencies for lean4game..." && \
    cd /home/node/lean4game && npm install

# Now copy the rest of the project
COPY --chown=node:node . .

# Build the project (only this step runs if game files change)
RUN echo "Building Lean project..." && lake build

# Pre-build lean4game server and client to avoid runtime memory issues
RUN echo "Pre-building lean4game server and client..." && \
    cd /home/node/lean4game && \
    npm run build_server && \
    VITE_LEAN4GAME_SINGLE=true VITE_LEAN4GAME_OWNER=local VITE_LEAN4GAME_REPO=game npm run build_client

# Apply port binding fix to relay server
COPY relay-patch.mjs /home/node/lean4game/relay/index.mjs

# Create games directory and link our game for lean4game to find it
RUN mkdir -p /home/node/lean4game/games/local && \
    ln -sf /home/node/game /home/node/lean4game/games/local/game && \
    echo "Verifying symlink was created..." && \
    ls -la /home/node/lean4game/games/local/

EXPOSE 3000

CMD ["/home/node/start-server.sh"]
