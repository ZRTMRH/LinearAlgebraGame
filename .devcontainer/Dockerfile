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
RUN git clone https://github.com/leanprover-community/lean4game.git --branch v4.28.0 /home/node/lean4game && \
    chown -R node:node /home/node/lean4game

# Pre-install npm dependencies during Docker build (npm workspaces: installs client + relay)
RUN echo "Pre-installing npm dependencies for lean4game..." && \
    cd /home/node/lean4game && npm install

# Now copy the rest of the project
COPY --chown=node:node . .

# Build the project (only this step runs if game files change)
RUN echo "Building Lean project..." && lake build

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
