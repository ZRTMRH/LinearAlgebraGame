FROM node:20

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

# Build lean4game production bundle during Docker build to avoid runtime timeouts
RUN echo "Building lean4game production bundle..." && \
    cd /home/node/lean4game && \
    npm run build_server && \
    npm run build_relay && \
    npm run build_client

EXPOSE 3000

CMD ["/home/node/start-server.sh"]
