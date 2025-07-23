FROM python:3.13-slim

ARG DEBIAN_FRONTEND=noninteractive
ARG APP_VERSION
ENV APP_VERSION=${APP_VERSION}
LABEL version="${APP_VERSION}"

# Environment settings -- to update
ENV LEAN_SERVER_PORT=80 \
    LEAN_SERVER_ENVIRONMENT=production \
    LEAN_SERVER_LOG_LEVEL=INFO \
    LEAN_SERVER_LEAN_VERSION=v4.15.0 \
    LEAN_SERVER_MAX_REPLS= \
    LEAN_SERVER_MAX_REPL_USES=100 \
    LEAN_SERVER_MAX_REPL_MEM=8G \
    LEAN_SERVER_INIT_REPLS= \
    LEAN_SERVER_REPL_PATH=/root/repl/.lake/build/bin/repl \
    LEAN_SERVER_PROJECT_DIR=/root/mathlib4 \
    LEAN_SERVER_DATABASE_URL= 


# Update the package list and install dependencies
RUN apt-get update && apt-get install -y ca-certificates \
    curl \
    git \
    build-essential \
    unzip \
    jq \
  && apt-get clean && rm -rf /var/lib/apt/lists/*

# Install Elan + set default Lean version
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain ${LEAN_SERVER_LEAN_VERSION} -y
ENV PATH=/root/.elan/bin:$PATH

# Install Lean (first use)
RUN lean --version

# Install REPL
RUN git clone --branch ${LEAN_SERVER_LEAN_VERSION} --single-branch --depth 1 https://github.com/leanprover-community/repl.git /root/repl
WORKDIR /root/repl
RUN git checkout ${LEAN_SERVER_LEAN_VERSION} && lake build

# Install Mathlib
RUN git clone --branch ${LEAN_SERVER_LEAN_VERSION} --single-branch --depth 1 https://github.com/leanprover-community/mathlib4.git /root/mathlib4
WORKDIR /root/mathlib4
RUN git checkout ${LEAN_SERVER_LEAN_VERSION} && \
    lake exe cache get && \
    lake build

WORKDIR /root/kimina-lean-server

# Install Astral UV
RUN curl -LsSf https://astral.sh/uv/install.sh | sh
ENV PATH=/root/.local/bin:$PATH

COPY server server
COPY client client
COPY prisma prisma
COPY pyproject.toml pyproject.toml
COPY uv.lock uv.lock

# Needed by uv
COPY README-client.md README-client.md 

RUN uv export --no-dev --no-emit-project > requirements.txt
RUN pip install --no-cache-dir -r requirements.txt
RUN pip install --no-cache-dir -e .
RUN prisma generate

EXPOSE 80

# TODO: add back prisma migrate deploy later + use entry point
CMD ["uv", "run", "python", "-m", "server"]
