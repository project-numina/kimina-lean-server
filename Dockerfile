FROM python:3.13-slim

ARG APP_VERSION=2.0.0
ARG LEAN_SERVER_LEAN_VERSION=v4.26.0
ARG REPL_REPO_URL=https://github.com/FrederickPu/repl.git
ARG REPL_BRANCH=lean415compat
ARG MATHLIB_REPO_URL=https://github.com/leanprover-community/mathlib4.git
ARG MATHLIB_BRANCH=${LEAN_SERVER_LEAN_VERSION}

LABEL version="${APP_VERSION}"

# Override with docker compose / docker run -e
ENV LEAN_SERVER_LEAN_VERSION=${LEAN_SERVER_LEAN_VERSION} \
    LEAN_SERVER_HOST=0.0.0.0 \
    LEAN_SERVER_PORT=8000 \
    LEAN_SERVER_LOG_LEVEL=INFO \
    LEAN_SERVER_ENVIRONMENT=prod \
    LEAN_SERVER_LEAN_VERSION=${LEAN_SERVER_LEAN_VERSION} \
    LEAN_SERVER_REPL_PATH=/repl/.lake/build/bin/repl \
    LEAN_SERVER_PROJECT_DIR=/mathlib4 \
    LEAN_SERVER_MAX_REPLS= \
    LEAN_SERVER_MAX_REPL_USES=-1 \
    LEAN_SERVER_MAX_REPL_MEM=8G \
    LEAN_SERVER_MAX_WAIT=60 \
    LEAN_SERVER_INIT_REPLS={}
    # LEAN_SERVER_API_KEY is provided at runtime via docker-compose (.env) or -e

RUN apt-get update && apt-get install -y \
      ca-certificates curl git build-essential unzip jq \
    && apt-get clean && rm -rf /var/lib/apt/lists/*

COPY setup.sh /usr/local/bin/
RUN chmod +x /usr/local/bin/setup.sh \
 && /usr/local/bin/setup.sh

ENV PATH=/root/.elan/bin:/root/.local/bin:$PATH

WORKDIR /root/kimina-lean-server

RUN curl -LsSf https://astral.sh/uv/install.sh | sh

COPY server server
COPY client client
COPY pyproject.toml uv.lock README-client.md ./

RUN uv export --extra server --no-dev --no-emit-project > requirements.txt \
 && pip install --no-cache-dir -r requirements.txt \
 && pip install --no-cache-dir -e .

EXPOSE ${LEAN_SERVER_PORT}


CMD ["python", "-m", "server"]
