FROM python:3.13-slim

ARG APP_VERSION
ARG LEAN_SERVER_LEAN_VERSION=v4.15.0
ARG REPL_VERSION=${LEAN_SERVER_LEAN_VERSION}
ARG MATHLIB_VERSION=${LEAN_SERVER_LEAN_VERSION}

LABEL version="${APP_VERSION}"

# Override with docker compose / docker run -e
ENV APP_VERSION=${APP_VERSION} \
    LEAN_SERVER_LEAN_VERSION=${LEAN_SERVER_LEAN_VERSION} \
    REPL_VERSION=${REPL_VERSION} \
    MATHLIB_VERSION=${MATHLIB_VERSION} \
    LEAN_SERVER_HOST=0.0.0.0 \
    LEAN_SERVER_PORT=8000 \
    # LEAN_SERVER_API_KEY is provided at runtime via docker-compose (.env) or -e
    LEAN_SERVER_LOG_LEVEL=INFO \
    LEAN_SERVER_ENVIRONMENT=prod \
    LEAN_SERVER_LEAN_VERSION=${LEAN_SERVER_LEAN_VERSION} \
    LEAN_SERVER_REPL_PATH=/root/repl/.lake/build/bin/repl \
    LEAN_SERVER_PROJECT_DIR=/root/mathlib4 \
    LEAN_SERVER_MAX_REPLS= \
    LEAN_SERVER_MAX_REPL_USES=-1 \
    LEAN_SERVER_MAX_REPL_MEM=8G \
    LEAN_SERVER_MAX_WAIT=60 \
    LEAN_SERVER_INIT_REPLS={} \
    LEAN_SERVER_DATABASE_URL=

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
COPY prisma prisma
COPY pyproject.toml uv.lock README-client.md ./

RUN uv export --no-dev --no-emit-project > requirements.txt \
 && pip install --no-cache-dir -r requirements.txt \
 && pip install --no-cache-dir -e . \
 && prisma generate

EXPOSE ${LEAN_SERVER_PORT}


CMD ["python", "-m", "server"]
