FROM python:3.13-slim

ARG DEBIAN_FRONTEND=noninteractive
ARG APP_VERSION
ENV APP_VERSION=${APP_VERSION}
LABEL version="${APP_VERSION}"

# Environment settings
ENV BASE=/root \
    # REPL_BIN_PATH=/root/repl/.lake/build/bin/repl \
    # PATH_TO_MATHLIB=/root/mathlib4 \
    LOG_LEVEL=INFO \
    MAX_REPLS=4 \
    MAX_USES=10 \
    MAX_MEM=8G \
    INIT_REPLS={"import Mathlib\nimport Aesop":1} \
    LEAN_VERSION=v4.15.0 \
    DATABASE_URL= 


# Update the package list and install dependencies
RUN apt-get update && apt-get install -y ca-certificates \
    curl \
    git \
    build-essential \
    unzip \
    jq \
  && apt-get clean && rm -rf /var/lib/apt/lists/*

# Install Elan + set default Lean version
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain ${LEAN_VERSION} -y
ENV PATH=/root/.elan/bin:$PATH

# Install Lean (first use)
RUN lean --version

# Install REPL
RUN git clone --branch ${LEAN_VERSION} --single-branch --depth 1 https://github.com/leanprover-community/repl.git /root/repl
WORKDIR /root/repl
RUN git checkout ${LEAN_VERSION} && lake build

# Install Mathlib
RUN git clone --branch ${LEAN_VERSION} --single-branch --depth 1 https://github.com/leanprover-community/mathlib4.git /root/mathlib4
WORKDIR /root/mathlib4
RUN git checkout ${LEAN_VERSION} && \
    lake exe cache get && \
    lake build

WORKDIR /root/fast-repl

# Install Astral UV
RUN curl -LsSf https://astral.sh/uv/install.sh | sh
ENV PATH=/root/.local/bin:$PATH

COPY app app
COPY prisma prisma
COPY pyproject.toml pyproject.toml
COPY uv.lock uv.lock

# Needed by uv
COPY README.md README.md 

RUN uv export --no-dev --no-emit-project > requirements.txt
RUN pip install --no-cache-dir -r requirements.txt
RUN pip install --no-cache-dir -e .
RUN prisma generate

EXPOSE 80

CMD ["sh", "-c", "prisma migrate deploy && uvicorn --host 0.0.0.0 --port 80 app.main:app"]
