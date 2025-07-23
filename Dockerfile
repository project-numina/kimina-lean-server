FROM python:3.11-slim 

ARG LEAN_VERSION=v4.15.0
ENV LEAN_VERSION=${LEAN_VERSION}
ENV DEBIAN_FRONTEND=noninteractive

# Update the package list and install dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    unzip \
    jq \
    && apt-get clean && rm -rf /var/lib/apt/lists/*

# Install Lean
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain ${LEAN_VERSION} -y
ENV PATH=/root/.elan/bin:$PATH

# Install REPL
RUN git clone https://github.com/FrederickPu/repl.git /root/repl
COPY loadDynlib.py /root/loadDynlib.py
WORKDIR /root/repl
RUN git checkout lean415compat && python ../loadDynlib.py && lake build

# Install LeanGeo
# TODO :: change to use git clone once LeanGeo repo is public
COPY LeanGeo /root/LeanGeo
# RUN git clone https://github.com/leanprover-community/mathlib4.git /root/mathlib4
WORKDIR /root/LeanGeo
RUN lake run cvc5/downloadRelease && \
    lake script run check && \
    lake exe cache get && \
    lake build && \
    lake build LeanGeo

WORKDIR /root

COPY requirements.txt .
RUN pip3 install --no-cache-dir --upgrade pip
RUN pip3 install --no-cache-dir -r requirements.txt

COPY server/ ./server
COPY utils/ ./utils

RUN mkdir -p /root/logs

RUN echo "Lean version: ${LEAN_VERSION}" > /root/version_info.txt

CMD ["python", "-m", "server"]