FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    ca-certificates \
    git \
    build-essential \
    sudo \
    python3 \
    && rm -rf /var/lib/apt/lists/*

# Create vscode user
RUN groupadd -g 1000 vscode \
    && useradd -m -u 1000 -g 1000 -s /bin/bash vscode \
    && echo "vscode ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers

# Install elan (Lean version manager) system-wide
ENV ELAN_HOME=/usr/local/elan \
    PATH=/usr/local/elan/bin:$PATH

RUN mkdir -p $ELAN_HOME && chmod 777 $ELAN_HOME \
    && curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | sh -s -- -y --no-modify-path --default-toolchain none \
    && chmod -R a+w $ELAN_HOME

# Install Node.js 20 (for Claude Code)
RUN curl -fsSL https://deb.nodesource.com/setup_20.x | bash - \
    && apt-get install -y nodejs \
    && rm -rf /var/lib/apt/lists/*

# Install Claude Code
RUN npm install -g @anthropic-ai/claude-code

USER vscode
WORKDIR /workspace
