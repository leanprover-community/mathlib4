FROM mcr.microsoft.com/devcontainers/base:jammy

USER vscode
WORKDIR /home/vscode

RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

ENV PATH="/home/vscode/.elan/bin:${PATH}"
