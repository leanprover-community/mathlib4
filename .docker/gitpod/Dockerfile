# This is the Dockerfile for `leanprovercommunity/mathlib:gitpod`.

# gitpod doesn't support multiple FROM statements, (or rather, you can't copy from one to another)
# so we just install everything in one go
FROM ubuntu:jammy

USER root

RUN apt-get update && apt-get install git curl git -y && apt-get clean

RUN useradd -l -u 33333 -G sudo -md /home/gitpod -s /bin/bash -p gitpod gitpod
USER gitpod
WORKDIR /home/gitpod

SHELL ["/bin/bash", "-c"]

# install elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

# install whichever toolchain mathlib is currently using
RUN . ~/.profile && elan toolchain install $(curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain)

ENV PATH="/home/gitpod/.local/bin:/home/gitpod/.elan/bin:${PATH}"

# fix the infoview when the container is used on gitpod:
ENV VSCODE_API_VERSION="1.50.0"

# ssh to github once to bypass the unknown fingerprint warning
RUN ssh -o StrictHostKeyChecking=no github.com || true
