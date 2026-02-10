# This is the Dockerfile for `leanprovercommunity/lean4`.
# It is based on the generic `debian` image, and installs `elan` and the current stable version of `lean`.

# This container does not come with a pre-installed version of mathlib;
# you should call `lake exe cache get` which will download the most recent version.
# The only difference between this Dockerfile and leanprovercommunity/lean4 is that this image
# bypasses a warning that could occur when trying to connect to github for the first time.

# NOTE: to run this docker image on macos or windows,
# you will need to increase the allowed memory (in the docker GUI) beyond 2GB

FROM debian
USER root
# install prerequisites
RUN apt-get update && apt-get install curl git -y && apt-get clean
# create a non-root user
RUN useradd -m lean

USER lean
WORKDIR /home/lean

SHELL ["/bin/bash", "-c"]
# set the entrypoint to be a login shell, so everything is on the PATH
ENTRYPOINT ["/bin/bash", "-l"]

# make sure binaries are available even in non-login shells
ENV PATH="/home/lean/.elan/bin:/home/lean/.local/bin:$PATH"

# install elan
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none && \
    . ~/.profile && \
    elan toolchain install $(curl https://raw.githubusercontent.com/leanprover-community/mathlib/master/leanpkg.toml | grep lean_version | awk -F'"' '{print $2}') && \
    elan default stable

# ssh to github once to bypass the unknown fingerprint warning
RUN ssh -o StrictHostKeyChecking=no github.com || true
