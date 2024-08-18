# This is the Dockerfile for `leanprovercommunity/mathlib`.
# It is based on the `leanprovercommunity/lean` image.

# This container does not come with a pre-installed version of mathlib;
# you should call `lake exe cache get` which will download the most recent version.
# The only difference between this Dockerfile and leanprovercommunity/lean is that this image
# bypasses a warning that could occur when trying to connect to github for the first time.

FROM leanprovercommunity/lean:debian

# ssh to github once to bypass the unknown fingerprint warning
RUN ssh -o StrictHostKeyChecking=no github.com || true
