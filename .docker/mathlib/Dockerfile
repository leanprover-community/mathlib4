# This is the Dockerfile for `leanprovercommunity/mathlib`.
# It is based on the `leanprovercommunity/lean` image.
# This Dockerfile doesn't contain a copy of mathlib;
# you should call `lake exe cache get` which will download the most recent version.

FROM leanprovercommunity/lean:debian

# ssh to github once to bypass the unknown fingerprint warning
RUN ssh -o StrictHostKeyChecking=no github.com || true
