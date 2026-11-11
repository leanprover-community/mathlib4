# DownstreamTest

This directory is used for testing that a basic downstream project can be built using mathlib,
and that the mathlib cache works.

There is no `lean-toolchain` file: `Cache/test/downstream.sh` copies it from the main repo,
and runs the cache tests in this project. Its header lists the scenarios.
