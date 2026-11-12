# DownstreamTest

This directory is used for testing that a basic downstream project can be built using mathlib,
and that the mathlib cache works.

This directory has no `lean-toolchain` file. `Cache/test/downstream.sh` copies the file from
the Mathlib checkout and runs the cache tests here. The header of the script lists the scenarios.
