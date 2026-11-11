# DownstreamTest

This directory is used for testing that a basic downstream project can be built using mathlib,
and that the mathlib cache works.

There is no `lean-toolchain` file, because CI will copy it from the main repo during testing.

`DownstreamTest.Partial` imports Mathlib only through `DownstreamTest.Helper`.
`Cache/test/downstream.sh` uses these modules to test `cache get` with a downstream module.
