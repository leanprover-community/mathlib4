# mathlib4

Work in progress mathlib port for Lean 4.
This is not a port.
We are just trying things out
to gain experience for
the real port.

We're not planning
to have any review standards
in the mathlib4 repo
higher than your average wiki
during this experimentation phase.

We don't want to discourage others from trying to port stuff if it helps us learn how to work in lean 4,
but please understand that anything that is currently in mathlib4 is subject to change/deletion,
and the "real" port hasn't started yet

# Build instructions

* Get the newest version of `elan`. If you already have installed a version of Lean, you can run
  ```
  elan self update
  ```
  If the above command fails, or if you need to install `elan`, run
  ```
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```
  If this also fails, follow the instructions under `Regular install` [here](https://leanprover-community.github.io/get_started.html).
* To build `mathlib4` run `lake build`. To build and run all tests, run `make`.
* If you added a new file, run the following command to update `Mathlib.lean`
  ```
  find Mathlib -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Mathlib.lean
  ```
