Mathport prelude
===

This directory contains instructions for `mathport`,
helping it to translate `mathlib` and align declarations and tactics with `mathlib4`.
(These files were formerly part of `mathport`, in the directory `Mathport/Prelude/`.)

`SpecialNames.lean`
: Contains `#align X Y` statements, where `X` is an identifier from mathlib3
  which should be aligned with the identifier `Y` from mathlib4.
  Sometimes we need `#align` statements just to handle exceptions to casing rules,
  but there are also many exceptional cases.

`Syntax.lean`
: Contains unimplented stubs of tactics which need to be migrated from Lean3 to Lean4.
