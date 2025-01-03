Mathport prelude
===

This directory used to contain instructions for `mathport`,
helping it to translate `mathlib` and align declarations and tactics with `mathlib4`.

If you still need to use mathport, you will need to move back to the `v3-eol` tag of mathlib,
which still contains mathport infrastructure, and migrate your project to that tag,
and then upgrade the rest of the way.

(That tag also contains the final form of `Syntax.lean`,
which implicitly contained a TODO list of unported tactics from Lean 3,
which may still be of some interest.)
