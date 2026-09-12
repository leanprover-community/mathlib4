/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

module

public import Batteries.Util.LibraryNote
public import Mathlib.Init

/-! # Simp Lemmas With Weak Keys Library Note

This file contains a library note explaining how to handle `simp` lemmas that have "weak keys".

-/

@[expose] public section

library_note «Simp lemmas with weak keys» /--
Certain theorems shouldn't be tagged with the `simp` attribute as they have "weak keys", i.e. they
match on certain patterns that occur much more often than the lemmas are actually applicable.
This is harmful as it affects the performance of the `simp` tactic.
As a replacement, one can use `scoped simp` with an appropriate namespace.
See also the following PRs:
- https://github.com/leanprover-community/mathlib4/pull/15620
- https://github.com/leanprover-community/mathlib4/pull/15631
-/
