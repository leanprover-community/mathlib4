/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Module.Basic

/-!
### Finite support for f • g

This module contains lemmas showing that `f • g` has finite support when `f` or `g` has finite
support (under appropriate assumptions on `•`).

They live in their own file because they need to import `Mathlib.Algebra.Module.Basic`
(for `Function.support_smul_subset_left` and `..._right`), which is not allowed to be imported
by some modules downstream of `Mathlib.Algebra.FiniteSupport.Basic`.
-/

namespace Function

public section SMul

variable {α R M : Type*} [Zero M]

@[to_fun (attr := fun_prop)]
lemma HasFiniteSupport.smul_left [Zero R] [SMulWithZero R M] {f : α → R} (hf : f.HasFiniteSupport)
    (g : α → M) :
    (f • g).HasFiniteSupport :=
  Set.Finite.subset hf fun _ ha ↦ support_smul_subset_left f g ha

@[to_fun (attr := fun_prop)]
lemma HasFiniteSupport.smul_right [SMulZeroClass R M] (f : α → R) {g : α → M}
    (hg : g.HasFiniteSupport) :
    (f • g).HasFiniteSupport :=
  Set.Finite.subset hg fun _ ha ↦ support_smul_subset_right f g ha

end SMul

end Function
