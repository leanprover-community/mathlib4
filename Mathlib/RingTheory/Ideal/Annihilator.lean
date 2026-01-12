/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Exact
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs

/-!

# Annihilator Ideals

We provide the definition and related lemmas about annihilator ideals.

## Main definition
- `Submodule.ann I x`: The ideal of all `y` such that `y • x ∈ I`.

-/

@[expose] public section

namespace Submodule

open Ideal Submodule

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (I J : Submodule R M) (r : R) (m : M)

/-- The ideal of all `r` such that `r • m ∈ I`. -/
def ann : Ideal R where
  carrier := {r | r • m ∈ I}
  add_mem' ha hb := by simp [add_smul, I.add_mem ha hb]
  zero_mem' := by simp
  smul_mem' a b hb := by simp [mul_smul, I.smul_mem a hb]

variable {N r m} in
theorem mem_ann_iff : r ∈ I.ann m ↔ r • m ∈ I :=
  Iff.rfl

variable {I J} in
theorem ann_mono (h : I ≤ J) : I.ann m ≤ J.ann m :=
  fun _ hr ↦ h hr

variable {I} in
theorem ann_eq_top : I.ann m = ⊤ ↔ m ∈ I := by
  rw [eq_top_iff_one, mem_ann_iff, one_smul]

theorem colon_top_le : I.colon ⊤ ≤ I.ann m :=
  fun r hr ↦ mem_colon.mp hr m mem_top

end Semiring

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {I : Submodule R M} {m : M}

theorem IsPrimary.radical_ann_of_notMem (hI : I.IsPrimary) (hm : m ∉ I) :
    (I.ann m).radical = (I.colon ⊤).radical :=
  le_antisymm (radical_le_radical_iff.mpr fun y hy ↦ (hI.2 hy).resolve_left hm)
    (radical_mono (colon_top_le I m))

end CommSemiring

end Submodule
