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

open Ideal

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (I J : Submodule R M) (r : R) (m : M)

/-- The ideal of all `r` such that `r • m ∈ I`. -/
def ann : Ideal R where
  carrier := {r | r • m ∈ I}
  add_mem' ha hb := by simp [add_smul, I.add_mem ha hb]
  zero_mem' := by simp
  smul_mem' a b hb := by simp [← smul_smul, I.smul_mem a hb]

variable {I r m} in
theorem mem_ann_iff : r ∈ I.ann m ↔ r • m ∈ I :=
  Iff.rfl

variable {I J} in
theorem ann_mono (h : I ≤ J) : I.ann m ≤ J.ann m :=
  fun _ hr ↦ h hr

variable {I m} in
theorem ann_eq_top : I.ann m = ⊤ ↔ m ∈ I := by
  rw [eq_top_iff_one, mem_ann_iff, one_smul]

theorem _root_.Ideal.ann_le (I : Ideal R) [I.IsTwoSided] (r : R) : I ≤ I.ann r :=
  fun _ ↦ I.mul_mem_right r

theorem ann_inf : (I ⊓ J).ann m = I.ann m ⊓ J.ann m :=
  rfl

-- various other inf lemmas

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R] (I J : Ideal R) (x y : R)

variable {I x} in
theorem IsPrimary.radical_ann_of_notMem (hI : I.IsPrimary) (hx : x ∉ I) :
    (I.ann x).radical = I.radical := by
  refine le_antisymm (radical_le_radical_iff.mpr fun y hy ↦ ?_) (radical_mono (I.ann_le x))
  rw [mem_ann_iff, smul_eq_mul, mul_comm] at hy
  exact ((isPrimary_iff.mp hI).2 hy).resolve_left hx

variable {I x} in
theorem IsPrimary.ann_of_notMem_radical (hI : IsPrimary I) (hx : x ∉ I.radical) :
    (I.ann x) = I := by
  refine le_antisymm ?_ (I.ann_le x)
  intro y hy
  exact ((isPrimary_iff.mp hI).2 hy).resolve_right hx

end CommSemiring

end Submodule
