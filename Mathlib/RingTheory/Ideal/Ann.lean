/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.IsPrimary

/-!
# Annihilator Ideals

We provide the definition and related lemmas about annihilator ideals `ann m`.

## Main definition

- `Submodule.ann I m`: The ideal of all `r` such that `r • m ∈ I`.

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

variable {I r m} in
theorem mem_ann_iff : r ∈ I.ann m ↔ r • m ∈ I :=
  .rfl

variable {I J} in
theorem ann_mono (h : I ≤ J) : I.ann m ≤ J.ann m :=
  fun _ hr ↦ h hr

variable {I m} in
theorem ann_eq_top : I.ann m = ⊤ ↔ m ∈ I := by
  rw [eq_top_iff_one, mem_ann_iff, one_smul]

theorem ann_inf : (I ⊓ J).ann m = I.ann m ⊓ J.ann m :=
  rfl

theorem ann_iInf {ι : Type*} (f : ι → Submodule R M) : (⨅ i, f i).ann m = ⨅ i, (f i).ann m := by
  simp [Submodule.ext_iff, mem_ann_iff]

theorem ann_finset_inf {ι : Type*} (s : Finset ι) (f : ι → Submodule R M) :
    (s.inf f).ann m = s.inf (fun i ↦ (f i).ann m) := by
  simp [Submodule.ext_iff, mem_ann_iff]

theorem colon_top_le_ann : I.colon ⊤ ≤ I.ann m :=
  fun _ hr ↦ mem_colon.mp hr m mem_top

end Semiring

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {I : Submodule R M} {m : M}

theorem IsPrimary.radical_ann_of_notMem (hI : I.IsPrimary) (hm : m ∉ I) :
    (I.ann m).radical = (I.colon ⊤).radical :=
  le_antisymm (radical_le_radical_iff.mpr fun _ hy ↦ (hI.2 hy).resolve_left hm)
    (radical_mono (colon_top_le_ann I m))

end CommSemiring

end Submodule
