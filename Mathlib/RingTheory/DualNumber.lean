/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Algebraic properties of dual numbers

## Main results

* `DualNumber.instLocalRing`
The dual numbers over a field `K` form a local ring.

-/

namespace DualNumber

lemma isNilpotent_inr {R : Type*} [Semiring R] (r : R) :
    IsNilpotent (.inr r : R[ε]) :=
  ⟨2, by rw [pow_two, inr_eq_smul_eps]; ext <;> simp⟩

lemma isNilpotent_eps {R : Type*} [Semiring R] :
    IsNilpotent (ε : R[ε]) :=
  isNilpotent_inr 1

section Field

variable {K : Type*} [Field K]

lemma isUnit_fst {r : K} (hr : r ≠ 0) :
    IsUnit (.inl r : K[ε]) :=
  hr.isUnit.map (TrivSqZeroExt.inlAlgHom K K K)

lemma isUnit_or_isNilpotent (a : K[ε]) : IsUnit a ∨ IsNilpotent a := by
  by_cases ha : a.fst = 0
  · refine Or.inr ⟨2, ?_⟩
    ext <;> simp [ha]
  · refine Or.inl ?_
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]
    exact (isNilpotent_inr _).isUnit_add_left_of_commute (isUnit_fst ha) (.all _ _)

instance instLocalRing : LocalRing K[ε] where
  isUnit_or_isUnit_of_add_one := by
    intro a b h
    refine (isUnit_or_isNilpotent _).imp_right fun h' ↦ ?_
    rw [add_comm, eq_comm, ← sub_eq_iff_eq_add] at h
    rw [← h]
    exact h'.isUnit_one_sub

end Field

end DualNumber
