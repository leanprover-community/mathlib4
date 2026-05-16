/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Data.Fintype.Order

/-!
# Results on order homomorphism classes and lattice operations
-/

public lemma Finite.iSup_eq_iSup_subtype {ι K M F : Type*} [Finite ι] [Zero K] [Zero M]
    [ConditionallyCompleteLattice M] [FunLike F K M] [ZeroHomClass F K M] [NonnegHomClass F K M]
    {x : ι → K} (hx : x ≠ 0) {v : F} :
    ⨆ i, v (x i) =  ⨆ i : {j // x j ≠ 0}, v (x i) := by
  obtain ⟨i, hi⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty {j // x j ≠ 0} := .intro ⟨i, hi⟩
  have : Nonempty ι := .intro i
  refine le_antisymm ?_ <| ciSup_le fun ⟨j, hj⟩ ↦ le_ciSup_of_le j le_rfl
  refine ciSup_le fun j ↦ ?_
  rcases eq_or_ne (x j) 0 with h | h
  · rw [h, map_zero]
    exact le_ciSup_of_le ⟨i, hi⟩ (NonnegHomClass.apply_nonneg ..)
  · exact le_ciSup_of_le ⟨j, h⟩ le_rfl
