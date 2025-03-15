/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Andrew Yang
-/
import Mathlib.RingTheory.FiniteLength
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Main results

* `Module.length_eq_rank_of_field`: For a module over a field, its length is equal to its rank.
-/

variable (R M : Type*) [Field R] [AddCommGroup M] [Module R M]

/-- For a module over a field, its length is equal to its rank. -/
theorem Module.length_eq_rank_of_field : Module.length R M = (Module.rank R M).toENat := by
  by_cases h : IsArtinian R M
  · have h' : IsFiniteLength R M :=
      ((IsSemisimpleModule.finite_tfae (R := R) (M := M)).out 2 3).mp h
    induction h'
    case pos.of_subsingleton M _ _ h_triv =>
      rwa [rank_subsingleton', map_zero, WithBot.coe_zero, Module.length_eq_zero_iff]
    case pos.of_simple_quotient M _ _ N hN h_fin h' =>
      specialize h' (isFiniteLength_iff_isNoetherian_isArtinian.mp h_fin).2
      have : Module.rank R (M ⧸ N) = 1 := by
        rwa [rank_eq_one_iff_finrank_eq_one, ← isSimpleModule_iff_finrank_eq_one]
      rw [Module.length_additive_of_quotient (N := N), h', isSimpleModule_length_eq_one,
      ← rank_quotient_add_rank_of_divisionRing N, ← WithBot.coe_one, ← WithBot.coe_add,
      WithBot.coe_inj, map_add, this, map_one, add_comm]
  · have : ¬ IsNoetherian R M := fun H ↦ (h inferInstance)
    rw [IsNoetherian.iff_rank_lt_aleph0] at this
    rw [Cardinal.toENat_eq_top.mpr (le_of_not_lt this), WithBot.coe_top]
    contrapose h
    rw [← ne_eq, ← isFiniteLength_iff_length_finite R M] at h
    exact not_not.mpr <| (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2
