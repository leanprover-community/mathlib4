/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Power Series over Regular Local Ring


-/

variable {R : Type*} [CommRing R]

open PowerSeries IsLocalRing

set_option backward.isDefEq.respectTransparency false in
lemma PowerSeries.maximalIdeal_eq_sup [IsLocalRing R] : maximalIdeal R⟦X⟧ =
    (maximalIdeal R).map PowerSeries.C ⊔ Ideal.span {X} := by
  have maxeq : maximalIdeal R⟦X⟧ = (maximalIdeal R).comap constantCoeff := by
    ext
    simp only [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]
    rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← Ideal.mem_comap]
  have eqker : RingHom.ker (constantCoeff (R := R)) = Ideal.span {X} := by
    ext g
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have := PowerSeries.sub_const_eq_shift_mul_X g
      simp only [RingHom.mem_ker.mp h, map_zero, sub_zero] at this
      rw [this, Ideal.mem_span_singleton']
      use (mk fun p ↦ (coeff (p + 1)) g)
    · rcases Ideal.mem_span_singleton'.mp h with ⟨w, hw⟩
      simp [← hw]
  rw [maxeq, ← eqker, ← Ideal.comap_map_of_surjective' _ PowerSeries.constantCoeff_surj,
    Ideal.map_map, constantCoeff_comp_C, Ideal.map_id]

set_option backward.isDefEq.respectTransparency false in
lemma PowerSeries.isRegularLocalRing_of_isRegularLocalRing [IsRegularLocalRing R] :
    IsRegularLocalRing R⟦X⟧ := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  apply le_trans _ ringKrullDim_succ_le_ringKrullDim_powerseries
  rw [← (isRegularLocalRing_def R).mp ‹_›, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
  have maxeq : maximalIdeal R⟦X⟧ = Ideal.span ((C '' (maximalIdeal R).generators) ∪ {X}) := by
    rw [Ideal.span_union, ← Ideal.map_span, ← Ideal.submodule_span_eq,
      (maximalIdeal R).span_generators, PowerSeries.maximalIdeal_eq_sup]
  rw [maxeq]
  have fin' := Submodule.FG.finite_generators (maximalIdeal R).fg_of_isNoetherianRing
  have fin : (C '' (maximalIdeal R).generators).Finite := fin'.image _
  apply (Submodule.spanFinrank_span_le_ncard_of_finite (fin.union (Set.finite_singleton X))).trans
    ((Set.ncard_union_le _ _).trans _)
  simp only [Set.ncard_singleton, add_le_add_iff_right]
  exact le_of_le_of_eq (Set.ncard_image_le fin')
    (Submodule.FG.generators_ncard (maximalIdeal R).fg_of_isNoetherianRing)

lemma MvPowerSeries.isRegularLocalRing_of_isRegularLocalRing [IsRegularLocalRing R]
    {ι : Type*} [Finite ι] : IsRegularLocalRing (MvPowerSeries ι R) := by
  sorry
