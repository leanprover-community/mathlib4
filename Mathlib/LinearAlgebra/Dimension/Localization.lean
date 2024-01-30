/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Module.Submodule.Localization
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rank of localization

## Main statements

- `IsLocalizedModule.lift_rank_eq`: `rank_Rₚ Mₚ = rank R M`.
- `rank_quotient_add_rank_of_isDomain`: The **rank-nullity theorem** for commutative domains.

-/
open Cardinal nonZeroDivisors

section CommRing

universe u u' v v'

variable {R : Type u} (S : Type u') {M : Type v} {N : Type v'}
variable [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N] [Module R M]
variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable (hp : p ≤ R⁰)

lemma IsLocalizedModule.lift_rank_eq :
    Cardinal.lift.{v} (Module.rank S N) = Cardinal.lift.{v'} (Module.rank R M) := by
  cases' subsingleton_or_nontrivial R
  · have := (algebraMap R S).codomain_trivial; simp only [rank_subsingleton, lift_one]
  have := (IsLocalization.injective S hp).nontrivial
  apply le_antisymm
  · rw [Module.rank_def, lift_iSup (bddAbove_range.{v', v'} _)]
    apply ciSup_le'
    intro ⟨s, hs⟩
    choose sec hsec using IsLocalizedModule.surj p f
    refine LinearIndependent.cardinal_lift_le_rank (ι := s) (v := fun i ↦ (sec i).1) ?_
    rw [linearIndependent_iff'] at hs ⊢
    intro t g hg i hit
    apply hp (sec i).2.prop
    apply IsLocalization.injective S hp
    rw [map_zero]
    refine hs t (fun i ↦ algebraMap R S (g i * (sec i).2)) ?_ _ hit
    simp only [map_mul, mul_smul, algebraMap_smul, ← Submonoid.smul_def,
      hsec, ← map_smul, ← map_sum, hg, map_zero]
  · rw [Module.rank_def, lift_iSup (bddAbove_range.{v, v} _)]
    apply ciSup_le'
    intro ⟨s, hs⟩
    choose sec hsec using IsLocalization.surj p (S := S)
    refine LinearIndependent.cardinal_lift_le_rank (ι := s) (v := fun i ↦ f i) ?_
    rw [linearIndependent_iff'] at hs ⊢
    intro t g hg i hit
    apply (IsLocalization.map_units S (sec (g i)).2).mul_left_injective
    classical
    let u := fun (i : s) ↦ (t.erase i).prod (fun j ↦ (sec (g j)).2)
    have : f (t.sum fun i ↦ u i • (sec (g i)).1 • i) = f 0
    · convert congr_arg (t.prod (fun j ↦ (sec (g j)).2) • ·) hg
      · simp only [map_sum, map_smul, Submonoid.smul_def, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [← @IsScalarTower.algebraMap_smul R S N, Submonoid.coe_finset_prod, map_prod]
        rw [← hsec, mul_comm (g j), mul_smul, ← mul_smul, Finset.prod_erase_mul (h := hj)]
      rw [map_zero, smul_zero]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p) this
    simp_rw [smul_zero, Finset.smul_sum, ← mul_smul, Submonoid.smul_def, ← mul_smul, mul_comm] at hc
    simp only [hsec, zero_mul, map_eq_zero_iff (algebraMap R S) (IsLocalization.injective S hp)]
    apply hp (c * u i).prop
    exact hs t _ hc _ hit

lemma IsLocalizedModule.rank_eq {N : Type v} [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[R] N) [IsLocalizedModule p f] :
    Module.rank S N = Module.rank R M := by simpa using IsLocalizedModule.lift_rank_eq S p f hp

/-- The **rank-nullity theorem** for commutative domains. -/
theorem rank_quotient_add_rank_of_isDomain [IsDomain R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' = Module.rank R M := by
  apply lift_injective.{max u v}
  rw [lift_add, ← IsLocalizedModule.lift_rank_eq (FractionRing R) R⁰ (M'.toLocalized R⁰) le_rfl,
    ← IsLocalizedModule.lift_rank_eq (FractionRing R) R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl,
    ← IsLocalizedModule.lift_rank_eq (FractionRing R) R⁰ (M'.toLocalizedQuotient R⁰) le_rfl,
    ← lift_add, rank_quotient_add_rank]

end CommRing
