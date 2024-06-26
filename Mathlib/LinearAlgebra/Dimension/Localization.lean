/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Module.Submodule.Localization
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.OreLocalization.OreSet

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
variable [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable (hp : p ≤ R⁰)

variable {S} in
lemma IsLocalizedModule.linearIndependent_lift {ι} {v : ι → N} (hf : LinearIndependent S v) :
    ∃ w : ι → M, LinearIndependent R w := by
  choose sec hsec using IsLocalizedModule.surj p f
  use fun i ↦ (sec (v i)).1
  rw [linearIndependent_iff'] at hf ⊢
  intro t g hg i hit
  apply hp (sec (v i)).2.prop
  apply IsLocalization.injective S hp
  rw [map_zero]
  refine hf t (fun i ↦ algebraMap R S (g i * (sec (v i)).2)) ?_ _ hit
  simp only [map_mul, mul_smul, algebraMap_smul, ← Submonoid.smul_def,
    hsec, ← map_smul, ← map_sum, hg, map_zero]

lemma IsLocalizedModule.lift_rank_eq :
    Cardinal.lift.{v} (Module.rank S N) = Cardinal.lift.{v'} (Module.rank R M) := by
  cases' subsingleton_or_nontrivial R
  · have := (algebraMap R S).codomain_trivial; simp only [rank_subsingleton, lift_one]
  have := (IsLocalization.injective S hp).nontrivial
  apply le_antisymm
  · rw [Module.rank_def, lift_iSup (bddAbove_range.{v', v'} _)]
    apply ciSup_le'
    intro ⟨s, hs⟩
    exact (IsLocalizedModule.linearIndependent_lift p f hp hs).choose_spec.cardinal_lift_le_rank
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
    have : f (t.sum fun i ↦ u i • (sec (g i)).1 • i) = f 0 := by
      convert congr_arg (t.prod (fun j ↦ (sec (g j)).2) • ·) hg
      · simp only [map_sum, map_smul, Submonoid.smul_def, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [u, ← @IsScalarTower.algebraMap_smul R S N, Submonoid.coe_finset_prod, map_prod]
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

variable (R M) in
theorem exists_set_linearIndependent_of_isDomain [IsDomain R] :
    ∃ s : Set M, #s = Module.rank R M ∧ LinearIndependent (ι := s) R Subtype.val := by
  obtain ⟨w, hw⟩ :=
    IsLocalizedModule.linearIndependent_lift R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl
      (Module.Free.chooseBasis (FractionRing R) (LocalizedModule R⁰ M)).linearIndependent
  refine ⟨Set.range w, ?_, (linearIndependent_subtype_range hw.injective).mpr hw⟩
  apply Cardinal.lift_injective.{max u v}
  rw [Cardinal.mk_range_eq_of_injective hw.injective, ← Module.Free.rank_eq_card_chooseBasisIndex,
  IsLocalizedModule.lift_rank_eq (FractionRing R) R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl]

/-- The **rank-nullity theorem** for commutative domains. Also see `rank_quotient_add_rank`. -/
theorem rank_quotient_add_rank_of_isDomain [IsDomain R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' = Module.rank R M := by
  apply lift_injective.{max u v}
  rw [lift_add, ← IsLocalizedModule.lift_rank_eq (FractionRing R) R⁰ (M'.toLocalized R⁰) le_rfl,
    ← IsLocalizedModule.lift_rank_eq (FractionRing R) R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl,
    ← IsLocalizedModule.lift_rank_eq (FractionRing R) R⁰ (M'.toLocalizedQuotient R⁰) le_rfl,
    ← lift_add, rank_quotient_add_rank_of_divisionRing]

universe w in
instance IsDomain.hasRankNullity [IsDomain R] : HasRankNullity.{w} R where
  rank_quotient_add_rank := rank_quotient_add_rank_of_isDomain
  exists_set_linearIndependent M := exists_set_linearIndependent_of_isDomain R M

end CommRing

section Ring

variable {R} [Ring R] [IsDomain R] (S : Submonoid R)

/-- A domain that is not (left) Ore is of infinite rank.
See [cohn_1995] Proposition 1.3.6 -/
lemma aleph0_le_rank_of_isEmpty_oreSet (hS : IsEmpty (OreLocalization.OreSet R⁰)) :
    ℵ₀ ≤ Module.rank R R := by
  classical
  rw [← not_nonempty_iff, OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors] at hS
  push_neg at hS
  obtain ⟨r, s, h⟩ := hS
  refine Cardinal.aleph0_le.mpr fun n ↦ ?_
  suffices LinearIndependent R (fun (i : Fin n) ↦ r * s ^ (i : ℕ)) by
    simpa using this.cardinal_lift_le_rank
  suffices ∀ (g : ℕ → R) (x), (∑ i ∈ Finset.range n, g i • (r * s ^ (i + x))) = 0 →
      ∀ i < n, g i = 0 by
    refine Fintype.linearIndependent_iff.mpr fun g hg i ↦ ?_
    simpa only [dif_pos i.prop] using this (fun i ↦ if h : i < n then g ⟨i, h⟩ else 0) 0
      (by simp [← Fin.sum_univ_eq_sum_range, ← hg]) i i.prop
  intro g x hg i hin
  induction' n with n IH generalizing g x i
  · exact (hin.not_le (zero_le i)).elim
  · rw [Finset.sum_range_succ'] at hg
    by_cases hg0 : g 0 = 0
    · simp only [hg0, zero_smul, add_zero, add_assoc] at hg
      cases i; exacts [hg0, IH _ _ hg _ (Nat.succ_lt_succ_iff.mp hin)]
    simp only [MulOpposite.smul_eq_mul_unop, zero_add, ← add_comm _ x, pow_add _ _ x,
      ← mul_assoc, pow_succ, ← Finset.sum_mul, pow_zero, one_mul, smul_eq_mul] at hg
    rw [← neg_eq_iff_add_eq_zero, ← neg_mul, ← neg_mul] at hg
    have := mul_right_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp (s ^ x).prop) hg
    exact (h _ ⟨(g 0), mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa)⟩ this.symm).elim

-- TODO: Upgrade this to an iff. See [lam_1999] Exercise 10.21
lemma nonempty_oreSet_of_strongRankCondition [StrongRankCondition R] :
    Nonempty (OreLocalization.OreSet R⁰) := by
  by_contra h
  have := aleph0_le_rank_of_isEmpty_oreSet (not_nonempty_iff.mp h)
  rw [rank_self] at this
  exact this.not_lt one_lt_aleph0

end Ring
