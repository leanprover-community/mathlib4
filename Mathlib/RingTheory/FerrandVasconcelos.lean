/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.GlobalDimension
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Module.SpanRank
/-!

# Ferrand Vasconcelos Theorem

-/

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing CategoryTheory RingTheory.Sequence

local instance [Small.{v} R] (I : Ideal R) : Small.{v} I :=
  small_of_injective I.subtype_injective

lemma quotSMulTop_nontrivial' [IsLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (L : Type*) [AddCommGroup L] [Module R L] [Module.Finite R L] [Nontrivial L] :
    Nontrivial (QuotSMulTop x L) := by
  apply Submodule.Quotient.nontrivial_of_lt_top _ (Ne.lt_top' _)
  apply Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
  exact IsLocalRing.maximalIdeal_le_jacobson _ mem

lemma projectiveDimension_eq_quotient [IsLocalRing R] [IsNoetherianRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] (x : R) (reg1 : IsSMulRegular R x) (reg2 : IsSMulRegular M x)
    (mem : x ∈ maximalIdeal R) : projectiveDimension.{v} M =
    projectiveDimension.{v} (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) := by
  have aux (n : ℕ): projectiveDimension M ≤ n ↔
    projectiveDimension.{v} (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) ≤ n := by
    simp only [projectiveDimension_le_iff]
    induction n generalizing M
    · simp only [HasProjectiveDimensionLE, zero_add, ← hasProjectiveDimensionLT_one_iff]

      sorry
    · rename_i n ih

      sorry
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, projectiveDimension_eq_bot_iff,
      projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun h ↦ (Submodule.Quotient.mk_surjective _).subsingleton, fun h ↦ ?_⟩
    by_contra ntr
    have : Nontrivial M := not_subsingleton_iff_nontrivial.mp ntr
    exact (not_subsingleton_iff_nontrivial.mpr (quotSMulTop_nontrivial' R mem M)) h
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n

lemma exist_isSMulRegular_of_exist_hasProjectiveDimensionLE [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (I : Ideal R) (netop : I ≠ ⊤) (nebot : I ≠ ⊥)
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} I)) n) :
    ∃ x ∈ I, x ∉ maximalIdeal R * I ∧ IsSMulRegular R x := by
  --use prime avoidance to `mI` and associated primes of `R`
  sorry

--IsLocalRing.map_mkQ_eq_top

variable {R}

theorem Ferrand_Vasconcelos_aux [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
    {I : Ideal R} (netop : I ≠ ⊤)
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} I)) n)
    (free : Module.Free (R ⧸ I) I.Cotangent) (n : ℕ) : Submodule.spanFinrank I = n →
    ∃ rs : List R, IsRegular R rs ∧ Ideal.ofList rs = I := by
  induction n generalizing R I
  · intro hrank
    have : I.FG := (isNoetherianRing_iff_ideal_fg R).mp ‹_› I
    have : Submodule.spanRank I = 0 := by
      simp [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr this, hrank]
    simp only [Submodule.spanRank_eq_zero_iff_eq_bot] at this
    use []
    simpa [this] using RingTheory.Sequence.IsRegular.nil R R
  · rename_i n ih _ _ _ _
    intro hrank
    sorry

theorem Ferrand_Vasconcelos [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
    {I : Ideal R} (netop : I ≠ ⊤)
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} I)) n)
    (free : Module.Free (R ⧸ I) I.Cotangent) :
    ∃ rs : List R, IsRegular R rs ∧ Ideal.ofList rs = I :=
  Ferrand_Vasconcelos_aux  netop h free (Submodule.spanFinrank I) rfl
