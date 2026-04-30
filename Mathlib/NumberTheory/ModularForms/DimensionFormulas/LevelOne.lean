/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Dimension formula for level 1 modular forms

This file proves the dimension formula for the space of modular forms for `𝒮ℒ` (= `SL(2, ℤ)`)
of even weight.

## Main results

* `CuspForm.discriminantEquiv`: `CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)`.
* `ModularForm.rank_eq_one_add_rank_cuspForm`: `rank M_k = 1 + rank S_k` for even `k ≥ 3`.
* `ModularForm.dimension_level_one`: the full dimension formula for all even `k : ℕ`.
* `ModularForm.levelOne_odd_weight_rank_zero`: modular forms of odd weight are zero.
* A `FiniteDimensional ℂ (ModularForm 𝒮ℒ k)` instance for every `k : ℤ`.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm SlashInvariantForm SlashInvariantFormClass ModularFormClass
  CuspFormClass MatrixGroups OnePoint Filter EisensteinSeries Asymptotics

open scoped Topology

section DeltaIsomorphism

variable {k : ℤ}

local notation "Δ" => ModularForm.discriminant

namespace CuspForm

/-- Multiply a modular form of weight `k - 12` by the discriminant to get a cusp form of
weight `k`. Built directly as a `CuspForm` via `CuspForm.mulModularForm`. -/
def ofMulDiscriminant (f : ModularForm 𝒮ℒ (k - 12)) : CuspForm 𝒮ℒ k :=
  CuspForm.mcast (by ring) (CuspForm.discriminant.mulModularForm f)

@[simp]
lemma ofMulDiscriminant_apply (f : ModularForm 𝒮ℒ (k - 12)) (z : ℍ) :
    (ofMulDiscriminant f) z = Δ z * f z := rfl

private lemma divByDiscriminant_slash_eq (f : CuspForm 𝒮ℒ k) (γ : SL(2, ℤ)) :
    (fun z ↦ f z / Δ z) ∣[k - 12] γ = fun z ↦ f z / Δ z := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  change (⇑f / ⇑CuspForm.discriminant) ∣[k - 12] γ = ⇑f / ⇑CuspForm.discriminant
  simp_rw [div_slash_SL2, SL_slash, slash_action_eqn _ _ hγ]

/-- Divide a cusp form by the discriminant to get a modular form of weight `k - 12`. -/
@[no_expose] def divDiscriminant (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k - 12) where
  toFun z := f z / Δ z
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ divByDiscriminant_slash_eq f γ
  holo' := f.holo'.div CuspForm.discriminant.holo' discriminant_ne_zero
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [divByDiscriminant_slash_eq f γ, IsBoundedAtImInfty, BoundedAtFilter]
    exact (div_isBoundedUnder_of_isBigO (exp_decay_isBigO_discriminant f)).isBigO_one ℝ

@[simp]
lemma divDiscriminant_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    (divDiscriminant f) z = f z / Δ z := (rfl)

/-- The linear equivalence between cusp forms of weight `k` and modular forms of weight `k - 12`,
given by division by the discriminant. -/
def discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12) where
  toFun := divDiscriminant
  map_add' a b := by
    ext z
    simp [add_div]
  map_smul' c a := by
    ext z
    simp [mul_div_assoc]
  invFun := ofMulDiscriminant
  left_inv f := by
    ext z
    exact mul_div_cancel₀ (f z) (discriminant_ne_zero z)
  right_inv f := by
    ext z
    exact mul_div_cancel_left₀ (f z) (discriminant_ne_zero z)

end CuspForm

end DeltaIsomorphism

section RankIdentity

variable {k : ℤ}

/-- A `𝒮ℒ` modular form of odd weight is zero (evaluate at `-1 ∈ SL(2, ℤ)`). -/
lemma ModularForm.levelOne_odd_weight_eq_zero (hk : Odd k) (f : ModularForm 𝒮ℒ k) : f = 0 :=
  ModularForm.eq_zero_of_neg_one_mem (show (-1 : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨-1, by ext; simp⟩) hk f

/-- Modular forms of odd weight for `𝒮ℒ` are zero-dimensional. -/
lemma ModularForm.levelOne_odd_weight_rank_zero (hk : Odd k) :
    Module.rank ℂ (ModularForm 𝒮ℒ k) = 0 :=
  rank_zero_iff_forall_zero.mpr (levelOne_odd_weight_eq_zero hk)

/-- Cusp forms of weight `k < 12` for `𝒮ℒ` are zero-dimensional. -/
lemma CuspForm.rank_eq_zero_of_weight_lt_twelve (hk : k < 12) :
    Module.rank ℂ (CuspForm 𝒮ℒ k) = 0 :=
  CuspForm.discriminantEquiv.rank_eq.trans (levelOne_neg_weight_rank_zero (by lia))

/-- The space of weight 12 cusp forms for `𝒮ℒ` has rank 1. -/
lemma CuspForm.rank_eq_one_of_weight_eq_twelve : Module.rank ℂ (CuspForm 𝒮ℒ 12) = 1 := by
  simpa [CuspForm.discriminantEquiv.rank_eq] using levelOne_weight_zero_rank_one

/-- Every weight 12 cusp form for `𝒮ℒ` is a scalar multiple of the discriminant. -/
lemma CuspForm.exists_smul_discriminant_of_weight_eq_twelve (f : CuspForm 𝒮ℒ 12) :
    ∃ c : ℂ, c • CuspForm.discriminant = f :=
  (finrank_eq_one_iff_of_nonzero' _ (DFunLike.ne_iff.mpr ⟨I, discriminant_ne_zero _⟩)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp CuspForm.rank_eq_one_of_weight_eq_twelve) f

/-- For even `k ≥ 3`, the rank of `𝒮ℒ` modular forms is one more than the rank of
cusp forms. -/
lemma ModularForm.rank_eq_one_add_rank_cuspForm {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Module.rank ℂ (ModularForm 𝒮ℒ k) = 1 + Module.rank ℂ (CuspForm 𝒮ℒ k) := by
  suffices Module.rank ℂ (ModularForm 𝒮ℒ k ⧸ cuspFormSubmodule 𝒮ℒ k) = 1 by
    rw [(CuspForm.equivCuspFormSubmodule 𝒮ℒ k).rank_eq,
      ← Submodule.rank_quotient_add_rank (cuspFormSubmodule 𝒮ℒ k), this]
  apply rank_eq_one (Submodule.Quotient.mk (E hk))
  · intro h
    have hE := E_qExpansion_coeff_zero hk hk2
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact one_ne_zero <| hE.symm.trans <| (isCuspForm_iff_coeffZero_eq_zero _).mp h
  · refine (Submodule.Quotient.forall _).mpr fun f ↦ ⟨(qExpansion 1 f).coeff 0, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, mem_cuspFormSubmodule_iff,
      isCuspForm_iff_coeffZero_eq_zero, ModularForm.coe_sub, ModularFormClass.qExpansion_sub,
      IsGLPos.coe_smul, ModularFormClass.qExpansion_smul, map_sub,
      PowerSeries.coeff_smul, E_qExpansion_coeff_zero hk hk2, smul_eq_mul, mul_one, sub_self]
    all_goals simp

end RankIdentity

section DimensionFormula

namespace ModularForm

lemma levelOne_weight_four_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ 4) = 1 :=
  (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨2, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))

lemma levelOne_weight_six_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ 6) = 1 :=
  (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨3, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))

lemma E₄_qExpansion_coeff_one : (qExpansion 1 E₄).coeff 1 = 240 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]

lemma E₆_qExpansion_coeff_one : (qExpansion 1 E₆).coeff 1 = -504 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]

/- Algebraic core of the weight-2 vanishing argument: if `p : PowerSeries ℂ`
satisfies `c₄ • p₄ = p²` and `c₆ • p₆ = p³` for power series `p₄`, `p₆` with
constant term `1` and first-order coefficients `240` and `-504`, then `p = 0`. -/
private lemma eq_zero_of_pow_eq_smul {p p4 p6 : PowerSeries ℂ} {c4 c6 : ℂ}
    (hp4_0 : p4.coeff 0 = 1) (hp6_0 : p6.coeff 0 = 1) (hp4_1 : p4.coeff 1 = 240)
    (hp6_1 : p6.coeff 1 = -504) (hqc4 : c4 • p4 = p ^ 2)
    (hqc6 : c6 • p6 = p ^ 3) : p = 0 := by
  simp_all only [PowerSeries.coeff_zero_eq_constantCoeff]
  let D := (c4 • p4) ^ 3 - (c6 • p6) ^ 2
  have hD0 : D.coeff 0 = c4 ^ 3 - c6 ^ 2 := by simp [D, hp4_0, hp6_0]
  have hD1 : D.coeff 1 = 720 * c4 ^ 3 + 1008 * c6 ^ 2 := by
    simp [D, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
    grind
  grind [pow_eq_zero_iff, zero_smul]

private lemma weight_two_qExpansion_eq_zero (f : ModularForm 𝒮ℒ 2) : qExpansion 1 f = 0 := by
  obtain ⟨c4, hc4⟩ : ∃ c4, c4 • E₄ = f.mul f :=
    (finrank_eq_one_iff_of_nonzero' E₄ (E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_four_rank_one) _
  obtain ⟨c6, hc6⟩ : ∃ c6, c6 • E₆ = (f.mul f).mul f :=
    (finrank_eq_one_iff_of_nonzero' E₆ (E_ne_zero _ ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_six_rank_one) _
  have hqc4 : c4 • qExpansion 1 (E₄ : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) ^ 2 := by
    rw [pow_two, ← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f f,
      ← ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL c4 E₄,
      show (c4 • E₄ : ℍ → ℂ) = (f.mul f) from congrArg DFunLike.coe hc4]
  have hqc6 : c6 • qExpansion 1 E₆ = qExpansion 1 (f : ℍ → ℂ) ^ 3 := by
    rw [pow_succ, pow_two, ← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f f,
      ← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL (f.mul f) f,
      ← ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL c6 E₆,
      show (c6 • E₆ : ℍ → ℂ) = (f.mul f).mul f from congrArg DFunLike.coe hc6]
  exact eq_zero_of_pow_eq_smul (E_qExpansion_coeff_zero _ ⟨2, rfl⟩)
    (E_qExpansion_coeff_zero _ ⟨3, rfl⟩) E₄_qExpansion_coeff_one E₆_qExpansion_coeff_one hqc4 hqc6

/-- Modular forms of weight 2 for `𝒮ℒ` are zero. -/
theorem levelOne_weight_two_rank_zero : Module.rank ℂ (ModularForm 𝒮ℒ 2) = 0 := by
  simpa [rank_zero_iff_forall_zero, ModularForm.qExpansion_eq_zero_iff]
    using weight_two_qExpansion_eq_zero

/-- The dimension formula for `𝒮ℒ` modular forms of even weight. -/
theorem dimension_level_one (k : ℕ) (hk2 : Even k) :
    Module.rank ℂ (ModularForm 𝒮ℒ k) =
      if 12 ∣ ((k : ℤ) - 2) then Nat.floor ((k : ℚ) / 12)
      else Nat.floor ((k : ℚ) / 12) + 1 := by
  induction k using Nat.strong_induction_on with | h k ihn =>
  by_cases hk3 : 3 ≤ k
  · rw [rank_eq_one_add_rank_cuspForm hk3 hk2, CuspForm.discriminantEquiv.rank_eq]
    by_cases HK : (3 : ℤ) ≤ (k : ℤ) - 12
    · have iH := ihn (k - 12) (by omega) ((Nat.even_sub (by omega)).mpr (by grind))
      have hk12 : (((k - 12) : ℕ) : ℤ) = k - 12 := by grind
      rw [hk12] at iH
      rw [iH, show ((k - 12 : ℕ) : ℚ) = k - 12 by norm_cast]
      have hfl (hk' : 12 ≤ k) : ⌊(k : ℚ) / 12⌋₊ = 1 + ⌊((k : ℚ) - 12) / 12⌋₊ := by
        rw [Nat.floor_div_ofNat, Nat.floor_div_ofNat, Nat.floor_sub_ofNat,
          Nat.div_eq_sub_div (by norm_num) (mod_cast hk'), add_comm, Nat.floor_natCast]
      by_cases h12 : 12 ∣ (k : ℤ) - 2
      · simp only [show 12 ∣ (k : ℤ) - 12 - 2 by omega, ↓reduceIte, h12]
        norm_cast at *
        rw [hfl (by omega)]
      · simp only [show ¬ 12 ∣ (k : ℤ) - 12 - 2 by omega, ↓reduceIte, h12, Nat.cast_add,
          Nat.cast_one]
        norm_cast at *
        rw [← add_assoc, ← hfl (by omega)]
    · simp only [not_le] at HK
      have hkop : k ∈ Finset.filter Even (Finset.Icc 3 14) := by
        simp only [Finset.mem_filter, Finset.mem_Icc, hk2, and_true]
        omega
      rw [show Finset.filter Even (Finset.Icc 3 14) = ({4, 6, 8, 10, 12, 14} : Finset ℕ) by
        decide] at hkop
      fin_cases hkop <;> simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg] at *
      all_goals first
        | exact (congrArg (1 + ·) (levelOne_neg_weight_rank_zero (by omega))).trans (by norm_cast)
        | exact (congrArg (1 + ·) levelOne_weight_zero_rank_one).trans (by norm_cast)
        | exact (congrArg (1 + ·) levelOne_weight_two_rank_zero).trans (by norm_cast)
  · have hk_lt : k < 3 := by omega
    interval_cases k
    · simpa using levelOne_weight_zero_rank_one
    · simp [show ¬ Even 1 by decide] at hk2
    · convert levelOne_weight_two_rank_zero
      norm_num

instance (k : ℤ) : FiniteDimensional ℂ (ModularForm 𝒮ℒ k) := by
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  rcases lt_or_ge k 0 with hk_neg | hk_nonneg
  · rw [levelOne_neg_weight_rank_zero hk_neg]
    exact Cardinal.aleph0_pos
  rcases Int.even_or_odd k with hk_even | hk_odd
  · lift k to ℕ using hk_nonneg
    rw [dimension_level_one k (mod_cast hk_even)]
    split_ifs <;> exact_mod_cast Cardinal.natCast_lt_aleph0
  · rw [levelOne_odd_weight_rank_zero hk_odd]
    exact Cardinal.aleph0_pos

end ModularForm

end DimensionFormula
