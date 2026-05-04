/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.DimensionFormulas.LevelOne
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The graded ring of level-1 modular forms

This file collects structural results about the graded ring `⨁ k, ModularForm 𝒮ℒ k` of
level-1 modular forms.

## Main definitions

* `ModularForm.evalE₄E₆`: the evaluation homomorphism
  `ℂ[X₀, X₁] →ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k` sending `X₀ ↦ E₄`, `X₁ ↦ E₆`.

## Main results

* `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`: the pointwise identity
  `Δ = (E₄³ - E₆²) / 1728`.
* `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq_graded`: the same identity in the graded
  ring `⨁ k, ModularForm 𝒮ℒ k`.
* `ModularForm.evalE₄E₆_surjective`: `evalE₄E₆` is surjective.
* `ModularForm.evalE₄E₆_injective`: `evalE₄E₆` is injective (E₄ and E₆ are algebraically
  independent).
* `ModularForm.modularFormsEquivMvPolynomial`: the algebra isomorphism
  `ℂ[X₀, X₁] ≃ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k`.
* `ModularForm.E₄E₆_generate`: `E₄, E₆` generate the graded ring as an ℂ-algebra.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups EisensteinSeries

namespace ModularForm

/-- The combination `E₄³ - E₆²` viewed as a level-1 modular form of weight 12. -/
private noncomputable def E₄CubeSubE₆SqForm : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

private lemma E₄CubeSubE₆SqForm_apply (z : ℍ) :
    E₄CubeSubE₆SqForm z = E₄ z ^ 3 - E₆ z ^ 2 := by
  change ⇑(E₄.pow 3) z - ⇑(E₆.pow 2) z = _
  rw [coe_pow, coe_pow]
  rfl

private lemma E₄CubeSubE₆SqForm_qExpansion_eq :
    qExpansion 1 E₄CubeSubE₆SqForm = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ -
      qExpansion 1 E₆ * qExpansion 1 E₆ := by
  rw [show qExpansion 1 E₄CubeSubE₆SqForm =
        qExpansion 1 (E₄.pow 3) - qExpansion 1 (E₆.pow 2) from
      ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL
        (ModularForm.mcast (by decide) (E₄.pow 3))
        (ModularForm.mcast (by decide) (E₆.pow 2)),
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₆ 2]
  ring

private lemma E₄CubeSubE₆SqForm_isCuspForm : IsCuspForm E₄CubeSubE₆SqForm := by
  refine (isCuspForm_iff_coeffZero_eq_zero _).mpr ?_
  rw [E₄CubeSubE₆SqForm_qExpansion_eq]
  simp [PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

private lemma E₄CubeSubE₆SqForm_qExpansion_coeff_one :
    (qExpansion 1 E₄CubeSubE₆SqForm).coeff 1 = 1728 := by
  rw [E₄CubeSubE₆SqForm_qExpansion_eq]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
    E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

/-- The modular discriminant equals `(E₄³ - E₆²) / 1728`. -/
theorem discriminant_eq_E₄_cube_sub_E₆_sq (z : ℍ) :
    discriminant z = (1 / 1728) * (E₄ z ^ 3 - E₆ z ^ 2) := by
  obtain ⟨g, hg⟩ := E₄CubeSubE₆SqForm_isCuspForm
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hgE : (g : ℍ → ℂ) = E₄CubeSubE₆SqForm := congrArg DFunLike.coe hg
  have hc_eq : c = 1728 := by
    have hcΔ : (c • CuspForm.discriminant : ℍ → ℂ) = g := congrArg DFunLike.coe hc
    have hgΔ := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c
      CuspForm.discriminant
    rw [hcΔ, hgE] at hgΔ
    simpa [PowerSeries.coeff_smul, discriminant_qExpansion_coeff_one,
      E₄CubeSubE₆SqForm_qExpansion_coeff_one] using (congr_arg (·.coeff 1) hgΔ).symm
  have h1728 : (1728 : ℂ) * discriminant z = E₄ z ^ 3 - E₆ z ^ 2 := by
    rw [← hc_eq, show c * discriminant z = (c • CuspForm.discriminant) z from rfl, hc,
      congr_fun hgE z, E₄CubeSubE₆SqForm_apply]
  linear_combination h1728 / 1728

/-- The modular discriminant equals `(E₄³ - E₆²) / 1728` in the graded ring
`⨁ k, ModularForm 𝒮ℒ k`. -/
theorem discriminant_eq_E₄_cube_sub_E₆_sq_graded :
    DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant =
      (1 / 1728 : ℂ) • (.of (ModularForm 𝒮ℒ) 4 E₄ ^ 3 - .of (ModularForm 𝒮ℒ) 6 E₆ ^ 2) := by
  have hE4 : DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ 3 = DirectSum.of (ModularForm 𝒮ℒ) 12
      (ModularForm.mcast (by decide) ((E₄.mul E₄).mul E₄)) := by
    rw [pow_succ (n := 2), pow_two, DirectSum.of_mul_of, DirectSum.of_mul_of]
    rfl
  have hE6 : DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ 2 =
      DirectSum.of (ModularForm 𝒮ℒ) 12 (ModularForm.mcast (by decide) (E₆.mul E₆)) := by
    rw [pow_two, DirectSum.of_mul_of]
    rfl
  rw [hE4, hE6, ← map_sub (DirectSum.of (ModularForm 𝒮ℒ) 12), ← DirectSum.of_smul]
  congr 1
  ext z
  change ModularForm.discriminant z = (1 / 1728 : ℂ) * (E₄ z * E₄ z * E₄ z - E₆ z * E₆ z)
  grind [discriminant_eq_E₄_cube_sub_E₆_sq z]

/-- Evaluation homomorphism sending `ℂ[X₀, X₁]` to the graded ring of level 1 modular forms
via `X₀ ↦ E₄` and `X₁ ↦ E₆`. -/
noncomputable def evalE₄E₆ :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] DirectSum ℤ (ModularForm 𝒮ℒ) :=
  MvPolynomial.aeval
    ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄, DirectSum.of (ModularForm 𝒮ℒ) 6 E₆]

@[simp]
lemma evalE₄E₆_X0 :
    evalE₄E₆ (MvPolynomial.X 0) = DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ := by
  simp [evalE₄E₆]

@[simp]
lemma evalE₄E₆_X1 :
    evalE₄E₆ (MvPolynomial.X 1) = DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ := by
  simp [evalE₄E₆]

lemma evalE₄E₆_C (c : ℂ) :
    evalE₄E₆ (MvPolynomial.C c) = algebraMap ℂ (DirectSum ℤ (ModularForm 𝒮ℒ)) c :=
  MvPolynomial.aeval_C _ c

lemma evalE₄E₆_monomial (a b : ℕ) :
    evalE₄E₆ (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b := by
  simp [map_mul, map_pow]

private lemma evalE₄E₆_X_sq :
    evalE₄E₆ (MvPolynomial.X 0 ^ 2) = DirectSum.of (ModularForm 𝒮ℒ) 8 (E₄.mul E₄) := by
  rw [map_pow, evalE₄E₆_X0, pow_two, DirectSum.of_mul_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (ModularForm.gradedMonoid_eq_of_cast (show ((4 : ℤ) + 4 : ℤ) = 8 by norm_num).symm rfl)

private lemma evalE₄E₆_X0_X1 :
    evalE₄E₆ (MvPolynomial.X 0 * MvPolynomial.X 1) =
      DirectSum.of (ModularForm 𝒮ℒ) 10 (E₄.mul E₆) := by
  rw [map_mul, evalE₄E₆_X0, evalE₄E₆_X1, DirectSum.of_mul_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (ModularForm.gradedMonoid_eq_of_cast (show ((4 : ℤ) + 6 : ℤ) = 10 by norm_num).symm rfl)

private lemma exists_monomial_weight {k : ℕ} (hk : 4 ≤ k) (hkeven : Even k) :
    ∃ a b : ℕ, 4 * a + 6 * b = k := by
  obtain ⟨m, rfl⟩ := hkeven
  rcases Nat.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
  exacts [⟨n, 0, by omega⟩, ⟨n - 1, 1, by omega⟩]

private lemma surj_of_rank_one {k : ℤ}
    (hrank : Module.rank ℂ (ModularForm 𝒮ℒ k) = 1) {g : ModularForm 𝒮ℒ k} (hg : g ≠ 0)
    (p : MvPolynomial (Fin 2) ℂ) (hp : evalE₄E₆ p = DirectSum.of _ k g)
    (f : ModularForm 𝒮ℒ k) :
    DirectSum.of _ k f ∈ Set.range evalE₄E₆ := by
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' g hg).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) f
  refine ⟨MvPolynomial.C c * p, ?_⟩
  rw [map_mul, evalE₄E₆_C, hp, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, ← DirectSum.of_smul]

private lemma directSum_of_E₄_pow_mul_E₆_pow_apply {a b n : ℕ}
    (hab : 4 * a + 6 * b = n) :
    DirectSum.of (ModularForm 𝒮ℒ) (↑n : ℤ)
        ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
          DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b) (↑n : ℤ)) =
      DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b := by
  rw [DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of,
    show (↑n : ℤ) = a • (4 : ℤ) + b • (6 : ℤ) by
      simp only [Int.nsmul_eq_mul]
      push_cast [← hab]
      ring,
    DirectSum.of_eq_same]

private lemma monomial_qExpansion_coeff_zero_eq_one {n a b : ℕ} (hab : 4 * a + 6 * b = n) :
    (qExpansion 1
      ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b) (n : ℤ))).coeff 0 = 1 := by
  rw [← ModularForm.qExpansionRingHom_apply (h := 1) one_pos one_mem_strictPeriods_SL,
    directSum_of_E₄_pow_mul_E₆_pow_apply hab, map_mul, map_pow, map_pow,
    ModularForm.qExpansionRingHom_apply, ModularForm.qExpansionRingHom_apply,
    PowerSeries.coeff_mul]
  simp [Finset.antidiagonal_zero, PowerSeries.coeff_pow,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

private lemma cuspForm_eq_discriminant_mul {n : ℕ} (g : ModularForm 𝒮ℒ ↑n)
    (hg : ModularForm.IsCuspForm g) :
    DirectSum.of (ModularForm 𝒮ℒ) (↑n : ℤ) g =
      DirectSum.of (ModularForm 𝒮ℒ) (↑n - 12 : ℤ)
        (CuspForm.discriminantEquiv (ModularForm.toCuspForm g
          ((ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp hg))) *
        DirectSum.of (ModularForm 𝒮ℒ) 12
          ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12) := by
  rw [DirectSum.of_mul_of]
  symm
  refine DirectSum.of_eq_of_gradedMonoid_eq
    (ModularForm.gradedMonoid_eq_of_cast (by change (↑n - 12 + 12 : ℤ) = ↑n; ring) ?_)
  ext z
  let hcusp := (ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp hg
  change ((CuspForm.discriminantEquiv (ModularForm.toCuspForm g hcusp)).mul
      ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12)) z = g z
  rw [ModularForm.coe_mul, Pi.mul_apply,
    show (CuspForm.discriminantEquiv (ModularForm.toCuspForm g hcusp)) z =
        g z / ModularForm.discriminant z from
      CuspForm.divDiscriminant_apply (ModularForm.toCuspForm g hcusp) z]
  exact div_mul_cancel₀ _ (discriminant_ne_zero z)

private noncomputable def discriminantPoly : MvPolynomial (Fin 2) ℂ :=
  (1 / 1728 : ℂ) • (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)

private lemma evalE₄E₆_discriminantPoly :
    evalE₄E₆ discriminantPoly =
      DirectSum.of (ModularForm 𝒮ℒ) 12
        ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12) := by
  rw [discriminantPoly, map_smul, map_sub, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1,
    ← discriminant_eq_E₄_cube_sub_E₆_sq_graded]

private lemma discriminant_mem_range_evalE₄E₆ :
    DirectSum.of (ModularForm 𝒮ℒ) 12
        ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12) ∈
      Set.range evalE₄E₆ :=
  ⟨_, evalE₄E₆_discriminantPoly⟩

private lemma surj_at_weight_inductive {n : ℕ} (hn12 : 12 ≤ n) (hk_even : Even (n : ℤ))
    (ih : ∀ m < n, ∀ (f : ModularForm 𝒮ℒ ↑m),
      DirectSum.of _ (↑m : ℤ) f ∈ Set.range evalE₄E₆)
    (f : ModularForm 𝒮ℒ ↑n) :
    DirectSum.of _ (↑n : ℤ) f ∈ Set.range evalE₄E₆ := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 4 * a + 6 * b = n :=
    exists_monomial_weight (by omega) (by exact_mod_cast hk_even)
  set mn := (DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
    DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b) (↑n : ℤ)
  set c := (qExpansion 1 f).coeff 0
  have hg_cusp : ModularForm.IsCuspForm (f - c • mn) :=
    ModularForm.sub_smul_isCuspForm f mn (monomial_qExpansion_coeff_zero_eq_one hab)
  have hcast : ((↑n : ℤ) - 12 : ℤ) = ((n - 12 : ℕ) : ℤ) := by omega
  obtain ⟨p1, hp1⟩ : DirectSum.of (ModularForm 𝒮ℒ) ((↑n : ℤ) - 12)
      (CuspForm.discriminantEquiv (ModularForm.toCuspForm (f - c • mn)
        ((ModularForm.isCuspForm_iff_coeffZero_eq_zero _).mp hg_cusp))) ∈
        Set.range evalE₄E₆ := by
    rw [DirectSum.of_eq_of_eq hcast]
    exact ih _ (by omega) _
  rw [DirectSum.of_eq_sub_add_smul f mn c, directSum_of_E₄_pow_mul_E₆_pow_apply hab]
  exact ⟨p1 * discriminantPoly + MvPolynomial.C c * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b),
    by rw [map_add, map_mul, hp1, evalE₄E₆_discriminantPoly,
      cuspForm_eq_discriminant_mul (f - c • mn) hg_cusp, map_mul,
      evalE₄E₆_C, evalE₄E₆_monomial a b,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]⟩

private lemma rank_one_of_lt_twelve {k : ℕ} (hk3 : 3 ≤ k) (hk2 : Even k) (hk12 : k < 12) :
    Module.rank ℂ (ModularForm 𝒮ℒ (↑k : ℤ)) = 1 := by
  rw [ModularForm.rank_eq_one_add_rank_cuspForm hk3 hk2,
    CuspForm.rank_eq_zero_of_weight_lt_twelve (mod_cast hk12 : (↑k : ℤ) < 12)]
  norm_cast

private lemma one_ne_zero_modularForm : (1 : ModularForm 𝒮ℒ 0) ≠ 0 := fun h =>
  one_ne_zero (α := ℂ) (congr_fun (congr_arg (DFunLike.coe (F := ModularForm 𝒮ℒ 0)) h)
    UpperHalfPlane.I)

private lemma surj_of_zero_form {k : ℤ} (h : ∀ f : ModularForm 𝒮ℒ k, f = 0)
    (f : ModularForm 𝒮ℒ k) :
    DirectSum.of (ModularForm 𝒮ℒ) k f ∈ Set.range evalE₄E₆ := by
  rw [h f, map_zero]
  exact ⟨0, map_zero _⟩

private lemma surj_at_small_weight {n : ℕ} (hn12 : n < 12) (hk_even : Even (n : ℤ))
    (f : ModularForm 𝒮ℒ ↑n) :
    DirectSum.of _ (↑n : ℤ) f ∈ Set.range evalE₄E₆ := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl :
      n = 0 ∨ n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 := by
    rcases hk_even with ⟨m, hm⟩
    omega
  · exact surj_of_rank_one ModularForm.levelOne_weight_zero_rank_one
      one_ne_zero_modularForm 1
      ((map_one _).trans (DirectSum.of_zero_one _).symm) f
  · exact surj_of_zero_form (rank_zero_iff_forall_zero.mp
      ModularForm.levelOne_weight_two_rank_zero) f
  · exact surj_of_rank_one ModularForm.levelOne_weight_four_rank_one
      (E_ne_zero (k := 4) (by norm_num) ⟨2, rfl⟩)
      (MvPolynomial.X 0) evalE₄E₆_X0 f
  · exact surj_of_rank_one ModularForm.levelOne_weight_six_rank_one
      (E_ne_zero (k := 6) (by norm_num) ⟨3, rfl⟩)
      (MvPolynomial.X 1) evalE₄E₆_X1 f
  · exact surj_of_rank_one (rank_one_of_lt_twelve (by norm_num) ⟨4, rfl⟩ (by norm_num))
      (ModularForm.mul_ne_zero one_pos one_mem_strictPeriods_SL (f := E₄) (g := E₄)
        (E_ne_zero (by norm_num) ⟨2, rfl⟩) (E_ne_zero (by norm_num) ⟨2, rfl⟩))
      (MvPolynomial.X 0 ^ 2) evalE₄E₆_X_sq f
  · exact surj_of_rank_one (rank_one_of_lt_twelve (by norm_num) ⟨5, rfl⟩ (by norm_num))
      (ModularForm.mul_ne_zero one_pos one_mem_strictPeriods_SL (f := E₄) (g := E₆)
        (E_ne_zero (by norm_num) ⟨2, rfl⟩) (E_ne_zero (by norm_num) ⟨3, rfl⟩))
      (MvPolynomial.X 0 * MvPolynomial.X 1) evalE₄E₆_X0_X1 f

private lemma surj_of_weight : ∀ (k : ℤ) (f : ModularForm 𝒮ℒ k),
    DirectSum.of (ModularForm 𝒮ℒ) k f ∈ Set.range evalE₄E₆ := by
  intro k f
  by_cases hk_neg : k < 0
  · exact surj_of_zero_form
      (rank_zero_iff_forall_zero.mp (ModularForm.levelOne_neg_weight_rank_zero hk_neg)) f
  push Not at hk_neg
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
  clear hk_neg
  revert f
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  intro f
  by_cases hk_odd : Odd (n : ℤ)
  · exact surj_of_zero_form (fun f => ModularForm.levelOne_odd_weight_eq_zero hk_odd f) f
  rw [Int.not_odd_iff_even] at hk_odd
  by_cases hn12 : n < 12
  · exact surj_at_small_weight hn12 hk_odd f
  push Not at hn12
  exact surj_at_weight_inductive hn12 hk_odd ih f

/-- The evaluation homomorphism `evalE₄E₆` is surjective. -/
theorem evalE₄E₆_surjective : Function.Surjective evalE₄E₆ := by
  classical
  intro x
  rw [show x = x.sum (fun i m => DirectSum.of _ i m) from (DFinsupp.sum_single (f := x)).symm,
    ← AlgHom.mem_range]
  exact Subalgebra.sum_mem _ fun k _ => surj_of_weight k (x k)

private lemma weight_fin2 (w : Fin 2 → ℕ) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight w d = d 0 * w 0 + d 1 * w 1 := by
  rw [Finsupp.weight_apply, d.sum_fintype (fun i c => c • w i) fun _ => zero_smul _ _]
  simp [Fin.sum_univ_two, mul_comm]

private lemma weight_eq_4a_6b (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (![4, 6] : Fin 2 → ℕ) d = d 0 * 4 + d 1 * 6 := by
  rw [weight_fin2]
  rfl

private lemma weight_fin2_cast (d : Fin 2 →₀ ℕ) :
    (Finsupp.weight (![4, 6] : Fin 2 → ℕ) d : ℤ) = ↑(d 0) * 4 + ↑(d 1) * 6 := by
  rw [weight_eq_4a_6b]
  push_cast
  ring

private lemma no_weight_monomial_of_odd {n : ℕ} (hn : Odd n) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (![4, 6] : Fin 2 → ℕ) d ≠ n := by
  intro h
  rw [weight_eq_4a_6b] at h
  exact Nat.not_odd_iff_even.mpr ⟨d 0 * 2 + d 1 * 3, by omega⟩ hn

private lemma no_weight_monomial_of_two (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (![4, 6] : Fin 2 → ℕ) d ≠ 2 := by
  intro h
  rw [weight_eq_4a_6b] at h
  omega

private lemma unique_small_weight_solution {a₁ b₁ a₂ b₂ : ℕ}
    (ha₁ : a₁ < 3) (ha₂ : a₂ < 3)
    (h : a₁ * 4 + b₁ * 6 = a₂ * 4 + b₂ * 6) : a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨by interval_cases a₁ <;> interval_cases a₂ <;> omega, by omega⟩

private lemma monomial_fin2_eq {R : Type*} [CommSemiring R] (d : Fin 2 →₀ ℕ) (c : R) :
    MvPolynomial.monomial d c =
      MvPolynomial.C c * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 := by
  rw [MvPolynomial.monomial_eq, mul_assoc, d.prod_fintype _ fun _ => pow_zero _]
  simp [Fin.prod_univ_two]

private lemma evalE₄E₆_X_pow_mul_apply_eq_zero_of_ne (a b : ℕ) (k : ℤ)
    (hk : k ≠ (↑a * 4 + ↑b * 6 : ℤ)) :
    (evalE₄E₆ (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) k = 0 := by
  rw [evalE₄E₆_monomial, DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
  refine DirectSum.of_eq_of_ne _ _ _ fun heq => hk ?_
  simp only [Int.nsmul_eq_mul] at heq
  omega

private lemma evalE₄E₆_monomial_apply_eq_zero_of_ne (d : Fin 2 →₀ ℕ) (c : ℂ) (k : ℤ)
    (hk : k ≠ (↑(d 0) * 4 + ↑(d 1) * 6 : ℤ)) :
    (evalE₄E₆ (MvPolynomial.monomial d c)) k = 0 := by
  rw [monomial_fin2_eq, mul_assoc, map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, DirectSum.smul_apply,
    evalE₄E₆_X_pow_mul_apply_eq_zero_of_ne (d 0) (d 1) k hk, smul_zero]

private lemma evalE₄E₆_apply_eq_zero_of_ne {n : ℕ} (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (k : ℤ) (hk : k ≠ ↑n) :
    (evalE₄E₆ p) k = 0 := by
  rw [← MvPolynomial.support_sum_monomial_coeff p, map_sum, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun d hd =>
    evalE₄E₆_monomial_apply_eq_zero_of_ne _ _ _ fun heq => hk ?_
  rw [heq, ← weight_fin2_cast d, hp (MvPolynomial.mem_support_iff.mp hd)]

private lemma evalE₄E₆_eq_of_apply (n : ℕ) (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n) :
    evalE₄E₆ p = DirectSum.of (ModularForm 𝒮ℒ) (↑n : ℤ) ((evalE₄E₆ p) ↑n) := by
  refine DFinsupp.ext fun k : ℤ => ?_
  by_cases hk : k = (↑n : ℤ)
  · subst hk
    simp
  · rw [DirectSum.of_eq_of_ne _ _ _ hk, evalE₄E₆_apply_eq_zero_of_ne p hp k hk]

private lemma evalE₄E₆_component_eq (p : MvPolynomial (Fin 2) ℂ) (n : ℕ) :
    (evalE₄E₆
        (MvPolynomial.weightedHomogeneousComponent (![4, 6] : Fin 2 → ℕ) n p)) (↑n : ℤ) =
      (evalE₄E₆ p) (↑n : ℤ) := by
  set q := p - MvPolynomial.weightedHomogeneousComponent (![4, 6] : Fin 2 → ℕ) n p with hq_def
  have hdecomp :
      p = MvPolynomial.weightedHomogeneousComponent (![4, 6] : Fin 2 → ℕ) n p + q := by
    simp [q]
  conv_rhs => rw [hdecomp, map_add, DirectSum.add_apply]
  suffices h : (evalE₄E₆ q) (↑n : ℤ) = 0 by rw [h, add_zero]
  rw [← MvPolynomial.support_sum_monomial_coeff q, map_sum, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun d hd =>
    evalE₄E₆_monomial_apply_eq_zero_of_ne _ _ _ fun heq => MvPolynomial.mem_support_iff.mp hd ?_
  rw [hq_def, MvPolynomial.coeff_sub, MvPolynomial.coeff_weightedHomogeneousComponent,
    if_pos ?_, sub_self]
  rw [weight_eq_4a_6b]
  omega

private lemma X0_pow_mul_X1_pow_isWeightedHomogeneous (a b n : ℕ) (hab : a * 4 + b * 6 = n) :
    MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ)
      (MvPolynomial.X (0 : Fin 2) ^ a * MvPolynomial.X (1 : Fin 2) ^ b :
        MvPolynomial (Fin 2) ℂ) n := by
  convert
    ((MvPolynomial.isWeightedHomogeneous_X ℂ (![4, 6] : Fin 2 → ℕ) (0 : Fin 2)).pow a).mul
      ((MvPolynomial.isWeightedHomogeneous_X ℂ (![4, 6] : Fin 2 → ℕ) (1 : Fin 2)).pow b)
    using 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  omega

private lemma discriminantPoly_isWeightedHomogeneous :
    MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) discriminantPoly 12 := by
  rw [discriminantPoly, MvPolynomial.smul_eq_C_mul]
  refine MvPolynomial.IsWeightedHomogeneous.C_mul (.sub ?_ ?_) _
  · convert (MvPolynomial.isWeightedHomogeneous_X ℂ (![4, 6] : Fin 2 → ℕ) (0 : Fin 2)).pow 3 using 1
  · convert (MvPolynomial.isWeightedHomogeneous_X ℂ (![4, 6] : Fin 2 → ℕ) (1 : Fin 2)).pow 2 using 1

private lemma evalE₄E₆_discriminantPoly_mul_coeff_zero {n : ℕ} (hn12 : 12 ≤ n)
    (s : MvPolynomial (Fin 2) ℂ)
    (hs : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) s (n - 12)) :
    (qExpansion 1 ↑((evalE₄E₆ (discriminantPoly * s)) (↑n : ℤ))).coeff 0 = 0 := by
  rw [map_mul, evalE₄E₆_discriminantPoly,
    evalE₄E₆_eq_of_apply (n - 12) s hs, DirectSum.of_mul_of]
  have hcast : (12 : ℤ) + ((n - 12 : ℕ) : ℤ) = (↑n : ℤ) := by omega
  rw [DirectSum.of_apply, dif_pos hcast]
  set f := ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12)
  set g := (evalE₄E₆ s) ((n - 12 : ℕ) : ℤ)
  rw [show ((hcast ▸ GradedMonoid.GMul.mul f g : ModularForm 𝒮ℒ ↑n) : ℍ → ℂ) =
      ((f.mul g : ModularForm 𝒮ℒ (12 + ((n - 12 : ℕ) : ℤ))) : ℍ → ℂ) from
        funext fun z => ModularForm.cast_apply hcast _ z,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f g, PowerSeries.coeff_mul]
  simp [Finset.antidiagonal_zero,
    (ModularForm.isCuspForm_iff_coeffZero_eq_zero f).mp ⟨CuspForm.discriminant, rfl⟩]

private lemma per_weight_injective_unique_monomial {n : ℕ} (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0)
    (d₀ : Fin 2 →₀ ℕ)
    (huniq : ∀ d : Fin 2 →₀ ℕ, Finsupp.weight (![4, 6] : Fin 2 → ℕ) d = n → d = d₀)
    (hmf_ne : (DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ d₀ 0 *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ d₀ 1) (↑n : ℤ) ≠ 0) : p = 0 := by
  have hpc := hp.eq_monomial_of_unique_weight d₀ huniq
  rw [hpc] at heval ⊢
  rw [monomial_fin2_eq, mul_assoc, map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, evalE₄E₆_monomial, DirectSum.smul_apply] at heval
  rcases smul_eq_zero.mp heval with hc | hmz
  · rw [hc, MvPolynomial.monomial_zero]
  · exact absurd hmz hmf_ne

private lemma per_weight_injective_small {n : ℕ} (a b : ℕ) (ha : a < 3) (hn : n < 12)
    (hab : 4 * a + 6 * b = n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0) : p = 0 := by
  obtain ⟨d₀, hd0a, hd0b⟩ : ∃ d : Fin 2 →₀ ℕ, d 0 = a ∧ d 1 = b :=
    ⟨Finsupp.equivFunOnFinite.invFun ![a, b], rfl, rfl⟩
  apply per_weight_injective_unique_monomial p hp heval d₀
  · intro d hd
    have h46 := weight_eq_4a_6b d
    rw [hd] at h46
    obtain ⟨hda, hdb⟩ := unique_small_weight_solution (by omega : d 0 < 3) ha
      (show d 0 * 4 + d 1 * 6 = a * 4 + b * 6 by omega)
    ext i
    fin_cases i <;> [exact hda ▸ hd0a.symm; exact hdb ▸ hd0b.symm]
  · rw [hd0a, hd0b]
    intro habs
    have hcz := monomial_qExpansion_coeff_zero_eq_one (n := n) (a := a) (b := b) (by omega)
    rw [habs] at hcz
    simp [UpperHalfPlane.qExpansion_zero] at hcz

private lemma per_weight_injective_zero
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p 0)
    (heval : (evalE₄E₆ p) (0 : ℤ) = 0) : p = 0 := by
  have hpc : p = MvPolynomial.monomial (0 : Fin 2 →₀ ℕ) (MvPolynomial.coeff 0 p) :=
    hp.eq_monomial_of_unique_weight 0 (fun d hd => by
      rw [weight_eq_4a_6b] at hd
      ext i
      fin_cases i <;> simp <;> omega)
  rw [hpc, MvPolynomial.monomial_zero'] at heval ⊢
  rw [evalE₄E₆_C, Algebra.algebraMap_eq_smul_one, DirectSum.smul_apply,
    show (1 : DirectSum ℤ (ModularForm 𝒮ℒ)) (0 : ℤ) = (1 : ModularForm 𝒮ℒ 0) from by
      conv_lhs => rw [← DirectSum.of_zero_one (ModularForm 𝒮ℒ)]
      exact DirectSum.of_eq_same _ _] at heval
  rcases smul_eq_zero.mp heval with hc | h1z
  · simp [hc]
  · exact absurd h1z one_ne_zero_modularForm

private lemma discriminantPoly_piece_isWeightedHomogeneous {n : ℕ} (hn12 : 12 ≤ n)
    (d : Fin 2 →₀ ℕ) (hd_ge : 3 ≤ d 0) (hwd : d 0 * 4 + d 1 * 6 = n) (c : ℂ) :
    MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ)
      (MvPolynomial.C c * ((1728 : ℂ) • discriminantPoly *
        (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
          MvPolynomial.X (1 : Fin 2) ^ (d 1)))) n := by
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  rw [MvPolynomial.smul_eq_C_mul,
    show MvPolynomial.C (1728 : ℂ) * discriminantPoly *
        (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1) =
        MvPolynomial.C (1728 : ℂ) * (discriminantPoly *
          (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
            MvPolynomial.X (1 : Fin 2) ^ d 1)) from by ring]
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  convert discriminantPoly_isWeightedHomogeneous.mul
    (X0_pow_mul_X1_pow_isWeightedHomogeneous (d 0 - 3) (d 1) (n - 12) (by omega))
    using 1
  omega

private lemma discriminantPoly_piece_eq_monomial_sub
    (d : Fin 2 →₀ ℕ) (hd_ge : 3 ≤ d 0) (c : ℂ) :
    MvPolynomial.C c * ((1728 : ℂ) • discriminantPoly *
        (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1)) =
    MvPolynomial.monomial d c - MvPolynomial.monomial
      (Finsupp.single (0 : Fin 2) (d 0 - 3) + Finsupp.single (1 : Fin 2) (d 1 + 2)) c := by
  have h1728 : (1728 : ℂ) • discriminantPoly =
      MvPolynomial.X (0 : Fin 2) ^ 3 - MvPolynomial.X (1 : Fin 2) ^ 2 := by
    simp only [discriminantPoly, smul_smul]
    norm_num
  have hX0 : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ d 0 =
      MvPolynomial.X 0 ^ 3 * MvPolynomial.X 0 ^ (d 0 - 3) := by
    rw [← pow_add]
    congr 1
    omega
  have h0 : (Finsupp.single (0 : Fin 2) (d 0 - 3) + Finsupp.single (1 : Fin 2) (d 1 + 2)) 0
      = d 0 - 3 := by simp
  have h1 : (Finsupp.single (0 : Fin 2) (d 0 - 3) + Finsupp.single (1 : Fin 2) (d 1 + 2)) 1
      = d 1 + 2 := by simp
  rw [h1728, monomial_fin2_eq, monomial_fin2_eq, h0, h1, hX0,
    pow_add (MvPolynomial.X (1 : Fin 2)) (d 1) 2]
  ring

private lemma sum_lt_sum_of_replace {α : Type*} [DecidableEq α]
    (S S' : Finset α) (f : α → ℕ) (d d' : α)
    (hd_mem : d ∈ S) (hd_not : d ∉ S')
    (hS' : S' ⊆ S.erase d ∪ {d'})
    (hlt : f d' < f d) :
    ∑ x ∈ S', f x < ∑ x ∈ S, f x := by
  by_cases hd'S : d' ∈ S
  · calc ∑ x ∈ S', f x
        ≤ ∑ x ∈ S.erase d, f x := Finset.sum_le_sum_of_subset (fun x hx =>
          Finset.mem_erase.mpr ⟨fun h => hd_not (h ▸ hx),
            match Finset.mem_union.mp (hS' hx) with
            | .inl h => Finset.mem_of_mem_erase h
            | .inr h => Finset.mem_singleton.mp h ▸ hd'S⟩)
      _ < ∑ x ∈ S.erase d, f x + f d :=
          Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero (by omega))
      _ = ∑ x ∈ S, f x := Finset.sum_erase_add S f hd_mem
  · calc ∑ x ∈ S', f x
        ≤ ∑ x ∈ S.erase d ∪ {d'}, f x := Finset.sum_le_sum_of_subset hS'
      _ = ∑ x ∈ S.erase d, f x + f d' := by
          rw [Finset.sum_union (Finset.disjoint_singleton_right.mpr
            (fun h => hd'S (Finset.mem_of_mem_erase h))), Finset.sum_singleton]
      _ < ∑ x ∈ S.erase d, f x + f d := Nat.add_lt_add_left hlt _
      _ = ∑ x ∈ S, f x := Finset.sum_erase_add S f hd_mem

open Classical in
private lemma mvPolynomial_support_after_reduction {σ R : Type*} [CommRing R] [DecidableEq σ]
    (p : MvPolynomial σ R) (d d' : σ →₀ ℕ) (c : R)
    (hdd' : d ≠ d') (hc : MvPolynomial.coeff d p = c) :
    let δ := MvPolynomial.monomial d c - MvPolynomial.monomial d' c
    d ∉ (p - δ).support ∧ (p - δ).support ⊆ p.support.erase d ∪ {d'} := by
  have hd_not : d ∉ (p - (MvPolynomial.monomial d c -
      MvPolynomial.monomial d' c)).support := by
    rw [MvPolynomial.notMem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial,
      if_pos rfl, if_neg hdd'.symm, sub_zero, hc, sub_self]
  refine ⟨hd_not, fun x hx => ?_⟩
  rcases Finset.mem_union.mp (MvPolynomial.support_sub σ p _ hx) with hp | hdelta
  · by_cases hxd : x = d
    · exact absurd (hxd ▸ hx) hd_not
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxd, hp⟩)
  rcases Finset.mem_union.mp (MvPolynomial.support_sub σ _ _ hdelta) with h1 | h2
  · rw [MvPolynomial.support_monomial] at h1
    split_ifs at h1
    · exact absurd h1 (Finset.notMem_empty _)
    exact absurd ((Finset.mem_singleton.mp h1) ▸ hx) hd_not
  rw [MvPolynomial.support_monomial] at h2
  split_ifs at h2
  · exact absurd h2 (Finset.notMem_empty _)
  exact Finset.mem_union_right _ (by rwa [Finset.mem_singleton] at h2 ⊢)

private lemma support_sum_lt_after_sub_δ_piece (p : MvPolynomial (Fin 2) ℂ)
    {d : Fin 2 →₀ ℕ} (hd_mem : d ∈ p.support) (hd_ge : 3 ≤ d 0) :
    ∑ d' ∈ (p - MvPolynomial.C (MvPolynomial.coeff d p) * ((1728 : ℂ) • discriminantPoly *
          (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
            MvPolynomial.X (1 : Fin 2) ^ d 1))).support, d' 0 <
      ∑ d' ∈ p.support, d' 0 := by
  set d' := Finsupp.single (0 : Fin 2) (d 0 - 3) + Finsupp.single (1 : Fin 2) (d 1 + 2)
  have hdd' : d ≠ d' := fun heq => by
    have h0 := Finsupp.ext_iff.mp heq (0 : Fin 2)
    simp only [Fin.isValue, d', Finsupp.add_apply, Finsupp.single_eq_same,
      ne_eq, zero_ne_one, not_false_eq_true, Finsupp.single_eq_of_ne, add_zero] at h0
    omega
  obtain ⟨hd_not, hsupp⟩ := (discriminantPoly_piece_eq_monomial_sub d hd_ge _ : _ = _) ▸
    mvPolynomial_support_after_reduction p d d' _ hdd' rfl
  refine sum_lt_sum_of_replace p.support _ (· 0) d d' hd_mem hd_not hsupp ?_
  simp [d', Finsupp.add_apply]
  omega

private lemma weightedHomogeneous_poly_Delta_decomp_step {n : ℕ} (hn12 : 12 ≤ n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (hnotall : ¬ ∀ d ∈ p.support, d 0 < 3) :
    ∃ p' q₁ : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p' n ∧
      MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) q₁ (n - 12) ∧
      p = p' + discriminantPoly * q₁ ∧
      ∑ d ∈ p'.support, d 0 < ∑ d ∈ p.support, d 0 := by
  push Not at hnotall
  obtain ⟨d, hd_mem, hd_ge⟩ := hnotall
  have hwd : d 0 * 4 + d 1 * 6 = n := by
    have := (weight_eq_4a_6b d).symm.trans <| hp <| MvPolynomial.mem_support_iff.mp hd_mem
    omega
  set c := MvPolynomial.coeff d p
  set δ_piece := MvPolynomial.C c * ((1728 : ℂ) • discriminantPoly *
    (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1))
  set q₁ := MvPolynomial.C (c * 1728) *
    (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1)
  have hδ_eq : δ_piece = discriminantPoly * q₁ := by
    simp only [δ_piece, q₁, MvPolynomial.smul_eq_C_mul, map_mul]
    ring
  refine ⟨p - δ_piece, q₁, hp.sub
      (discriminantPoly_piece_isWeightedHomogeneous hn12 d hd_ge hwd c),
    .C_mul (X0_pow_mul_X1_pow_isWeightedHomogeneous (d 0 - 3) (d 1) (n - 12) (by omega)) _, ?_,
    support_sum_lt_after_sub_δ_piece p hd_mem hd_ge⟩
  rw [← hδ_eq]
  ring

private lemma weightedHomogeneous_poly_Delta_decomp {n : ℕ} (hn12 : 12 ≤ n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n) :
    ∃ r s : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) r n ∧
      MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) s (n - 12) ∧
      p = r + discriminantPoly * s ∧
      (∀ d ∈ r.support, d 0 < 3) := by
  generalize hM : ∑ d ∈ p.support, d 0 = M
  induction M using Nat.strong_induction_on generalizing p with | _ M ih => ?_
  by_cases hall : ∀ d ∈ p.support, d 0 < 3
  · exact ⟨p, 0, hp, MvPolynomial.isWeightedHomogeneous_zero ℂ _ _,
      by simp only [mul_zero, add_zero], hall⟩
  obtain ⟨p', q₁, hp'_wh, hq₁_wh, hp_eq, hlt⟩ :=
    weightedHomogeneous_poly_Delta_decomp_step hn12 p hp hall
  obtain ⟨r, s', hr_wh, hs'_wh, hp'_eq, hr_red⟩ :=
    ih _ (hM ▸ hlt) p' hp'_wh rfl
  refine ⟨r, s' + q₁, hr_wh, hs'_wh.add hq₁_wh, ?_, hr_red⟩
  rw [hp_eq, hp'_eq, mul_add]
  ring

private lemma reduced_isWeightedHomogeneous_eq_monomial {n : ℕ}
    (r : MvPolynomial (Fin 2) ℂ)
    (hr : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) r n)
    (hr_red : ∀ d ∈ r.support, d 0 < 3) {d₀ : Fin 2 →₀ ℕ} (hd₀ : d₀ ∈ r.support) :
    r = MvPolynomial.monomial d₀ (MvPolynomial.coeff d₀ r) := by
  have hwd₀ := hr (MvPolynomial.mem_support_iff.mp hd₀)
  ext d
  rw [MvPolynomial.coeff_monomial]
  by_cases hd : d = d₀
  · simp [hd]
  rw [if_neg (Ne.symm hd)]
  by_cases hd_supp : d ∈ r.support
  · have h1 := weight_eq_4a_6b d
    rw [hr (MvPolynomial.mem_support_iff.mp hd_supp)] at h1
    have h2 := weight_eq_4a_6b d₀
    rw [hwd₀] at h2
    obtain ⟨ha, hb⟩ := unique_small_weight_solution (hr_red d hd_supp) (hr_red d₀ hd₀)
      (show d 0 * 4 + d 1 * 6 = d₀ 0 * 4 + d₀ 1 * 6 by omega)
    exact absurd (Finsupp.ext fun i => by fin_cases i <;> [exact ha; exact hb]) hd
  · rwa [MvPolynomial.mem_support_iff, not_not] at hd_supp

private lemma evalE₄E₆_monomial_qExpansion_coeff_zero {n : ℕ} {d₀ : Fin 2 →₀ ℕ}
    (hd₀_weight : 4 * d₀ 0 + 6 * d₀ 1 = n) (c : ℂ) :
    (qExpansion 1 ↑((evalE₄E₆ (MvPolynomial.monomial d₀ c)) (↑n : ℤ))).coeff 0 = c := by
  rw [monomial_fin2_eq, mul_assoc, map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, evalE₄E₆_monomial, DirectSum.smul_apply,
    show (↑(c • ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ d₀ 0 *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ d₀ 1) (↑n : ℤ))) : ℍ → ℂ) =
      c • (↑((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ d₀ 0 *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ d₀ 1) (↑n : ℤ)) : ℍ → ℂ) from rfl,
    UpperHalfPlane.qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero _
      one_pos one_mem_strictPeriods_SL) c, PowerSeries.coeff_smul,
    monomial_qExpansion_coeff_zero_eq_one hd₀_weight]
  simp

private lemma reduced_part_eq_zero {n : ℕ} (hn12 : 12 ≤ n)
    (r s : MvPolynomial (Fin 2) ℂ)
    (hr : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) r n)
    (hs : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) s (n - 12))
    (hr_red : ∀ d ∈ r.support, d 0 < 3)
    (heval : (evalE₄E₆ (r + discriminantPoly * s)) (↑n : ℤ) = 0) :
    r = 0 := by
  by_cases hr_empty : r.support = ∅
  · rwa [MvPolynomial.support_eq_empty] at hr_empty
  obtain ⟨d₀, hd₀⟩ := Finset.nonempty_of_ne_empty hr_empty
  have hr_mono := reduced_isWeightedHomogeneous_eq_monomial r hr hr_red hd₀
  set c := MvPolynomial.coeff d₀ r
  suffices hc : c = 0 by rw [hr_mono, hc, MvPolynomial.monomial_zero]
  have hd₀_weight : 4 * d₀ 0 + 6 * d₀ 1 = n := by
    have := (weight_eq_4a_6b d₀).symm.trans (hr (MvPolynomial.mem_support_iff.mp hd₀))
    omega
  rw [hr_mono, map_add, DirectSum.add_apply] at heval
  set Q := ModularForm.qExpansionAddHom (h := 1) one_pos one_mem_strictPeriods_SL (↑n : ℤ)
  have hQ : (Q ((evalE₄E₆ (MvPolynomial.monomial d₀ c)) (↑n : ℤ))).coeff 0 +
      (Q ((evalE₄E₆ (discriminantPoly * s)) (↑n : ℤ))).coeff 0 = 0 := by
    rw [← LinearMap.map_add, ← Q.map_add, heval, map_zero, map_zero]
  rw [show (Q ((evalE₄E₆ (discriminantPoly * s)) (↑n : ℤ))).coeff 0 = 0 from
      evalE₄E₆_discriminantPoly_mul_coeff_zero hn12 s hs,
    add_zero,
    show (Q ((evalE₄E₆ (MvPolynomial.monomial d₀ c)) (↑n : ℤ))).coeff 0 = c from
      evalE₄E₆_monomial_qExpansion_coeff_zero hd₀_weight c] at hQ
  exact hQ

private lemma eval_discriminantPoly_mul_eq_zero_imp_eval_eq_zero {n : ℕ} (hn12 : 12 ≤ n)
    (s : MvPolynomial (Fin 2) ℂ)
    (hs : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) s (n - 12))
    (hds : (evalE₄E₆ (discriminantPoly * s)) (↑n : ℤ) = 0) :
    (evalE₄E₆ s) (↑(n - 12) : ℤ) = 0 := by
  rw [map_mul, evalE₄E₆_discriminantPoly,
    evalE₄E₆_eq_of_apply (n - 12) s hs, DirectSum.of_mul_of] at hds
  have hcast : (12 : ℤ) + ((n - 12 : ℕ) : ℤ) = (↑n : ℤ) := by omega
  rw [DirectSum.of_apply, dif_pos hcast] at hds
  ext z
  have hpw := DFunLike.congr_fun hds z
  simp only [ModularForm.zero_apply, ModularForm.cast_apply hcast] at hpw ⊢
  exact (mul_eq_zero.mp hpw).resolve_left (discriminant_ne_zero z)

private lemma per_weight_injective_inductive_step (n : ℕ)
    (ih : ∀ m < n, ∀ (p : MvPolynomial (Fin 2) ℂ),
      MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p m →
        (evalE₄E₆ p) (↑m : ℤ) = 0 → p = 0)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0)
    (hn12 : 12 ≤ n) : p = 0 := by
  obtain ⟨r, s, hr_wh, hs_wh, hp_eq, hr_red⟩ := weightedHomogeneous_poly_Delta_decomp hn12 p hp
  have hr0 : r = 0 := reduced_part_eq_zero hn12 r s hr_wh hs_wh hr_red (hp_eq ▸ heval)
  rw [hp_eq, hr0, zero_add] at heval ⊢
  rw [ih (n - 12) (by omega) s hs_wh
    (eval_discriminantPoly_mul_eq_zero_imp_eval_eq_zero hn12 s hs_wh heval), mul_zero]

private lemma per_weight_injective_at_small_weight {n : ℕ} (hn12 : n < 12) (hk_even : Even n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0) : p = 0 := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl :
      n = 0 ∨ n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 := by
    rcases hk_even with ⟨m, hm⟩
    omega
  · exact per_weight_injective_zero p hp heval
  · exact hp.eq_zero_of_no_monomials no_weight_monomial_of_two
  · exact per_weight_injective_small 1 0 (by omega) (by omega) rfl p hp heval
  · exact per_weight_injective_small 0 1 (by omega) (by omega) rfl p hp heval
  · exact per_weight_injective_small 2 0 (by omega) (by omega) rfl p hp heval
  · exact per_weight_injective_small 1 1 (by omega) (by omega) rfl p hp heval

private lemma per_weight_injective : ∀ (n : ℕ) (p : MvPolynomial (Fin 2) ℂ),
    MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n →
    (evalE₄E₆ p) (↑n : ℤ) = 0 → p = 0 := by
  intro n
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  intro p hp heval
  by_cases hk_odd : Odd n
  · exact hp.eq_zero_of_no_monomials (no_weight_monomial_of_odd hk_odd)
  rw [Nat.not_odd_iff_even] at hk_odd
  by_cases hn12 : n < 12
  · exact per_weight_injective_at_small_weight hn12 hk_odd p hp heval
  push Not at hn12
  exact per_weight_injective_inductive_step n ih p hp heval hn12

/-- The evaluation homomorphism `evalE₄E₆` is injective: `E₄` and `E₆` are algebraically
independent. -/
theorem evalE₄E₆_injective : Function.Injective evalE₄E₆ := by
  intro p q hpq
  rw [← sub_eq_zero,
    ← MvPolynomial.sum_weightedHomogeneousComponent ((![4, 6] : Fin 2 → ℕ)) (p - q)]
  refine finsum_eq_zero_of_forall_eq_zero fun n => per_weight_injective n _
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _) ?_
  rw [evalE₄E₆_component_eq, map_sub, hpq, sub_self]
  rfl

/-- The graded ring of level-1 modular forms is isomorphic to the polynomial ring
`ℂ[X₀, X₁]` via evaluation at `E₄` and `E₆`. -/
noncomputable def modularFormsEquivMvPolynomial :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] DirectSum ℤ (ModularForm 𝒮ℒ) :=
  AlgEquiv.ofBijective evalE₄E₆ ⟨evalE₄E₆_injective, evalE₄E₆_surjective⟩

/-- `E₄` and `E₆` generate the entire graded ring of level 1 modular forms as an
`ℂ`-algebra. -/
theorem E₄E₆_generate :
    Algebra.adjoin ℂ ({DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆} :
      Set (DirectSum ℤ (ModularForm 𝒮ℒ))) = ⊤ := by
  rw [show ({DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆} : Set _) =
      Set.range (![DirectSum.of _ 4 E₄, DirectSum.of _ 6 E₆] : Fin 2 → _)
    from (Matrix.range_cons_cons_empty _ _ _).symm,
    Algebra.adjoin_range_eq_range_aeval]
  exact (AlgHom.range_eq_top evalE₄E₆).mpr evalE₄E₆_surjective

end ModularForm

end
