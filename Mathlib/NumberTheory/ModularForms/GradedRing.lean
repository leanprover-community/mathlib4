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

* `ModularForm.E₄E₆Weight`: the weight function `Fin 2 → ℕ` mapping `0 ↦ 4`, `1 ↦ 6`.
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

/-! ### `Δ = (E₄³ - E₆²) / 1728` -/

/-- The combination `E₄³ - E₆²` viewed as a level-1 modular form of weight 12. -/
private noncomputable def E₄CubeSubE₆SqForm : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num) ((E₄.mul E₄).mul E₄) -
    ModularForm.mcast (by norm_num) (E₆.mul E₆)

private lemma E₄CubeSubE₆SqForm_apply (z : ℍ) :
    E₄CubeSubE₆SqForm z = E₄ z ^ 3 - E₆ z ^ 2 := by
  change E₄ z * E₄ z * E₄ z - E₆ z * E₆ z = _
  ring

private lemma E₄CubeSubE₆SqForm_qExpansion_eq :
    qExpansion 1 E₄CubeSubE₆SqForm = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ -
      qExpansion 1 E₆ * qExpansion 1 E₆ := by
  rw [show qExpansion 1 E₄CubeSubE₆SqForm =
        qExpansion 1 ((E₄.mul E₄).mul E₄) - qExpansion 1 (E₆.mul E₆) from
      ModularFormClass.qExpansion_sub one_pos one_mem_strictPeriods_SL
        (ModularForm.mcast (by norm_num) ((E₄.mul E₄).mul E₄))
        (ModularForm.mcast (by norm_num) (E₆.mul E₆)),
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL (E₄.mul E₄) E₄,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL E₄ E₄,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL E₆ E₆]

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
    have hgΔ := ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL c
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

/-! ### Generators of the graded ring

The remainder of this file establishes that `E₄, E₆` generate the graded ring of level-1
modular forms freely as an `ℂ`-algebra: the evaluation homomorphism `evalE₄E₆` is an
isomorphism. The proofs are ported from
<https://github.com/CBirkbeck/LeanModularForms> (`Modularforms/Generators/`). -/

/-- Weight function assigning weight 4 to E₄ (variable 0) and weight 6 to E₆ (variable 1). -/
def E₄E₆Weight : Fin 2 → ℕ := ![4, 6]

/-- Evaluation homomorphism sending `ℂ[X₀, X₁]` to the graded ring of level 1 modular forms
via `X₀ ↦ E₄` and `X₁ ↦ E₆`. -/
noncomputable def evalE₄E₆ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] DirectSum ℤ (ModularForm 𝒮ℒ) :=
  MvPolynomial.aeval
    ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄, DirectSum.of (ModularForm 𝒮ℒ) 6 E₆]

@[simp]
lemma evalE₄E₆_X0 : evalE₄E₆ (MvPolynomial.X 0) = DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ := by
  simp [evalE₄E₆]

@[simp]
lemma evalE₄E₆_X1 : evalE₄E₆ (MvPolynomial.X 1) = DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ := by
  simp [evalE₄E₆]

lemma evalE₄E₆_C (c : ℂ) :
    evalE₄E₆ (MvPolynomial.C c) = algebraMap ℂ (DirectSum ℤ (ModularForm 𝒮ℒ)) c :=
  MvPolynomial.aeval_C _ c

/-- `evalE₄E₆` maps the monomial `X₀^a * X₁^b` to `(of _ 4 E₄)^a * (of _ 6 E₆)^b`. -/
lemma evalE₄E₆_monomial (a b : ℕ) :
    evalE₄E₆ (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b := by
  rw [map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1]

/-- For even `k ≥ 4`, there exist `a, b ∈ ℕ` with `4a + 6b = k`. -/
private lemma exists_monomial_weight {k : ℕ} (hk : 4 ≤ k) (hkeven : Even k) :
    ∃ a b : ℕ, 4 * a + 6 * b = k := by
  obtain ⟨m, rfl⟩ := hkeven
  rcases Nat.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact ⟨n, 0, by omega⟩
  · exact ⟨n - 1, 1, by omega⟩

/-! ### Surjectivity of `evalE₄E₆` -/

/-- In a 1-dimensional weight space, if `g ≠ 0` is in the image of `evalE₄E₆`,
then every element of that weight is in the image. -/
private lemma surj_of_rank_one {k : ℤ}
    (hrank : Module.rank ℂ (ModularForm 𝒮ℒ k) = 1) {g : ModularForm 𝒮ℒ k} (hg : g ≠ 0)
    (p : MvPolynomial (Fin 2) ℂ) (hp : evalE₄E₆ p = DirectSum.of _ k g)
    (f : ModularForm 𝒮ℒ k) :
    DirectSum.of _ k f ∈ Set.range evalE₄E₆ := by
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' g hg).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) f
  exact ⟨MvPolynomial.C c * p, by
    rw [map_mul, evalE₄E₆_C, hp, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, ← DirectSum.of_smul]⟩

/-- The product `f * g` of two modular forms with constant-term-1 q-expansions is nonzero. -/
private lemma mul_modularForm_ne_zero_of_qExpansion_coeff_zero_eq_one {k₁ k₂ : ℤ}
    (f : ModularForm 𝒮ℒ k₁) (g : ModularForm 𝒮ℒ k₂)
    (hf : (qExpansion 1 f).coeff 0 = 1) (hg : (qExpansion 1 g).coeff 0 = 1) :
    f.mul g ≠ 0 := by
  intro h
  have : (qExpansion 1 (f.mul g)).coeff 0 = 0 := by
    rw [show (f.mul g : ModularForm 𝒮ℒ (k₁ + k₂)) = 0 from h]
    simp [UpperHalfPlane.qExpansion_zero]
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f g,
    PowerSeries.coeff_mul] at this
  simp [hf, hg] at this

/-- The 0th q-expansion coefficient of `(of _ 4 E₄)^a * (of _ 6 E₆)^b` evaluated at
weight `n = 4a + 6b` equals `1`. -/
private lemma monomial_qExpansion_coeff_zero_eq_one {n a b : ℕ} (hab : 4 * a + 6 * b = n) :
    (qExpansion 1
      ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b) (n : ℤ))).coeff 0 = 1 := by
  -- TODO: complete proof. Strategy: show the product is concentrated at weight n,
  -- use ModularForm.qExpansion_mul and ModularForm.qExpansion_of_pow to compute
  -- the q-expansion as `(qExpansion E₄)^a * (qExpansion E₆)^b`, then use
  -- E_qExpansion_coeff_zero to reduce to 1 * 1 = 1.
  sorry

/-- For weight 12 ≤ n, every cusp form of weight n is `Δ * h` for some modular form
`h` of weight `n - 12`. Lifted to the graded ring. -/
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
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine ModularForm.gradedMonoid_eq_of_cast ?_ ?_
  · change (↑n - 12 + 12 : ℤ) = ↑n; ring
  ext z
  set hcusp := (ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp hg
  change ((CuspForm.discriminantEquiv (ModularForm.toCuspForm g hcusp)).mul
      ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12)) z = g z
  have hdiv : (CuspForm.discriminantEquiv (ModularForm.toCuspForm g hcusp)) z =
      g z / ModularForm.discriminant z :=
    CuspForm.divDiscriminant_apply (ModularForm.toCuspForm g hcusp) z
  rw [ModularForm.coe_mul, Pi.mul_apply, hdiv]
  change g z / ModularForm.discriminant z * ModularForm.discriminant z = g z
  exact div_mul_cancel₀ _ (discriminant_ne_zero z)

/-- The discriminant `Δ`, viewed as a modular form of weight 12, lies in the range of
`evalE₄E₆`. -/
private lemma discriminant_mem_range_evalE₄E₆ :
    DirectSum.of (ModularForm 𝒮ℒ) 12
        ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12) ∈ Set.range evalE₄E₆ := by
  refine ⟨(1 / 1728 : ℂ) • (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2), ?_⟩
  simp only [map_smul, map_sub, map_pow, evalE₄E₆_X0, evalE₄E₆_X1]
  rw [← discriminant_eq_E₄_cube_sub_E₆_sq_graded]

/-- Weight casting: rewriting the index of `DirectSum.of` along an equality of weights. -/
private lemma directSumOf_cast_eq {k₁ k₂ : ℤ} (hk : k₁ = k₂) (x : ModularForm 𝒮ℒ k₁) :
    DirectSum.of (ModularForm 𝒮ℒ) k₁ x = DirectSum.of (ModularForm 𝒮ℒ) k₂ (hk ▸ x) := by
  subst hk; rfl

/-- Inductive step: for `n ≥ 12` even, surjectivity at weight `n` follows from surjectivity
at all lower weights via the cusp-form / `Δ` decomposition. -/
private lemma surj_at_weight_inductive {n : ℕ} (hn12 : 12 ≤ n) (hk_even : Even (n : ℤ))
    (ih : ∀ m < n, ∀ (f : ModularForm 𝒮ℒ ↑m),
      DirectSum.of _ (↑m : ℤ) f ∈ Set.range evalE₄E₆)
    (f : ModularForm 𝒮ℒ ↑n) :
    DirectSum.of _ (↑n : ℤ) f ∈ Set.range evalE₄E₆ := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 4 * a + 6 * b = n :=
    exists_monomial_weight (by omega) (by exact_mod_cast hk_even)
  set mo := DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a * DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b
  set mn := mo (↑n : ℤ)
  set c := (qExpansion 1 f).coeff 0
  have hmn_coeff : (qExpansion 1 mn).coeff 0 = 1 := monomial_qExpansion_coeff_zero_eq_one hab
  have hg_cusp : ModularForm.IsCuspForm (f - c • mn) := by
    -- TODO: fill in via qExpansion linearity (subtraction + smul).
    sorry
  have hcast : ((↑n : ℤ) - 12 : ℤ) = ((n - 12 : ℕ) : ℤ) := by omega
  set h' := CuspForm.discriminantEquiv
    (ModularForm.toCuspForm (f - c • mn)
      ((ModularForm.isCuspForm_iff_coeffZero_eq_zero _).mp hg_cusp))
  have hg_ds : DirectSum.of (ModularForm 𝒮ℒ) (↑n : ℤ) (f - c • mn) =
      DirectSum.of _ ((↑n : ℤ) - 12) h' *
      DirectSum.of _ 12
        ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12) :=
    cuspForm_eq_discriminant_mul _ hg_cusp
  have hih : DirectSum.of (ModularForm 𝒮ℒ) ((↑n : ℤ) - 12) h' ∈ Set.range evalE₄E₆ := by
    rw [directSumOf_cast_eq hcast]
    exact ih (n - 12) (by omega) (hcast ▸ h')
  have hg_in : DirectSum.of _ (↑n : ℤ) (f - c • mn) ∈ Set.range evalE₄E₆ := by
    rw [hg_ds]
    obtain ⟨p1, hp1⟩ := hih
    obtain ⟨p2, hp2⟩ := discriminant_mem_range_evalE₄E₆
    exact ⟨p1 * p2, by rw [map_mul, hp1, hp2]⟩
  have hmn_in : mo ∈ Set.range evalE₄E₆ :=
    ⟨MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b, evalE₄E₆_monomial a b⟩
  have hmn_eq : DirectSum.of _ (↑n : ℤ) mn = mo := by
    have h4 : ((a : ℤ) * 4 + b * 6) = ↑n := by push_cast [← hab]; ring
    simp only [mn, mo, DirectSum.ofPow, DirectSum.of_mul_of]
    rw [show (↑n : ℤ) = a • (4 : ℤ) + b • (6 : ℤ) from by
      simp only [Int.nsmul_eq_mul]; linarith, DirectSum.of_eq_same]
  have hf_ds : DirectSum.of _ (↑n : ℤ) f =
      DirectSum.of _ (↑n : ℤ) (f - c • mn) + c • DirectSum.of _ (↑n : ℤ) mn := by
    rw [← DirectSum.of_smul, ← map_add]
    congr 1
    abel
  rw [hf_ds, hmn_eq]
  obtain ⟨p1, hp1⟩ := hg_in
  obtain ⟨p2, hp2⟩ := hmn_in
  exact ⟨p1 + MvPolynomial.C c * p2, by
    rw [map_add, hp1, map_mul, evalE₄E₆_C, hp2,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]⟩

private lemma weight_eight_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ 8) = 1 :=
  (ModularForm.rank_eq_one_add_rank_cuspForm (by norm_num) ⟨4, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))

private lemma weight_ten_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ 10) = 1 :=
  (ModularForm.rank_eq_one_add_rank_cuspForm (by norm_num) ⟨5, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))

private lemma one_ne_zero_modularForm : (1 : ModularForm 𝒮ℒ 0) ≠ 0 := by
  intro h
  have := congr_arg (DFunLike.coe (F := ModularForm 𝒮ℒ 0)) h
  exact (one_ne_zero (α := ℂ)) (congr_fun this UpperHalfPlane.I)

/-- For each weight `k`, every element of weight `k` lies in the range of `evalE₄E₆`. -/
private lemma surj_of_weight : ∀ (k : ℤ) (f : ModularForm 𝒮ℒ k),
    DirectSum.of (ModularForm 𝒮ℒ) k f ∈ Set.range evalE₄E₆ := by
  intro k f
  by_cases hk_neg : k < 0
  · rw [(rank_zero_iff_forall_zero.mp (ModularForm.levelOne_neg_weight_rank_zero hk_neg)) f,
      map_zero]
    exact ⟨0, map_zero _⟩
  push Not at hk_neg
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
  clear hk_neg
  revert f
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  intro f
  by_cases hk_odd : Odd (n : ℤ)
  · rw [ModularForm.levelOne_odd_weight_eq_zero hk_odd f, map_zero]
    exact ⟨0, map_zero _⟩
  rw [Int.not_odd_iff_even] at hk_odd
  by_cases hn12 : n < 12
  · interval_cases n
    · exact surj_of_rank_one ModularForm.levelOne_weight_zero_rank_one
        one_ne_zero_modularForm 1 (by rw [map_one]; rfl) f
    · rcases hk_odd with ⟨r, hr⟩; omega
    · rw [(rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero) f, map_zero]
      exact ⟨0, map_zero _⟩
    · rcases hk_odd with ⟨r, hr⟩; omega
    · exact surj_of_rank_one ModularForm.levelOne_weight_four_rank_one
        (show E₄ ≠ 0 from E_ne_zero (by norm_num) ⟨2, rfl⟩) (MvPolynomial.X 0) evalE₄E₆_X0 f
    · rcases hk_odd with ⟨r, hr⟩; omega
    · exact surj_of_rank_one ModularForm.levelOne_weight_six_rank_one
        (show E₆ ≠ 0 from E_ne_zero (by norm_num) ⟨3, rfl⟩) (MvPolynomial.X 1) evalE₄E₆_X1 f
    · rcases hk_odd with ⟨r, hr⟩; omega
    · refine surj_of_rank_one weight_eight_rank_one
        (mul_modularForm_ne_zero_of_qExpansion_coeff_zero_eq_one E₄ E₄
          (E_qExpansion_coeff_zero _ ⟨2, rfl⟩) (E_qExpansion_coeff_zero _ ⟨2, rfl⟩))
        (MvPolynomial.X 0 ^ 2) ?_ f
      rw [map_pow, evalE₄E₆_X0, pow_two, DirectSum.of_mul_of]
      apply DirectSum.of_eq_of_gradedMonoid_eq
      exact ModularForm.gradedMonoid_eq_of_cast (show ((4 : ℤ) + 4 : ℤ) = 8 from by norm_num).symm
        rfl
    · rcases hk_odd with ⟨r, hr⟩; omega
    · refine surj_of_rank_one weight_ten_rank_one
        (mul_modularForm_ne_zero_of_qExpansion_coeff_zero_eq_one E₄ E₆
          (E_qExpansion_coeff_zero _ ⟨2, rfl⟩) (E_qExpansion_coeff_zero _ ⟨3, rfl⟩))
        (MvPolynomial.X 0 * MvPolynomial.X 1) ?_ f
      rw [map_mul, evalE₄E₆_X0, evalE₄E₆_X1, DirectSum.of_mul_of]
      apply DirectSum.of_eq_of_gradedMonoid_eq
      exact ModularForm.gradedMonoid_eq_of_cast (show ((4 : ℤ) + 6 : ℤ) = 10 from by norm_num).symm
        rfl
    · rcases hk_odd with ⟨r, hr⟩; omega
  · push Not at hn12
    exact surj_at_weight_inductive hn12 hk_odd ih f

/-- The evaluation homomorphism `evalE₄E₆` is surjective. -/
theorem evalE₄E₆_surjective : Function.Surjective evalE₄E₆ := by
  classical
  intro x
  suffices x ∈ Set.range evalE₄E₆ from this
  rw [show x = x.sum (fun i m => DirectSum.of _ i m) from (DFinsupp.sum_single (f := x)).symm,
    show (Set.range evalE₄E₆ : Set _) = ↑evalE₄E₆.range from (AlgHom.coe_range evalE₄E₆).symm]
  exact Subalgebra.sum_mem _ (fun k _ => surj_of_weight k (x k))

/-- The evaluation homomorphism `evalE₄E₆` is injective: `E₄` and `E₆` are algebraically
independent. -/
theorem evalE₄E₆_injective : Function.Injective evalE₄E₆ := by
  -- Port from `LeanModularForms/Modularforms/Generators/Injectivity.lean`.
  -- Decompose into weighted-homogeneous components (weights `![4, 6]`); show each maps
  -- independently into a single graded piece. Per-weight injectivity is by strong induction
  -- on the weight, using the relation `X₀³ - X₁² = 1728 · Δ_poly`.
  sorry

/-- The graded ring of level-1 modular forms is isomorphic to the polynomial ring
`ℂ[X₀, X₁]` via evaluation at `E₄` and `E₆`. -/
noncomputable def modularFormsEquivMvPolynomial :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] DirectSum ℤ (ModularForm 𝒮ℒ) :=
  AlgEquiv.ofBijective evalE₄E₆ ⟨evalE₄E₆_injective, evalE₄E₆_surjective⟩

/-- `E₄` and `E₆` generate the entire graded ring of level 1 modular forms as an
`ℂ`-algebra. -/
theorem E₄E₆_generate :
    Algebra.adjoin ℂ ({DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆} : Set (DirectSum ℤ (ModularForm 𝒮ℒ))) = ⊤ := by
  rw [show ({DirectSum.of (ModularForm 𝒮ℒ) 4 E₄, DirectSum.of (ModularForm 𝒮ℒ) 6 E₆} : Set _) =
      Set.range (![DirectSum.of _ 4 E₄, DirectSum.of _ 6 E₆] : Fin 2 → _)
    from (Matrix.range_cons_cons_empty _ _ _).symm,
    Algebra.adjoin_range_eq_range_aeval,
    show MvPolynomial.aeval (![DirectSum.of _ 4 E₄, DirectSum.of _ 6 E₆] : Fin 2 → _) =
      evalE₄E₆ from rfl]
  exact (AlgHom.range_eq_top evalE₄E₆).mpr evalE₄E₆_surjective

end ModularForm

end
