/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Surjectivity of `ℂ[X₀, X₁] → ⨁ k, ModularForm 𝒮ℒ k`

This file defines the evaluation map `evalE₄E₆ : ℂ[X₀, X₁] →ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k`
sending `X₀ ↦ E₄`, `X₁ ↦ E₆`, and proves it is surjective.

## Main definitions

* `ModularForm.evalE₄E₆`: the evaluation homomorphism
  `ℂ[X₀, X₁] →ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k` sending `X₀ ↦ E₄`, `X₁ ↦ E₆`.

## Main results

* `ModularForm.evalE₄E₆_surjective`: `evalE₄E₆` is surjective — every level-1 modular form is
  a polynomial in `E₄` and `E₆`.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups EisensteinSeries

namespace ModularForm

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
  exacts [⟨n, 0, by lia⟩, ⟨n - 1, 1, by lia⟩]

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
    exists_monomial_weight (by lia) (by exact_mod_cast hk_even)
  set mn := (DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
    DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b) (↑n : ℤ)
  set c := (qExpansion 1 f).coeff 0
  have hg_cusp : ModularForm.IsCuspForm (f - c • mn) :=
    ModularForm.sub_smul_isCuspForm f mn (monomial_qExpansion_coeff_zero_eq_one hab)
  have hcast : ((↑n : ℤ) - 12 : ℤ) = ((n - 12 : ℕ) : ℤ) := by lia
  obtain ⟨p1, hp1⟩ : DirectSum.of (ModularForm 𝒮ℒ) ((↑n : ℤ) - 12)
      (CuspForm.discriminantEquiv (ModularForm.toCuspForm (f - c • mn)
        ((ModularForm.isCuspForm_iff_coeffZero_eq_zero _).mp hg_cusp))) ∈
        Set.range evalE₄E₆ := by
    rw [DirectSum.of_eq_of_eq hcast]
    exact ih _ (by lia) _
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

private lemma one_ne_zero_modularForm : (1 : ModularForm 𝒮ℒ 0) ≠ 0 := fun h ↦
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
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by lia⟩
  clear hk_neg
  revert f
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  intro f
  by_cases hk_odd : Odd (n : ℤ)
  · exact surj_of_zero_form (fun f ↦ ModularForm.levelOne_odd_weight_eq_zero hk_odd f) f
  rw [Int.not_odd_iff_even] at hk_odd
  by_cases hn12 : n < 12
  · exact surj_at_small_weight hn12 hk_odd f
  push Not at hn12
  exact surj_at_weight_inductive hn12 hk_odd ih f

/-- The evaluation homomorphism `evalE₄E₆` is surjective. -/
theorem evalE₄E₆_surjective : Function.Surjective evalE₄E₆ := by
  classical
  intro x
  rw [show x = x.sum (fun i m ↦ DirectSum.of _ i m) from (DFinsupp.sum_single (f := x)).symm,
    ← AlgHom.mem_range]
  exact Subalgebra.sum_mem _ fun k _ ↦ surj_of_weight k (x k)

end ModularForm

end
