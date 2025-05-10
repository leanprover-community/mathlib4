/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Unbundled.FiniteExtension
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# algNormOfAlgEquiv and algNormOfAut

Let `K` be a nonarchimedean normed field and `L/K` be a finite algebraic extension. In the comments,
`‖ ⬝ ‖` denotes any power-multiplicative `K`-algebra norm on `L` extending the norm on `K`.

## Main Definitions

* `IsNonarchimedean.algNormOfAlgEquiv` : given `σ : L ≃ₐ[K] L`, the function `L → ℝ` sending `x : L`
to `‖ σ x ‖` is a `K`-algebra norm on `L`.
* `IsNonarchimedean.algNormOfAut` : the function `L → ℝ` sending `x : L` to the maximum of `‖ σ x ‖`
over all `σ : L ≃ₐ[K] L` is a `K`-algebra norm on `L`.

## Main Results
* `IsNonarchimedean.isPowMul_algNormOfAlgEquiv` : `algNormOfAlgEquiv` is power-multiplicative.
* `IsNonarchimedean.isNonarchimedean_algNormOfAlgEquiv` : `algNormOfAlgEquiv` is nonarchimedean.
* `IsNonarchimedean.algNormOfAlgEquiv_extends` : `algNormOfAlgEquiv` extends the norm on `K`.
* `IsNonarchimedean.isPowMul_algNormOfAut` : `algNormOfAut` is power-multiplicative.
* `IsNonarchimedean.isNonarchimedean_algNormOfAut` : `algNormOfAut` is nonarchimedean.
* `IsNonarchimedean.algNormOfAut_extends` : `algNormOfAut` extends the norm on `K`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

algNormOfAlgEquiv, algNormOfAut, norm, nonarchimedean
-/

open scoped NNReal

noncomputable section

variable {K : Type*} [NormedField K] {L : Type*} [Field L] [Algebra K L]
  (h_fin : FiniteDimensional K L)

namespace IsNonarchimedean
section algNormOfAlgEquiv

/-- Given a normed field `K`, a finite algebraic extension `L/K` and `σ : L ≃ₐ[K] L`, the function
`L → ℝ` sending `x : L` to `‖ σ x ‖`, where `‖ ⬝ ‖` is any power-multiplicative algebra norm on `L`
extending the norm on `K`, is an algebra norm on `K`. -/
def algNormOfAlgEquiv (hna : IsNonarchimedean (norm : K → ℝ)) (σ : L ≃ₐ[K] L) :
    AlgebraNorm K L where
  toFun x     := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hna) (σ x)
  map_zero'   := by simp [map_eq_zero_iff_eq_zero, EmbeddingLike.map_eq_zero_iff]
  add_le' x y := by simp [map_add σ, map_add_le_add]
  neg' x      := by simp [map_neg σ, map_neg_eq_map]
  mul_le' x y := by simp [map_mul σ, map_mul_le_mul]
  smul' x y   := by simp [map_smul σ, map_smul_eq_mul]
  eq_zero_of_map_eq_zero' x hx := EmbeddingLike.map_eq_zero_iff.mp (eq_zero_of_map_eq_zero _ hx)

theorem algNormOfAlgEquiv_apply (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) :
    algNormOfAlgEquiv h_fin hna σ x =
      Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)
        (σ x) := rfl

/-- The algebra norm `algNormOfAlgEquiv` is power-multiplicative. -/
theorem isPowMul_algNormOfAlgEquiv (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsPowMul (algNormOfAlgEquiv h_fin hna σ) := by
  intro x n hn
  simp only [algNormOfAlgEquiv_apply, map_pow σ x n]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hna)).1 _ hn

/-- The algebra norm `algNormOfAlgEquiv` is nonarchimedean. -/
theorem isNonarchimedean_algNormOfAlgEquiv (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsNonarchimedean (algNormOfAlgEquiv h_fin hna σ) := by
  intro x y
  simp only [algNormOfAlgEquiv_apply, map_add σ]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hna)).2.2 _ _

/-- The algebra norm `algNormOfAlgEquiv` extends the norm on `K`. -/
theorem algNormOfAlgEquiv_extends (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) (x : K) :
    (algNormOfAlgEquiv h_fin hna σ) ((algebraMap K L) x) = ‖x‖ := by
  simp only [algNormOfAlgEquiv_apply, AlgEquiv.commutes]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hna)).2.1 _

end algNormOfAlgEquiv

section algNormOfAut

/-- The function `L → ℝ` sending `x : L` to the maximum of `algNormOfAlgEquiv h_fin hna σ` over
  all `σ : L ≃ₐ[K] L` is an algebra norm on `L`. -/
def algNormOfAut (hna : IsNonarchimedean (norm : K → ℝ)) : AlgebraNorm K L where
  toFun x := iSup fun σ : L ≃ₐ[K] L ↦ algNormOfAlgEquiv h_fin hna σ x
  map_zero' := by simp only [map_zero, ciSup_const]
  add_le' x y := ciSup_le fun σ ↦ le_trans (map_add_le_add (algNormOfAlgEquiv h_fin hna σ) x y)
    (add_le_add (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _))
      (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _)))
  neg' x := by simp only [map_neg_eq_map]
  mul_le' x y := ciSup_le fun σ ↦ le_trans (map_mul_le_mul (algNormOfAlgEquiv h_fin hna σ) x y)
    (mul_le_mul (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _))
      (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _)) (apply_nonneg _ _)
      (le_ciSup_of_le (Set.finite_range _).bddAbove σ (apply_nonneg _ _)))
  eq_zero_of_map_eq_zero' x := by
    contrapose!
    exact fun hx ↦ ne_of_gt (lt_of_lt_of_le (map_pos_of_ne_zero _ hx)
      (le_ciSup (Set.range fun σ : L ≃ₐ[K] L ↦ algNormOfAlgEquiv h_fin hna σ x).toFinite.bddAbove
        AlgEquiv.refl))
  smul' r x := by
    simp only [AlgebraNormClass.map_smul_eq_mul, NormedRing.toRingNorm_apply,
      Real.mul_iSup_of_nonneg (norm_nonneg _)]

@[simp]
theorem algNormOfAut_apply (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) :
    algNormOfAut h_fin hna x = iSup fun σ : L ≃ₐ[K] L ↦ algNormOfAlgEquiv h_fin hna σ x :=
  rfl

/-- The algebra norm `algNormOfAut` is power-multiplicative. -/
theorem isPowMul_algNormOfAut (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsPowMul (algNormOfAut h_fin hna) := by
  intro x n hn
  rw [algNormOfAut_apply, algNormOfAut_apply, Real.iSup_pow
    (fun σ ↦ apply_nonneg (algNormOfAlgEquiv h_fin hna σ) x)]
  exact iSup_congr fun σ ↦ isPowMul_algNormOfAlgEquiv h_fin σ hna _ hn

/-- The algebra norm `algNormOfAut` is nonarchimedean. -/
theorem isNonarchimedean_algNormOfAut (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsNonarchimedean (algNormOfAut h_fin hna) := fun x y ↦
  ciSup_le fun σ ↦ le_trans ((isNonarchimedean_algNormOfAlgEquiv h_fin σ hna) x y)
    (max_le_max (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _))
      (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _)))

/-- The algebra norm `algNormOfAut` extends the norm on `K`. -/
theorem algNormOfAut_extends (hna : IsNonarchimedean (norm : K → ℝ)) (x : K) :
    (algNormOfAut h_fin hna) (algebraMap K L x) = ‖x‖ := by
  rw [algNormOfAut, ← AlgebraNorm.toFun_eq_coe]
  simp [AlgebraNorm.toFun_eq_coe, algNormOfAlgEquiv_extends h_fin _ hna x, ciSup_const]

end algNormOfAut

end IsNonarchimedean
