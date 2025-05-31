/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!

# Singular cubics with cusps

We develop the basic theory of singular cubics with cusps.

## TODO (Andrew)
- classify singular cubics with cusps

-/

namespace WeierstrassCurve

variable {R K : Type*} [CommRing R] [Field K] [DecidableEq K]

variable (R) in
/-- The standard cusp `y² = x³`. -/
@[simps]
def standardCusp : WeierstrassCurve R :=
  ⟨0, 0, 0, 0, 0⟩

@[local simp]
lemma standardCusp_equation_iff {x y : R} :
    (standardCusp R).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 := by
  simp [Affine.equation_iff]

@[local simp]
lemma standardCusp_nonsingular_iff [IsDomain R] {x y : R} :
    (standardCusp R).toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 ∧ x ≠ 0 ∧ y ≠ 0 := by
  suffices y ^ 2 = x ^ 3 → ((3 : R) ≠ 0 ∧ x ≠ 0 ∨ (2 : R) ≠ 0 ∧ y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0) by
    simpa [Affine.nonsingular_iff, standardCusp_equation_iff, eq_neg_iff_add_eq_zero, ← two_mul]
  intro H
  have h : y = 0 ↔ x = 0 := by rw [← pow_eq_zero_iff two_ne_zero, H, pow_eq_zero_iff three_ne_zero]
  simp only [ne_eq, h, and_self, ← or_and_right, and_iff_right_iff_imp]
  exact fun _ ↦ not_and_or.mp fun h ↦ one_ne_zero (by linear_combination h.1 - h.2)

/-- The group of nonsigular rational points on the standard cusp `y² = x³`
is isomorphic (as groups) to `K`. -/
noncomputable
def standardCuspEquiv : (standardCusp K).toAffine.Point ≃+ K where
  toFun
  | .zero => 0
  | .some (x := x) (y := y) h => x / y
  invFun k :=
    if hk : k = 0 then 0 else
      .some (x := k⁻¹ ^ 2) (y := k⁻¹ ^ 3) (by simp [pow_right_comm _ 2 3, hk])
  left_inv
  | .zero => dif_pos rfl
  | .some (x := x) (y := y) h => by
    simp only [div_eq_zero_iff, inv_div]
    split_ifs with h'
    · obtain rfl | rfl := h'
      · by_cases y = 0 <;> simp [Affine.nonsingular_iff', Affine.equation_iff', *] at h
      · by_cases x = 0 <;> simp [Affine.nonsingular_iff', Affine.equation_iff', *] at h
    · simp only [Affine.Point.some.injEq]
      have : y ^ 2 = x ^ 3 := by simpa [Affine.equation_iff', sub_eq_zero] using h.1
      push_neg at h'
      constructor
      · field_simp [this, h'.1]; ring
      · field_simp [← this, h'.2]; ring
  right_inv k := by
    simp only [inv_pow]
    split_ifs with h'
    · simp [h']
    · field_simp [h']; ring
  map_add'
  | .zero, .zero => by simp [← Affine.Point.zero_def]
  | .some h, .zero => by simp [← Affine.Point.zero_def]
  | .zero, .some h' => by simp [← Affine.Point.zero_def]
  | .some (x := x₁) (y := y₁) h₁, .some (x := x₂) (y := y₂) h₂ => by
    by_cases H : x₁ = x₂ ∧ y₁ = (standardCusp K).toAffine.negY x₂ y₂
    · obtain ⟨rfl, rfl⟩ : x₁ = x₂ ∧ y₁ = -y₂ := by simpa [Affine.negY] using H
      simp [div_neg]
    simp only [Affine.Point.add_some H]
    have h₃ := Affine.nonsingular_add h₁ h₂ H
    replace H : x₁ = x₂ → y₁ ≠ -y₂ := by simpa [Affine.negY] using H
    simp only [standardCusp_nonsingular_iff, standardCusp_equation_iff] at h₁ h₂ h₃
    refine div_eq_of_eq_mul h₃.2.2 ?_
    generalize hα : (standardCusp K).toAffine.slope x₁ x₂ y₁ y₂ = α
    suffices (α ^ 2 - x₁ - x₂) * (y₁ * y₂) =
        (x₁ * y₂ + x₂ * y₁) * (-y₁ + -(α * (α ^ 2 - x₁ - x₂ - x₁))) by
      field_simp [h₁.2.2, h₂.2.2, this]
    by_cases hx₁x₂ : x₁ = x₂
    · subst hx₁x₂
      obtain rfl := (eq_or_eq_neg_of_sq_eq_sq _ _ (h₁.1.trans h₂.1.symm)).resolve_right (H rfl)
      have : 3 * x₁ ^ 2 / (2 * y₁) = α := by simpa [Affine.slope, H rfl, two_mul] using hα
      have h2 : (2 : K) ≠ 0 := fun h ↦ H rfl <| by linear_combination y₁ * h
      simp only [← this]
      field_simp [h₁.2.2]
      linear_combination - h₁.1 * x₁ ^ 4 * y₁ ^ 3 * 216
    replace hα : (y₁ - y₂) / (x₁ - x₂) = α := by simpa [Affine.slope, hx₁x₂] using hα
    field_simp [sub_ne_zero_of_ne hx₁x₂, ← hα]
    linear_combination
      (x₁ - x₂) ^ 2 * (y₁ - y₂) * ((y₂ * (2 * x₁ - 3 * x₂) + y₁ * x₂) * h₁.1 +
        (y₂ * x₁ - y₁ * (3 * x₁ - 2 * x₂)) * h₂.1)

@[simp]
lemma standardCuspEquiv_some {x y : K}
    (h : (standardCusp K).toAffine.Nonsingular x y) :
  standardCuspEquiv (.some h) = x / y := rfl

@[simp]
lemma standardCuspEquiv_symm_of_ne {k : K} (hk : k ≠ 0) :
    standardCuspEquiv.symm k =
      .some (x := k⁻¹ ^ 2) (y := k⁻¹ ^ 3) (by simp [pow_right_comm _ 2 3, hk]) :=
  dif_neg hk

lemma standardCuspEquiv_symm_inv_of_ne {k : K} (hk : k ≠ 0) :
    standardCuspEquiv.symm k⁻¹ =
      .some (x := k ^ 2) (y := k ^ 3) (by simp [pow_right_comm _ 2 3, hk]) := by
  rw [standardCuspEquiv_symm_of_ne]
  · congr <;> simp
  · simpa

end WeierstrassCurve
