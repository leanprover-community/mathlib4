/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!

# Singular cubics with nodes

We develop the basic theory of singular cubics with nodes.

## TODO (Andrew)
- classify singular cubics with nodes

-/

namespace WeierstrassCurve

variable {R K : Type*} [CommRing R] (E : WeierstrassCurve R) [Field K]

/-- A Weierstrass curve is in split-singular normal form if it is of the form `y² + a₁xy = x³`.

TODO(Andrew): Any singular cubic with a ractional point whose tangent splits in the base field
can be turned into split-singular normal form. -/
class IsSplitSingularNF (E : WeierstrassCurve R) where
  a₂ (E) : E.a₂ = 0
  a₃ (E) : E.a₃ = 0
  a₄ (E) : E.a₄ = 0
  a₆ (E) : E.a₆ = 0

section

variable [E.IsSplitSingularNF]

@[simp] alias a₂_of_isSplitSingularNF := IsSplitSingularNF.a₂
@[simp] alias a₃_of_isSplitSingularNF := IsSplitSingularNF.a₃
@[simp] alias a₄_of_isSplitSingularNF := IsSplitSingularNF.a₄
@[simp] alias a₆_of_isSplitSingularNF := IsSplitSingularNF.a₆
        lemma b₂_of_isSplitSingularNF : E.b₂ = E.a₁ ^ 2   := by simp [b₂]
@[simp] lemma b₄_of_isSplitSingularNF : E.b₄ = 0          := by simp [b₄]
@[simp] lemma b₆_of_isSplitSingularNF : E.b₆ = 0          := by simp [b₆]
@[simp] lemma b₈_of_isSplitSingularNF : E.b₈ = 0          := by simp [b₈]
        lemma c₄_of_isSplitSingularNF : E.c₄ = E.a₁ ^ 4   := by simp [c₄, b₂]; ring
        lemma c₆_of_isSplitSingularNF : E.c₆ = - E.a₁ ^ 6 := by simp [c₆, b₂]; ring
@[simp] lemma Δ_of_isSplitSingularNF  : E.Δ  = 0          := by simp [Δ]

end

section IsNodal

/-- We say that a `WeierstrassCurve` is nodal if its `Δ = 0` but its `c₄ ≠ 0`. -/
class IsNodal (E : WeierstrassCurve R) : Prop where
  c₄_eq_zero (E) : E.c₄ ≠ 0
  Δ_eq_zero (E) : E.Δ = 0

alias c₄_of_isNodal := IsNodal.c₄_eq_zero
@[simp] alias Δ_of_isNodal := IsNodal.Δ_eq_zero

lemma c₄_pow_three_of_isNodal [E.IsNodal] : E.c₄ ^ 3 = E.c₆ ^ 2 := by
  simpa [sub_eq_zero, @eq_comm R 0] using E.c_relation

lemma c₆_of_isNodal [IsReduced R] [E.IsNodal] : E.c₆ ≠ 0 :=
  fun e ↦ E.c₄_of_isNodal (by simpa [e] using E.c₄_pow_three_of_isNodal)

lemma a₁_of_isSplitSingularNF_of_isNodal [IsReduced R] [E.IsNodal] [E.IsSplitSingularNF] :
    E.a₁ ≠ 0 := by
  simpa [c₄_of_isSplitSingularNF] using E.c₄_of_isNodal

lemma pointEquivOfIsNodalOfIsSplitSingularNF.aux [IsReduced R]
    (E : WeierstrassCurve R) [E.IsSplitSingularNF]
    (x y : R) (h : E.toAffine.Nonsingular x y) :
    x ≠ 0 ∧ y ≠ -E.a₁ * x ∧ y ≠ 0 := by
  have H₁ : y ^ 2 + E.a₁ * x * y - x ^ 3 = 0 := by simpa [Affine.equation_iff'] using h.1
  by_contra H
  simp only [ne_eq, neg_mul, not_and_or, not_not] at H
  suffices x ^ 3 = 0 by aesop
  obtain (rfl | rfl | rfl) := H
  · simp
  · linear_combination -H₁
  · linear_combination -H₁

lemma pointEquivOfIsNodalOfIsSplitSingularNF_nonsingular
    (E : WeierstrassCurve K) [E.IsNodal] [E.IsSplitSingularNF] (k : K)
    (hk1 : k ≠ 1) (hk0 : k ≠ 0) :
    E.toAffine.Nonsingular (k * E.a₁ ^ 2 / (k - 1) ^ 2)
    (k * E.a₁ ^ 3 / (k - 1) ^ 3) := by
  convert_to E.toAffine.Nonsingular (k * E.a₁ ^ 2 * (k - 1) / (k - 1) ^ 3)
    (k * E.a₁ ^ 3 / (k - 1) ^ 3)
  · field_simp [sub_ne_zero.mpr hk1]; ring
  rw [Affine.nonsingular_div_iff (by simpa [sub_eq_zero]),
    Affine.equation_div_iff (by simpa [sub_eq_zero]), or_iff_not_imp_right]
  simp only [toAffine, a₃_of_isSplitSingularNF, zero_mul, add_zero, a₂_of_isSplitSingularNF,
    a₄_of_isSplitSingularNF, a₆_of_isSplitSingularNF, ne_eq, not_not, mul_zero]
  constructor
  · ring
  · intro H H'
    have : k * (k + 1) * E.a₁ ^ 3 = 0 := by linear_combination H
    obtain rfl : k = -1 := by
      simpa [add_eq_zero_iff_eq_neg, hk0, E.a₁_of_isSplitSingularNF_of_isNodal] using this
    have : E.a₁ ^ 4 * (-1 - 1) ^ 2 = 0 := by linear_combination -H'
    simp [sub_eq_zero, hk1, E.a₁_of_isSplitSingularNF_of_isNodal] at this

open pointEquivOfIsNodalOfIsSplitSingularNF in
/-- The group of rational points of `y² + a₁xy = x³` (`a₁ ≠ 0`) is isomorphic (as groups) to
`Kˣ`. -/
noncomputable
def pointEquivOfIsNodalOfIsSplitSingularNF [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsNodal] [E.IsSplitSingularNF] :
    E.toAffine.Point ≃+ Additive Kˣ where
  toFun
  | .zero => 0
  | .some (x := x) (y := y) h => Additive.ofMul
      (isUnit_iff_ne_zero (a := ((y + E.a₁ * x) / y)).mpr (by
      simpa [add_eq_zero_iff_eq_neg] using (aux E _ _ h).2)).unit
  invFun k := if H : k.toMul = 1 then 0 else .some (x := k.toMul * E.a₁ ^ 2 / (k.toMul - 1) ^ 2)
      (y := k.toMul * E.a₁ ^ 3 / (k.toMul - 1) ^ 3)
      (pointEquivOfIsNodalOfIsSplitSingularNF_nonsingular E k.toMul (by simpa) (by simp))
  left_inv
  | .zero => by simp; rfl
  | .some (x := x) (y := y) h => by
    suffices (y + E.a₁ * x) * E.a₁ ^ 2 * y ^ 2 = x * (y * (E.a₁ * x) ^ 2) ∧
      (y + E.a₁ * x) * E.a₁ ^ 3 * y ^ 3 = y * (y * (E.a₁ * x) ^ 3) by
      field_simp [E.a₁_of_isSplitSingularNF_of_isNodal, Units.ext_iff, div_eq_iff_mul_eq,
        (aux E _ _ h).1, (aux E _ _ h).2.2, this]
    have H₁ : y ^ 2 + E.a₁ * x * y - x ^ 3 = 0 := by simpa [Affine.equation_iff'] using h.1
    constructor
    · linear_combination H₁ * E.a₁ ^ 2 * y
    · linear_combination H₁ * E.a₁ ^ 3 * y ^ 2
  right_inv k := by
    dsimp only
    split_ifs with H
    · aesop
    · apply Additive.toMul.injective
      ext
      dsimp
      generalize k.toMul = k at H ⊢
      have hk0 : (k : K) ≠ 0 := by simp
      have hk1 : (k : K) ≠ 1 := by simpa
      generalize (k : K) = k at hk0 hk1 ⊢
      field_simp [hk0, hk1, sub_eq_zero, E.a₁_of_isSplitSingularNF_of_isNodal]
      ring_nf
  map_add'
  | .zero, .zero => by simp [← Affine.Point.zero_def]
  | .some h, .zero => by simp [← Affine.Point.zero_def]
  | .zero, .some h' => by simp [← Affine.Point.zero_def]
  | .some (x := x₁) (y := y₁) h₁, .some (x := x₂) (y := y₂) h₂ => by
    by_cases H : x₁ = x₂ ∧ y₁ = E.toAffine.negY x₂ y₂
    · obtain ⟨rfl, rfl⟩ : x₁ = x₂ ∧ y₁ = - y₂ - E.a₁ * x₂ := by simpa [Affine.negY] using H
      apply Additive.toMul.injective
      suffices 1 = y₂ / (E.a₁ * x₁ + y₂) * ((E.a₁ * x₁ + y₂) / y₂) by
        ext; simpa [neg_div, ← div_neg, add_comm y₂]
      rw [div_mul_div_cancel₀, div_self (aux E _ _ h₂).2.2]
      rw [ne_eq, add_eq_zero_iff_eq_neg', ← neg_mul]
      exact (aux E _ _ h₂).2.1
    simp only [Affine.Point.add_some H]
    apply Additive.toMul.injective
    ext
    have h₄ := aux E _ _ (Affine.nonsingular_add h₁ h₂ H)
    simp only [toAffine,
      a₂_of_isSplitSingularNF, sub_zero, neg_add_rev, a₃_of_isSplitSingularNF, sub_add_cancel,
      toMul_ofMul, IsUnit.unit_spec, toMul_add, Units.val_mul, div_eq_iff_mul_eq h₄.2.2]
    generalize hα : Affine.slope E x₁ x₂ y₁ y₂ = α
    suffices (y₁ + E.a₁ * x₁) * (y₂ + E.a₁ * x₂) *
        (-y₁ - α * (α + E.a₁) ^ 2 + (2 * α + E.a₁) * x₁ + (α + E.a₁) * x₂) =
      (-y₁ + α * x₁ * 2 + α * x₂ - α ^ 2 * (α + E.a₁)) * y₁ * y₂ by
      field_simp [(aux E _ _ h₁).2.2, (aux E _ _ h₂).2.2]
      linear_combination this
    simp only [toAffine, Affine.nonsingular_iff, Affine.equation_iff, a₃_of_isSplitSingularNF,
      zero_mul, add_zero, a₂_of_isSplitSingularNF, a₄_of_isSplitSingularNF, a₆_of_isSplitSingularNF,
      mul_zero, ne_eq, sub_zero] at h₁ h₂
    by_cases hx₁x₂ : x₁ = x₂
    · subst hx₁x₂
      replace H : y₁ ≠ E.toAffine.negY x₁ y₂ := by simpa using H
      have : (y₁ - y₂) * (y₁ - (-y₂ - E.a₁ * x₁)) = 0 := by
        linear_combination h₁.1 - h₂.1
      obtain rfl := sub_eq_zero.mp
        ((mul_eq_zero.mp this).resolve_right (by simpa [sub_eq_zero] using H))
      obtain rfl : (3 * x₁ ^ 2 - E.a₁ * y₁) / (y₁ - (-y₁ - E.a₁ * x₁)) = α := by
        simpa [Affine.slope_of_Y_ne rfl H, toAffine] using hα
      simp only [Affine.negY, a₃_of_isSplitSingularNF, sub_zero, ne_eq, toAffine] at H
      field_simp [sub_eq_zero, H]
      linear_combination
        E.a₁ * (E.a₁ * x₁ + 2 * y₁) ^ 7 *
          (E.a₁ ^ 4 * x₁ ^ 2 + E.a₁ ^ 3 * x₁ * y₁ + 9 * E.a₁ ^ 2 * x₁ ^ 3 +
            E.a₁ ^ 2 * y₁ ^ 2 + 27 * x₁ ^ 4) * h₁.1
    obtain H : (y₁ - y₂) / (x₁ - x₂) = α := by simpa [Affine.slope, hx₁x₂] using hα
    suffices (y₁ + E.a₁ * x₁) * (y₂ + E.a₁ * x₂) *
        (-y₁ * (x₁ - x₂) ^ 3 - (y₁ - y₂) * ((y₁ - y₂) + (x₁ - x₂) * E.a₁) ^ 2 +
        (2 * (y₁ - y₂) + (x₁ - x₂) * E.a₁) * x₁ * (x₁ - x₂) ^ 2 +
        ((y₁ - y₂) + (x₁ - x₂) * E.a₁) * x₂ * (x₁ - x₂) ^ 2) =
        (-y₁ * (x₁ - x₂) ^ 3 + (y₁ - y₂) * x₁ * 2 * (x₁ - x₂) ^ 2 + (y₁ - y₂) * x₂ * (x₁ - x₂) ^ 2 -
        (y₁ - y₂) ^ 2 * ((y₁ - y₂) + (x₁ - x₂) * E.a₁)) * y₁ * y₂ by
      rw [← (mul_left_injective₀ (pow_ne_zero 3 (sub_ne_zero_of_ne hx₁x₂))).eq_iff]
      convert this using 1 <;> field_simp [sub_ne_zero_of_ne hx₁x₂, ← H] <;> ring1
    linear_combination
      -h₁.1 * E.a₁ * (E.a₁ ^ 2 * (x₁ - x₂) ^ 2 * x₂ + 2 * E.a₁ * (x₁ * y₂ + x₂ * y₁) * (x₁ - x₂) -
        (E.a₁ * x₁ - 2 * y₁) * x₁ * y₂ - (2 * x₁ - 3 * x₂) * x₂ ^ 3 + x₂ * y₁ * (y₁ - 4 * y₂)) +
      h₂.1 * E.a₁ * (E.a₁ ^ 2 * (x₁ - x₂) ^ 2 * x₁ - 2 * E.a₁ * (x₁ * y₂ + x₂ * y₁) * (x₁ - x₂) -
        (E.a₁ * x₂ - 2 * y₂) * x₂ * y₁ - (2 * x₂ - 3 * x₁) * x₁ ^ 3 + x₁ * y₂ * (y₂ - 4 * y₁)
        + 5 * (x₁ - x₂) * (y₁ ^ 2 + E.a₁ * x₁ * y₁ - x₁ ^ 3))

open pointEquivOfIsNodalOfIsSplitSingularNF in
lemma pointEquivOfIsNodalOfIsSplitSingularNF_some [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsNodal] [E.IsSplitSingularNF]
    {x y : K} (h : E.toAffine.Nonsingular x y) :
  E.pointEquivOfIsNodalOfIsSplitSingularNF (.some h) = Additive.ofMul
      (isUnit_iff_ne_zero (a := ((y + E.a₁ * x) / y)).mpr (by
      simpa [add_eq_zero_iff_eq_neg] using (aux E _ _ h).2)).unit := rfl

@[simp]
lemma pointEquivOfIsNodalOfIsSplitSingularNF_some_val [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsNodal] [E.IsSplitSingularNF]
    {x y : K} (h : E.toAffine.Nonsingular x y) :
    (E.pointEquivOfIsNodalOfIsSplitSingularNF (.some h)).toMul = (y + E.a₁ * x) / y := rfl

@[simp]
lemma pointEquivOfIsNodalOfIsSplitSingularNF_symm_of_ne [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsNodal] [E.IsSplitSingularNF] (k : Kˣ) (hk : k ≠ 1) :
    E.pointEquivOfIsNodalOfIsSplitSingularNF.symm (.ofMul k) =
    .some (x := k * E.a₁ ^ 2 / (k - 1) ^ 2) (y := k * E.a₁ ^ 3 / (k - 1) ^ 3)
      (pointEquivOfIsNodalOfIsSplitSingularNF_nonsingular E k (by simpa) (by simp)) :=
  dif_neg (by simpa)

end IsNodal

end WeierstrassCurve
