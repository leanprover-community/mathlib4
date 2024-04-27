/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.StandardGeometricRepresentation
import Mathlib.GroupTheory.Coxeter.Inversion

/-! # The long element
Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

-/

namespace CoxeterSystem

variable {B : Type*}
variable {W : Type*} [Group W] [Finite W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "α" => CoxeterMatrix.simpleRoot
local prefix:100 "ρ" => cs.sgr
local notation:max "⟪"  a  ","  b  "⟫" => M.standardBilinForm a b
local notation:100 "σ" i => M.simpleOrthoReflection i
local notation "V" => B →₀ ℝ

/- The maximum length of the elements of `W`. -/
private noncomputable def maxLength (cs : CoxeterSystem M W) : ℕ := sorry

/- The set of all elements of `W` with maximum length. (It will turn out that there is a unique
such element, so this is a singleton.) -/
private noncomputable def maxLengthElementSet (cs : CoxeterSystem M W) : Set W := sorry

private lemma maxLengthElementSet_nonempty : Nonempty cs.maxLengthElementSet := sorry

private lemma isRightDescent_of_mem_maxLengthElementSet (w : cs.maxLengthElementSet) (i : B) :
    cs.IsRightDescent w.val i := by sorry

private lemma sgr_apply_neg_of_pos_of_maxLengthElementSet {v : V} (w : cs.maxLengthElementSet)
    (hv : v > 0) : (ρ w.val) v < 0 := by sorry

private lemma sgr_apply_pos_of_neg_of_maxLengthElementSet {v : V} (w : cs.maxLengthElementSet)
    (hv : v < 0) : (ρ w.val) v > 0 := by sorry

private lemma sgr_apply_pos_of_pos {v : V} (w w' : cs.maxLengthElementSet)
    (hv : v > 0) : (ρ (w.val * w'.val)) v > 0 := by sorry

private lemma maxLengthElement_mul_maxLengthElement_eq_one (w w' : cs.maxLengthElementSet) :
    w.val * w'.val = 1 := by sorry

private lemma maxLengthElementSet_subsingleton : Subsingleton cs.maxLengthElementSet := by
  sorry

/-- The unique element of `W` with maximum length. -/
noncomputable def longElement (cs : CoxeterSystem M W) : W := sorry

local notation "w₀" => cs.longElement

private lemma longElement_mem_maxLengthElementSet : w₀ ∈ cs.maxLengthElementSet := by sorry

private lemma length_longElement_eq_maxLength : ℓ w₀ = cs.maxLength := by sorry

theorem length_le_length_longElement (w : W) : ℓ w ≤ ℓ w₀ := by sorry

theorem eq_longElement_of_length_eq_length_longElement {w : W} (hw : ℓ w = ℓ w₀) : w = w₀ := by
  sorry

theorem eq_longElement_iff_length_eq_length_longElement (w : W) : ℓ w = ℓ w₀ ↔ w = w₀ := by
  sorry

theorem isRightDescent_longElement (i : B) : cs.IsRightDescent w₀ i := by sorry

theorem isLeftDescent_longElement (i : B) : cs.IsLeftDescent w₀ i := by sorry

theorem isRightInversion_longElement {t : W} (ht : cs.IsReflection t) :
    cs.IsRightInversion w₀ t := by sorry

theorem isLeftInversion_longElement {t : W} (ht : cs.IsReflection t) :
    cs.IsLeftInversion w₀ t := by sorry

theorem sgr_longElement_apply_neg_of_pos {v : V} (hv : v > 0) :
    (ρ w₀) v < 0 := by sorry

theorem sgr_longElement_apply_pos_of_neg {v : V} (hv : v < 0) :
    (ρ w₀) v > 0 := by sorry

@[simp]
theorem longElement_mul_self : w₀ * w₀ = 1 := by sorry

@[simp]
theorem longElement_sq : w₀ ^ 2 = 1 := by sorry

@[simp]
theorem longElement_inv : w₀⁻¹ = w₀ := by sorry

theorem isRightDescent_longElement_mul_iff (w : W) (i : B) :
    cs.IsRightDescent (w₀ * w) i ↔ ¬cs.IsRightDescent w i := by sorry

theorem length_longElement_mul_add_length (w : W) : ℓ (w₀ * w) + ℓ w = ℓ w₀ := by sorry

theorem length_longElement_mul (w : W) : ℓ (w₀ * w) = ℓ w₀ - ℓ w := by sorry

theorem isRightInversion_longElement_mul_iff (w : W) {t : W} (ht : cs.IsReflection t) :
    cs.IsRightInversion (w₀ * w) t ↔ ¬cs.IsRightInversion w t := by sorry

theorem isLeftDescent_mul_longElement_iff (w : W) (i : B) :
    cs.IsLeftDescent (w * w₀) i ↔ ¬cs.IsLeftDescent w i := by sorry

theorem length_mul_longElement_add_length (w : W) : ℓ (w * w₀) + ℓ w = ℓ w₀ := by sorry

theorem length_mul_longElement (w : W) : ℓ (w * w₀) = ℓ w₀ - ℓ w := by sorry

theorem isLeftInversion_mul_longElement_iff (w : W) {t : W} (ht : cs.IsReflection t) :
    cs.IsLeftInversion (w * w₀) t ↔ ¬cs.IsLeftInversion w t := by sorry

@[simp]
theorem length_longElement_mul_mul_longElement (w : W) : ℓ (w₀ * w * w₀) = ℓ w := by sorry

theorem eq_longElement_of_forall_isRightDescent {w : W} (hw : ∀ i, cs.IsRightDescent w i) :
    w = w₀ := by
  sorry

theorem eq_longElement_of_forall_isLeftDescent {w : W} (hw : ∀ i, cs.IsLeftDescent w i) :
    w = w₀ := by
  sorry

theorem eq_longElement_of_forall_isRightInversion {w : W}
    (hw : ∀ t, cs.IsReflection t → cs.IsRightInversion w t) : w = w₀ := by
  sorry

theorem eq_longElement_of_forall_isLeftInversion {w : W}
    (hw : ∀ t, cs.IsReflection t → cs.IsLeftInversion w t) : w = w₀ := by
  sorry

end CoxeterSystem
