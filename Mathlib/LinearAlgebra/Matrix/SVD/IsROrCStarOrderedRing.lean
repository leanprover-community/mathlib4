import Mathlib.Data.IsROrC.Basic

-- set_option trace.profiler true
-- set_option trace.Meta.synthInstance true
-- set_option synthInstance.maxHeartbeats 10000
-- set_option synthInstance.maxSize 400

variable {K} [IsROrC K]

namespace IsROrC

instance toPartialOrder : PartialOrder K :=
{
  le := fun w z => (IsROrC.re w ≤ IsROrC.re z) ∧ (IsROrC.im w = IsROrC.im z)
  le_refl := by
    intros a
    dsimp
    simp only [le_refl, and_self]
  le_trans := by
    intros a b c hab hbc
    dsimp at *
    exact ⟨ hab.1.trans hbc.1, hab.2.trans hbc.2 ⟩
  le_antisymm := by
    intros a b hab hba
    dsimp at *
    rw [IsROrC.ext_iff]
    exact ⟨ hab.1.antisymm hba.1, hab.2 ⟩ }

lemma le_def {w z: K}: w ≤ z ↔ (IsROrC.re w ≤ IsROrC.re z) ∧ (IsROrC.im w = IsROrC.im z) := by
  unfold LE.le Preorder.toLE PartialOrder.toPreorder toPartialOrder LE.le
  simp only [and_congr_left_iff]

instance toStarOrderedRing : StarOrderedRing K := by
  apply StarOrderedRing.ofNonnegIff'
  intros x y h z
  rw [le_def] at *
  simp only [map_add, add_le_add_iff_left, add_right_inj, h.1, h.2]
  intros z
  constructor
  intros h
  use Real.sqrt (IsROrC.re z)
  rw [IsROrC.ext_iff, le_def, star_def, map_zero, map_zero, conj_ofReal] at *
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, mul_im, zero_mul, add_zero,
    Real.mul_self_sqrt h.1, true_and, h.2.symm]
  intros h
  cases' h with s hs
  rw [hs, star_def, le_def, map_zero, map_zero]
  simp only [mul_re, conj_re, conj_im, neg_mul,
    sub_neg_eq_add, sub_neg_eq_add, ←sub_eq_add_neg, mul_im,
    ← IsROrC.norm_sq_eq_def, ← IsROrC.normSq_eq_def', IsROrC.normSq_nonneg s,
    mul_comm (im s) (re s), sub_self, eq_self ]

end IsROrC
