/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!

# Dot Product and Cross Product on Projective Spaces

This file defines the dot product and cross product on projective spaces.

## Definitions
- `Projectivization.orthogonal v w` is defined as vanishing of the dot product.
- `Projectivization.cross v w` for `v w : ℙ F (Fin 3 → F)` is defined as the cross product of
  `v` and `w` provided that `v ≠ w`. If `v = w`, then the cross product would be zero, so we
  instead define `cross v v = v`.

-/

variable {F : Type*} [Field F] {m : Type*} [Fintype m]

namespace Projectivization

open scoped LinearAlgebra.Projectivization

section DotProduct

/-- Orthogonality on the projective plane. -/
def orthogonal : ℙ F (m → F) → ℙ F (m → F) → Prop :=
  Quotient.lift₂ (fun v w ↦ v.1 ⬝ᵥ w.1 = 0) (fun _ _ _ _ ⟨_, h1⟩ ⟨_, h2⟩ ↦ by
    simp_rw [← h1, ← h2, dotProduct_smul, smul_dotProduct, smul_smul,
      smul_eq_zero_iff_eq])

lemma orthogonal_mk {v w : m → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    orthogonal (mk F v hv) (mk F w hw) ↔ v ⬝ᵥ w = 0 :=
  Iff.rfl

lemma orthogonal_comm {v w : ℙ F (m → F)} : orthogonal v w ↔ orthogonal w v := by
  induction v with | h v hv => induction w with | h w hw =>
  rw [orthogonal_mk hv hw, orthogonal_mk hw hv, dotProduct_comm]

lemma exists_not_self_orthogonal (v : ℙ F (m → F)) : ∃ w, ¬ orthogonal v w := by
  induction v with | h v hv =>
  rw [ne_eq, ← dotProduct_eq_zero_iff, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨mk F w fun h ↦ hw (by rw [h, dotProduct_zero]), hw⟩

lemma exists_not_orthogonal_self (v : ℙ F (m → F)) : ∃ w, ¬ orthogonal w v := by
  simp only [orthogonal_comm]
  exact exists_not_self_orthogonal v

end DotProduct

section CrossProduct

lemma mk_eq_mk_iff_crossProduct_eq_zero {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk F v hv = mk F w hw ↔ crossProduct v w = 0 := by
  rw [← not_iff_not, mk_eq_mk_iff', not_exists, ← LinearIndependent.pair_iff' hw,
    ← crossProduct_ne_zero_iff_linearIndependent, ← cross_anticomm, neg_ne_zero]

variable [DecidableEq F]

/-- Cross product on the projective plane. -/
def cross : ℙ F (Fin 3 → F) → ℙ F (Fin 3 → F) → ℙ F (Fin 3 → F) :=
  Quotient.map₂ (fun v w ↦ if h : crossProduct v.1 w.1 = 0 then v else ⟨crossProduct v.1 w.1, h⟩)
    (fun _ _ ⟨a, ha⟩ _ _ ⟨b, hb⟩ ↦ by
      simp_rw [← ha, ← hb, LinearMap.map_smul_of_tower, LinearMap.smul_apply, smul_smul,
        mul_comm b a, smul_eq_zero_iff_eq]
      split_ifs
      · use a
      · use a * b)

lemma cross_mk {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    cross (mk F v hv) (mk F w hw) =
      if h : crossProduct v w = 0 then mk F v hv else mk F (crossProduct v w) h := by
  change Quotient.mk'' _ = _
  split_ifs with h <;> simp only [h] <;> rfl

lemma cross_mk_of_cross_eq_zero {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : crossProduct v w = 0) :
    cross (mk F v hv) (mk F w hw) = mk F v hv := by
  rw [cross_mk, dif_pos h]

lemma cross_mk_of_cross_ne_zero {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : crossProduct v w ≠ 0) :
    cross (mk F v hv) (mk F w hw) = mk F (crossProduct v w) h := by
  rw [cross_mk, dif_neg h]

lemma cross_self (v : ℙ F (Fin 3 → F)) : cross v v = v := by
  induction v with | h v hv =>
  rw [cross_mk_of_cross_eq_zero]
  rw [← mk_eq_mk_iff_crossProduct_eq_zero hv]

lemma cross_mk_of_ne {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0) (h : mk F v hv ≠ mk F w hw) :
    cross (mk F v hv) (mk F w hw) = mk F (crossProduct v w)
      (mt (mk_eq_mk_iff_crossProduct_eq_zero hv hw).mpr h) := by
  rw [cross_mk_of_cross_ne_zero]

lemma cross_comm (v w : ℙ F (Fin 3 → F)) : cross v w = cross w v := by
  rcases eq_or_ne v w with rfl | h
  · rfl
  · induction v with | h v hv =>
    induction w with | h w hw =>
    rw [cross_mk_of_ne hv hw h, cross_mk_of_ne hw hv h.symm, mk_eq_mk_iff_crossProduct_eq_zero,
      ← cross_anticomm v w, map_neg, _root_.cross_self, neg_zero]

theorem cross_orthogonal_left {v w : ℙ F (Fin 3 → F)} (h : v ≠ w) :
    (cross v w).orthogonal v := by
  induction v with | h v hv =>
  induction w with | h w hw =>
  rw [cross_mk_of_ne hv hw h, orthogonal_mk, dotProduct_comm, dot_self_cross]

theorem cross_orthogonal_right {v w : ℙ F (Fin 3 → F)} (h : v ≠ w) :
    (cross v w).orthogonal w := by
  rw [cross_comm]
  exact cross_orthogonal_left h.symm

theorem orthogonal_cross_left {v w : ℙ F (Fin 3 → F)} (h : v ≠ w) :
    v.orthogonal (cross v w) := by
  rw [orthogonal_comm]
  exact cross_orthogonal_left h

lemma orthogonal_cross_right {v w : ℙ F (Fin 3 → F)} (h : v ≠ w) :
    w.orthogonal (cross v w) := by
  rw [orthogonal_comm]
  exact cross_orthogonal_right h

end CrossProduct

end Projectivization
