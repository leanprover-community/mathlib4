/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Generators

/-!
Documentation
-/

open Function

namespace exteriorPower

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (k : ℕ)

variable {R M}
variable (B : LinearMap.BilinForm R M)

theorem auxCol {ι : Type*} [DecidableEq ι] (v w : ι → M) (z : M) (l : ι) :
    (Matrix.of fun i j ↦ B (v i) (Function.update w l z j)) =
    (Matrix.of fun i j ↦ B (v i) (w j)).updateColumn l (fun i ↦ B (v i) z) := by
  ext i j
  simp only [update_apply, Matrix.of_apply, Matrix.updateColumn_apply]
  aesop

theorem auxRow {ι : Type*} [DecidableEq ι] (v w : ι → M) (z : M) (l : ι) :
    (Matrix.of fun i j ↦ B (Function.update v l z i) (w j)) =
    (Matrix.of fun i j ↦ B (v i) (w j)).updateRow l (fun j ↦ B z (w j)) := by
  ext i j
  simp only [update_apply, Matrix.of_apply, Matrix.updateRow_apply]
  aesop

private def BilinFormAux :
    M [⋀^Fin k]→ₗ[R] M [⋀^Fin k]→ₗ[R] R where
  toFun v :=
    { toFun := fun w ↦ (Matrix.of fun i j ↦ B (v i) (w j)).det
      map_add' := fun {_i} w l x y ↦ by
        simp only [auxCol, map_add]
        convert Matrix.det_updateColumn_add _ l _ _
      map_smul' := fun {_i} w l t x ↦ by
        simp only [auxCol, map_smul]
        convert Matrix.det_updateColumn_smul _ l t _
      map_eq_zero_of_eq' := fun w l₁ l₂ hl hl' ↦ Matrix.det_zero_of_column_eq hl' <| by simp [hl] }
  map_add' {_i} v l x y := by
    ext w
    simp only [AlternatingMap.coe_mk, MultilinearMap.coe_mk, AlternatingMap.add_apply,
      auxRow, map_add, LinearMap.add_apply]
    convert Matrix.det_updateRow_add _ l _ _
  map_smul' {_i} v l t x := by
    ext w
    simp only [AlternatingMap.coe_mk, MultilinearMap.coe_mk, AlternatingMap.smul_apply, smul_eq_mul,
      auxRow, map_smul, LinearMap.smul_apply, smul_eq_mul]
    convert Matrix.det_updateRow_smul _ l t _
  map_eq_zero_of_eq' v l₁ l₂ hl hl' :=
    AlternatingMap.ext fun w ↦ Matrix.det_zero_of_row_eq hl' <| funext fun i ↦ by simp [hl]

protected def BilinForm : LinearMap.BilinForm R (⋀[R]^k M) :=
  (liftAlternating k) ∘ₗ liftAlternating k (BilinFormAux k B)

local notation "⟪" v ", " w "⟫" => exteriorPower.BilinForm k B v w

theorem bilin_apply_ιMulti (v w : Fin k → M) :
  ⟪(ιMulti R k v), (ιMulti R k w)⟫ = (Matrix.of fun i j ↦ B (v i) (w j)).det := by
  unfold exteriorPower.BilinForm
  simp only [LinearMap.coe_comp, comp_apply, liftAlternating_apply_ιMulti]
  rfl

theorem bilin_apply_ιMulti_family {I : Type*} [LinearOrder I] (b c : I → M)
  (s t : Finset I) (hs : s.card = k) (ht : t.card = k) :
  ⟪ιMulti_family R k b ⟨s, hs⟩, ιMulti_family R k c ⟨t, ht⟩⟫ = (Matrix.of fun i j ↦
  B (b (Finset.orderIsoOfFin s hs i)) (c (Finset.orderIsoOfFin t ht j))).det := by
  unfold exteriorPower.BilinForm
  unfold ιMulti_family
  simp only [LinearMap.coe_comp, comp_apply, liftAlternating_apply_ιMulti]
  rfl

theorem bilin_symm_ιMulti (h : B.IsSymm) : ∀ v w : Fin k → M, ⟪(ιMulti R k v), (ιMulti R k w)⟫ =
  ⟪(ιMulti R k w), (ιMulti R k v)⟫ := by
  intro v w
  simp only [bilin_apply_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [← h (v j) (w i)]
  simp only [RingHom.id_apply]

theorem bilin_symm (hS : B.IsSymm) : (exteriorPower.BilinForm k B).IsSymm := by
  intro v w
  simp only [RingHom.id_apply]
  --apply Submodule.span_induction₂ (p := fun v w hv hw ↦
  --  ((exteriorPower.BilinForm k B) v) w = ((exteriorPower.BilinForm k B) w) v)
  sorry

section overField

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
variable (B : LinearMap.BilinForm K M) (hN : B.Nondegenerate)
variable {I : Type*} [LinearOrder I] [Finite I] (b : Basis I K M)
variable {k : ℕ}

local notation "⟪" v ", " w "⟫" => exteriorPower.BilinForm k B v w

omit [Finite I] in
theorem diff_elt_of_neq_subset (s t : Finset I) (hs : s.card = k) (ht : t.card = k)
  (neq : s ≠ t) : ∃ i : I, i ∈ s ∧ i ∉ t := by
  by_contra h
  push_neg at h
  apply neq
  have : s ⊆ t := h
  rw [Finset.eq_of_subset_of_card_le this]
  simp [hs, ht]

omit [Finite I] in
theorem diff_index_of_neq_subset (s t : Finset I) (hs : s.card = k) (ht : t.card = k)
  (neq : s ≠ t) : ∃ (i : Fin k), ∀ (j : Fin k),
  (((t.orderIsoOfFin ht) j) : I) ≠ ((s.orderIsoOfFin hs) i) := by
  obtain ⟨e, he⟩ := diff_elt_of_neq_subset s t hs ht neq
  use (s.orderIsoOfFin hs).symm ⟨e, he.1⟩
  simp only [OrderIso.apply_symm_apply]
  intro j
  by_contra h
  apply he.2
  rw[← h]
  simp only [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_mem]

theorem exteriorPower_dualBasis (s t : Finset I) (hs : s.card = k) (ht : t.card = k) :
  ⟪Basis.exteriorPower K k (B.dualBasis hN b) ⟨s, hs⟩, Basis.exteriorPower K k b ⟨t, ht⟩⟫ =
  if s = t then 1 else 0 := by
  simp only [basis_apply]
  simp only [bilin_apply_ιMulti_family]
  simp only [LinearMap.BilinForm.apply_dualBasis_left]
  rcases eq_or_ne s t with h | h
  · rw [if_pos h]
    simp [h]
    nth_rw 2 [← @Matrix.det_one (Fin k)]
    congr
    exact Matrix.transpose_eq_one.mp rfl
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := (diff_index_of_neq_subset s t hs ht) h
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    rw [Matrix.of_apply]
    rw [if_neg (hi j)]

theorem exteriorPower_dualBasis' (s t : {a : Finset I // a.card = k}) :
  ⟪Basis.exteriorPower K k (B.dualBasis hN b) s, Basis.exteriorPower K k b t⟫ =
  if s = t then 1 else 0 := by
  rw [exteriorPower_dualBasis]
  aesop

instance : Fintype { s : Finset I // s.card = k } := sorry

theorem exteriorPower_repr (s : Finset I) (hs : s.card = k) (v : ⋀[K]^k M) :
  (Basis.exteriorPower K k b).repr v ⟨s, hs⟩ =
  ⟪Basis.exteriorPower K k (B.dualBasis hN b) ⟨s, hs⟩, v⟫ := by
  nth_rw 2 [← Basis.sum_repr (Basis.exteriorPower K k b) v]
  rw [LinearMap.BilinForm.sum_right]
  simp only [map_smul, smul_eq_mul]
  simp only [exteriorPower_dualBasis']
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem bilinNondegen' (b : Basis I K M) (hN : B.Nondegenerate)
  (hS : B.IsSymm) :
  (exteriorPower.BilinForm k B).Nondegenerate := by
  intro v h
  rw [← Basis.forall_coord_eq_zero_iff (Basis.exteriorPower K k b)]
  intro ⟨s, hs⟩
  simp only [Basis.coord_apply]
  rw [exteriorPower_repr B hN]
  rw [← h (((Basis.exteriorPower K k (B.dualBasis hN b)) ⟨s, hs⟩))]
  rw [← (bilin_symm k B hS) v _]
  simp only [basis_apply, RingHom.id_apply]

end overField

end exteriorPower
