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
import Mathlib.RingTheory.Finiteness

/-!
Documentation
-/

open Function

namespace exteriorPower

section overModule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : LinearMap.BilinForm R M) (k : ℕ)

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
  (liftAlternating k) ∘ₗ liftAlternating k (BilinFormAux B k)

local notation "⟪" v ", " w "⟫" => exteriorPower.BilinForm B k v w

theorem bilin_apply_ιMulti (v w : Fin k → M) :
  ⟪(ιMulti R k v), (ιMulti R k w)⟫ = (Matrix.of fun i j ↦ B (v i) (w j)).det := by
  unfold exteriorPower.BilinForm
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

theorem bilin_symm (hS : B.IsSymm) [Module.Finite R M] :
  (exteriorPower.BilinForm B k).IsSymm := by
  intro v w
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [RingHom.id_apply]
  apply Submodule.span_induction₂ (R := R) (p := fun a b _ _ ↦ ⟪a, b⟫ = ⟪b, a⟫)
    (s := Set.range (ιMulti_family R k s))
  · intro x y hx hy
    obtain ⟨s, rfl⟩ := Set.mem_range.mp hx
    obtain ⟨t, rfl⟩ := Set.mem_range.mp hy
    unfold ιMulti_family
    rw [bilin_symm_ιMulti (h := hS)]
  · simp only [map_zero, LinearMap.zero_apply, implies_true]
  · simp only [map_zero, LinearMap.zero_apply, implies_true]
  · intro x y z _ _ _  a a_1
    simp_all only [map_add, LinearMap.add_apply]
  · intro x y z _ _ _ a a_1
    simp_all only [map_add, LinearMap.add_apply]
  · intro r x y _ _ a
    simp_all only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  · intro r x y _ _ a
    simp_all only [map_smul, smul_eq_mul, LinearMap.smul_apply]
  · simp only [h, span_top_of_span_top', Submodule.mem_top]
  · simp only [h, span_top_of_span_top', Submodule.mem_top]

variable {I : Type*} {k}

theorem diff_elt_of_neq_subset (s t : Finset I) (hs : s.card = k) (ht : t.card = k)
  (neq : s ≠ t) : ∃ i : I, i ∈ s ∧ i ∉ t := by
  by_contra h
  push_neg at h
  apply neq
  have : s ⊆ t := h
  rw [Finset.eq_of_subset_of_card_le this]
  simp [hs, ht]

variable [LinearOrder I]

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

theorem bilin_apply_ιMulti_family (b c : I → M)
  (s t : Finset I) (hs : s.card = k) (ht : t.card = k) :
  ⟪ιMulti_family R k b ⟨s, hs⟩, ιMulti_family R k c ⟨t, ht⟩⟫ = (Matrix.of fun i j ↦
  B (b (Finset.orderIsoOfFin s hs i)) (c (Finset.orderIsoOfFin t ht j))).det := by
  unfold exteriorPower.BilinForm
  unfold ιMulti_family
  simp only [LinearMap.coe_comp, comp_apply, liftAlternating_apply_ιMulti]
  rfl

end overModule

section basis

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) {k : ℕ}
variable {I : Type*} [Finite I] [LinearOrder I]
variable (b : Basis I F V) (hN : B.Nondegenerate)

local notation "⟪" v ", " w "⟫" => exteriorPower.BilinForm B k v w

theorem exteriorPower_dualBasis (s t : Finset I) (hs : s.card = k) (ht : t.card = k) :
  ⟪Basis.exteriorPower F k (B.dualBasis hN b) ⟨s, hs⟩, Basis.exteriorPower F k b ⟨t, ht⟩⟫ =
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
  ⟪Basis.exteriorPower F k (B.dualBasis hN b) s, Basis.exteriorPower F k b t⟫ =
  if s = t then 1 else 0 := by
  rw [exteriorPower_dualBasis]
  aesop

noncomputable instance : Fintype I := Fintype.ofFinite I
noncomputable instance : Fintype { s : Finset I // s.card = k } := by
  apply Fintype.subtype (Finset.powersetCard k Finset.univ)
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, implies_true]

theorem exteriorPower_repr (s : Finset I) (hs : s.card = k) (v : ⋀[F]^k V) :
  (Basis.exteriorPower F k b).repr v ⟨s, hs⟩ =
  ⟪Basis.exteriorPower F k (B.dualBasis hN b) ⟨s, hs⟩, v⟫ := by
  nth_rw 2 [← Basis.sum_repr (Basis.exteriorPower F k b) v]
  rw [LinearMap.BilinForm.sum_right]
  simp only [map_smul, smul_eq_mul]
  simp only [exteriorPower_dualBasis']
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem exteriorPower_repr_dual (s : Finset I) (hs : s.card = k) (v : ⋀[F]^k V) :
  (Basis.exteriorPower F k (B.dualBasis hN b)).repr v ⟨s, hs⟩ =
  ⟪v, Basis.exteriorPower F k b ⟨s, hs⟩⟫ := by
  nth_rw 2 [← Basis.sum_repr (Basis.exteriorPower F k (B.dualBasis hN b)) v]
  rw [LinearMap.BilinForm.sum_left]
  simp only [LinearMap.BilinForm.smul_left]
  simp only [exteriorPower_dualBasis']
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end basis

section overVectorSpace

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (k : ℕ)

local notation "⟪" v ", " w "⟫" => exteriorPower.BilinForm B k v w

theorem bilin_nondegen [FiniteDimensional F V] (hN : B.Nondegenerate) :
  (exteriorPower.BilinForm B k).Nondegenerate := by
  let b := Module.finBasis F V
  intro v h
  rw [← Basis.forall_coord_eq_zero_iff (Basis.exteriorPower F k (B.dualBasis hN b))]
  intro ⟨s, hs⟩
  simp only [Basis.coord_apply]
  rw [Subsingleton.elim (@instDecidableEqFin (Module.finrank F V))
    (fun a b ↦ LinearOrder.decidableEq a b)]
  rw [exteriorPower_repr_dual B b hN s hs v]
  rw [← h (((Basis.exteriorPower F k b) ⟨s, hs⟩))]

end overVectorSpace

end exteriorPower
