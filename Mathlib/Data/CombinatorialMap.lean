/-
Copyright (c) 2024 Kyle Miller, Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rida Hamadani
-/
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Combinatorial Maps

This module defines combinatorial maps, which are used to represent an object by its boundaries.
They provide a nice way to represent graph embeddings into a surface.

Only two-dimensional combinatorial maps are considered.

## TODO
- Provide a way to get a `combinatorialMap` using three maps satisfying the conditions of a
  combinatorial map. This will allow us to get a `combinatorialMap` without having to worry about
  whether our maps are permutations or not.

## Tags
combinatorial map, rotation system

-/


/--
A two-dimension combinatorial map is a collection `D` of darts, and maps `vertexPerm`, `edgePerm`,
and `facePerm`. `edgePerm` is a fixed-point-free involution.

Note: this definition excludes disjoint isolated vertices.
-/
structure CombinatorialMap (D : Type*) where
  /--
  Permutation whose orbits correspond to vertices, it gives the next dart counter-clockwise around
  an edge.
  -/
  vertexPerm : Equiv.Perm D
  /-- Permutation whose orbits correspond to edges, it gives the opposite dart of an edge. -/
  edgePerm : Equiv.Perm D
  /--
  Permutation whose orbits correspond to faces, it gives the next dart counter-clockwise of the same
  face.
  -/
  facePerm : Equiv.Perm D
  face_mul_edge_mul_vertex_eq_one : facePerm * edgePerm * vertexPerm = 1
  edgePerm_involutive : Function.Involutive edgePerm
  isEmpty_fixedPoints_edgePerm : IsEmpty (Function.fixedPoints edgePerm)

namespace CombinatorialMap

variable {D D' : Type*} {M : CombinatorialMap D} {M' : CombinatorialMap D'}

lemma edge_mul_vertex_mul_face_eq_one : M.edgePerm * M.vertexPerm * M.facePerm = 1 := by
  rw [← mul_eq_left (a := M.facePerm), ← mul_assoc, ← mul_assoc,
    M.face_mul_edge_mul_vertex_eq_one, one_mul]

lemma vertex_mul_face_mul_edge_eq_one : M.vertexPerm * M.facePerm * M.edgePerm = 1 := by
  rw [← mul_eq_left (a := M.edgePerm), ← mul_assoc, ← mul_assoc,
    M.edge_mul_vertex_mul_face_eq_one, one_mul]

/-- `facePerm` expressed in terms of `vertexPerm` and `edgePerm`. -/
lemma facePerm_eq : M.facePerm = M.vertexPerm⁻¹ * M.edgePerm := by
  have h := M.face_mul_edge_mul_vertex_eq_one
  replace h := congr($h * M.vertexPerm⁻¹ * M.edgePerm⁻¹)
  rw [mul_inv_cancel_right, mul_inv_cancel_right, one_mul] at h
  rw [← M.edgePerm_involutive.symm_eq_self_of_involutive, h]
  rfl

lemma edge_mul_edge_eq_one : M.edgePerm * M.edgePerm = 1 := by
  ext x
  rw [M.edgePerm.mul_apply M.edgePerm, Equiv.Perm.coe_one, id_eq, M.edgePerm_involutive]

/--
A homomorphism of `CombinatorialMap`s is a function that commutes with each of the respective
permutations.
-/
structure Hom (M : CombinatorialMap D) (M' : CombinatorialMap D') where
  /-- The function inducing the homomorphism. -/
  toFun : D → D'
  vertex_comm : toFun ∘ M.vertexPerm = M'.vertexPerm ∘ toFun
  edge_comm : toFun ∘ M.edgePerm = M'.edgePerm ∘ toFun
  face_comm : toFun ∘ M.facePerm = M'.facePerm ∘ toFun

/--
An isomorphism of `CombinatorialMap`s is a homomorphism that is also an equivalence.
-/
structure Iso (M : CombinatorialMap D) (M' : CombinatorialMap D') extends (D ≃ D'), Hom M M'

/-- Interpret an `Iso` as a `Hom`. -/
add_decl_doc Iso.toHom

private lemma hom_inv_is_hom_aux {p₁ : Equiv.Perm D} {p₂ : Equiv.Perm D'} {f : Equiv D D'}
    (h : f ∘ p₁ = p₂ ∘ f) : f.symm ∘ p₂ = p₁ ∘ f.symm :=
  calc f.symm ∘ p₂ = f.symm ∘ p₂ ∘ id := rfl
    _ = f.symm ∘ p₂ ∘ (f ∘ f.symm) := by rw [← Equiv.self_comp_symm]
    _ = f.symm ∘ (p₂ ∘ f) ∘ f.symm := rfl
    _ = f.symm ∘ (f ∘ p₁) ∘ f.symm := by rw [← h]
    _ = (f.symm ∘ f) ∘ p₁ ∘ f.symm := rfl
    _ = id ∘ p₁ ∘ f.symm := by rw [Equiv.symm_comp_self]

/-- The inverse of an isomorphism between `CombinatorialMap`s. It is also an isomorphism. -/
def invIso (f : Iso M M') : Iso M' M where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.toEquiv.right_inv
  right_inv := f.toEquiv.left_inv
  vertex_comm := by simp [hom_inv_is_hom_aux f.vertex_comm]
  edge_comm := by simp [hom_inv_is_hom_aux f.edge_comm]
  face_comm := by simp [hom_inv_is_hom_aux f.face_comm]

/-- The opposite of a `CombinatorialMap` which reverses the identities of the darts on each edge. -/
def op (M : CombinatorialMap D) : CombinatorialMap D where
  vertexPerm := M.edgePerm * M.vertexPerm * M.edgePerm
  edgePerm := M.edgePerm
  facePerm := M.edgePerm * M.facePerm * M.edgePerm
  face_mul_edge_mul_vertex_eq_one := calc
    _ = M.edgePerm * M.facePerm * M.edgePerm * M.vertexPerm * M.edgePerm := by
      rw [mul_assoc _ M.edgePerm M.edgePerm, edge_mul_edge_eq_one]; rfl
    _ = M.edgePerm * (M.facePerm * M.edgePerm * M.vertexPerm) * M.edgePerm := rfl
    _ = M.edgePerm * M.edgePerm := by rw [M.face_mul_edge_mul_vertex_eq_one, mul_one]
    _ = 1 := edge_mul_edge_eq_one
  edgePerm_involutive := M.edgePerm_involutive
  isEmpty_fixedPoints_edgePerm := M.isEmpty_fixedPoints_edgePerm

/-- `CombinatorialMap.op` results in an automorphism. -/
def opIso (M : CombinatorialMap D) : Iso M M.op where
  toEquiv := M.edgePerm
  vertex_comm := by
    rw [← (M.edgePerm.toFun ∘ M.vertexPerm).comp_id, ← Function.RightInverse.id
      M.edgePerm_involutive]
    rfl
  edge_comm := rfl
  face_comm := by
    rw [← (M.edgePerm.toFun ∘ M.facePerm).comp_id, ← Function.RightInverse.id
      M.edgePerm_involutive]
    rfl

/-- The dual of a `CombinatorialMap` swaps the roles of vertices and faces -/
def dual (M : CombinatorialMap D) : CombinatorialMap D where
  vertexPerm := M.facePerm⁻¹
  edgePerm := M.edgePerm⁻¹
  facePerm := M.vertexPerm⁻¹
  face_mul_edge_mul_vertex_eq_one := by
    rw [← mul_inv_rev, ← mul_inv_rev, ← mul_assoc, M.face_mul_edge_mul_vertex_eq_one, inv_one]
  edgePerm_involutive := by
    simp [Inv.inv, M.edgePerm_involutive.symm_eq_self_of_involutive, M.edgePerm_involutive]
  isEmpty_fixedPoints_edgePerm := by
    simp [Inv.inv, M.edgePerm_involutive.symm_eq_self_of_involutive, M.isEmpty_fixedPoints_edgePerm]

lemma dual_dual (M : CombinatorialMap D) : M.dual.dual = M := rfl

/-- The vertices of a `CombinatorialMap`. -/
abbrev Vertex (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.vertexPerm)

/-- The edges of a `CombinatorialMap`. -/
abbrev Edge (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.edgePerm)

/-- The faces of a `CombinatorialMap`. -/
abbrev Face (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.facePerm)

/-- The vertex corresponding to a dart `d`. -/
abbrev Vertex_mk (M : CombinatorialMap D) (d : D) : M.Vertex :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid M.vertexPerm) d

/-- The edge corresponding to a dart `d`. -/
abbrev Edge_mk (M : CombinatorialMap D) (d : D) : M.Edge :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgePerm) d

/-- The face corresponding to a dart `d`. -/
abbrev Face_mk (M : CombinatorialMap D) (d : D) : M.Face :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid M.facePerm) d

private noncomputable instance [Fintype D] [DecidableEq D] {w : D} :
    Fintype {u | M.vertexPerm.SameCycle w u} :=
  Fintype.ofFinite {u | M.vertexPerm.SameCycle w u}

/-- The degree of a vertex is the number of incident darts. -/
noncomputable def Vertex.deg [Fintype D] [DecidableEq D] (v : M.Vertex) : ℕ :=
  Quotient.lift (fun w ↦ Fintype.card {u | M.vertexPerm.SameCycle w u}) (fun w u h ↦ by
    simp [Set.coe_setOf, Set.mem_setOf_eq]
    suffices M.vertexPerm.SameCycle w = M.vertexPerm.SameCycle u by
      classical
      simp_all only
      convert rfl
    ext
    exact ⟨h.symm.trans, h.trans⟩) v

noncomputable instance [Fintype D] : Fintype M.Vertex :=
  Fintype.ofFinite M.Vertex

noncomputable instance [Fintype D] : Fintype M.Edge :=
  Fintype.ofFinite M.Edge

noncomputable instance [Fintype D] : Fintype M.Face :=
  Fintype.ofFinite M.Face

/-- The Euler characteristic of a `CombinatorialMap`. -/
noncomputable def eulerCharacteristic [Fintype D] : ℤ :=
  Fintype.card M.Vertex - Fintype.card M.Edge + Fintype.card M.Face

/-- Planarity is characterized by Euler's formula. -/
def IsPlanar [Fintype D] : Prop :=
  M.eulerCharacteristic = 2

end CombinatorialMap
