/-
Copyright (c) 2024 Kyle Miller, Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rida Hamadani
-/
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Combinatorial Maps

This module defines combinatorial maps, which are used to represent an object by its boundaries.

Only two-dimensional combinatorial maps are considered.

-/


/--
A two-dimension combinatorial map is a collection `D` of darts, and permutations `σ`, `α`, and `φ`.
`α` is a fixed-point-free involution.

Note: this definition excludes disjoint isolated vertices.
-/
structure CombinatorialMap (D : Type*) where
  /--
  Permutation `σ` whose orbits correspond to vertices. `σ` gives the next dart counter-clockwise
  around an edge.
  -/
  σ : Equiv.Perm D
  /-- Permutation `α` whose orbits correspond to edges. `α` gives the opposite dart of an edge. -/
  α : Equiv.Perm D
  /--
  Permutation `φ` whose orbits correspond to faces. `φ` gives the next dart counter-clockwise of the
  same face.
  -/
  φ : Equiv.Perm D
  composition : α.trans (σ.trans φ) = 1
  involutive : Function.Involutive α
  fixedPoints_isEmpty : IsEmpty (Function.fixedPoints α)

namespace CombinatorialMap

variable {D D' : Type*} {M : CombinatorialMap D} {M' : CombinatorialMap D'}

/-- The permutation `φ` expressed in terms of `σ` and `α`. -/
lemma φ_eq : M.φ = M.σ.symm.trans M.α := by
  have h : M.φ * M.σ * M.α = 1 := M.composition
  replace h := congr($h * M.α⁻¹ * M.σ⁻¹)
  rw [mul_inv_cancel_right, mul_inv_cancel_right, one_mul] at h
  rw [← M.involutive.symm_eq_self_of_involutive, h]
  rfl

lemma composition_φ : M.φ * M.σ * M.α = 1 := by
  convert_to M.α.trans (M.σ.trans M.φ) = 1
  simp [M.composition]

lemma composition_φ_apply {x : D} : M.φ (M.σ (M.α x)) = x := by
  convert_to M.α.trans (M.σ.trans M.φ) x = x
  simp [M.composition]

lemma composition_α : M.α * M.φ * M.σ = 1 :=
  have (y : D) : (M.α * M.φ * M.σ) y = y := by
    obtain ⟨_, h⟩ := M.α.surjective y
    simp [← h, composition_φ_apply]
  Equiv.Perm.ext fun _ ↦ this _

lemma composition_α_apply {x : D} : M.α (M.φ (M.σ x)) = x := by
  convert_to (M.α * M.φ * M.σ) x = x
  simp [M.composition_α]

lemma composition_σ : M.σ * M.α * M.φ = 1 :=
  have (y : D) : (M.σ * M.α * M.φ) y = y := by
    obtain ⟨_, h⟩ := M.σ.surjective y
    simp [← h, composition_α_apply]
  Equiv.Perm.ext fun _ ↦ this _

lemma composition_σ_apply {x : D} : M.σ (M.α (M.φ x)) = x := by
  convert_to (M.σ * M.α * M.φ) x = x
  simp [M.composition_σ]

/--
A homomorphism of `CombinatorialMap`s is a function that commutes with each of the respective
permutations.
-/
def Hom (M : CombinatorialMap D) (M' : CombinatorialMap D') (f : D → D') : Prop :=
  f ∘ M.σ = M'.σ ∘ f ∧
  f ∘ M.α = M'.α ∘ f ∧
  f ∘ M.φ = M'.φ ∘ f

private lemma hom_inv_is_hom_aux {p₁ : Equiv.Perm D} {p₂ : Equiv.Perm D'} {f : Equiv D D'}
    (h : f ∘ p₁ = p₂ ∘ f) : f.symm ∘ p₂ = p₁ ∘ f.symm :=
  calc f.symm ∘ p₂ = f.symm ∘ p₂ ∘ id := rfl
    _ = f.symm ∘ p₂ ∘ (f ∘ f.symm) := by rw [← Equiv.self_comp_symm]
    _ = f.symm ∘ (p₂ ∘ f) ∘ f.symm := rfl
    _ = f.symm ∘ (f ∘ p₁) ∘ f.symm := by rw [← h]
    _ = (f.symm ∘ f) ∘ p₁ ∘ f.symm := rfl
    _ = id ∘ p₁ ∘ f.symm := by rw [Equiv.symm_comp_self]

/-- The inverse of a homomorphism between `CombinatorialMap`s is itself a homomorphism. -/
lemma hom_inv_is_hom (M : CombinatorialMap D) (M' : CombinatorialMap D') (f : Equiv D D')
    (h : Hom M M' f) : Hom M' M f.symm :=
  ⟨hom_inv_is_hom_aux h.1, hom_inv_is_hom_aux h.2.1, hom_inv_is_hom_aux h.2.2⟩

/-- The opposite of a `CombinatorialMap` which reverses the identities of the darts on each edge. -/
def opp (M : CombinatorialMap D) : CombinatorialMap D where
  σ := (M.α.trans M.σ).trans M.α
  α := M.α
  φ := (M.α.trans M.φ).trans M.α
  involutive := M.involutive
  fixedPoints_isEmpty := M.fixedPoints_isEmpty
  composition := by
    ext x
    simp only [Equiv.trans_apply, Equiv.Perm.coe_one, id_eq]
    rw [M.involutive, M.involutive, composition_α_apply]

lemma opp_equiv (M : CombinatorialMap D) : ∃ (f : Equiv D D), Hom M M.opp f :=
  ⟨M.α, ⟨by rw [← (M.α ∘ M.σ).comp_id, ← Function.RightInverse.id M.involutive]; rfl, rfl,
  by rw [← (M.α ∘ M.φ).comp_id, ← Function.RightInverse.id M.involutive]; rfl⟩⟩

/-- The dual of a `CombinatorialMap` swaps the roles of vertices and faces -/
def dual (M : CombinatorialMap D) : CombinatorialMap D where
  σ := M.φ.symm
  α := M.α.symm
  φ := M.σ.symm
  composition := by
    ext x
    apply_fun M.α * M.φ * M.σ
    simp [composition_α_apply]
  involutive := by
    have : M.α.symm = M.α := M.involutive.symm_eq_self_of_involutive
    simp [this, M.involutive]
  fixedPoints_isEmpty := by
    have : M.α.symm = M.α := M.involutive.symm_eq_self_of_involutive
    simp [this, M.fixedPoints_isEmpty]

/-- The double dual of a `CombinatorialMap` is equal to the original map. -/
lemma double_dual_eq (M : CombinatorialMap D) : M.dual.dual = M := rfl

/-- The vertices of a `CombinatorialMap`. -/
@[reducible] def vertices (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.σ)

/-- The edges of a `CombinatorialMap`. -/
@[reducible] def edges (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.α)

/-- The faces of a `CombinatorialMap`. -/
@[reducible] def faces (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.φ)

/-- The vertex corresponding to a dart `d`. -/
@[reducible] def dartVertex (M : CombinatorialMap D) (d : D) : M.vertices :=
  @Quotient.mk _ (Equiv.Perm.SameCycle.setoid M.σ) d

/-- The edge corresponding to a dart `d`. -/
@[reducible] def dartEdge (M : CombinatorialMap D) (d : D) : M.edges :=
  @Quotient.mk _ (Equiv.Perm.SameCycle.setoid M.α) d

/-- The face corresponding to a dart `d`. -/
@[reducible] def dartFace (M : CombinatorialMap D) (d : D) : M.faces :=
  @Quotient.mk _ (Equiv.Perm.SameCycle.setoid M.φ) d

end CombinatorialMap
