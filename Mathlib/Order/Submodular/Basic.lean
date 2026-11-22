/-
Copyright (c) 2026 Alberto Schiabel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alberto Schiabel
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Hom.Lattice
public import Mathlib.Order.Submodular.Defs

/-!
# Basic properties of submodular, supermodular, and modular functions

This file develops the core algebraic and order-theoretic API for `Submodular`, `Supermodular`,
and `Modular` functions on lattices.

## Main results

* `LinearOrder.modular`: Every function on a linear order into an additive commutative magma is
  modular (and hence both submodular and supermodular).
* `submodular_comp_ofDual_iff`: Submodularity is invariant under reversing the order of the domain.
* `submodular_neg_iff`: Negation exchanges submodularity and supermodularity.
* `Submodular.add`, `Submodular.sub`, `Submodular.smul`: Convex cone closure properties.
* `Submodular.comp_latticeHom`, `Submodular.comp_orderIso`: Precomposition with lattice
  homomorphisms and order isomorphisms preserves submodularity.
* `Submodular.inf_const`: Truncating a monotone submodular function from above preserves
  submodularity.
* `Submodular.sup_le_add_of_disjoint`: A submodular function with `0 ≤ f ⊥` is subadditive on
  disjoint elements.

## Tags

submodular, supermodular, modular, lattice, convex cone, duality
-/

public section

open Function OrderDual

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ### Constants and linear orders -/

section Const

variable [Lattice α] [Add β]

theorem modular_const (c : β) : Modular (fun _ : α ↦ c) :=
  fun _ _ ↦ rfl

theorem submodular_const [Preorder β] (c : β) : Submodular (fun _ : α ↦ c) :=
  (modular_const c).submodular

theorem supermodular_const [Preorder β] (c : β) : Supermodular (fun _ : α ↦ c) :=
  (modular_const c).supermodular

end Const

section LinearOrder

variable [LinearOrder α] [AddCommMagma β]

/-- Every function on a linear order is modular. -/
theorem LinearOrder.modular (f : α → β) : Modular f := by
  intro a b
  rcases le_total a b with h | h
  · rw [inf_eq_left.mpr h, sup_eq_right.mpr h]
  · rw [inf_eq_right.mpr h, sup_eq_left.mpr h, add_comm]

theorem LinearOrder.submodular [Preorder β] (f : α → β) : Submodular f :=
  (LinearOrder.modular f).submodular

theorem LinearOrder.supermodular [Preorder β] (f : α → β) : Supermodular f :=
  (LinearOrder.modular f).supermodular

end LinearOrder

/-! ### Order dual and negation duality -/

section OrderDual

variable [Lattice α] [AddCommMagma β] {f : α → β}

@[simp]
theorem submodular_comp_ofDual_iff [Preorder β] : Submodular (f ∘ ofDual) ↔ Submodular f := by
  refine ⟨fun h a b ↦ ?_, fun h a b ↦ ?_⟩
  · simpa [add_comm] using h (toDual a) (toDual b)
  · simpa [add_comm] using h (ofDual a) (ofDual b)

@[simp]
theorem supermodular_comp_ofDual_iff [Preorder β] :
    Supermodular (f ∘ ofDual) ↔ Supermodular f := by
  refine ⟨fun h a b ↦ ?_, fun h a b ↦ ?_⟩
  · simpa [add_comm] using h (toDual a) (toDual b)
  · simpa [add_comm] using h (ofDual a) (ofDual b)

@[simp]
theorem modular_comp_ofDual_iff : Modular (f ∘ ofDual) ↔ Modular f := by
  refine ⟨fun h a b ↦ ?_, fun h a b ↦ ?_⟩
  · simpa [add_comm] using h (toDual a) (toDual b)
  · simpa [add_comm] using h (ofDual a) (ofDual b)

end OrderDual

section Neg

variable [Lattice α] [AddCommGroup β] {f : α → β}

@[simp]
theorem modular_neg_iff : Modular (-f) ↔ Modular f := by
  simp only [Modular, Pi.neg_apply, ← neg_add, neg_inj]

alias ⟨_, Modular.neg⟩ := modular_neg_iff

variable [PartialOrder β] [IsOrderedAddMonoid β]

@[simp]
theorem submodular_neg_iff : Submodular (-f) ↔ Supermodular f := by
  simp only [Submodular, Supermodular, Pi.neg_apply, ← neg_add, neg_le_neg_iff]

@[simp]
theorem supermodular_neg_iff : Supermodular (-f) ↔ Submodular f := by
  simp only [Submodular, Supermodular, Pi.neg_apply, ← neg_add, neg_le_neg_iff]

alias ⟨_, Supermodular.neg⟩ := submodular_neg_iff
alias ⟨_, Submodular.neg⟩ := supermodular_neg_iff

end Neg

/-! ### Cone operations -/

section Add

variable [Lattice α] [AddCommSemigroup β] {f g : α → β}

theorem Modular.add (hf : Modular f) (hg : Modular g) : Modular (f + g) := fun a b ↦ by
  simp only [Pi.add_apply]
  rw [add_add_add_comm, hf a b, hg a b, add_add_add_comm]

variable [Preorder β] [AddLeftMono β] [AddRightMono β]

theorem Submodular.add (hf : Submodular f) (hg : Submodular g) : Submodular (f + g) :=
  fun a b ↦ by
    simp only [Pi.add_apply]
    rw [add_add_add_comm, add_add_add_comm (f a)]
    exact add_le_add (hf a b) (hg a b)

theorem Supermodular.add (hf : Supermodular f) (hg : Supermodular g) : Supermodular (f + g) :=
  fun a b ↦ by
    simp only [Pi.add_apply]
    rw [add_add_add_comm, add_add_add_comm (f (a ⊓ b))]
    exact add_le_add (hf a b) (hg a b)

end Add

section Sub

variable [Lattice α] [AddCommGroup β] {f g : α → β}

theorem Modular.sub (hf : Modular f) (hg : Modular g) : Modular (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

variable [PartialOrder β] [IsOrderedAddMonoid β]

theorem Submodular.sub (hf : Submodular f) (hg : Supermodular g) : Submodular (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem Supermodular.sub (hf : Supermodular f) (hg : Submodular g) : Supermodular (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

end Sub

section SMul

variable {R : Type*} [Lattice α] [Semiring R] [AddCommMonoid β] [Module R β] {f : α → β}

theorem Modular.smul (hf : Modular f) (c : R) : Modular (c • f) := fun a b ↦ by
  simp only [Pi.smul_apply, ← smul_add, hf a b]

variable [PartialOrder R] [PartialOrder β] [PosSMulMono R β] {c : R}

theorem Submodular.smul (hf : Submodular f) (hc : 0 ≤ c) : Submodular (c • f) := fun a b ↦ by
  simp only [Pi.smul_apply, ← smul_add]
  exact smul_le_smul_of_nonneg_left (hf a b) hc

theorem Supermodular.smul (hf : Supermodular f) (hc : 0 ≤ c) : Supermodular (c • f) :=
  fun a b ↦ by
    simp only [Pi.smul_apply, ← smul_add]
    exact smul_le_smul_of_nonneg_left (hf a b) hc

end SMul

/-! ### Lattice homomorphisms, truncation, and subadditivity -/

section LatticeHom

variable [Lattice α] [Lattice γ] [Add β] {f : γ → β}

theorem Submodular.comp_latticeHom [Preorder β] (hf : Submodular f) (g : LatticeHom α γ) :
    Submodular (f ∘ g) := fun a b ↦ by
  simpa only [comp_apply, map_inf, map_sup] using hf (g a) (g b)

theorem Supermodular.comp_latticeHom [Preorder β] (hf : Supermodular f) (g : LatticeHom α γ) :
    Supermodular (f ∘ g) := fun a b ↦ by
  simpa only [comp_apply, map_inf, map_sup] using hf (g a) (g b)

theorem Modular.comp_latticeHom (hf : Modular f) (g : LatticeHom α γ) :
    Modular (f ∘ g) := fun a b ↦ by
  simpa only [comp_apply, map_inf, map_sup] using hf (g a) (g b)

theorem Submodular.comp_orderIso [Preorder β] (hf : Submodular f) (g : α ≃o γ) :
    Submodular (f ∘ g) := fun a b ↦ by
  simpa only [comp_apply, map_inf, map_sup] using hf (g a) (g b)

theorem Supermodular.comp_orderIso [Preorder β] (hf : Supermodular f) (g : α ≃o γ) :
    Supermodular (f ∘ g) := fun a b ↦ by
  simpa only [comp_apply, map_inf, map_sup] using hf (g a) (g b)

theorem Modular.comp_orderIso (hf : Modular f) (g : α ≃o γ) :
    Modular (f ∘ g) := fun a b ↦ by
  simpa only [comp_apply, map_inf, map_sup] using hf (g a) (g b)

end LatticeHom

section Truncation

variable [Lattice α] [AddCommMagma β] [LinearOrder β] [AddLeftMono β] [AddRightMono β]
  {f : α → β}

/-- Truncating a monotone submodular function from above preserves submodularity. -/
theorem Submodular.inf_const (hf : Submodular f) (hmono : Monotone f) (c : β) :
    Submodular (fun x ↦ f x ⊓ c) := by
  intro a b
  dsimp only
  rcases le_total c (f a) with ha | ha
  · have hab : c ≤ f (a ⊔ b) := ha.trans (hmono le_sup_left)
    rw [inf_eq_right.mpr ha, inf_eq_right.mpr hab, add_comm (f (a ⊓ b) ⊓ c)]
    exact add_le_add_right (inf_le_inf_right c (hmono inf_le_right)) c
  · rcases le_total c (f b) with hb | hb
    · have hab : c ≤ f (a ⊔ b) := hb.trans (hmono le_sup_right)
      rw [inf_eq_right.mpr hb, inf_eq_right.mpr hab]
      exact add_le_add_left (inf_le_inf_right c (hmono inf_le_left)) c
    · rw [inf_eq_left.mpr ha, inf_eq_left.mpr hb]
      exact (add_le_add inf_le_left inf_le_left).trans (hf a b)

end Truncation

section Subadditive

variable [Lattice α] [AddCommMonoid β] [Preorder β] [AddRightMono β] {f : α → β}

/-- A submodular function with `0 ≤ f ⊥` is subadditive on disjoint elements. -/
theorem Submodular.sup_le_add_of_disjoint [OrderBot α] (hf : Submodular f) (hbot : 0 ≤ f ⊥)
    {a b : α} (hd : Disjoint a b) : f (a ⊔ b) ≤ f a + f b :=
  (le_add_of_nonneg_left (by rwa [hd.eq_bot])).trans (hf a b)

end Subadditive
