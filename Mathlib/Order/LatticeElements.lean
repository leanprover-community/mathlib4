/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Order.Lattice
import Mathlib.Tactic.TFAE
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Lattice.Congruence

/-!
# Distributive, Standard and Neutral elements

Defines distinguished sets of elements within a `Lattice` and considers their properties.

## Main definitions

- `IsDistrib` : `a` is distributive if, for all `x` and `y`, `a ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y)`
- `IsStandard` : `a` is standard if, for all `x` and `y`, `x ⊓ (a ⊔ y) = (x ⊓ a) ⊔ (x ⊓ y)`
- `IsNeutral` : `a` is neutral if, for all `x` and `y`,
  `(a ⊓ x) ⊔ (a ⊓ y) ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y) ⊓ (x ⊔ y)`

## Main statements

- `isDistrib_iff` : Sufficient and necessary conditions for `a` to be distributive
- `isStandard_iff` : Sufficient and necessary conditions for `a` to be standard

## References

* [Grätzer et al, *General lattice theory*][Graetzer2003]

## Tags

lattice, distributive, neutral
-/

variable {α : Type*}

/-- Element is distributive -/
def IsDistrib [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), a ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y)

/-- Element is standard -/
def IsStandard [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), x ⊓ (a ⊔ y) = (x ⊓ a) ⊔ (x ⊓ y)

/-- Element is neutral -/
def IsNeutral [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), (a ⊓ x) ⊔ (a ⊓ y) ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y) ⊓ (x ⊔ y)

variable [Lattice α]

/-- Grätzer III.2, Theorem 2 1 → 2 -/
def const_sup_left_of_isDistrib {a : α} (h : IsDistrib a) : LatticeHom α α := {
  __ := supLeft a
  map_inf' := h
}

/-
Grätzer III.2, Theorem 2 2 → 3
#check LatticeCon.ker
-/

lemma isDistrib_iff {a : α} : IsDistrib a ↔
    ∀ ⦃w x y z : α⦄, (Setoid.ker (supLeft a)).r w x ∧ (Setoid.ker (supLeft a)).r y z →
    (Setoid.ker (supLeft a)).r (w ⊓ y) (x ⊓ z) := by
  constructor
  · intro h w x y z ⟨h₁, h₂⟩
    simp_all [supLeft, Setoid.ker_def]
    rw [h, h, h₁, h₂]
  · intro h x y
    have e1 : a ⊔ x ⊓ y = a ⊔ ((a ⊔ x) ⊓ (a ⊔ y)) := by
      apply h
      constructor
      · simp [supLeft, Setoid.ker_def]
      · simp [supLeft, Setoid.ker_def]
    simp [e1]

/-- Grätzer III.2, Theorem 2 3 → 1 -/
lemma isDistrib_of_congruence {a : α}
    {c : LatticeCon α} (h : ∀ ⦃x y : α⦄, c.r x y ↔ a ⊔ x = a ⊔ y) : IsDistrib a := by
  apply isDistrib_iff.mpr
  simp [supLeft,  Setoid.ker_def]
  intro w x y z h1 h2
  rw [← h] at *
  exact c.inf h1 h2

instance {a : α} :
    IsRefl α (fun x y => ∃ a₁, a₁ ≤ a ∧ (x ⊓ y) ⊔ a₁ = x ⊔ y) where
  refl x := by
    use x ⊓ a
    constructor
    · exact inf_le_right
    · rw [inf_idem, sup_idem, sup_of_le_left inf_le_left]

/-- Grätzer III.2, Theorem 3 1 → 2 -/
def of_isStandard {a : α} (h : IsStandard a) : LatticeCon α := LatticeCon.mk'
  (fun x y => ∃ a₁, a₁ ≤ a ∧ (x ⊓ y) ⊔ a₁ = x ⊔ y)
  (by
    intro x y
    constructor
    · intro ⟨a₁, ha1, ha2⟩
      use a₁
      constructor
      · exact ha1
      · rw [← ha2, inf_of_le_left le_sup_left, sup_of_le_right le_sup_left]
    · intro ⟨a₁, ha1, ha2⟩
      rw [sup_of_le_right inf_le_sup, inf_of_le_left inf_le_sup] at ha2
      use a₁)
  (by
    intro x y z hxy hyz ⟨a₁, ha11, ha12⟩ ⟨a₂, ha21, ha22⟩
    use a₁ ⊔ a₂
    constructor
    · exact sup_le ha11 ha21
    · rw [inf_eq_left.mpr hxy, sup_eq_right.mpr hxy] at ha12
      rw [inf_eq_left.mpr hyz, sup_eq_right.mpr hyz] at ha22
      rw [inf_eq_left.mpr (Preorder.le_trans x y z hxy hyz),
        sup_eq_right.mpr (Preorder.le_trans x y z hxy hyz), ← ha22, ← ha12, ← sup_assoc])
  (by
    intro x y t hxy ⟨a₁, ha1, ha2⟩
    constructor
    · use y ⊓ t ⊓ a
      constructor
      · exact inf_le_right
      · rw [inf_eq_left.mpr hxy, sup_eq_right.mpr hxy] at ha2
        rw [inf_assoc, inf_of_le_right inf_le_right, inf_comm, sup_comm, ←  h (y ⊓ t) x,
          sup_comm, inf_eq_left.mpr
          (le_trans (b := x ⊔ a₁) (by rw [ha2]; exact inf_le_left) (sup_le_sup_left ha1 x))]
        exact le_antisymm_iff.mpr ⟨le_sup_right,
          le_inf_iff.mpr ⟨sup_le_iff.mpr ⟨inf_le_of_left_le hxy, inf_le_left⟩,
            sup_le_iff.mpr ⟨inf_le_right, inf_le_right⟩⟩⟩
    · use a₁
      constructor
      · exact ha1
      · rw [inf_eq_left.mpr hxy, sup_eq_right.mpr hxy] at ha2
        rw [←  ha2, sup_assoc, sup_comm a₁ t, ← sup_assoc, inf_of_le_left le_sup_left,
          sup_of_le_right le_sup_left])

/-- Grätzer III.2, Theorem 3 2 → 3 -/
lemma isDistrib_and {a : α} {c : LatticeCon α}
    (h : ∀ ⦃x y : α⦄, c.r x y ↔ ∃ a₁, a₁ ≤ a ∧ (x ⊓ y) ⊔ a₁ = x ⊔ y) :
    IsDistrib a ∧ ∀ x y : α, a ⊓ x = a ⊓ y ∧ a ⊔ x = a ⊔ y → x = y := by
  constructor
  · intro x y
    have e1 (x : α) : c.r x (a ⊔ x) := by --⟨a, by simp [sup_comm]⟩
      rw [h]
      exact ⟨a, by simp [sup_comm]⟩
    have e4 : x ⊓ y ⊔ (a ⊔ x) ⊓ (a ⊔ y) = (a ⊔ x) ⊓ (a ⊔ y) := sup_eq_right.mpr
      (le_inf_iff.mpr ⟨le_trans inf_le_left le_sup_right, le_trans inf_le_right le_sup_right⟩)
    obtain ⟨a₁, ha1, ha2⟩ := h.mp (c.inf (e1 x) (e1 y))
    rw [e4, sup_eq_iff_inf_eq.mp e4] at ha2
    rw [le_antisymm_iff]
    constructor
    · simp only [le_inf_iff, sup_le_iff, le_sup_left, true_and]
      exact ⟨le_trans inf_le_left le_sup_right, le_trans inf_le_right le_sup_right⟩
    · rw [← ha2, sup_comm]
      exact sup_le_sup_right ha1 (x ⊓ y)
  · have step1 {x y : α} (h₁ : a ⊓ x = a ⊓ y) (h₂ : a ⊔ x = a ⊔ y) : x ⊓ y = x := by
      have e2 : c.r (x ⊓ y) (x ⊓ (a ⊔ y)) := c.inf (c.refl x)
        (by rw [h]; exact ⟨a, by simp [sup_comm]⟩)
      rw [← h₂] at e2
      simp only [le_sup_right, inf_of_le_left] at e2
      obtain ⟨a₁, ha1, ha2⟩ := h.mp e2
      simp at ha2
      have e3 : a₁ ≤ a ⊓ x := le_inf ha1 (by rw [← ha2]; exact le_sup_right)
      conv_rhs => rw [← ha2]
      symm
      rw [sup_eq_left]
      exact le_inf (le_inf_iff.mp e3).2 (by rw [h₁] at e3; exact (le_inf_iff.mp e3).2)
    intro x y ⟨h₁, h₂⟩
    rw [← step1 h₁ h₂, inf_comm, step1 h₁.symm h₂.symm]

/-- Grätzer III.2, Theorem 3 3 → 1 -/
lemma isStandard_of_isDistrib_and {a : α}
    (h : IsDistrib a ∧ ∀ x y : α, a ⊓ x = a ⊓ y ∧ a ⊔ x = a ⊔ y → x = y) : IsStandard a := by
  intro x y
  apply h.2 _ _
  constructor
  · apply le_antisymm (by
        rw [← inf_assoc, inf_of_le_left (le_trans inf_le_left le_sup_left), le_inf_iff]
        exact ⟨inf_le_left, by rw [inf_comm]; exact le_sup_left⟩
        ) (inf_le_inf_left _ (le_inf_iff.mpr ⟨sup_le_iff.mpr ⟨inf_le_left,inf_le_left⟩,
          sup_le_sup inf_le_right inf_le_right⟩))
  · rw [h.1, sup_of_le_right le_sup_left, ← h.1]
    exact le_antisymm (sup_le_sup_left le_sup_right _) (by simp [← sup_assoc])
