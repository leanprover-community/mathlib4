/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Order.Lattice

/-!
# Distributive, Standard and Neutral elements

TODO: Consider merging this into `Order.Lattice`.

-/


variable {α β : Type*}

def IsDistrib [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), a ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y)

def IsStandard [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), x ⊓ (a ⊔ y) = (x ⊓ a) ⊔ (x ⊓ y)

def IsNeutral [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), (a ⊓ x) ⊔ (a ⊓ y) ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y) ⊓ (x ⊔ y)

def ker (f : α → β) : α → α → Prop := fun a b => f a = f b

lemma equiv_ker (f : α → β) : Equivalence (ker f) where
  refl _ := rfl
  symm h := h.symm
  trans h1 h2 := h1.trans h2

variable [Lattice α] [Lattice β]





def Set.neutral : Set α :=
  { z | IsNeutral z }

structure IsLatticeHom (f : α → β) : Prop where
  map_inf (a b : α) : f (a ⊓ b) = f a ⊓ f b
  map_sup (a b : α) : f (a ⊔ b) = f a ⊔ f b

lemma kercong (f : α → β) (h : IsLatticeHom f) :  IsLatticeCon (ker f) := {
      equiv_ker f with
      inf := fun h1 h2 => by
        unfold ker
        rw [h.map_inf, h.map_inf, h1, h2]
      sup := fun h1 h2 => by
        unfold ker
        rw [h.map_sup, h.map_sup, h1, h2]
  }



lemma theorem2_i_ii (a : α) : IsDistrib a → IsLatticeHom (fun x => a ⊔ x) := fun h => {
  map_inf := h
  map_sup := sup_sup_distrib_left _
}

lemma theorem2_ii_iii (a : α) (h : IsLatticeHom (fun x => a ⊔ x)) :
    IsLatticeCon (ker (fun x => a ⊔ x)) := kercong _ h

lemma theorem2_iii_i (a : α) (h : IsLatticeCon (ker (fun x => a ⊔ x))) : IsDistrib a := by
  intro x y
  have e1 : a ⊔ x ⊓ y = a ⊔ ((a ⊔ x) ⊓ (a ⊔ y)) := by
    apply h.inf
    · unfold ker
      simp
    · unfold ker
      simp
  rw [e1]
  simp

lemma theorem3_i_ii (a : α) (h : IsStandard a) :
    IsLatticeCon (fun x y => ∃ a₁, a₁ ≤ a ∧ (x ⊓ y) ⊔ a₁ = x ⊔ y) := by
  rw [isLatticCon_iff]
  constructor
  · constructor
    · intro x
      use x ⊓ a
      constructor
      · exact inf_le_right
      · simp only [le_refl, inf_of_le_left, inf_le_left, sup_of_le_left]
  · constructor
    · intro x y
      constructor
      · intro h
        obtain ⟨a₁, ha1, ha2⟩ := h
        use a₁
        constructor
        · exact ha1
        · rw [← ha2]
          simp only [le_sup_left, inf_of_le_left, sup_of_le_right]
      · intro h
        obtain ⟨a₁, ha1, ha2⟩ := h
        use a₁
        constructor
        · exact ha1
        · have e1 : x ⊓ y ⊔ (x ⊔ y) = x ⊔ y := sup_of_le_right inf_le_sup
          rw [e1] at ha2
          have e2 : x ⊓ y ⊓ (x ⊔ y) = x ⊓ y := inf_of_le_left inf_le_sup
          rw [e2] at ha2
          exact ha2
    · constructor
      · intro x y z hxy hyz h1 h2
        obtain ⟨a₁, ha11, ha12⟩ := h1
        obtain ⟨a₂, ha21, ha22⟩ := h2
        use a₁ ⊔ a₂
        constructor
        · exact sup_le ha11 ha21
        · have exyi : x ⊓ y = x := by
            apply inf_eq_left.mpr hxy
          have exys : x ⊔ y = y := by
            apply sup_eq_right.mpr hxy
          rw [exyi, exys] at ha12
          have eyzi : y ⊓ z = y := by
            apply inf_eq_left.mpr hyz
          have eyzs : y ⊔ z = z := by
            apply sup_eq_right.mpr hyz
          rw [eyzi, eyzs] at ha22
          have exzi : x ⊓ z = x := by
            apply inf_eq_left.mpr
            exact Preorder.le_trans x y z hxy hyz
          have exzs : x ⊔ z = z := by
            apply sup_eq_right.mpr
            exact Preorder.le_trans x y z hxy hyz
          rw [exzi, exzs]
          rw [← ha22]
          rw [← ha12]
          rw [← sup_assoc]

            --exact?
      · sorry







/-
  refl := by
    intro x
    use x ⊓ a
    constructor
    · exact inf_le_right
    · simp only [le_refl, inf_of_le_left, inf_le_left, sup_of_le_left]
  symm := by
    intro x y h
    obtain ⟨a₁, ha1, ha2⟩ := h
    use a₁
    constructor
    · exact ha1
    · rw [sup_comm y x, inf_comm, ha2]
  trans := by
    intro x y z h1 h2
    obtain ⟨a₁, ha11, ha12⟩ := h1
    obtain ⟨a₂, ha21, ha22⟩ := h2
    use a₁ ⊓ a₂
    constructor
    · exact inf_le_of_right_le ha21
    ·

  inf := sorry
  sup := sorry
-/


lemma theorem3_iii_i (a : α) (h1 : IsDistrib a)
    (h2 : ∀ x y : α, a ⊓ x = a ⊓ y ∧ a ⊔ x = a ⊔ y → x = y) : IsStandard a := fun x y => h2 _  _
  ⟨le_antisymm (by
      rw [← inf_assoc, inf_of_le_left (le_trans inf_le_left le_sup_left), le_inf_iff]
      exact ⟨inf_le_left, by rw [inf_comm]; exact le_sup_left⟩
      ) (inf_le_inf_left _ (le_inf_iff.mpr ⟨sup_le_iff.mpr ⟨inf_le_left,inf_le_left⟩,
        sup_le_sup inf_le_right inf_le_right⟩)),
  by
    rw [h1, sup_of_le_right le_sup_left, ← h1]
    exact le_antisymm (sup_le_sup_left le_sup_right _) (by simp [← sup_assoc])⟩

lemma theorem4_i_ii (a : α) (h1 : IsNeutral a) : IsDistrib a := by
  intro x y
  have e1 (h : a ≤ x) : a ⊔ (x ⊓ y) = x ⊓ (a ⊔ y) :=
    calc
      a ⊔ (x ⊓ y) = (a ⊓ x) ⊔ (x ⊓ y) ⊔ (y ⊓ a) := by
        aesop
        rw [inf_comm]
        apply inf_le_inf_right
      _ = x ⊓ (a ⊔ y) := sorry
