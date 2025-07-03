import Mathlib

--import Mathlib.Order.Lattice


variable {α : Type*}

def IsDistrib [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), a ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y)

def IsStandard [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), x ⊓ (a ⊔ y) = (x ⊓ a) ⊔ (x ⊓ y)

def IsNeutral [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), (a ⊓ x) ⊔ (a ⊓ y) ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y) ⊓ (x ⊔ y)

variable [Lattice α]

def Set.neutral : Set α :=
  { z | IsNeutral z }

lemma theorem3_iii_i (a : α) (h1 : IsDistrib a)
    (h2 : ∀ x y : α, a ⊓ x = a ⊓ y ∧ a ⊔ x = a ⊔ y → x = y) : IsStandard a := by
  intro x y
  let b := x ⊓ (a ⊔ y)
  let c := (x ⊓ a) ⊔ (x ⊓ y)
  have i1 : (x ⊓ a) ⊔ (x ⊓ y) ≤ x ⊓ (a ⊔ y) := by
    simp_all only [and_imp, le_inf_iff]
    constructor
    · simp_all only [sup_le_iff, inf_le_left, and_self]
    · apply sup_le_sup
      exact inf_le_right
      exact inf_le_right
  apply h2
  constructor
  · apply le_antisymm
    · rw [← inf_assoc]
      have e1 : a ⊓ x ⊓ (a ⊔ y) = a ⊓ x := by
        have e2 : a ⊓ x ≤ a ⊔ y := by
          apply le_trans (b := a)
          exact inf_le_left
          exact le_sup_left
        aesop
      rw [e1]
      rw [le_inf_iff]
      constructor
      · exact inf_le_left
      · rw [inf_comm]
        exact le_sup_left
    · apply inf_le_inf_left
      exact i1
  · rw [h1]
    simp only [le_sup_left, sup_of_le_right]
    rw [← h1]
    apply le_antisymm
    · apply sup_le_sup_left
      exact le_sup_right
    · rw [← sup_assoc]
      aesop
