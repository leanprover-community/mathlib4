/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Order.Lattice
import Mathlib.Tactic.TFAE
import Mathlib.Data.Setoid.Basic

/-!
# Distributive, Standard and Neutral elements

TODO: Consider merging this into `Order.Lattice`.

-/


variable {α β : Type*}

/-- Element is distributive -/
def IsDistrib [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), a ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y)

/-- Element is standard -/
def IsStandard [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), x ⊓ (a ⊔ y) = (x ⊓ a) ⊔ (x ⊓ y)

/-- Element is neutral -/
def IsNeutral [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), (a ⊓ x) ⊔ (a ⊓ y) ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y) ⊓ (x ⊔ y)

variable [Lattice α] [Lattice β]

/-- The set of neutral elements of a lattice -/
def Set.neutral : Set α :=
  { z | IsNeutral z }

/-- Lattice homomorphism is a structure preserving map between lattices -/
structure IsLatticeHom (f : α → β) : Prop where
  /-- f preserves inf -/
  map_inf (a b : α) : f (a ⊓ b) = f a ⊓ f b
  /-- f preserves sup -/
  map_sup (a b : α) : f (a ⊔ b) = f a ⊔ f b

lemma kercong (f : α → β) (h : IsLatticeHom f) :  IsLatticeCon (Setoid.ker f) := {
      (Setoid.ker f).iseqv with
      inf := fun h1 h2 => by
        simp_all [Setoid.ker, Function.onFun, h.map_inf]
      sup := fun h1 h2 => by
        simp_all [Setoid.ker, Function.onFun, h.map_sup]
  }

lemma theorem2_i_ii (a : α) : IsDistrib a → IsLatticeHom (fun x => a ⊔ x) := fun h => {
  map_inf := h
  map_sup := sup_sup_distrib_left _
}

lemma theorem2_ii_iii (a : α) (h : IsLatticeHom (fun x => a ⊔ x)) :
    IsLatticeCon (Setoid.ker (fun x => a ⊔ x)) := kercong _ h

lemma theorem2_iii_i (a : α) (h : IsLatticeCon (Setoid.ker (fun x => a ⊔ x))) : IsDistrib a := by
  intro x y
  have e1 : a ⊔ x ⊓ y = a ⊔ ((a ⊔ x) ⊓ (a ⊔ y)) := by
    apply h.inf
    · simp [Setoid.ker, Function.onFun]
    · simp [Setoid.ker, Function.onFun]
  rw [e1]
  simp

open List in
theorem theorem2 (a : α) : TFAE [
    IsDistrib a,
    IsLatticeHom (fun x => a ⊔ x),
    IsLatticeCon (Setoid.ker (fun x => a ⊔ x))] := by
  tfae_have 1 → 2
  | h => by (expose_names; exact theorem2_i_ii a h_1)
  tfae_have 2 → 3
  | h => by (expose_names; exact theorem2_ii_iii a h_1)
  tfae_have 3 → 1
  | h => by (expose_names; exact theorem2_iii_i a h_1)
  tfae_finish

lemma theorem3_i_ii (a : α) (h : IsStandard a) :
    IsLatticeCon (fun x y => ∃ a₁, a₁ ≤ a ∧ (x ⊓ y) ⊔ a₁ = x ⊔ y) := by
  rw [isLatticCon_iff]
  constructor
  · constructor
    · intro x
      use x ⊓ a
      constructor
      · exact inf_le_right
      · rw [inf_idem, sup_idem, sup_of_le_left inf_le_left]
  · constructor
    · intro x y
      constructor
      · intro ⟨a₁, ha1, ha2⟩
        use a₁
        constructor
        · exact ha1
        · rw [← ha2, inf_of_le_left le_sup_left, sup_of_le_right le_sup_left]
      · intro ⟨a₁, ha1, ha2⟩
        rw [sup_of_le_right inf_le_sup, inf_of_le_left inf_le_sup] at ha2
        use a₁
    · constructor
      · intro x y z hxy hyz ⟨a₁, ha11, ha12⟩ ⟨a₂, ha21, ha22⟩
        use a₁ ⊔ a₂
        constructor
        · exact sup_le ha11 ha21
        · rw [inf_eq_left.mpr hxy, sup_eq_right.mpr hxy] at ha12
          rw [inf_eq_left.mpr hyz, sup_eq_right.mpr hyz] at ha22
          rw [inf_eq_left.mpr (Preorder.le_trans x y z hxy hyz),
            sup_eq_right.mpr (Preorder.le_trans x y z hxy hyz), ← ha22, ← ha12, ← sup_assoc]
      · intro x y t hxy ⟨a₁, ha1, ha2⟩
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
              sup_of_le_right le_sup_left]


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

open List in
theorem theorem3 (a : α) : TFAE [
    IsStandard a,
    IsLatticeCon (fun x y => ∃ a₁, a₁ ≤ a ∧ (x ⊓ y) ⊔ a₁ = x ⊔ y),
    IsDistrib a ∧ ∀ x y : α, a ⊓ x = a ⊓ y ∧ a ⊔ x = a ⊔ y → x = y] := by
  tfae_have 1 → 2
  | h => by (expose_names; exact theorem3_i_ii a h_1)
  tfae_have 2 → 3
  | h => by
    let r x' y' := ∃ a₁ ≤ a,(x' ⊓ y') ⊔ a₁ = x' ⊔ y'
    constructor
    · have e1 (x : α) : r x (a ⊔ x) := by
        use a
        simp
        rw [sup_comm]
      intro x y
      have e2 : r (x ⊓ y) ((a ⊔ x) ⊓ (a ⊔ y)) := by
        apply h.inf (e1 x) (e1 y)
      have e3 : r (x ⊓ y) (x ⊓ y) := by
        apply h.inf (h.refl x) (h.refl y)
      unfold r at e3
      obtain ⟨a₁, ha1, ha2⟩ := e2
      simp at ha2
      have e4 : x ⊓ y ⊔ (a ⊔ x) ⊓ (a ⊔ y) = (a ⊔ x) ⊓ (a ⊔ y) := by
        simp
        constructor
        · rw [sup_comm]
          exact le_trans (b := x) inf_le_left le_sup_left
        · exact le_trans inf_le_right le_sup_right
      rw [e4] at ha2
      have e5 : ((a ⊔ x) ⊓ (a ⊔ y)) ⊔ a₁ = (a ⊔ x) ⊓ (a ⊔ y) := by
        simp
        constructor
        · exact le_sup_of_le_left ha1
        · exact le_sup_of_le_left ha1
      have testn : x ⊓ y ⊓ ((a ⊔ x) ⊓ (a ⊔ y)) = x ⊓ y := by
        exact sup_eq_iff_inf_eq.mp e4
      rw [testn] at ha2
      rw [le_antisymm_iff]
      constructor
      · simp
        constructor
        · apply le_trans (b := x) inf_le_left le_sup_right
        · apply le_trans (b := y) inf_le_right le_sup_right
      · rw [← ha2]
        rw [sup_comm]
        exact sup_le_sup_right ha1 (x ⊓ y)
    · have step1 {x y : α} (h₁ : a ⊓ x = a ⊓ y) (h₂ : a ⊔ x = a ⊔ y) : x ⊓ y = x := by

        have e1 : ∃ a₁ ≤ a,((a ⊔ y) ⊓ y) ⊔ a₁ = (a ⊔ y) ⊔ y := by
          use a
          simp
          rw [sup_comm]
        have e1' : r (a ⊔ y) y := by
          exact e1
        have e2 : r (x ⊓ y) (x ⊓ (a ⊔ y)) := by
          apply h.inf (h.refl x) (h.symm e1')
        rw [← h₂] at e2
        simp only [le_sup_right, inf_of_le_left] at e2
        obtain ⟨a₁, ha1, ha2⟩ := e2
        simp at ha2
        have e3 : a₁ ≤ a ⊓ x := by
          apply le_inf ha1
          rw [← ha2]
          apply le_sup_right
        --rw [h₁] at e3
        have e4 : a₁ ≤ x ⊓ y := by
          apply le_inf (le_inf_iff.mp e3).2
          rw [h₁] at e3
          exact (le_inf_iff.mp e3).2
        have e5 : x ⊓ y = x := by
          conv_rhs => rw [← ha2]
          symm
          rw [sup_eq_left]
          exact e4
        exact e5
      intro x y ⟨h₁, h₂⟩
      rw [← step1 h₁ h₂]
      rw [inf_comm]
      rw [step1 h₁.symm h₂.symm]
  tfae_have 3 → 1
  | ⟨h1,h2⟩ => by exact theorem3_iii_i a h1 h2
  tfae_finish


/-
lemma theorem4_i_ii (a : α) (h1 : IsNeutral a) : IsDistrib a := by
  intro x y
  have e1 (h : a ≤ x) : a ⊔ (x ⊓ y) = x ⊓ (a ⊔ y) :=
    calc
      a ⊔ (x ⊓ y) = (a ⊓ x) ⊔ (x ⊓ y) ⊔ (y ⊓ a) := by
        aesop
        rw [inf_comm]
        apply inf_le_inf_right
      _ = x ⊓ (a ⊔ y) := sorry
-/
