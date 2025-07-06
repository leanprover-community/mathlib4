import Mathlib

--import Mathlib.Order.Lattice


variable {α β : Type*}

def IsDistrib [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), a ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y)

def IsStandard [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), x ⊓ (a ⊔ y) = (x ⊓ a) ⊔ (x ⊓ y)

def IsNeutral [Lattice α] (a : α) : Prop :=
  ∀ (x y : α), (a ⊓ x) ⊔ (a ⊓ y) ⊔ (x ⊓ y) = (a ⊔ x) ⊓ (a ⊔ y) ⊓ (x ⊔ y)

structure IsLatticeCon [Lattice α] (r : α → α → Prop) : Prop extends Equivalence r where
  inf : ∀ {w x y z}, r w x → r y z → r (w ⊓ y) (x ⊓ z)
  sup : ∀ {w x y z}, r w x → r y z → r (w ⊔ y) (x ⊔ z)

lemma isLatticCon_iff [Lattice α] (r : α → α → Prop) (h : IsRefl _ r) : IsLatticeCon r ↔
    (∀ x y : α, r x y ↔ r (x ⊓ y) (x ⊔ y)) ∧
    (∀ x y z : α, x ≤ y → y ≤ z → r x y → r y z → r x z) ∧
    (∀ x y t : α, x ≤ y → r x y → r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t)) := by
  constructor
  · intro hlc
    constructor
    · intro x y
      constructor
      · intro h
        exact hlc.trans (y := y) (by
          conv_rhs => rw [← inf_idem y]
          exact hlc.inf h (hlc.refl y)) (by
          conv_lhs => rw [← sup_idem y]
          exact hlc.sup (hlc.symm h) (hlc.refl y))
      · intro h
        have e1 : r x (x ⊓ y)  := by
          conv_lhs => rw [← inf_sup_self (a := x) (b := y)]
          conv_rhs => rw [← inf_idem x, inf_assoc]
          exact hlc.inf (hlc.refl x) (hlc.symm h)
        have e2 : r (x ⊓ y) y  := by
          conv_rhs => rw [← inf_sup_self (a := y) (b := x)]
          conv_lhs => rw [← inf_idem y, inf_comm, inf_assoc]
          apply hlc.inf (hlc.refl y)
          rw [inf_comm, sup_comm]
          exact h
        exact hlc.trans e1 e2
    · exact ⟨fun _ _ _ _ _ => hlc.trans, fun _ _ t _ h2 =>
        ⟨hlc.inf h2 (hlc.refl t), hlc.sup h2 (hlc.refl t)⟩⟩
  · intro ⟨h1,h2,h3⟩
    have e1 (a b c d : α) (hb : b ∈ Set.Icc a d) (hc : c ∈ Set.Icc a d) (h : r a d) : r b c := by
      rw [h1]
      conv_lhs => rw [← inf_eq_left.mpr inf_le_sup]
      conv_rhs => rw [← inf_eq_right.mpr (sup_le hb.2 hc.2)]
      apply (h3 _ _ _ (inf_le_of_left_le hb.2) _).1
      rw [← sup_eq_right.mpr (le_inf hb.1 hc.1), ← sup_eq_left.mpr (inf_le_of_left_le hb.2)]
      exact (h3 _ _ _ (le_trans hb.1 hb.2) h).2
    constructor
    · constructor
      · intro x
        exact h.refl _
      · intro x y hxy
        rw [h1, inf_comm, sup_comm, ← h1]
        exact hxy
      · intro x y z hxy hyz
        apply e1 (a := x ⊓ y ⊓ z) (d := x ⊔ y ⊔ z)
        rw [Set.mem_Icc]
        constructor
        · rw [inf_assoc]
          exact inf_le_left
        · rw [sup_assoc]
          exact le_sup_left
        simp only [Set.mem_Icc, inf_le_right, le_sup_right, and_self]
        have e2 : r ((x ⊓ y) ⊔ (y ⊔ z)) ((x ⊔ y) ⊔ (y ⊔ z)) :=
          (h3 _ _ _ inf_le_sup ((h1 x y).mp hxy)).2
        have e3 : (x ⊔ y) ⊔ (y ⊔ z) = x ⊔ y ⊔ z := by
          rw [sup_comm x y, ← sup_sup_distrib_left, sup_assoc]
        have e4 : (x ⊓ y) ⊔ (y ⊔ z) = (y ⊔ z) :=
          sup_eq_right.mpr (le_trans inf_le_right le_sup_left)
        rw [e3, e4] at e2
        have e2' : r ((x ⊓ y) ⊓ (y ⊓ z)) ((x ⊔ y) ⊓ (y ⊓ z))  :=
          (h3 _ _ _ inf_le_sup ((h1 x y).mp hxy)).1
        have e3' : (x ⊓ y) ⊓ (y ⊓ z) = x ⊓ y ⊓ z := by
          rw [inf_comm x y, ← inf_inf_distrib_left, inf_assoc]
        --have e4' : (x ⊔ y) ⊓ (y ⊓ z) = x ⊓ z :=
        --  inf_eq_right.mpr (le_trans inf_le_right le_sup_right)
        have e4' : (x ⊔ y) ⊓ (y ⊓ z) = (y ⊓ z) :=
          inf_eq_right.mpr (le_trans inf_le_left le_sup_right)
        rw [e3', e4'] at e2'
        have e5 : r (x ⊓ y ⊓ z) (y ⊔ z) := h2 (y := y ⊓ z) _ _
          (by rw [inf_assoc]; exact inf_le_right) inf_le_sup e2' ((h1 _ _).mp hyz)
        apply h2 (y := y ⊔ z)
        rw [inf_assoc]
        apply inf_le_of_right_le
        exact inf_le_sup
        rw [sup_assoc]
        exact le_sup_right
        apply e5
        apply e2






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
    IsLatticeCon (fun x y => ∃ a₁, a₁ ≤ a ∧ (x ⊓ y) ⊔ a₁ = x ⊔ y) where
  refl := sorry
  symm := sorry
  trans := sorry
  inf := sorry
  sup := sorry

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
