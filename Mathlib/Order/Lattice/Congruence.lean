/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Hom.Lattice

/-!
# Lattice Congruences

## Main definitions

- `LatticeCon`: An equivalence relation is a congruence relation for the latice structure if it is
  compatible with the `inf` and `sup` operations.
- `LatticeCon.ker`: The kernel of a lattice homomorphism as a lattice congruence.

## Main statements

- `LatticeCon.mk3`: Alternative conditions for a relation to be a lattice congruence.

## References

* [Grätzer et al, *General lattice theory*][Grätzer2003]

## Tags

Lattice, Congruence
-/

variable {α : Type*}

/-- An equivalence relation is a congruence relation for the latice structure if it is compatible
with the `inf` and `sup` operations. -/
structure LatticeCon (α) [Lattice α] extends Setoid α where
  inf : ∀ {w x y z}, r w x → r y z → r (w ⊓ y) (x ⊓ z)
  sup : ∀ {w x y z}, r w x → r y z → r (w ⊔ y) (x ⊔ z)

namespace LatticeCon

@[simp]
lemma r_inf_sup_iff [Lattice α] (c : LatticeCon α) {x y : α} : c.r (x ⊓ y) (x ⊔ y) ↔ c.r x y where
  mp h := c.trans (by simpa using c.inf (c.refl x) (c.symm h)) (by simpa using c.inf h (c.refl y))
  mpr h := c.trans (by simpa using c.inf h (c.refl y)) (by simpa using c.sup (c.symm h) (c.refl y))

private lemma closed_interval [Lattice α] {r : α → α → Prop}
    (h₂ : ∀ ⦃x y : α⦄, r x y ↔ r (x ⊓ y) (x ⊔ y))
    (h₄ : ∀ ⦃x y t : α⦄, x ≤ y → r x y → r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t))
    (a b c d : α) (hab : a ≤ b) (hbd : b ≤ d) (hac : a ≤ c) (hcd : c ≤ d) (had : r a d) :
    r b c := by
  rw [h₂]
  conv_lhs => rw [← inf_eq_left.mpr inf_le_sup]
  conv_rhs => rw [← inf_eq_right.mpr (sup_le hbd hcd)]
  apply (h₄ (inf_le_of_left_le hbd) _).1
  rw [← sup_eq_right.mpr (le_inf hab hac), ← sup_eq_left.mpr (inf_le_of_left_le hbd)]
  exact (h₄ (le_trans hab hbd) had).2

private lemma transitive [Lattice α] {r : α → α → Prop}
    (h₂ : ∀ ⦃x y : α⦄, r x y ↔ r (x ⊓ y) (x ⊔ y))
    (h₃ : ∀ ⦃x y z : α⦄, x ≤ y → y ≤ z → r x y → r y z → r x z)
    (h₄ : ∀ ⦃x y t : α⦄, x ≤ y → r x y → r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t)) :
    ∀ {x y z : α}, r x y → r y z → r x z := by
  intro x y z hxy hyz
  exact closed_interval h₂ h₄ (x ⊓ y ⊓ z) _ _ (x ⊔ y ⊔ z) (by simp [inf_assoc, inf_le_left])
    (by simp [sup_assoc, le_sup_left]) inf_le_right le_sup_right
    (h₃ (by simpa [inf_assoc] using inf_le_of_right_le inf_le_sup)
    (by simp [sup_assoc, le_sup_right]) (h₃
    (by rw [inf_assoc]; exact inf_le_right) inf_le_sup (by
      conv_lhs => rw [inf_comm x, inf_assoc, inf_inf_distrib_left, inf_comm _ x]
      conv_rhs => rw [← inf_eq_right.mpr (le_trans inf_le_left le_sup_right)]
      exact (h₄ inf_le_sup (h₂.mp hxy)).1) (h₂.mp hyz)) (by
      conv_rhs => rw [sup_comm x, sup_assoc, sup_sup_distrib_left, sup_comm _ x]
      conv_lhs => rw [← sup_eq_right.mpr (le_trans inf_le_right le_sup_left)]
      exact (h₄ inf_le_sup (h₂.mp hxy)).2))

/-- Alternative conditions for a lattice congruence. -/
def mk3 [Lattice α] (r : α → α → Prop) (h₁ : IsRefl α r)
    (h₂ : ∀ ⦃x y : α⦄, r x y ↔ r (x ⊓ y) (x ⊔ y))
    (h₃ : ∀ ⦃x y z : α⦄, x ≤ y → y ≤ z → r x y → r y z → r x z)
    (h₄ : ∀ ⦃x y t : α⦄, x ≤ y → r x y → r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t)) : LatticeCon α :=
  LatticeCon.mk (Setoid.mk r (Equivalence.mk h₁.refl
  (fun h => by rw [h₂, inf_comm, sup_comm, ← h₂]; exact h)
  (fun hxy hxz => transitive h₂ h₃ h₄ hxy hxz))) (fun h1 h2 => by
    have compatible_left_inf {x y t : α} (hh : r x y) : r (x ⊓ t) (y ⊓ t) :=
      closed_interval h₂ h₄ ((x ⊓ y) ⊓ t) _ _ ((x ⊔ y) ⊓ t)
            (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ le_sup_left)
            (inf_le_inf_right _ inf_le_right) (inf_le_inf_right _ le_sup_right)
            (h₄ inf_le_sup (h₂.mp hh)).1
    exact transitive h₂ h₃ h₄ (by
          conv_lhs => rw [inf_comm]
          conv_rhs => rw [inf_comm]
          exact compatible_left_inf h2)
      (compatible_left_inf h1)) (fun h1 h2 => by
        have compatible_left_sup {x y t : α} (hh : r x y) : r (x ⊔ t) (y ⊔ t) :=
          closed_interval h₂ h₄ ((x ⊓ y) ⊔ t) _ _ ((x ⊔ y) ⊔ t)
            (sup_le_sup_right inf_le_left _) (sup_le_sup_right le_sup_left _)
            (sup_le_sup_right inf_le_right _) (sup_le_sup_right le_sup_right _)
            (h₄ inf_le_sup (h₂.mp hh)).2
        exact transitive h₂ h₃ h₄ (by
          conv_lhs => rw [sup_comm]
          conv_rhs => rw [sup_comm]
          exact compatible_left_sup h2) (compatible_left_sup h1))

variable {β F : Type*} [FunLike F α β]

open Function

/-- The kernel of a lattice homomorphism as a lattice congruence. -/
@[simps!]
def ker [Lattice α] [Lattice β] [LatticeHomClass F α β] (f : F) : LatticeCon α where
  toSetoid := Setoid.ker f
  inf _ _ := by simp_all only [Setoid.ker, onFun, map_inf]
  sup _ _ := by simp_all only [Setoid.ker, onFun, map_sup]

end LatticeCon
