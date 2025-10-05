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

- `LatticeCon`: An equivalence relation is a congruence relation for the lattice structure if it is
  compatible with the `inf` and `sup` operations.
- `LatticeCon.ker`: The kernel of a lattice homomorphism as a lattice congruence.

## Main statements

- `LatticeCon.mk'`: Alternative conditions for a relation to be a lattice congruence.

## References

* [Grätzer et al, *General lattice theory*][Graetzer2003]

## Tags

Lattice, Congruence
-/

variable {F α β : Type*} [Lattice α] [Lattice β]

variable (α) in
/-- An equivalence relation is a congruence relation for the latice structure if it is compatible
with the `inf` and `sup` operations. -/
structure LatticeCon extends Setoid α where
  inf : ∀ {w x y z}, r w x → r y z → r (w ⊓ y) (x ⊓ z)
  sup : ∀ {w x y z}, r w x → r y z → r (w ⊔ y) (x ⊔ z)

namespace LatticeCon

@[simp]
lemma r_inf_sup_iff (c : LatticeCon α) {x y : α} : c.r (x ⊓ y) (x ⊔ y) ↔ c.r x y where
  mp h := c.trans (by simpa using c.inf (c.refl x) (c.symm h)) (by simpa using c.inf h (c.refl y))
  mpr h := c.trans (by simpa using c.inf h (c.refl y)) (by simpa using c.sup (c.symm h) (c.refl y))

private lemma closed_interval {r : α → α → Prop}
    (h₂ : ∀ ⦃x y : α⦄, r x y ↔ r (x ⊓ y) (x ⊔ y))
    (h₄ : ∀ ⦃x y t : α⦄, x ≤ y → r x y → r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t))
    (a b c d : α) (hab : a ≤ b) (hbd : b ≤ d) (hac : a ≤ c) (hcd : c ≤ d) (had : r a d) :
    r b c := by
  suffices r (b ⊓ c ⊓ (b ⊔ c)) (d ⊓ (b ⊔ c)) by
    simpa [h₂, inf_eq_right.mpr (sup_le hbd hcd)] using this
  apply (h₄ (inf_le_of_left_le hbd) _).1
  simpa [sup_eq_right.mpr (le_inf hab hac), sup_eq_left.mpr (inf_le_of_left_le hbd)] using
    ((h₄ (le_trans hab hbd) had).2 : r (a ⊔ b ⊓ c) (d ⊔ b ⊓ c))

private lemma transitive {r : α → α → Prop}
    (h₂ : ∀ ⦃x y : α⦄, r x y ↔ r (x ⊓ y) (x ⊔ y))
    (h₃ : ∀ ⦃x y z : α⦄, x ≤ y → y ≤ z → r x y → r y z → r x z)
    (h₄ : ∀ ⦃x y t : α⦄, x ≤ y → r x y → r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t)) :
    ∀ {x y z : α}, r x y → r y z → r x z := by
  intro x y z hxy hyz
  exact closed_interval h₂ h₄ (x ⊓ y ⊓ z) _ _ (x ⊔ y ⊔ z) (by simp [inf_assoc, inf_le_left])
    (by simp [sup_assoc, le_sup_left]) inf_le_right le_sup_right
    (h₃ (by simpa [inf_assoc] using inf_le_of_right_le inf_le_sup)
    (by simp [sup_assoc, le_sup_right]) (h₃
    (by simpa [inf_assoc] using inf_le_right (b := y ⊓ z)) inf_le_sup (by
      suffices r (x ⊓ y ⊓ (y ⊓ z)) ((x ⊔ y) ⊓ (y ⊓ z)) by
        rw [inf_comm x, inf_assoc]
        simpa [inf_comm x, ← inf_inf_distrib_left] using this
      exact (h₄ inf_le_sup (h₂.mp hxy)).1) (h₂.mp hyz)) (by
        simpa [sup_comm y x, sup_sup_distrib_left y x z, sup_assoc] using
          ((h₄ inf_le_sup (h₂.mp hxy)).2 : r (x ⊓ y ⊔ (y ⊔ z)) (x ⊔ y ⊔ (y ⊔ z)))))

/-- Alternative conditions for a lattice congruence. -/
def mk' [Lattice α] (r : α → α → Prop) [h₁ : IsRefl α r]
    (h₂ : ∀ ⦃x y : α⦄, r x y ↔ r (x ⊓ y) (x ⊔ y))
    (h₃ : ∀ ⦃x y z : α⦄, x ≤ y → y ≤ z → r x y → r y z → r x z)
    (h₄ : ∀ ⦃x y t : α⦄, x ≤ y → r x y → r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t)) : LatticeCon α where
  r := r
  iseqv.refl := h₁.refl
  iseqv.symm h := by simpa [h₂, inf_comm, sup_comm, ← h₂] using h
  iseqv.trans hxy hxz := transitive h₂ h₃ h₄ hxy hxz
  inf := by
    intro w _ _ _ h1 h2
    have compatible_left_inf {x y t : α} (hh : r x y) : r (x ⊓ t) (y ⊓ t) :=
      closed_interval h₂ h₄ ((x ⊓ y) ⊓ t) _ _ ((x ⊔ y) ⊓ t)
            (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ le_sup_left)
            (inf_le_inf_right _ inf_le_right) (inf_le_inf_right _ le_sup_right)
            (h₄ inf_le_sup (h₂.mp hh)).1
    exact transitive h₂ h₃ h₄ (by
          simpa [inf_comm w] using compatible_left_inf h2) (compatible_left_inf h1)
  sup := by
    intro w _ _ _ h1 h2
    have compatible_left_sup {x y t : α} (hh : r x y) : r (x ⊔ t) (y ⊔ t) :=
      closed_interval h₂ h₄ ((x ⊓ y) ⊔ t) _ _ ((x ⊔ y) ⊔ t)
        (sup_le_sup_right inf_le_left _) (sup_le_sup_right le_sup_left _)
        (sup_le_sup_right inf_le_right _) (sup_le_sup_right le_sup_right _)
        (h₄ inf_le_sup (h₂.mp hh)).2
    exact transitive h₂ h₃ h₄ (by
      simpa [sup_comm w] using compatible_left_sup h2)
      (compatible_left_sup h1)

variable [FunLike F α β]

open Function

/-- The kernel of a lattice homomorphism as a lattice congruence. -/
@[simps!]
def ker [Lattice α] [Lattice β] [LatticeHomClass F α β] (f : F) : LatticeCon α where
  toSetoid := Setoid.ker f
  inf _ _ := by simp_all only [Setoid.ker, onFun, map_inf]
  sup _ _ := by simp_all only [Setoid.ker, onFun, map_sup]

end LatticeCon
