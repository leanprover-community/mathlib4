/-
Copyright (c) 2026 Skyler Niedzielski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skyler Niedzielski
-/
module

public import Mathlib.Order.ModularLattice

/-!
# The pentagon and diamond characterisations of modular and distributive lattices

A lattice contains a *pentagon* `N₅` if there are `a < c` and `b` with `a ⊓ b = c ⊓ b` and
`a ⊔ b = c ⊔ b`, and a *diamond* `M₃` if there are three distinct elements with a common pairwise
meet and a common pairwise join. We prove the classical characterisations, stated without naming
these sublattices.

## Main results

* `isModularLattice_iff_eq_of_le_of_inf_eq_of_sup_eq` (Dedekind): a lattice is modular if and only
  if it contains no pentagon.
* `IsModularLattice.inf_sup_le_of_eq_of_inf_eq_of_sup_eq` (Birkhoff): a modular lattice without a
  diamond is distributive.
* `DistribLattice.ofEqOfInfEqSupEq`: a lattice is distributive as soon as `b ⊓ a = c ⊓ a` and
  `b ⊔ a = c ⊔ a` imply `b = c`, i.e. if it contains neither a pentagon nor a diamond. The converse
  is `eq_of_inf_eq_sup_eq`.

## Implementation notes

For `x y z` in a modular lattice, let `d` and `e` be the two sides of the median identity
`(x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x) ≤ (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x)`. Then `x ⊓ d = (x ⊓ y) ⊔ (x ⊓ z)` and
`x ⊓ e = x ⊓ (y ⊔ z)`, so `d = e` gives distributivity, while `(x ⊓ e) ⊔ d`, `(y ⊓ e) ⊔ d` and
`(z ⊓ e) ⊔ d` pairwise meet in `d` and join in `e`, so they form a diamond unless `d = e`.

## References

* [G. Grätzer, *Lattice Theory: Foundation*, Theorems 101 and 102][Gratzer2011]
-/

public section

variable {α : Type*} [Lattice α]

/-- **Dedekind's `N₅` theorem**: a lattice is modular if and only if it contains no pentagon,
namely `a ≤ c` with `a ⊓ b = c ⊓ b` and `a ⊔ b = c ⊔ b` only when `a = c`. -/
theorem isModularLattice_iff_eq_of_le_of_inf_eq_of_sup_eq :
    IsModularLattice α ↔ ∀ ⦃a b c : α⦄, a ≤ c → a ⊓ b = c ⊓ b → a ⊔ b = c ⊔ b → a = c := by
  refine ⟨fun _ a b c hac hi hs ↦ eq_of_le_of_inf_le_of_sup_le hac hi.ge hs.ge, fun h ↦ ⟨?_⟩⟩
  intro x y z hxz
  have hac : x ⊔ y ⊓ z ≤ (x ⊔ y) ⊓ z :=
    sup_le (le_inf le_sup_left hxz) (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  refine (h (b := y) hac ?_ ?_).ge
  · refine le_antisymm (inf_le_inf_right _ hac) (le_inf ?_ inf_le_right)
    exact (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans le_sup_right
  · refine le_antisymm (sup_le_sup_right hac _) (sup_le ?_ le_sup_right)
    exact inf_le_left.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)

namespace IsModularLattice

/-- The lower side of the median identity. -/
private def med (x y z : α) : α := x ⊓ y ⊔ y ⊓ z ⊔ z ⊓ x

/-- The upper side of the median identity. -/
private def dmed (x y z : α) : α := (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x)

private lemma med_rot (x y z : α) : med y z x = med x y z := by
  simp only [med]; ac_rfl

private lemma dmed_rot (x y z : α) : dmed y z x = dmed x y z := by
  simp only [dmed]; ac_rfl

private lemma med_le_dmed (x y z : α) : med x y z ≤ dmed x y z := by
  simp only [med, dmed]
  refine sup_le (sup_le ?_ ?_) ?_ <;> refine le_inf (le_inf ?_ ?_) ?_ <;>
    first
    | exact inf_le_left.trans le_sup_left
    | exact inf_le_left.trans le_sup_right
    | exact inf_le_right.trans le_sup_left

private lemma inf_dmed (x y z : α) : x ⊓ dmed x y z = x ⊓ (y ⊔ z) := by
  simp only [dmed]
  refine le_antisymm (le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right))) ?_
  exact le_inf inf_le_left (le_inf (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
    (inf_le_left.trans le_sup_right))

variable [IsModularLattice α]

private lemma inf_med (x y z : α) : x ⊓ med x y z = x ⊓ y ⊔ x ⊓ z := by
  simp only [med]
  have ha : x ⊓ y ⊔ z ⊓ x ≤ x := sup_le inf_le_left inf_le_right
  have hm : x ⊓ y ⊔ y ⊓ z ⊔ z ⊓ x = (x ⊓ y ⊔ z ⊓ x) ⊔ y ⊓ z := by ac_rfl
  rw [hm, inf_comm, sup_inf_assoc_of_le _ ha, inf_comm z x]
  refine le_antisymm (sup_le le_rfl ?_) le_sup_left
  exact (le_inf inf_le_right (inf_le_left.trans inf_le_left)).trans le_sup_left

private lemma inf_le_med (x y z : α) : (x ⊔ y ⊓ z) ⊓ (y ⊔ z ⊓ x) ≤ med x y z := by
  have m1 : (z ⊓ x ⊔ y) ⊓ x = z ⊓ x ⊔ y ⊓ x := sup_inf_assoc_of_le y inf_le_right
  have m2 : (y ⊓ z ⊔ x) ⊓ (y ⊔ z ⊓ x) = y ⊓ z ⊔ x ⊓ (y ⊔ z ⊓ x) :=
    sup_inf_assoc_of_le x (inf_le_left.trans le_sup_left)
  have m3 : x ⊓ (y ⊔ z ⊓ x) = z ⊓ x ⊔ y ⊓ x := by
    rw [← m1, inf_comm x, sup_comm y]
  rw [sup_comm x, m2, m3]
  simp only [med]
  exact sup_le (le_sup_of_le_left le_sup_right)
    (sup_le le_sup_right (le_sup_of_le_left (le_sup_of_le_left (by rw [inf_comm]))))

private lemma dmed_le_sup (x y z : α) : dmed x y z ≤ x ⊓ (y ⊔ z) ⊔ y ⊓ (z ⊔ x) := by
  have n1 : (y ⊔ x) ⊓ (y ⊔ z) = y ⊔ x ⊓ (y ⊔ z) := sup_inf_assoc_of_le x le_sup_left
  have n2 : (x ⊓ (y ⊔ z) ⊔ y) ⊓ (z ⊔ x) = x ⊓ (y ⊔ z) ⊔ y ⊓ (z ⊔ x) :=
    sup_inf_assoc_of_le y (inf_le_left.trans le_sup_right)
  rw [← n2, sup_comm _ y, ← n1]
  simp only [dmed]
  exact le_inf (le_inf (inf_le_left.trans (inf_le_left.trans (le_of_eq (sup_comm x y))))
    (inf_le_left.trans inf_le_right)) inf_le_right

/-- `(x ⊓ e) ⊔ d` and `(y ⊓ e) ⊔ d` meet in `d` and join in `e`. -/
private lemma inf_eq_med_and_sup_eq_dmed (x y z : α) :
    (x ⊓ dmed x y z ⊔ med x y z) ⊓ (y ⊓ dmed x y z ⊔ med x y z) = med x y z ∧
      (x ⊓ dmed x y z ⊔ med x y z) ⊔ (y ⊓ dmed x y z ⊔ med x y z) = dmed x y z := by
  have hde := med_le_dmed x y z
  constructor
  · refine le_antisymm (le_trans (inf_le_inf ?_ ?_) (inf_le_med x y z))
      (le_inf le_sup_right le_sup_right)
    · refine sup_le (inf_le_left.trans le_sup_left) ?_
      simp only [med]
      exact sup_le (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
        (inf_le_right.trans le_sup_left)
    · refine sup_le (inf_le_left.trans le_sup_left) ?_
      simp only [med]
      exact sup_le (sup_le (inf_le_right.trans le_sup_left) (inf_le_left.trans le_sup_left))
        le_sup_right
  · refine le_antisymm (sup_le (sup_le inf_le_right hde) (sup_le inf_le_right hde)) ?_
    refine (dmed_le_sup x y z).trans (sup_le_sup ?_ ?_)
    · rw [← inf_dmed]; exact le_sup_left
    · have : y ⊓ dmed x y z = y ⊓ (z ⊔ x) := by rw [← dmed_rot, inf_dmed]
      rw [← this]; exact le_sup_left

/-- **Birkhoff's `M₃` theorem**: a modular lattice which contains no diamond is distributive.

Here "no diamond" is stated as: three elements with a common pairwise meet and a common pairwise
join cannot have two distinct among them. -/
theorem inf_sup_le_of_eq_of_inf_eq_of_sup_eq
    (h : ∀ ⦃x y z : α⦄, x ⊓ y = y ⊓ z → y ⊓ z = z ⊓ x → x ⊔ y = y ⊔ z → y ⊔ z = z ⊔ x → x = y)
    (a b c : α) : a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c := by
  suffices hm : med a b c = dmed a b c by rw [← inf_dmed, ← hm, inf_med]
  obtain ⟨i1, s1⟩ := inf_eq_med_and_sup_eq_dmed a b c
  obtain ⟨i2, s2⟩ := inf_eq_med_and_sup_eq_dmed b c a
  obtain ⟨i3, s3⟩ := inf_eq_med_and_sup_eq_dmed c a b
  rw [dmed_rot, med_rot] at i2 s2
  rw [← dmed_rot, ← med_rot] at i3 s3
  have := h (i1.trans i2.symm) (i2.trans i3.symm) (s1.trans s2.symm) (s2.trans s3.symm)
  rw [← this, inf_idem] at i1
  rw [← this, sup_idem] at s1
  exact i1.symm.trans s1

end IsModularLattice

/-- **Birkhoff's `M₃`-`N₅` theorem**, in cancellative form: a lattice in which `b ⊓ a = c ⊓ a` and
`b ⊔ a = c ⊔ a` imply `b = c` is distributive. The converse is `eq_of_inf_eq_sup_eq`. -/
theorem inf_sup_le_of_eq_of_inf_eq_sup_eq
    (h : ∀ ⦃a b c : α⦄, b ⊓ a = c ⊓ a → b ⊔ a = c ⊔ a → b = c) (a b c : α) :
    a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c :=
  have := isModularLattice_iff_eq_of_le_of_inf_eq_of_sup_eq (α := α) |>.2
    fun _ _ _ _ hi hs ↦ h hi hs
  IsModularLattice.inf_sup_le_of_eq_of_inf_eq_of_sup_eq
    (fun x _ z _ hi _ hs ↦ h ((inf_comm x z).trans hi.symm) ((sup_comm x z).trans hs.symm)) a b c

-- See note [reducible non-instances]
/-- Prove distributivity of an existing lattice from cancellation: if `b ⊓ a = c ⊓ a` and
`b ⊔ a = c ⊔ a` imply `b = c`, then the lattice is distributive. -/
abbrev DistribLattice.ofEqOfInfEqSupEq
    (h : ∀ ⦃a b c : α⦄, b ⊓ a = c ⊓ a → b ⊔ a = c ⊔ a → b = c) : DistribLattice α :=
  .ofInfSupLe <| inf_sup_le_of_eq_of_inf_eq_sup_eq h

end
