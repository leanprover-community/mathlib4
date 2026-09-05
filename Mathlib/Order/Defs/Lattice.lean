/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation

import Mathlib.Tactic.GRewrite

/-!
# (Semi-)lattices

Semilattices are partially ordered sets with join (least upper bound, or `⊔`) or meet (greatest
lower bound, or `⊓`) operations. Lattices are posets that are both join-semilattices and
meet-semilattices.

Distributive lattices are lattices which satisfy any of four equivalent distributivity properties,
of `⊔` over `⊓`, on the left or on the right.

## Main declarations

* `SemilatticeSup`: a type class for join semilattices
* `SemilatticeInf`: a type class for meet semilattices
* `Lattice`: a type class for lattices
* `DistribLattice`: a type class for distributive lattices.

## Notation

* `a ⊔ b`: the supremum or join of `a` and `b`
* `a ⊓ b`: the infimum or meet of `a` and `b`

## Implementation notes

The join operation of `SemilatticeSup` is represented by `max`, so that it uses the same constant
for its operation as `LinearOrder`. Analogously, the meet operation of `SemilatticeInf` is
represented by `min`. Lemmas about them should use the names `sup` and `inf`, except in the case of
linear orders.

## Tags

semilattice, lattice

-/

@[expose] public section

assert_not_exists LinearOrder

universe u v

variable {α : Type u} {β : Type v}

/-!
### Semilattices
-/

/-- A `SemilatticeSup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors. -/
class SemilatticeSup (α : Type u) extends Max α, PartialOrder α where
  /-- The supremum is an upper bound on the first argument -/
  protected le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  /-- The supremum is an upper bound on the second argument -/
  protected le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  /-- The supremum is the *least* upper bound -/
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c

/-- A `SemilatticeInf` is a meet-semilattice, that is, a partial order
  with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
  `⊓` which is the greatest element smaller than both factors. -/
@[to_dual]
class SemilatticeInf (α : Type u) extends Min α, PartialOrder α where
  /-- The infimum is a lower bound on the first argument -/
  protected inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  /-- The infimum is a lower bound on the second argument -/
  protected inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  /-- The infimum is the *greatest* lower bound -/
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c

attribute [to_dual existing] SemilatticeSup.casesOn

@[to_dual (attr := deprecated (since := "2026-xx-xx"))]
alias SemilatticeSup.sup := Max.max

section SemilatticeSup

variable [SemilatticeSup α] {a b c d : α}

@[to_dual (attr := simp) inf_le_left]
theorem le_sup_left : a ≤ a ⊔ b :=
  SemilatticeSup.le_sup_left a b

@[to_dual (attr := simp) inf_le_right]
theorem le_sup_right : b ≤ a ⊔ b :=
  SemilatticeSup.le_sup_right a b

@[to_dual (reorder := a b c) le_inf]
theorem sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
  SemilatticeSup.sup_le a b c

@[to_dual inf_le_of_left_le]
theorem le_sup_of_le_left (h : c ≤ a) : c ≤ a ⊔ b :=
  le_trans h le_sup_left

@[to_dual inf_le_of_right_le]
theorem le_sup_of_le_right (h : c ≤ b) : c ≤ a ⊔ b :=
  le_trans h le_sup_right

@[to_dual inf_lt_of_left_lt]
theorem lt_sup_of_lt_left (h : c < a) : c < a ⊔ b :=
  lt_of_lt_of_le h le_sup_left

@[to_dual inf_lt_of_right_lt]
theorem lt_sup_of_lt_right (h : c < b) : c < a ⊔ b :=
  lt_of_lt_of_le h le_sup_right

@[to_dual (attr := simp) (reorder := a b c) le_inf_iff]
theorem sup_le_iff : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h : a ⊔ b ≤ c => ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩,
   fun ⟨h₁, h₂⟩ => sup_le h₁ h₂⟩

@[to_dual (attr := simp)]
theorem sup_eq_left : a ⊔ b = a ↔ b ≤ a :=
  le_antisymm_iff.trans <| by simp

@[to_dual (attr := simp)]
theorem sup_eq_right : a ⊔ b = b ↔ a ≤ b :=
  le_antisymm_iff.trans <| by simp

@[to_dual (attr := simp)]
theorem left_eq_sup : a = a ⊔ b ↔ b ≤ a :=
  eq_comm.trans sup_eq_left

@[to_dual (attr := simp)]
theorem right_eq_sup : b = a ⊔ b ↔ a ≤ b :=
  eq_comm.trans sup_eq_right

alias ⟨le_of_sup_eq', sup_of_le_left⟩ := sup_eq_left

alias ⟨le_of_sup_eq, sup_of_le_right⟩ := sup_eq_right

attribute [to_dual (attr := simp)] sup_of_le_left sup_of_le_right
attribute [to_dual le_of_inf_eq'] le_of_sup_eq
attribute [to_dual le_of_inf_eq] le_of_sup_eq'

@[to_dual (attr := gcongr)]
theorem sup_le_sup (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
  sup_le (le_sup_of_le_left h₁) (le_sup_of_le_right h₂)

-- FIXME: these theorems use the wrong `left`/`right` naming convention.
-- FIXME: the fact that the following theorems use `(reorder := h₁ c)` is not good.
-- Instead, we should use a consistent argument ordering.
@[to_dual (reorder := h₁ c)]
theorem sup_le_sup_left (h₁ : a ≤ b) (c) : c ⊔ a ≤ c ⊔ b :=
  sup_le_sup le_rfl h₁

@[to_dual (reorder := h₁ c)]
theorem sup_le_sup_right (h₁ : a ≤ b) (c) : a ⊔ c ≤ b ⊔ c :=
  sup_le_sup h₁ le_rfl

@[to_dual]
theorem sup_idem (a : α) : a ⊔ a = a := by simp

@[to_dual]
instance : Std.IdempotentOp (α := α) (· ⊔ ·) := ⟨sup_idem⟩

@[to_dual]
theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by apply le_antisymm <;> simp

@[to_dual]
instance : Std.Commutative (α := α) (· ⊔ ·) := ⟨sup_comm⟩

@[to_dual]
theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
  eq_of_forall_ge_iff fun x => by simp only [sup_le_iff]; rw [and_assoc]

@[to_dual]
instance : Std.Associative (α := α) (· ⊔ ·) := ⟨sup_assoc⟩

@[to_dual]
theorem sup_left_right_swap (a b c : α) : a ⊔ b ⊔ c = c ⊔ b ⊔ a := by
  rw [sup_comm, sup_comm a, sup_assoc]

@[to_dual]
theorem sup_left_idem (a b : α) : a ⊔ (a ⊔ b) = a ⊔ b := by simp

@[to_dual]
theorem sup_right_idem (a b : α) : a ⊔ b ⊔ b = a ⊔ b := by simp

@[to_dual]
theorem sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) := by
  rw [← sup_assoc, ← sup_assoc, @sup_comm α _ a]

@[to_dual]
theorem sup_right_comm (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ b := by
  rw [sup_assoc, sup_assoc, sup_comm b]

@[to_dual]
theorem sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔ c ⊔ (b ⊔ d) := by
  rw [sup_assoc, sup_left_comm b, ← sup_assoc]

@[to_dual]
theorem sup_rotate (a b c : α) : a ⊔ b ⊔ c = b ⊔ c ⊔ a := by
  rw [sup_assoc, sup_comm]

@[to_dual]
theorem sup_rotate' (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (c ⊔ a) := by
  rw [sup_comm, sup_assoc]

@[to_dual]
theorem sup_sup_distrib_left (a b c : α) : a ⊔ (b ⊔ c) = a ⊔ b ⊔ (a ⊔ c) := by
  rw [sup_sup_sup_comm, sup_idem]

@[to_dual]
theorem sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ (b ⊔ c) := by
  rw [sup_sup_sup_comm, sup_idem]

end SemilatticeSup

/-!
### Lattices
-/


/-- A lattice is a join-semilattice which is also a meet-semilattice. -/
class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α

attribute [to_dual existing] Lattice.toSemilatticeInf

/-- Auxiliary constructor for `to_dual`. -/
@[to_dual existing mk, instance_reducible]
def Lattice.mkDual {α : Type*} [SemilatticeInf α] [Max α]
    (le_sup_left : ∀ a b : α, a ≤ a ⊔ b) (le_sup_right : ∀ a b : α, b ≤ a ⊔ b)
    (sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c) : Lattice α where
  le_sup_left
  le_sup_right
  sup_le

section Lattice

variable [Lattice α] {a b c : α}

theorem inf_le_sup : a ⊓ b ≤ a ⊔ b :=
  le_trans inf_le_left le_sup_left

theorem sup_le_inf : a ⊔ b ≤ a ⊓ b ↔ a = b := by simp [le_antisymm_iff, and_comm]

@[to_dual (attr := simp) inf_right_le_sup_left]
lemma inf_left_le_sup_right : (a ⊓ b) ≤ (b ⊔ c) := le_trans inf_le_right le_sup_left

@[simp, to_dual self]
lemma inf_right_le_sup_right : (b ⊓ a) ≤ (b ⊔ c) := le_trans inf_le_left le_sup_left

@[simp, to_dual self]
lemma inf_left_le_sup_left : (a ⊓ b) ≤ (c ⊔ b) := le_trans inf_le_right le_sup_right

/-!
#### Distributivity laws
-/


-- TODO: better names?
@[to_dual le_inf_sup]
theorem sup_inf_le : a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
  le_inf (sup_le_sup_left inf_le_left _) (sup_le_sup_left inf_le_right _)

@[to_dual]
theorem inf_sup_self : a ⊓ (a ⊔ b) = a := by simp

@[to_dual]
theorem sup_eq_iff_inf_eq : a ⊔ b = b ↔ a ⊓ b = a := by rw [sup_eq_right, ← inf_eq_left]

end Lattice

/-!
### Distributive lattices
-/


/-- A distributive lattice is a lattice that satisfies any of four
equivalent distributive properties (of `sup` over `inf` or `inf` over `sup`,
on the left or right).

The definition here chooses `le_sup_inf`: `(x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z)`. To prove distributivity
from the dual law, use `DistribLattice.ofInfSupLe`.

A classic example of a distributive lattice
is the lattice of subsets of a set, and in fact this example is
generic in the sense that every distributive lattice is realizable
as a sublattice of a powerset lattice. -/
class DistribLattice (α) extends Lattice α where
  /-- The infimum distributes over the supremum -/
  protected le_sup_inf : ∀ x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z

-- See note [reducible non-instances]
/-- Prove distributivity of an existing lattice from the dual distributive law. -/
@[to_dual existing mk]
abbrev DistribLattice.ofInfSupLe
    [Lattice α] (inf_sup_le : ∀ a b c : α, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c) : DistribLattice α where
  le_sup_inf x y z := by
    grw [inf_sup_le]
    apply sup_le
    · grw [inf_le_right, ← le_sup_left]
    · grw [inf_comm, inf_sup_le, inf_comm z y, inf_le_right]

section DistribLattice

variable [DistribLattice α] {x y z : α}

theorem le_sup_inf {x y z : α} : (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z :=
  DistribLattice.le_sup_inf x y z

theorem sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) :=
  le_antisymm sup_inf_le le_sup_inf

theorem sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) := by
  simp only [sup_inf_left, sup_comm _ c]

@[to_dual existing]
theorem inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c :=
  calc
    a ⊓ (b ⊔ c) = a ⊓ (a ⊔ c) ⊓ (b ⊔ c) := by rw [inf_sup_self]
    _ = a ⊓ (a ⊓ b ⊔ c) := by simp only [inf_assoc, sup_inf_right]
    _ = (a ⊔ a ⊓ b) ⊓ (a ⊓ b ⊔ c) := by rw [sup_inf_self]
    _ = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm]
    _ = a ⊓ b ⊔ a ⊓ c := by rw [sup_inf_left]

@[to_dual existing le_sup_inf]
theorem inf_sup_le {x y z : α} : x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z) := by
  rw [inf_sup_left]

@[to_dual existing]
theorem inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c := by
  simp only [inf_sup_left, inf_comm _ c]

@[to_dual self (reorder := x y, h₁ h₂)]
theorem le_of_inf_le_sup_le (h₁ : x ⊓ z ≤ y ⊓ z) (h₂ : x ⊔ z ≤ y ⊔ z) : x ≤ y :=
  calc
    x ≤ y ⊓ z ⊔ x := le_sup_right
    _ = (y ⊔ x) ⊓ (x ⊔ z) := by rw [sup_inf_right, sup_comm x]
    _ ≤ (y ⊔ x) ⊓ (y ⊔ z) := inf_le_inf_left _ h₂
    _ = y ⊔ x ⊓ z := by rw [← sup_inf_left]
    _ ≤ y ⊔ y ⊓ z := sup_le_sup_left h₁ _
    _ ≤ _ := sup_le (le_refl y) inf_le_left

@[to_dual self (reorder := h₁ h₂)]
theorem eq_of_inf_eq_sup_eq {a b c : α} (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) : b = c :=
  le_antisymm (le_of_inf_le_sup_le (le_of_eq h₁) (le_of_eq h₂))
    (le_of_inf_le_sup_le (le_of_eq h₁.symm) (le_of_eq h₂.symm))

end DistribLattice
