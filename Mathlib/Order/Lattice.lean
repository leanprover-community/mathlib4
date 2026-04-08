/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Bool.Basic
public import Mathlib.Logic.Pairwise
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.ULift

/-!
# (Semi-)lattices

Semilattices are partially ordered sets with join (least upper bound, or `sup`) or meet (greatest
lower bound, or `inf`) operations. Lattices are posets that are both join-semilattices and
meet-semilattices.

Distributive lattices are lattices which satisfy any of four equivalent distributivity properties,
of `sup` over `inf`, on the left or on the right.

## Main declarations

* `SemilatticeSup`: a type class for join semilattices
* `SemilatticeSup.mk'`: an alternative constructor for `SemilatticeSup` via proofs that `⊔` is
  commutative, associative and idempotent.
* `SemilatticeInf`: a type class for meet semilattices
* `SemilatticeSup.mk'`: an alternative constructor for `SemilatticeInf` via proofs that `⊓` is
  commutative, associative and idempotent.

* `Lattice`: a type class for lattices
* `Lattice.mk'`: an alternative constructor for `Lattice` via proofs that `⊔` and `⊓` are
  commutative, associative and satisfy a pair of "absorption laws".

* `DistribLattice`: a type class for distributive lattices.

## Notation

* `a ⊔ b`: the supremum or join of `a` and `b`
* `a ⊓ b`: the infimum or meet of `a` and `b`

## TODO

* (Semi-)lattice homomorphisms
* Alternative constructors for distributive lattices from the other distributive properties

## Tags

semilattice, lattice

-/

@[expose] public section

universe u v w

variable {α : Type u} {β : Type v}

/-!
### Join-semilattices
-/

/-- A `SemilatticeSup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors. -/
class SemilatticeSup (α : Type u) extends PartialOrder α where
  /-- The binary supremum, used to derive `Max α` -/
  sup : α → α → α
  /-- The supremum is an upper bound on the first argument -/
  protected le_sup_left : ∀ a b : α, a ≤ sup a b
  /-- The supremum is an upper bound on the second argument -/
  protected le_sup_right : ∀ a b : α, b ≤ sup a b
  /-- The supremum is the *least* upper bound -/
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → sup a b ≤ c

/-- A `SemilatticeInf` is a meet-semilattice, that is, a partial order
  with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
  `⊓` which is the greatest element smaller than both factors. -/
@[to_dual]
class SemilatticeInf (α : Type u) extends PartialOrder α where
  /-- The binary infimum, used to derive `Min α` -/
  inf : α → α → α
  /-- The infimum is a lower bound on the first argument -/
  protected inf_le_left : ∀ a b : α, inf a b ≤ a
  /-- The infimum is a lower bound on the second argument -/
  protected inf_le_right : ∀ a b : α, inf a b ≤ b
  /-- The infimum is the *greatest* lower bound -/
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ inf b c

attribute [to_dual existing] SemilatticeSup.sup_le SemilatticeSup.mk SemilatticeSup.casesOn

@[to_dual]
instance SemilatticeSup.toMax [SemilatticeSup α] : Max α where max a b := SemilatticeSup.sup a b

-- Note: it is not possible for `to_dual` to translate `le a b := a ⊔ b = b` consistently.
/--
A type with a commutative, associative and idempotent binary `sup` operation has the structure of a
join-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
@[implicit_reducible]
def SemilatticeSup.mk' {α : Type*} [Max α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (sup_idem : ∀ a : α, a ⊔ a = a) :
    SemilatticeSup α where
  sup := (· ⊔ ·)
  le a b := a ⊔ b = b
  le_refl := sup_idem
  le_trans a b c hab hbc := by rw [← hbc, ← sup_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, sup_comm]
  le_sup_left a b := by rw [← sup_assoc, sup_idem]
  le_sup_right a b := by rw [sup_comm, sup_assoc, sup_idem]
  sup_le a b c hac hbc := by rwa [sup_assoc, hbc]

/--
A type with a commutative, associative and idempotent binary `inf` operation has the structure of a
meet-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `b ⊓ a = a`; cf. `inf_eq_right`.
-/
@[implicit_reducible]
def SemilatticeInf.mk' {α : Type*} [Min α] (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : ∀ a : α, a ⊓ a = a) :
    SemilatticeInf α where
  inf := (· ⊓ ·)
  le b a := a ⊓ b = b
  le_refl := inf_idem
  le_trans c b a hbc hab := by rw [← hbc, ← inf_assoc, hab]
  le_antisymm a b hba hab := by rwa [← hba, inf_comm]
  inf_le_left a b := by rw [← inf_assoc, inf_idem]
  inf_le_right a b := by rw [inf_comm, inf_assoc, inf_idem]
  le_inf a b c hac hbc := by rwa [inf_assoc, hbc]

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
  h.trans_le le_sup_left

@[to_dual inf_lt_of_right_lt]
theorem lt_sup_of_lt_right (h : c < b) : c < a ⊔ b :=
  h.trans_le le_sup_right

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

@[to_dual (attr := simp) inf_lt_left]
theorem left_lt_sup : a < a ⊔ b ↔ ¬b ≤ a :=
  le_sup_left.lt_iff_ne.trans <| not_congr left_eq_sup

@[to_dual (attr := simp) inf_lt_right]
theorem right_lt_sup : b < a ⊔ b ↔ ¬a ≤ b :=
  le_sup_right.lt_iff_ne.trans <| not_congr right_eq_sup

@[to_dual inf_lt_left_or_right]
theorem left_or_right_lt_sup (h : a ≠ b) : a < a ⊔ b ∨ b < a ⊔ b :=
  h.not_le_or_not_ge.symm.imp left_lt_sup.2 right_lt_sup.2

@[to_dual]
theorem le_iff_exists_sup : a ≤ b ↔ ∃ c, b = a ⊔ c := by
  constructor
  · intro h
    exact ⟨b, (sup_eq_right.mpr h).symm⟩
  · rintro ⟨c, rfl : _ = _ ⊔ _⟩
    exact le_sup_left

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
theorem sup_sup_distrib_left (a b c : α) : a ⊔ (b ⊔ c) = a ⊔ b ⊔ (a ⊔ c) := by
  rw [sup_sup_sup_comm, sup_idem]

@[to_dual]
theorem sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ (b ⊔ c) := by
  rw [sup_sup_sup_comm, sup_idem]

-- FIXME: These theorems use the wrong `left`/`right` naming convention.
@[to_dual]
theorem sup_congr_left (hb : b ≤ a ⊔ c) (hc : c ≤ a ⊔ b) : a ⊔ b = a ⊔ c :=
  (sup_le le_sup_left hb).antisymm <| sup_le le_sup_left hc

@[to_dual]
theorem sup_congr_right (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ⊔ c = b ⊔ c :=
  (sup_le ha le_sup_right).antisymm <| sup_le hb le_sup_right

@[to_dual]
theorem sup_eq_sup_iff_left : a ⊔ b = a ⊔ c ↔ b ≤ a ⊔ c ∧ c ≤ a ⊔ b :=
  ⟨fun h => ⟨h ▸ le_sup_right, h.symm ▸ le_sup_right⟩, fun h => sup_congr_left h.1 h.2⟩

@[to_dual]
theorem sup_eq_sup_iff_right : a ⊔ c = b ⊔ c ↔ a ≤ b ⊔ c ∧ b ≤ a ⊔ c :=
  ⟨fun h => ⟨h ▸ le_sup_left, h.symm ▸ le_sup_left⟩, fun h => sup_congr_right h.1 h.2⟩

@[to_dual inf_lt_or_inf_lt]
theorem Ne.lt_sup_or_lt_sup (hab : a ≠ b) : a < a ⊔ b ∨ b < a ⊔ b :=
  hab.symm.not_le_or_not_ge.imp left_lt_sup.2 right_lt_sup.2

@[to_dual inf_le_ite]
theorem ite_le_sup (a b : α) (P : Prop) [Decidable P] : ite P a b ≤ a ⊔ b :=
  if h : P then (if_pos h).trans_le le_sup_left else (if_neg h).trans_le le_sup_right

@[to_dual (reorder := H (x y))]
theorem SemilatticeSup.ext_sup {α} {A B : SemilatticeSup α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y)
    (x y : α) :
    (haveI := A; x ⊔ y) = x ⊔ y :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff]; rw [← H, @sup_le_iff α A, H, H]

@[to_dual (reorder := H (x y))]
theorem SemilatticeSup.ext {α} {A B : SemilatticeSup α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by
  cases A
  cases B
  cases PartialOrder.ext H
  congr
  ext; apply SemilatticeSup.ext_sup H

@[to_dual]
instance OrderDual.instSemilatticeSup (α) [h : SemilatticeInf α] : SemilatticeSup αᵒᵈ where
  sup a b := h.inf a b
  le_sup_left := h.inf_le_left
  le_sup_right := h.inf_le_right
  sup_le _ _ _ := h.le_inf _ _ _

@[to_dual]
theorem SemilatticeSup.dual_dual (α : Type*) [H : SemilatticeSup α] :
    OrderDual.instSemilatticeSup αᵒᵈ = H :=
  SemilatticeSup.ext fun _ _ => Iff.rfl

end SemilatticeSup

/-!
### Lattices
-/


/-- A lattice is a join-semilattice which is also a meet-semilattice. -/
class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α

attribute [to_dual existing] Lattice.toSemilatticeInf

instance OrderDual.instLattice (α) [Lattice α] : Lattice αᵒᵈ where

/-- The partial orders from `SemilatticeSup_mk'` and `SemilatticeInf_mk'` agree
if `sup` and `inf` satisfy the lattice absorption laws `sup_inf_self` (`a ⊔ a ⊓ b = a`)
and `inf_sup_self` (`a ⊓ (a ⊔ b) = a`). -/
theorem semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder
    {α : Type*} [Max α] [Min α]
    (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a) (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c))
    (sup_idem : ∀ a : α, a ⊔ a = a) (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : ∀ a : α, a ⊓ a = a)
    (sup_inf_self : ∀ a b : α, a ⊔ a ⊓ b = a) (inf_sup_self : ∀ a b : α, a ⊓ (a ⊔ b) = a) :
    @SemilatticeSup.toPartialOrder _ (SemilatticeSup.mk' sup_comm sup_assoc sup_idem) =
      @SemilatticeInf.toPartialOrder _ (SemilatticeInf.mk' inf_comm inf_assoc inf_idem) :=
  PartialOrder.ext fun a b =>
    show a ⊔ b = b ↔ b ⊓ a = a from
      ⟨fun h => by rw [← h, inf_comm, inf_sup_self], fun h => by rw [← h, sup_comm, sup_inf_self]⟩

/-- A type with a pair of commutative and associative binary operations which satisfy two absorption
laws relating the two operations has the structure of a lattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
@[implicit_reducible]
def Lattice.mk' {α : Type*} [Max α] [Min α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (sup_inf_self : ∀ a b : α, a ⊔ a ⊓ b = a)
    (inf_sup_self : ∀ a b : α, a ⊓ (a ⊔ b) = a) : Lattice α :=
  have sup_idem : ∀ b : α, b ⊔ b = b := fun b =>
    calc
      b ⊔ b = b ⊔ b ⊓ (b ⊔ b) := by rw [inf_sup_self]
      _ = b := by rw [sup_inf_self]
  have inf_idem : ∀ b : α, b ⊓ b = b := fun b =>
    calc
      b ⊓ b = b ⊓ (b ⊔ b ⊓ b) := by rw [sup_inf_self]
      _ = b := by rw [inf_sup_self]
  let semilatt_inf_inst := SemilatticeInf.mk' inf_comm inf_assoc inf_idem
  let semilatt_sup_inst := SemilatticeSup.mk' sup_comm sup_assoc sup_idem
  have partial_order_eq : @SemilatticeSup.toPartialOrder _ semilatt_sup_inst =
                          @SemilatticeInf.toPartialOrder _ semilatt_inf_inst :=
    semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder _ _ _ _ _ _
      sup_inf_self inf_sup_self
  { semilatt_sup_inst, semilatt_inf_inst with
    inf_le_left := fun a b => by
      rw [partial_order_eq]
      apply inf_le_left,
    inf_le_right := fun a b => by
      rw [partial_order_eq]
      apply inf_le_right,
    le_inf := fun a b c => by
      rw [partial_order_eq]
      apply le_inf }

section Lattice

variable [Lattice α] {a b c : α}

theorem inf_le_sup : a ⊓ b ≤ a ⊔ b :=
  inf_le_left.trans le_sup_left

theorem sup_le_inf : a ⊔ b ≤ a ⊓ b ↔ a = b := by simp [le_antisymm_iff, and_comm]

@[to_dual (attr := simp)]
lemma inf_eq_sup : a ⊓ b = a ⊔ b ↔ a = b := by rw [← inf_le_sup.ge_iff_eq, sup_le_inf]

@[simp] lemma inf_lt_sup : a ⊓ b < a ⊔ b ↔ a ≠ b := by rw [inf_le_sup.lt_iff_ne, Ne, inf_eq_sup]

@[to_dual (attr := simp) inf_right_le_sup_left]
lemma inf_left_le_sup_right : (a ⊓ b) ≤ (b ⊔ c) := le_trans inf_le_right le_sup_left

@[simp, to_dual self]
lemma inf_right_le_sup_right : (b ⊓ a) ≤ (b ⊔ c) := le_trans inf_le_left le_sup_left

@[simp, to_dual self]
lemma inf_left_le_sup_left : (a ⊓ b) ≤ (c ⊔ b) := le_trans inf_le_right le_sup_right

@[to_dual]
lemma inf_eq_and_sup_eq_iff : a ⊓ b = c ∧ a ⊔ b = c ↔ a = c ∧ b = c := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain rfl := sup_eq_inf.1 (h.2.trans h.1.symm)
    simpa using h
  · rintro ⟨rfl, rfl⟩
    exact ⟨inf_idem _, sup_idem _⟩

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

@[to_dual self]
theorem Lattice.ext {α} {A B : Lattice α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by
  cases A
  cases B
  cases SemilatticeSup.ext H
  cases SemilatticeInf.ext H
  congr

end Lattice

/-!
### Distributive lattices
-/


/-- A distributive lattice is a lattice that satisfies any of four
equivalent distributive properties (of `sup` over `inf` or `inf` over `sup`,
on the left or right).

The definition here chooses `le_sup_inf`: `(x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z)`. To prove distributivity
from the dual law, use `DistribLattice.of_inf_sup_le`.

A classic example of a distributive lattice
is the lattice of subsets of a set, and in fact this example is
generic in the sense that every distributive lattice is realizable
as a sublattice of a powerset lattice. -/
class DistribLattice (α) extends Lattice α where
  /-- The infimum distributes over the supremum -/
  protected le_sup_inf : ∀ x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z

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

instance OrderDual.instDistribLattice (α : Type*) [DistribLattice α] : DistribLattice αᵒᵈ where
  le_sup_inf _ _ _ := inf_sup_le

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

-- See note [reducible non-instances]
/-- Prove distributivity of an existing lattice from the dual distributive law. -/
@[to_dual existing mk]
abbrev DistribLattice.ofInfSupLe
    [Lattice α] (inf_sup_le : ∀ a b c : α, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c) : DistribLattice α where
  le_sup_inf := (@OrderDual.instDistribLattice αᵒᵈ { (inferInstance : Lattice αᵒᵈ) with
      le_sup_inf := inf_sup_le }).le_sup_inf

/-!
### Lattices derived from linear orders
-/

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.toLattice {α : Type u} [LinearOrder α] : Lattice α where
  sup := max
  inf := min
  le_sup_left := le_max_left; le_sup_right := le_max_right; sup_le _ _ _ := max_le
  inf_le_left := min_le_left; inf_le_right := min_le_right; le_inf _ _ _ := le_min

section LinearOrder

variable [LinearOrder α] {a b c d : α}

@[to_dual]
theorem sup_ind (a b : α) {p : α → Prop} (ha : p a) (hb : p b) : p (a ⊔ b) :=
  (Std.Total.total a b).elim (fun h : a ≤ b => by rwa [sup_eq_right.2 h]) fun h => by
  rwa [sup_eq_left.2 h]

@[to_dual (attr := simp) inf_le_iff]
theorem le_sup_iff : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c := by
  grind

@[to_dual (attr := simp) inf_lt_iff]
theorem lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c := by
  grind

@[to_dual (attr := simp) lt_inf_iff]
theorem sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a :=
  ⟨fun h => ⟨le_sup_left.trans_lt h, le_sup_right.trans_lt h⟩,
   fun h => sup_ind (p := (· < a)) b c h.1 h.2⟩

variable (a b c d)

@[to_dual]
theorem max_max_max_comm : max (max a b) (max c d) = max (max a c) (max b d) :=
  sup_sup_sup_comm _ _ _ _

end LinearOrder

theorem sup_eq_maxDefault [SemilatticeSup α] [DecidableLE α] [@Std.Total α (· ≤ ·)] :
    (· ⊔ ·) = (maxDefault : α → α → α) := by
  ext x y
  unfold maxDefault
  split_ifs with h'
  exacts [sup_of_le_right h', sup_of_le_left <| (total_of (· ≤ ·) x y).resolve_left h']

theorem inf_eq_minDefault [SemilatticeInf α] [DecidableLE α] [@Std.Total α (· ≤ ·)] :
    (· ⊓ ·) = (minDefault : α → α → α) := by
  ext x y
  unfold minDefault
  split_ifs with h'
  exacts [inf_of_le_left h', inf_of_le_right <| (total_of (· ≤ ·) x y).resolve_left h']

/-- A lattice with total order is a linear order.

See note [reducible non-instances]. -/
abbrev Lattice.toLinearOrder (α : Type u) [Lattice α] [DecidableEq α]
    [DecidableLE α] [DecidableLT α] [@Std.Total α (· ≤ ·)] : LinearOrder α where
  toDecidableLE := ‹_›
  toDecidableEq := ‹_›
  toDecidableLT := ‹_›
  le_total := total_of (· ≤ ·)
  max_def := by exact congr_fun₂ sup_eq_maxDefault
  min_def := by exact congr_fun₂ inf_eq_minDefault

-- see Note [lower instance priority]
instance (priority := 100) {α : Type u} [LinearOrder α] : DistribLattice α where
  le_sup_inf _ b c :=
    match le_total b c with
    | Or.inl h => inf_le_of_left_le <| sup_le_sup_left (le_inf (le_refl b) h) _
    | Or.inr h => inf_le_of_right_le <| sup_le_sup_left (le_inf h (le_refl c)) _

instance : DistribLattice ℕ := inferInstance
instance : Lattice ℤ := inferInstance

/-! ### Dual order -/


open OrderDual

@[to_dual (attr := simp)]
theorem ofDual_sup [Min α] (a b : αᵒᵈ) : ofDual (a ⊔ b) = ofDual a ⊓ ofDual b :=
  rfl

@[to_dual (attr := simp)]
theorem toDual_sup [Max α] (a b : α) : toDual (a ⊔ b) = toDual a ⊓ toDual b :=
  rfl

section LinearOrder

variable [LinearOrder α]

@[to_dual] theorem ofDual_max (a b : αᵒᵈ) : ofDual (max a b) = min (ofDual a) (ofDual b) :=
  rfl

@[to_dual] theorem toDual_max (a b : α) : toDual (max a b) = min (toDual a) (toDual b) :=
  rfl

end LinearOrder

/-! ### Function lattices -/


namespace Pi

variable {ι : Type*} {α' : ι → Type*}

@[to_dual]
instance [∀ i, Max (α' i)] : Max (∀ i, α' i) :=
  ⟨fun f g i => f i ⊔ g i⟩

@[to_dual (attr := simp)]
theorem sup_apply [∀ i, Max (α' i)] (f g : ∀ i, α' i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
  rfl

@[to_dual (attr := push ←)]
theorem sup_def [∀ i, Max (α' i)] (f g : ∀ i, α' i) : f ⊔ g = fun i => f i ⊔ g i :=
  rfl

@[to_dual]
instance instSemilatticeSup [∀ i, SemilatticeSup (α' i)] : SemilatticeSup (∀ i, α' i) where
  sup x y i := x i ⊔ y i
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ ac bc i := sup_le (ac i) (bc i)

instance instLattice [∀ i, Lattice (α' i)] : Lattice (∀ i, α' i) where

instance instDistribLattice [∀ i, DistribLattice (α' i)] : DistribLattice (∀ i, α' i) where
  le_sup_inf _ _ _ _ := le_sup_inf

end Pi

namespace Function

variable {ι : Type*} {π : ι → Type*} [DecidableEq ι]

-- Porting note: Dot notation on `Function.update` broke
@[to_dual]
theorem update_sup [∀ i, SemilatticeSup (π i)] (f : ∀ i, π i) (i : ι) (a b : π i) :
    update f i (a ⊔ b) = update f i a ⊔ update f i b :=
  funext fun j => by obtain rfl | hji := eq_or_ne j i <;> simp [update_of_ne, *]

end Function

/-!
### Monotone functions and lattices
-/


namespace Monotone

/-- Pointwise supremum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise infimum of two monotone functions is a monotone function. -/]
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} (hf : Monotone f)
    (hg : Monotone g) :
    Monotone (f ⊔ g) := fun _ _ h => sup_le_sup (hf h) (hg h)

/-- Pointwise maximum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise minimum of two monotone functions is a monotone function. -/]
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} (hf : Monotone f)
    (hg : Monotone g) :
    Monotone fun x => max (f x) (g x) :=
  hf.sup hg

@[to_dual map_inf_le]
theorem le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α → β} (h : Monotone f) (x y : α) :
    f x ⊔ f y ≤ f (x ⊔ y) :=
  sup_le (h le_sup_left) (h le_sup_right)

@[to_dual of_map_inf_le_left]
theorem of_left_le_map_sup [SemilatticeSup α] [Preorder β] {f : α → β}
    (h : ∀ x y, f x ≤ f (x ⊔ y)) : Monotone f := by
  intro x y hxy
  rw [← sup_eq_right.2 hxy]
  apply h

@[to_dual of_map_inf_le]
theorem of_le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α → β}
    (h : ∀ x y, f x ⊔ f y ≤ f (x ⊔ y)) : Monotone f :=
  of_left_le_map_sup fun x y ↦ le_sup_left.trans (h x y)

@[to_dual]
theorem of_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α → β}
    (h : ∀ x y, f (x ⊔ y) = f x ⊔ f y) : Monotone f :=
  of_le_map_sup fun x y ↦ (h x y).ge

variable [LinearOrder α]

@[to_dual]
theorem map_sup [SemilatticeSup β] {f : α → β} (hf : Monotone f) (x y : α) :
    f (x ⊔ y) = f x ⊔ f y :=
  (Std.Total.total x y).elim (fun h : x ≤ y => by simp only [h, hf h, sup_of_le_right]) fun h => by
    simp only [h, hf h, sup_of_le_left]

end Monotone

theorem exists_ge_and_iff_exists [SemilatticeSup α] {P : α → Prop} {x₀ : α} (hP : Monotone P) :
    (∃ x, x₀ ≤ x ∧ P x) ↔ ∃ x, P x :=
  ⟨fun h => h.imp fun _ h => h.2, fun ⟨x, hx⟩ => ⟨x ⊔ x₀, le_sup_right, hP le_sup_left hx⟩⟩

theorem exists_and_iff_of_monotone [SemilatticeSup α] {P Q : α → Prop}
    (hP : Monotone P) (hQ : Monotone Q) :
    ((∃ x, P x) ∧ ∃ x, Q x) ↔ (∃ x, P x ∧ Q x) :=
  ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ ↦ ⟨x ⊔ y, ⟨hP le_sup_left hPx, hQ le_sup_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ ↦ ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩

namespace MonotoneOn
variable {f : α → β} {s : Set α} {x y : α}

/-- Pointwise supremum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise infimum of two monotone functions is a monotone function. -/]
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} {s : Set α}
    (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (f ⊔ g) s :=
  fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)

/-- Pointwise maximum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise minimum of two monotone functions is a monotone function. -/]
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => max (f x) (g x)) s :=
  hf.sup hg

@[to_dual]
theorem of_map_sup [SemilatticeSup α] [SemilatticeSup β]
    (h : ∀ x ∈ s, ∀ y ∈ s, f (x ⊔ y) = f x ⊔ f y) : MonotoneOn f s := fun x hx y hy hxy =>
  sup_eq_right.1 <| by rw [← h _ hx _ hy, sup_eq_right.2 hxy]

variable [LinearOrder α]

@[to_dual]
theorem map_sup [SemilatticeSup β] (hf : MonotoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    f (x ⊔ y) = f x ⊔ f y := by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right]

end MonotoneOn

namespace Antitone

/-- Pointwise supremum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise infimum of two antitone functions is an antitone function. -/]
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} (hf : Antitone f)
    (hg : Antitone g) :
    Antitone (f ⊔ g) := fun _ _ h => sup_le_sup (hf h) (hg h)

/-- Pointwise maximum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise minimum of two antitone functions is an antitone function. -/]
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} (hf : Antitone f)
    (hg : Antitone g) :
    Antitone fun x => max (f x) (g x) :=
  hf.sup hg

@[to_dual le_map_inf]
theorem map_sup_le [SemilatticeSup α] [SemilatticeInf β] {f : α → β} (h : Antitone f) (x y : α) :
    f (x ⊔ y) ≤ f x ⊓ f y :=
  h.dual_right.le_map_sup x y

variable [LinearOrder α]

@[to_dual]
theorem map_sup [SemilatticeInf β] {f : α → β} (hf : Antitone f) (x y : α) :
    f (x ⊔ y) = f x ⊓ f y :=
  hf.dual_right.map_sup x y

end Antitone

theorem exists_le_and_iff_exists [SemilatticeInf α] {P : α → Prop} {x₀ : α} (hP : Antitone P) :
    (∃ x, x ≤ x₀ ∧ P x) ↔ ∃ x, P x :=
  exists_ge_and_iff_exists <| hP.dual_left

theorem exists_and_iff_of_antitone [SemilatticeInf α] {P Q : α → Prop}
    (hP : Antitone P) (hQ : Antitone Q) : ((∃ x, P x) ∧ ∃ x, Q x) ↔ (∃ x, P x ∧ Q x) :=
  ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ ↦ ⟨x ⊓ y, ⟨hP inf_le_left hPx, hQ inf_le_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ ↦ ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩

namespace AntitoneOn
variable {f : α → β} {s : Set α} {x y : α}

/-- Pointwise supremum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise infimum of two antitone functions is an antitone function. -/]
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} {s : Set α}
    (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (f ⊔ g) s :=
  fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)

/-- Pointwise maximum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise minimum of two antitone functions is an antitone function. -/]
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} {s : Set α} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => max (f x) (g x)) s :=
  hf.sup hg

@[to_dual]
theorem of_map_inf [SemilatticeInf α] [SemilatticeSup β]
    (h : ∀ x ∈ s, ∀ y ∈ s, f (x ⊓ y) = f x ⊔ f y) : AntitoneOn f s := fun x hx y hy hxy =>
  sup_eq_left.1 <| by rw [← h _ hx _ hy, inf_eq_left.2 hxy]

variable [LinearOrder α]

@[to_dual]
theorem map_sup [SemilatticeInf β] (hf : AntitoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    f (x ⊔ y) = f x ⊓ f y := by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right, inf_of_le_left, inf_of_le_right]

end AntitoneOn

/-!
### Products of (semi-)lattices
-/


namespace Prod

variable (α β)

@[to_dual]
instance [Max α] [Max β] : Max (α × β) :=
  ⟨fun p q => ⟨p.1 ⊔ q.1, p.2 ⊔ q.2⟩⟩

@[to_dual (attr := simp)]
theorem mk_sup_mk [Max α] [Max β] (a₁ a₂ : α) (b₁ b₂ : β) :
    (a₁, b₁) ⊔ (a₂, b₂) = (a₁ ⊔ a₂, b₁ ⊔ b₂) :=
  rfl

@[to_dual (attr := simp)]
theorem fst_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).fst = p.fst ⊔ q.fst :=
  rfl

@[to_dual (attr := simp)]
theorem snd_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).snd = p.snd ⊔ q.snd :=
  rfl

@[to_dual (attr := simp)]
theorem swap_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).swap = p.swap ⊔ q.swap :=
  rfl

@[to_dual]
theorem sup_def [Max α] [Max β] (p q : α × β) : p ⊔ q = (p.fst ⊔ q.fst, p.snd ⊔ q.snd) :=
  rfl

@[to_dual]
instance instSemilatticeSup [SemilatticeSup α] [SemilatticeSup β] : SemilatticeSup (α × β) where
  sup a b := ⟨a.1 ⊔ b.1, a.2 ⊔ b.2⟩
  sup_le _ _ _ h₁ h₂ := ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩

instance instLattice [Lattice α] [Lattice β] : Lattice (α × β) where

instance instDistribLattice [DistribLattice α] [DistribLattice β] : DistribLattice (α × β) where
  le_sup_inf _ _ _ := ⟨le_sup_inf, le_sup_inf⟩

end Prod

/-!
### Subtypes of (semi-)lattices
-/


namespace Subtype

/-- A subtype forms a `⊔`-semilattice if `⊔` preserves the property.
See note [reducible non-instances]. -/
@[to_dual (rename := Psup → Pinf)
/-- A subtype forms a `⊓`-semilattice if `⊓` preserves the property.
See note [reducible non-instances]. -/]
protected abbrev semilatticeSup [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) :
    SemilatticeSup { x : α // P x } where
  sup x y := ⟨x.1 ⊔ y.1, Psup x.2 y.2⟩
  le_sup_left _ _ := le_sup_left
  le_sup_right _ _ := le_sup_right
  sup_le _ _ _ h1 h2 := sup_le h1 h2

/-- A subtype forms a lattice if `⊔` and `⊓` preserve the property.
See note [reducible non-instances]. -/
protected abbrev lattice [Lattice α] {P : α → Prop} (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y))
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) : Lattice { x : α // P x } where
  __ := Subtype.semilatticeInf Pinf
  __ := Subtype.semilatticeSup Psup

@[to_dual (attr := simp, norm_cast) (rename := Psup → Pinf)]
theorem coe_sup [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (x y : Subtype P) :
    (haveI := Subtype.semilatticeSup Psup; (x ⊔ y : Subtype P) : α) = (x ⊔ y : α) :=
  rfl

@[to_dual (attr := simp) (rename := Psup → Pinf)]
theorem mk_sup_mk [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) {x y : α} (hx : P x) (hy : P y) :
    (haveI := Subtype.semilatticeSup Psup; (⟨x, hx⟩ ⊔ ⟨y, hy⟩ : Subtype P)) =
      ⟨x ⊔ y, Psup hx hy⟩ :=
  rfl

end Subtype

section lift

/-- A type endowed with `⊔` is a `SemilatticeSup`, if it admits an injective map that
preserves `⊔` to a `SemilatticeSup`.
See note [reducible non-instances]. -/
@[to_dual /-- A type endowed with `⊓` is a `SemilatticeInf`, if it admits an injective map that
preserves `⊓` to a `SemilatticeInf`.
See note [reducible non-instances]. -/]
protected abbrev Function.Injective.semilatticeSup [Max α] [LE α] [LT α] [SemilatticeSup β]
    (f : α → β) (hf_inj : Function.Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) :
    SemilatticeSup α where
  __ := hf_inj.partialOrder f le lt
  sup a b := max a b
  le_sup_left a b := by
    rw [← le, map_sup]
    exact le_sup_left
  le_sup_right a b := by
    rw [← le, map_sup]
    exact le_sup_right
  sup_le a b c ha hb := by
    rw [← le] at *
    rw [map_sup]
    exact sup_le ha hb

/-- A type endowed with `⊔` and `⊓` is a `Lattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `Lattice`.
See note [reducible non-instances]. -/
@[to_dual self (reorder := 3 4, le (x y), lt (x y), map_inf map_sup)]
protected abbrev Function.Injective.lattice [Max α] [Min α] [LE α] [LT α] [Lattice β]
    (f : α → β) (hf_inj : Function.Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    Lattice α where
  __ := hf_inj.semilatticeSup f le lt map_sup
  __ := hf_inj.semilatticeInf f le lt map_inf

/-- A type endowed with `⊔` and `⊓` is a `DistribLattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `DistribLattice`.
See note [reducible non-instances]. -/
@[to_dual self (reorder := 3 4, le (x y), lt (x y), map_inf map_sup)]
protected abbrev Function.Injective.distribLattice [Max α] [Min α] [LE α] [LT α] [DistribLattice β]
    (f : α → β) (hf_inj : Function.Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    DistribLattice α where
  __ := hf_inj.lattice f le lt map_sup map_inf
  le_sup_inf a b c := by
    rw [← le, map_inf, map_sup, map_sup, map_sup, map_inf]
    exact le_sup_inf

/-- A subtype forms a distributive lattice if `⊔` and `⊓` preserve the property.
See note [reducible non-instances]. -/
protected abbrev Subtype.distribLattice [DistribLattice α] {P : α → Prop}
    (Psup : ∀ ⦃s t : α⦄, P s → P t → P (s ⊔ t)) (Pinf : ∀ ⦃s t : α⦄, P s → P t → P (s ⊓ t)) :
    DistribLattice (Subtype P) :=
  letI := Subtype.lattice Psup Pinf
  Subtype.coe_injective.distribLattice _ coe_le_coe coe_lt_coe (coe_sup Psup) (coe_inf Pinf)

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `Preorder` across an `Equiv`. -/
protected abbrev preorder [Preorder β] : Preorder α := by
  let le := e.le
  let lt := e.lt
  apply Function.Injective.preorder e <;> intros <;> rfl

/-- Transfer `PartialOrder` across an `Equiv`. -/
protected abbrev partialOrder [PartialOrder β] : PartialOrder α := by
  let preorder := e.preorder
  apply e.injective.partialOrder <;> intros <;> rfl

/-- Transfer `LinearOrder` across an `Equiv`. -/
protected abbrev linearOrder [LinearOrder β] [DecidableEq α] : LinearOrder α := by
  let max := e.max
  let min := e.min
  let preorder := e.preorder
  let compare := e.ord
  apply e.injective.linearOrder <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `SemilatticeSup` across an `Equiv`. -/
protected abbrev semilatticeSup [SemilatticeSup β] : SemilatticeSup α := by
  let max := e.max
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeSup <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `SemilatticeInf` across an `Equiv`. -/
protected abbrev semilatticeInf [SemilatticeInf β] : SemilatticeInf α := by
  let min := e.min
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeInf <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `Lattice` across an `Equiv`. -/
protected abbrev lattice [Lattice β] : Lattice α := by
  let semilatticeSup := e.semilatticeSup
  let semilatticeInf := e.semilatticeInf
  apply e.injective.lattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `DistribLattice` across an `Equiv`. -/
protected abbrev distribLattice [DistribLattice β] : DistribLattice α := by
  let lattice := e.lattice
  apply e.injective.distribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv

end lift

namespace ULift

@[to_dual]
instance [SemilatticeSup α] : SemilatticeSup (ULift.{v} α) :=
  ULift.down_injective.semilatticeSup _ .rfl .rfl down_sup

instance [Lattice α] : Lattice (ULift.{v} α) where

instance [DistribLattice α] : DistribLattice (ULift.{v} α) :=
  ULift.down_injective.distribLattice _ .rfl .rfl down_sup down_inf

instance [LinearOrder α] : LinearOrder (ULift.{v} α) :=
  ULift.down_injective.linearOrder _ down_le down_lt down_inf down_sup down_compare

end ULift

--To avoid noncomputability poisoning from `Bool.completeBooleanAlgebra`
instance Bool.instPartialOrder : PartialOrder Bool := inferInstance
instance Bool.instDistribLattice : DistribLattice Bool := inferInstance

variable [LinearOrder α] {p : α → α → Prop}

lemma pairwise_iff_lt (hp : Symmetric p) : Pairwise p ↔ ∀ ⦃a b⦄, a < b → p a b := by
  simpa [Pairwise, ← lt_or_lt_iff_ne, or_imp, forall_and] using fun h a b hab ↦ hp <| h _ _ hab

lemma pairwise_iff_gt (hp : Symmetric p) : Pairwise p ↔ ∀ ⦃a b⦄, b < a → p a b := by
  simpa [Pairwise, ← lt_or_lt_iff_ne, or_imp, forall_and] using fun h a b hab ↦ hp <| h _ _ hab

alias ⟨_, Pairwise.of_lt⟩ := pairwise_iff_lt
alias ⟨_, Pairwise.of_gt⟩ := pairwise_iff_gt
