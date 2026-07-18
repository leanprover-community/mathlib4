/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Option.Basic
public import Mathlib.Logic.Nontrivial.Basic
public import Mathlib.Tactic.Common

/-!
# Adjoining a zero/one to semigroups and related algebraic structures

This file contains different results about adjoining an element to an algebraic structure which then
behaves like a zero or a one. An example is adjoining a one to a semigroup to obtain a monoid. That
this provides an example of an adjunction is proved in
`Mathlib/Algebra/Category/MonCat/Adjunctions.lean`.

Another result says that adjoining to a group an element `zero` gives a `GroupWithZero`. For more
information about these structures (which are not that standard in informal mathematics, see
`Mathlib/Algebra/GroupWithZero/Basic.lean`)

## TODO

`WithOne.coe_mul` and `WithZero.coe_mul` have inconsistent use of implicit parameters
-/

@[expose] public section

-- Check that we haven't needed to import all the basic lemmas about groups,
-- by asserting a random sample don't exist here:
assert_not_exists inv_involutive div_right_inj pow_ite MonoidWithZero DenselyOrdered

universe u v w

variable {α : Type u}

/-- Add an extra element `1` to a type -/
@[to_additive /-- Add an extra element `0` to a type -/]
def WithOne (α) :=
  Option α

instance WithZero.instRepr [Repr α] : Repr (WithZero α) :=
  ⟨fun o _ =>
    match o with
    | none => "0"
    | some a => "↑" ++ repr a⟩

namespace WithOne

@[to_additive existing]
instance [Repr α] : Repr (WithOne α) :=
  ⟨fun o _ =>
    match o with
    | none => "1"
    | some a => "↑" ++ repr a⟩

@[to_additive]
instance instMonad : Monad WithOne :=
  inferInstanceAs <| Monad Option

@[to_additive]
instance instOne : One (WithOne α) :=
  ⟨none⟩

@[to_additive]
instance instMul [Mul α] : Mul (WithOne α) :=
  ⟨Option.merge (· * ·)⟩

@[to_additive]
instance instInv [Inv α] : Inv (WithOne α) :=
  ⟨fun a => Option.map Inv.inv a⟩

@[to_additive]
instance instInvOneClass [Inv α] : InvOneClass (WithOne α) :=
  { inv_one := rfl }

@[to_additive]
instance inhabited : Inhabited (WithOne α) :=
  ⟨1⟩

@[to_additive]
instance instNontrivial [Nonempty α] : Nontrivial (WithOne α) :=
  Option.nontrivial

/-- The canonical map from `α` into `WithOne α` -/
@[to_additive (attr := coe, match_pattern) /-- The canonical map from `α` into `WithZero α` -/]
def coe : α → WithOne α :=
  Option.some

@[to_additive]
instance instCoeTC : CoeTC α (WithOne α) :=
  ⟨coe⟩

@[to_additive]
lemma «forall» {p : WithOne α → Prop} : (∀ x, p x) ↔ p 1 ∧ ∀ a : α, p a := Option.forall

@[to_additive]
lemma «exists» {p : WithOne α → Prop} : (∃ x, p x) ↔ p 1 ∨ ∃ a : α, p a := Option.exists

/-- Recursor for `WithZero` using the preferred forms `0` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def _root_.WithZero.recZeroCoe {motive : WithZero α → Sort*} (zero : motive 0)
    (coe : ∀ a : α, motive a) : ∀ n : WithZero α, motive n
  | Option.none => zero
  | Option.some x => coe x

/-- Recursor for `WithOne` using the preferred forms `1` and `↑a`. -/
@[to_additive existing, elab_as_elim, induction_eliminator, cases_eliminator]
def recOneCoe {motive : WithOne α → Sort*} (one : motive 1) (coe : ∀ a : α, motive a) :
    ∀ n : WithOne α, motive n
  | Option.none => one
  | Option.some x => coe x

@[to_additive (attr := simp)]
lemma recOneCoe_one {motive : WithOne α → Sort*} (h₁ h₂) :
    recOneCoe h₁ h₂ (1 : WithOne α) = (h₁ : motive 1) :=
  rfl

@[to_additive (attr := simp)]
lemma recOneCoe_coe {motive : WithOne α → Sort*} (h₁ h₂) (a : α) :
    recOneCoe h₁ h₂ (a : WithOne α) = (h₂ : ∀ a : α, motive a) a :=
  rfl

/-- Deconstruct an `x : WithOne α` to the underlying value in `α`, given a proof that `x ≠ 1`. -/
@[to_additive
/-- Deconstruct an `x : WithZero α` to the underlying value in `α`, given a proof that `x ≠ 0`. -/]
def unone : ∀ {x : WithOne α}, x ≠ 1 → α | (x : α), _ => x

@[to_additive (attr := simp)]
theorem unone_coe {x : α} (hx : (x : WithOne α) ≠ 1) : unone hx = x :=
  rfl

@[to_additive (attr := simp)]
lemma coe_unone : ∀ {x : WithOne α} (hx : x ≠ 1), unone hx = x
  | (x : α), _ => rfl

@[to_additive (attr := simp)]
theorem coe_ne_one {a : α} : (a : WithOne α) ≠ (1 : WithOne α) :=
  Option.some_ne_none a

@[to_additive (attr := simp)]
theorem one_ne_coe {a : α} : (1 : WithOne α) ≠ a :=
  coe_ne_one.symm

@[to_additive]
theorem ne_one_iff_exists {x : WithOne α} : x ≠ 1 ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists

@[to_additive]
instance instCanLift : CanLift (WithOne α) α (↑) fun a => a ≠ 1 where
  prf _ := ne_one_iff_exists.1

@[to_additive (attr := simp, norm_cast)]
theorem coe_inj {a b : α} : (a : WithOne α) = b ↔ a = b :=
  Option.some_inj

@[to_additive]
lemma coe_injective : Function.Injective (coe : α → WithOne α) :=
  Option.some_injective _

@[to_additive (attr := elab_as_elim)]
protected theorem cases_on {P : WithOne α → Prop} : ∀ x : WithOne α, P 1 → (∀ a : α, P a) → P x :=
  Option.casesOn

@[to_additive]
instance instMulOneClass [Mul α] : MulOneClass (WithOne α) where
  one_mul := (Option.lawfulIdentity_merge _).left_id
  mul_one := (Option.lawfulIdentity_merge _).right_id

@[to_additive (attr := simp, norm_cast)]
lemma coe_mul [Mul α] (a b : α) : (↑(a * b) : WithOne α) = a * b := rfl

@[to_additive]
instance instMonoid [Semigroup α] : Monoid (WithOne α) where
  __ := instMulOneClass
  mul_assoc
    | 1, b, c => by simp
    | (a : α), 1, c => by simp
    | (a : α), (b : α), 1 => by simp
    | (a : α), (b : α), (c : α) => by simp_rw [← coe_mul, mul_assoc]

@[to_additive]
instance instCommMonoid [CommSemigroup α] : CommMonoid (WithOne α) where
  mul_comm
    | (a : α), (b : α) => congr_arg some (mul_comm a b)
    | (_ : α), 1 => rfl
    | 1, (_ : α) => rfl
    | 1, 1 => rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv [Inv α] (a : α) : ((a⁻¹ : α) : WithOne α) = (a : WithOne α)⁻¹ :=
  rfl

/--
Specialization of `Option.getD` to values in `WithOne α` that respects API boundaries.
-/
@[to_additive
  /-- Specialization of `Option.getD` to values in `WithZero α` that respects API boundaries. -/]
def unoneD (d : α) (x : WithOne α) : α := recOneCoe d id x

@[to_additive (attr := simp)]
theorem unoneD_one (d : α) : unoneD d 1 = d :=
  rfl

@[to_additive (attr := simp)]
theorem unoneD_coe (d x : α) : unoneD d x = x :=
  rfl

@[to_additive]
theorem unoneD_eq_iff {d y : α} {x : WithOne α} : unoneD d x = y ↔ x = y ∨ x = 1 ∧ y = d := by
  induction x <;> simp [@eq_comm _ d]

@[to_additive (attr := simp)]
theorem unoneD_eq_self_iff {d : α} {x : WithOne α} : unoneD d x = d ↔ x = d ∨ x = 1 := by
  simp [unoneD_eq_iff]

@[to_additive]
theorem unoneD_eq_unoneD_iff {d : α} {x y : WithOne α} :
    unoneD d x = unoneD d y ↔ x = y ∨ x = d ∧ y = 1 ∨ x = 1 ∧ y = d := by
  induction y <;> simp [unoneD_eq_iff, or_comm]

@[to_additive]
lemma unoneD_eq_unone {d : α} {x : WithOne α} (hx : x ≠ 1) : unoneD d x = unone hx := by
  simp [unoneD_eq_iff]

end WithOne
