/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin

! This file was ported from Lean 3 source module algebra.group.with_one.defs
! leanprover-community/mathlib commit e574b1a4e891376b0ef974b926da39e05da12a06
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.WithBot
import Mathlib.Algebra.Ring.Defs

/-!
# Adjoining a zero/one to semigroups and related algebraic structures

This file contains different results about adjoining an element to an algebraic structure which then
behaves like a zero or a one. An example is adjoining a one to a semigroup to obtain a monoid. That
this provides an example of an adjunction is proved in `Algebra.Category.MonCat.Adjunctions`.

Another result says that adjoining to a group an element `zero` gives a `GroupWithZero`. For more
information about these structures (which are not that standard in informal mathematics, see
`Algebra.GroupWithZero.Basic`)
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Add an extra element `1` to a type -/
@[to_additive "Add an extra element `0` to a type"]
def WithOne (α) :=
  Option α
#align with_one WithOne
#align with_zero WithZero

namespace WithOne

instance [Repr α] : Repr (WithZero α) :=
  ⟨fun o _ =>
    match o with
    | none => "0"
    | some a => "↑" ++ repr a⟩

@[to_additive]
instance [Repr α] : Repr (WithOne α) :=
  ⟨fun o _ =>
    match o with
    | none => "1"
    | some a => "↑" ++ repr a⟩

@[to_additive]
instance monad : Monad WithOne :=
  instMonadOption

@[to_additive]
instance one : One (WithOne α) :=
  ⟨none⟩
#align with_one.has_one WithOne.one

@[to_additive]
instance mul [Mul α] : Mul (WithOne α) :=
  ⟨Option.liftOrGet (· * ·)⟩
#align with_one.has_mul WithOne.mul

@[to_additive]
instance inv [Inv α] : Inv (WithOne α) :=
  ⟨fun a => Option.map Inv.inv a⟩
#align with_one.has_inv WithOne.inv

@[to_additive]
instance involutiveInv [InvolutiveInv α] : InvolutiveInv (WithOne α) :=
  { WithOne.inv with
    inv_inv := fun a =>
      (Option.map_map _ _ _).trans <| by simp_rw [inv_comp_inv, Option.map_id, id] }

@[to_additive]
instance invOneClass [Inv α] : InvOneClass (WithOne α) :=
  { WithOne.one, WithOne.inv with inv_one := rfl }

@[to_additive]
instance inhabited : Inhabited (WithOne α) :=
  ⟨1⟩

@[to_additive]
instance nontrivial [Nonempty α] : Nontrivial (WithOne α) :=
  Option.nontrivial

-- porting note: this new declaration is here to make `((a : α): WithOne α)` have type `WithOne α` ;
-- otherwise the coercion kicks in and it becomes `Option.some a : WithOne α` which
-- becomes `Option.some a : Option α`.
/-- The canonical map from `α` into `WithOne α` -/
@[to_additive (attr := coe) "The canonical map from `α` into `WithZero α`"]
def coe : α → WithOne α :=
  Option.some

@[to_additive]
instance coeTC : CoeTC α (WithOne α) :=
  ⟨coe⟩

/-- Recursor for `WithOne` using the preferred forms `1` and `↑a`. -/
@[to_additive (attr := elab_as_elim)
  "Recursor for `WithZero` using the preferred forms `0` and `↑a`."]
def recOneCoe {C : WithOne α → Sort _} (h₁ : C 1) (h₂ : ∀ a : α, C a) : ∀ n : WithOne α, C n
  | Option.none => h₁
  | Option.some x => h₂ x
#align with_one.rec_one_coe WithOne.recOneCoe
#align with_zero.rec_zero_coe WithZero.recZeroCoe

-- porting note: in Lean 3 the to-additivised declaration
-- would automatically get this; right now in Lean 4...I don't
-- know if it does or not, and I don't know how to check, so
-- I'll add it manually just to be sure.
attribute [elab_as_elim] WithZero.recZeroCoe


/-- Deconstruct a `x : WithOne α` to the underlying value in `α`, given a proof that `x ≠ 1`. -/
@[to_additive unzero
      "Deconstruct a `x : WithZero α` to the underlying value in `α`, given a proof that `x ≠ 0`."]
def unone {x : WithOne α} (hx : x ≠ 1) : α :=
  WithBot.unbot x hx
#align with_one.unone WithOne.unone
#align with_zero.unzero WithZero.unzero

@[to_additive (attr := simp) unzero_coe]
theorem unone_coe {x : α} (hx : (x : WithOne α) ≠ 1) : unone hx = x :=
  rfl
#align with_one.unone_coe WithOne.unone_coe
#align with_zero.unzero_coe WithZero.unzero_coe

@[to_additive (attr := simp) coe_unzero]
theorem coe_unone {x : WithOne α} (hx : x ≠ 1) : ↑(unone hx) = x :=
  WithBot.coe_unbot x hx
#align with_one.coe_unone WithOne.coe_unone
#align with_zero.coe_unzero WithZero.coe_unzero

-- porting note: in Lean 4 the `some_eq_coe` lemmas present in the lean 3 version
-- of this file are syntactic tautologies
#noalign with_one.some_eq_coe
#noalign with_zero.some_eq_coe

@[to_additive (attr := simp)]
theorem coe_ne_one {a : α} : (a : WithOne α) ≠ (1 : WithOne α) :=
  Option.some_ne_none a
#align with_one.coe_ne_one WithOne.coe_ne_one
#align with_zero.coe_ne_zero WithZero.coe_ne_zero

@[to_additive (attr := simp)]
theorem one_ne_coe {a : α} : (1 : WithOne α) ≠ a :=
  coe_ne_one.symm
#align with_one.one_ne_coe WithOne.one_ne_coe
#align with_zero.zero_ne_coe WithZero.zero_ne_coe

@[to_additive]
theorem ne_one_iff_exists {x : WithOne α} : x ≠ 1 ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists
#align with_one.ne_one_iff_exists WithOne.ne_one_iff_exists
#align with_zero.ne_zero_iff_exists WithZero.ne_zero_iff_exists

-- porting note : waiting for `lift` tactic
--@[to_additive]
--instance canLift : CanLift (WithOne α) α coe fun a => a ≠ 1 where prf a := ne_one_iff_exists.1
--#align with_one.can_lift WithOne.canLift

@[to_additive (attr := simp, norm_cast)]
theorem coe_inj {a b : α} : (a : WithOne α) = b ↔ a = b :=
  Option.some_inj
#align with_one.coe_inj WithOne.coe_inj
#align with_zero.coe_inj WithZero.coe_inj

@[to_additive (attr := elab_as_elim)]
protected theorem cases_on {P : WithOne α → Prop} : ∀ x : WithOne α, P 1 → (∀ a : α, P a) → P x :=
  Option.casesOn
#align with_one.cases_on WithOne.cases_on
#align with_zero.cases_on WithZero.cases_on

-- port note: I don't know if `elab_as_elim` is being added to the additivised declaration.
attribute [elab_as_elim] WithZero.cases_on

-- porting note: in Lean 3 there was the following comment:
-- the `show` statements in the proofs are important, because otherwise the generated lemmas
-- `WithOne.mulOneClass._proof_{1,2}` have an ill-typed statement after `WithOne` is made
-- irreducible. Maybe one day when mathlib is ported to Lean 4 we can experiment
-- to see if these `show` comments can be removed.
@[to_additive]
instance mulOneClass [Mul α] : MulOneClass (WithOne α) where
  mul := (· * ·)
  one := 1
  one_mul := show ∀ x : WithOne α, 1 * x = x from (Option.liftOrGet_isLeftId _).1
  mul_one := show ∀ x : WithOne α, x * 1 = x from (Option.liftOrGet_isRightId _).1

@[to_additive]
instance monoid [Semigroup α] : Monoid (WithOne α) :=
  { WithOne.mulOneClass with mul_assoc := (Option.liftOrGet_isAssociative _).1 }

@[to_additive]
instance commMonoid [CommSemigroup α] : CommMonoid (WithOne α) :=
  { WithOne.monoid with mul_comm := (Option.liftOrGet_isCommutative _).1 }

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul [Mul α] (a b : α) : ((a * b : α) : WithOne α) = a * b :=
  rfl
#align with_one.coe_mul WithOne.coe_mul
#align with_zero.coe_add WithZero.coe_add

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv [Inv α] (a : α) : ((a⁻¹ : α) : WithOne α) = (a : WithOne α)⁻¹ :=
  rfl
#align with_one.coe_inv WithOne.coe_inv
#align with_zero.coe_neg WithZero.coe_neg

end WithOne

namespace WithZero

instance one [one : One α] : One (WithZero α) :=
  { one with }

@[simp, norm_cast]
theorem coe_one [One α] : ((1 : α) : WithZero α) = 1 :=
  rfl
#align with_zero.coe_one WithZero.coe_one

instance mulZeroClass [Mul α] : MulZeroClass (WithZero α) :=
  { WithZero.zero with
    mul := fun o₁ o₂ => o₁.bind fun a => Option.map (fun b => a * b) o₂,
    zero_mul := fun a => rfl,
    mul_zero := fun a => by cases a <;> rfl }

@[simp, norm_cast]
theorem coe_mul {α : Type u} [Mul α] {a b : α} : ((a * b : α) : WithZero α) = a * b :=
  rfl
#align with_zero.coe_mul WithZero.coe_mul

-- porting note: this used to be `@[simp]` in Lean 3 but in Lean 4 `simp` can already
-- prove it because we've just proved we're in MulZeroClass.
theorem zero_mul {α : Type u} [Mul α] (a : WithZero α) : 0 * a = 0 :=
  rfl
#align with_zero.zero_mul WithZero.zero_mul

-- porting note: in Lean 3 this was `@[simp]` but in Lean 4 `simp` can already prove it.
theorem mul_zero {α : Type u} [Mul α] (a : WithZero α) : a * 0 = 0 := by cases a <;> rfl
#align with_zero.mul_zero WithZero.mul_zero

instance noZeroDivisors [Mul α] : NoZeroDivisors (WithZero α) :=
  ⟨by
    rintro (a | a) (b | b) h
    exacts[Or.inl rfl, Or.inl rfl, Or.inr rfl, Option.noConfusion h]⟩

instance semigroupWithZero [Semigroup α] : SemigroupWithZero (WithZero α) :=
  { WithZero.mulZeroClass with
    mul_assoc := fun a b c =>
      match a, b, c with
      | none, _, _ => rfl
      | some _, none, _ => rfl
      | some _, some _, none => rfl
      | some a, some b, some c => congr_arg some (mul_assoc a b c) }

instance commSemigroup [CommSemigroup α] : CommSemigroup (WithZero α) :=
  { WithZero.semigroupWithZero with
    mul_comm := fun a b =>
      match a, b with
      | none, _ => (mul_zero _).symm
      | some _, none => rfl
      | some a, some b => congr_arg some (mul_comm a b) }

instance mulZeroOneClass [MulOneClass α] : MulZeroOneClass (WithZero α) :=
  { WithZero.mulZeroClass, WithZero.one with
    one_mul := fun a =>
      match a with
      | none => rfl
      | some a => congr_arg some <| one_mul a,
    mul_one := fun a =>
      match a with
      | none => rfl
      | some a => congr_arg some <| mul_one a }

instance pow [One α] [Pow α ℕ] : Pow (WithZero α) ℕ :=
  ⟨fun x n =>
    match x, n with
    | none, 0 => 1
    | none, _ + 1 => 0
    | some x, n => ↑(x ^ n)⟩

@[simp, norm_cast]
theorem coe_pow [One α] [Pow α ℕ] {a : α} (n : ℕ) :
    ↑(a ^ n : α) = ((a : WithZero α) ^ n : WithZero α) :=
  rfl
#align with_zero.coe_pow WithZero.coe_pow

instance monoidWithZero [Monoid α] : MonoidWithZero (WithZero α) :=
  { WithZero.mulZeroOneClass, WithZero.semigroupWithZero with
    npow := fun n x => x ^ n,
    npow_zero := fun x =>
      match x with
      | none => rfl
      | some x => congr_arg some <| pow_zero x,
    npow_succ := fun n x =>
      match x with
      | none => rfl
      | some x => congr_arg some <| pow_succ x n }

instance commMonoidWithZero [CommMonoid α] : CommMonoidWithZero (WithZero α) :=
  { WithZero.monoidWithZero, WithZero.commSemigroup with }

/-- Given an inverse operation on `α` there is an inverse operation
  on `WithZero α` sending `0` to `0`-/
instance inv [Inv α] : Inv (WithZero α) :=
  ⟨fun a => Option.map Inv.inv a⟩

@[simp, norm_cast]
theorem coe_inv [Inv α] (a : α) : ((a⁻¹ : α) : WithZero α) = (↑a)⁻¹ :=
  rfl
#align with_zero.coe_inv WithZero.coe_inv

@[simp]
theorem inv_zero [Inv α] : (0 : WithZero α)⁻¹ = 0 :=
  rfl
#align with_zero.inv_zero WithZero.inv_zero

instance involutiveInv [InvolutiveInv α] : InvolutiveInv (WithZero α) :=
  { WithZero.inv with
    inv_inv := fun a =>
      (Option.map_map _ _ _).trans <| by simp_rw [inv_comp_inv, Option.map_id, id] }

instance invOneClass [InvOneClass α] : InvOneClass (WithZero α) :=
  { WithZero.one, WithZero.inv with inv_one := show ((1⁻¹ : α) : WithZero α) = 1 by simp }

instance div [Div α] : Div (WithZero α) :=
  ⟨fun o₁ o₂ => o₁.bind fun a => Option.map (fun b => a / b) o₂⟩

@[norm_cast]
theorem coe_div [Div α] (a b : α) : ↑(a / b : α) = (a / b : WithZero α) :=
  rfl
#align with_zero.coe_div WithZero.coe_div

instance [One α] [Pow α ℤ] : Pow (WithZero α) ℤ :=
  ⟨fun x n =>
    match x, n with
    | none, Int.ofNat 0 => 1
    | none, Int.ofNat (Nat.succ _) => 0
    | none, Int.negSucc _ => 0
    | some x, n => ↑(x ^ n)⟩

@[simp, norm_cast]
theorem coe_zpow [DivInvMonoid α] {a : α} (n : ℤ) : ↑(a ^ n : α) = ((↑a : WithZero α) ^ n) :=
  rfl
#align with_zero.coe_zpow WithZero.coe_zpow

instance divInvMonoid [DivInvMonoid α] : DivInvMonoid (WithZero α) :=
  { WithZero.div, WithZero.inv, WithZero.monoidWithZero with
    div_eq_mul_inv := fun a b =>
      match a, b with
      | none, _ => rfl
      | some _, none => rfl
      | some a, some b => congr_arg some (div_eq_mul_inv a b),
    zpow := fun n x => x ^ n,
    zpow_zero' := fun x =>
      match x with
      | none => rfl
      | some x => congr_arg some <| zpow_zero x,
    zpow_succ' := fun n x =>
      match x with
      | none => rfl
      | some x => congr_arg some <| DivInvMonoid.zpow_succ' n x,
    zpow_neg' := fun n x =>
      match x with
      | none => rfl
      | some x => congr_arg some <| DivInvMonoid.zpow_neg' n x }

instance divInvOneMonoid [DivInvOneMonoid α] : DivInvOneMonoid (WithZero α) :=
  { WithZero.divInvMonoid, WithZero.invOneClass with }

instance divisionMonoid [DivisionMonoid α] : DivisionMonoid (WithZero α) :=
  { WithZero.divInvMonoid, WithZero.involutiveInv with
    mul_inv_rev := fun a b =>
      match a, b with
      | none, none => rfl
      | none, some b => rfl
      | some a, none => rfl
      | some a, some b => congr_arg some <| mul_inv_rev _ _,
    inv_eq_of_mul := fun a b ↦
      match a, b with
      | none, none => fun _ ↦ rfl
      | none, some b => fun _ ↦ by contradiction
      | some a, none => fun _ ↦ by contradiction
      | some a, some b => fun h ↦
        congr_arg some <| inv_eq_of_mul_eq_one_right <| Option.some_injective _ h }

instance divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (WithZero α) :=
  { WithZero.divisionMonoid, WithZero.commSemigroup with }

section Group

variable [Group α]

-- porting note: the lean 3 proof of this used the `lift` tactic, which was not
-- present in mathlib4 at the time of porting; we instead do a case split.
/-- if `G` is a group then `WithZero G` is a group with zero. -/
instance groupWithZero : GroupWithZero (WithZero α) :=
  { WithZero.monoidWithZero, WithZero.divInvMonoid, WithZero.nontrivial with
    inv_zero := inv_zero,
    mul_inv_cancel := fun a _ ↦
    match a with
    | Option.none => by contradiction
    | (x : α) => by
      norm_cast
      apply mul_right_inv
  }

end Group

instance commGroupWithZero [CommGroup α] : CommGroupWithZero (WithZero α) :=
  { WithZero.groupWithZero, WithZero.commMonoidWithZero with }

instance addMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (WithZero α) :=
  { WithZero.addMonoid, WithZero.one with
    natCast := fun n => if n = 0 then 0 else (n.cast : α),
    natCast_zero := rfl,
    natCast_succ := fun n => by
      cases n with
      | zero => show (((1 : ℕ) : α) : WithZero α) = 0 + 1; · rw [Nat.cast_one, coe_one, zero_add]
      | succ n =>
          show (((n + 2 : ℕ) : α) : WithZero α) = ((n + 1 : ℕ) : α) + 1
          rw [Nat.cast_succ, coe_add, coe_one]
      }

instance semiring [Semiring α] : Semiring (WithZero α) :=
  { WithZero.addMonoidWithOne, WithZero.addCommMonoid, WithZero.mulZeroClass,
    WithZero.monoidWithZero with
    left_distrib := fun a b c => by
      cases' a with a; · rfl
      cases' b with b <;> cases' c with c <;> try rfl
      exact congr_arg some (left_distrib _ _ _),
    right_distrib := fun a b c => by
      cases' c with c
      · change (a + b) * 0 = a * 0 + b * 0
        simp
      cases' a with a <;> cases' b with b <;> try rfl
      exact congr_arg some (right_distrib _ _ _) }

end WithZero
