/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Mathlib.Order.WithBot
import Mathlib.Algebra.Ring.Defs

#align_import algebra.group.with_one.defs from "leanprover-community/mathlib"@"995b47e555f1b6297c7cf16855f1023e355219fb"

/-!
# Adjoining a zero/one to semigroups and related algebraic structures

This file contains different results about adjoining an element to an algebraic structure which then
behaves like a zero or a one. An example is adjoining a one to a semigroup to obtain a monoid. That
this provides an example of an adjunction is proved in `Algebra.Category.MonCat.Adjunctions`.

Another result says that adjoining to a group an element `zero` gives a `GroupWithZero`. For more
information about these structures (which are not that standard in informal mathematics, see
`Algebra.GroupWithZero.Basic`)

## Porting notes

In Lean 3, we use `id` here and there to get correct types of proofs. This is required because
`WithOne` and `WithZero` are marked as `Irreducible` at the end of `algebra.group.with_one.defs`,
so proofs that use `Option α` instead of `WithOne α` no longer typecheck. In Lean 4, both types are
plain `def`s, so we don't need these `id`s.
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
#align with_zero.has_zero WithZero.zero

@[to_additive]
instance mul [Mul α] : Mul (WithOne α) :=
  ⟨Option.liftOrGet (· * ·)⟩
#align with_one.has_mul WithOne.mul
#align with_zero.has_add WithZero.add

@[to_additive]
instance inv [Inv α] : Inv (WithOne α) :=
  ⟨fun a => Option.map Inv.inv a⟩
#align with_one.has_inv WithOne.inv
#align with_zero.has_neg WithZero.neg

@[to_additive]
instance involutiveInv [InvolutiveInv α] : InvolutiveInv (WithOne α) :=
  { WithOne.inv with
    inv_inv := fun a =>
      (Option.map_map _ _ _).trans <| by simp_rw [inv_comp_inv, Option.map_id, id] }
                                         -- 🎉 no goals

@[to_additive]
instance invOneClass [Inv α] : InvOneClass (WithOne α) :=
  { WithOne.one, WithOne.inv with inv_one := rfl }

@[to_additive]
instance inhabited : Inhabited (WithOne α) :=
  ⟨1⟩

@[to_additive]
instance nontrivial [Nonempty α] : Nontrivial (WithOne α) :=
  Option.nontrivial

-- porting note: this new declaration is here to make `((a : α): WithOne α)` have type `WithOne α`;
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
def recOneCoe {C : WithOne α → Sort*} (h₁ : C 1) (h₂ : ∀ a : α, C a) : ∀ n : WithOne α, C n
  | Option.none => h₁
  | Option.some x => h₂ x
#align with_one.rec_one_coe WithOne.recOneCoe
#align with_zero.rec_zero_coe WithZero.recZeroCoe

-- porting note: in Lean 3 the to-additivised declaration
-- would automatically get this; right now in Lean 4...I don't
-- know if it does or not, and I don't know how to check, so
-- I'll add it manually just to be sure.
attribute [elab_as_elim] WithZero.recZeroCoe


/-- Deconstruct an `x : WithOne α` to the underlying value in `α`, given a proof that `x ≠ 1`. -/
@[to_additive unzero
      "Deconstruct an `x : WithZero α` to the underlying value in `α`, given a proof that `x ≠ 0`."]
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

@[to_additive]
instance canLift : CanLift (WithOne α) α (↑) fun a => a ≠ 1 where
  prf _ := ne_one_iff_exists.1
#align with_one.can_lift WithOne.canLift
#align with_zero.can_lift WithZero.canLift

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

@[to_additive]
instance mulOneClass [Mul α] : MulOneClass (WithOne α) where
  mul := (· * ·)
  one := 1
  one_mul := (Option.liftOrGet_isLeftId _).1
  mul_one := (Option.liftOrGet_isRightId _).1

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
    mul := Option.map₂ (· * ·),
    zero_mul := Option.map₂_none_left (· * ·),
    mul_zero := Option.map₂_none_right (· * ·) }

@[simp, norm_cast]
theorem coe_mul {α : Type u} [Mul α] {a b : α} : ((a * b : α) : WithZero α) = a * b :=
  rfl
#align with_zero.coe_mul WithZero.coe_mul

instance noZeroDivisors [Mul α] : NoZeroDivisors (WithZero α) :=
  ⟨Option.map₂_eq_none_iff.1⟩

instance semigroupWithZero [Semigroup α] : SemigroupWithZero (WithZero α) :=
  { WithZero.mulZeroClass with
    mul_assoc := fun _ _ _ => Option.map₂_assoc mul_assoc }

instance commSemigroup [CommSemigroup α] : CommSemigroup (WithZero α) :=
  { WithZero.semigroupWithZero with
    mul_comm := fun _ _ => Option.map₂_comm mul_comm }

instance mulZeroOneClass [MulOneClass α] : MulZeroOneClass (WithZero α) :=
  { WithZero.mulZeroClass, WithZero.one with
    one_mul := Option.map₂_left_identity one_mul,
    mul_one := Option.map₂_right_identity mul_one }

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
  on `WithZero α` sending `0` to `0`. -/
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
                                         -- 🎉 no goals

instance invOneClass [InvOneClass α] : InvOneClass (WithZero α) :=
  { WithZero.one, WithZero.inv with inv_one := show ((1⁻¹ : α) : WithZero α) = 1 by simp }
                                                                                    -- 🎉 no goals

instance div [Div α] : Div (WithZero α) :=
  ⟨Option.map₂ (· / ·)⟩

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
                                   -- 🎉 no goals
      | some a, none => fun _ ↦ by contradiction
                                   -- 🎉 no goals
      | some a, some b => fun h ↦
        congr_arg some <| inv_eq_of_mul_eq_one_right <| Option.some_injective _ h }

instance divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (WithZero α) :=
  { WithZero.divisionMonoid, WithZero.commSemigroup with }

section Group

variable [Group α]

/-- if `G` is a group then `WithZero G` is a group with zero. -/
instance groupWithZero : GroupWithZero (WithZero α) :=
  { WithZero.monoidWithZero, WithZero.divInvMonoid, WithZero.nontrivial with
    inv_zero := inv_zero,
    mul_inv_cancel := fun a ha ↦ by
      lift a to α using ha
      -- ⊢ ↑a * (↑a)⁻¹ = 1
      norm_cast
      -- ⊢ a * a⁻¹ = 1
      apply mul_right_inv }
      -- 🎉 no goals

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
      -- ⊢ none * (b + c) = none * b + none * c
                         -- 🎉 no goals
      cases' b with b <;> cases' c with c <;> try rfl
      -- ⊢ some a * (none + c) = some a * none + some a * c
                          -- ⊢ some a * (none + none) = some a * none + some a * none
                          -- ⊢ some a * (some b + none) = some a * some b + some a * none
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- ⊢ some a * (some b + some c) = some a * some b + some a * some c
      exact congr_arg some (left_distrib _ _ _),
      -- 🎉 no goals
    right_distrib := fun a b c => by
      cases' c with c
      -- ⊢ (a + b) * none = a * none + b * none
      · change (a + b) * 0 = a * 0 + b * 0
        -- ⊢ (a + b) * 0 = a * 0 + b * 0
        simp
        -- 🎉 no goals
      cases' a with a <;> cases' b with b <;> try rfl
      -- ⊢ (none + b) * some c = none * some c + b * some c
                          -- ⊢ (none + none) * some c = none * some c + none * some c
                          -- ⊢ (some a + none) * some c = some a * some c + none * some c
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- ⊢ (some a + some b) * some c = some a * some c + some b * some c
      exact congr_arg some (right_distrib _ _ _) }
      -- 🎉 no goals

end WithZero
