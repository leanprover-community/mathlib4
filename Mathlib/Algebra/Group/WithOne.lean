/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Mathlib.Order.WithBot
--import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Defs
import Std.Classes.LawfulMonad

set_option autoImplicit false
/-!
# Adjoining a zero/one to semigroups and related algebraic structures

This file contains different results about adjoining an element to an algebraic structure which then
behaves like a zero or a one. An example is adjoining a one to a semigroup to obtain a monoid. That
this provides an example of an adjunction is proved in `algebra.category.Mon.adjunctions`.

Another result says that adjoining to a group an element `zero` gives a `group_with_zero`. For more
information about these structures (which are not that standard in informal mathematics, see
`algebra.group_with_zero.basic`)
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Add an extra element `1` to a type -/
@[to_additive "Add an extra element `0` to a type"]
def WithOne (α) :=
  Option α
#align with_one WithOne

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

-- porting note: this new declaration is here
/-- The canonical map from `α` into `WithOne α` -/
@[coe, to_additive "The canonical map from `α` into `WithZero α`"] def coe : α → WithOne α :=
  Option.some

@[to_additive]
instance : Monad WithOne :=
  instMonadOption

@[to_additive]
instance : One (WithOne α) :=
  ⟨none⟩

@[to_additive]
instance [Mul α] : Mul (WithOne α) :=
  ⟨Option.liftOrGet (· * ·)⟩

@[to_additive]
instance [Inv α] : Inv (WithOne α) :=
  ⟨fun a => Option.map Inv.inv a⟩

@[to_additive]
instance [HasInvolutiveInv α] : HasInvolutiveInv (WithOne α) :=
  { instInvWithOne with
    inv_inv := fun a => (Option.map_map _ _ _).trans <| by simp_rw [inv_comp_inv, Option.map_id, id] }

@[to_additive]
instance [Inv α] : InvOneClass (WithOne α) :=
  { instOneWithOne, instInvWithOne with inv_one := rfl }

@[to_additive]
instance : Inhabited (WithOne α) :=
  ⟨1⟩

@[to_additive]
instance [Nonempty α] : Nontrivial (WithOne α) :=
  Option.nontrivial

@[to_additive]
instance : CoeTC α (WithOne α) :=
  ⟨coe⟩

/-- Recursor for `with_one` using the preferred forms `1` and `↑a`. -/
@[elab_as_elim, to_additive "Recursor for `with_zero` using the preferred forms `0` and `↑a`."]
def recOneCoe {C : WithOne α → Sort _} (h₁ : C 1) (h₂ : ∀ a : α, C a) : ∀ n : WithOne α, C n
  | Option.none => h₁
  | Option.some x => h₂ x
#align with_one.rec_one_coe WithOne.recOneCoe

/-- Deconstruct a `x : with_one α` to the underlying value in `α`, given a proof that `x ≠ 1`. -/
@[to_additive unzero "Deconstruct a `x : with_zero α` to the underlying value in `α`,
given a proof that `x ≠ 0`."]
def unone {x : WithOne α} (hx : x ≠ 1) : α :=
  WithBot.unbot x hx
#align with_one.unone WithOne.unone

@[simp, to_additive unzero_coe]
theorem unone_coe {x : α} (hx : (x : WithOne α) ≠ 1) : unone hx = x :=
  rfl

#align with_one.unone_coe WithOne.unone_coe

@[simp, to_additive coe_unzero]
theorem coe_unone {x : WithOne α} (hx : x ≠ 1) : ↑(unone hx) = x :=
  WithBot.coe_unbot x hx
#align with_one.coe_unone WithOne.coe_unone

@[to_additive]
theorem some_eq_coe {a : α} : (some a : WithOne α) = ↑a :=
  rfl
#align with_one.some_eq_coe WithOne.some_eq_coe

@[simp, to_additive]
theorem coe_ne_one {a : α} : (a : WithOne α) ≠ (1 : WithOne α) :=
  Option.some_ne_none a
#align with_one.coe_ne_one WithOne.coe_ne_one

@[simp, to_additive]
theorem one_ne_coe {a : α} : (1 : WithOne α) ≠ a :=
  coe_ne_one.symm
#align with_one.one_ne_coe WithOne.one_ne_coe

@[to_additive]
theorem ne_one_iff_exists {x : WithOne α} : x ≠ 1 ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists
#align with_one.ne_one_iff_exists WithOne.ne_one_iff_exists

-- **TODO** waiting for lift tactic
-- @[to_additive]
-- instance canLift : CanLift (WithOne α) α coe fun a => a ≠ 1 where prf a := ne_one_iff_exists.1
-- #align with_one.can_lift WithOne.canLift

@[simp, norm_cast, to_additive]
theorem coe_inj {a b : α} : (a : WithOne α) = b ↔ a = b :=
  Option.some_inj
#align with_one.coe_inj WithOne.coe_inj

@[elab_as_elim, to_additive]
protected theorem cases_on {P : WithOne α → Prop} : ∀ x : WithOne α, P 1 → (∀ a : α, P a) → P x :=
  Option.casesOn
#align with_one.cases_on WithOne.cases_on

-- the `show` statements in the proofs are important, because otherwise the generated lemmas
-- `with_one.mul_one_class._proof_{1,2}` have an ill-typed statement after `with_one` is made
-- irreducible.
@[to_additive]
instance [Mul α] : MulOneClass (WithOne α) where
  mul := (· * ·)
  one := 1
  one_mul := show ∀ x : WithOne α, 1 * x = x from (Option.liftOrGet_isLeftId _).1
  mul_one := show ∀ x : WithOne α, x * 1 = x from (Option.liftOrGet_isRightId _).1

variable (α : Type) [Semigroup α] in
example : IsAssociative α (· * ·) := inferInstance

@[to_additive]
instance [Semigroup α] : Monoid (WithOne α) :=
  { instMulOneClassWithOne with mul_assoc := (Option.liftOrGet_isAssociative _).1 }
--  { instMulOneClassWithOne with mul_assoc := (Option.liftOrGet_isAssociative _).1 }

example [Semigroup α] : @Monoid.toMulOneClass _ (@WithOne.monoid α _) = @WithOne.mulOneClass α _ :=
  rfl

@[to_additive]
instance [CommSemigroup α] : CommMonoid (WithOne α) :=
  { WithOne.monoid with mul_comm := (Option.liftOrGet_isCommutative _).1 }

section

-- workaround: we make `with_one`/`with_zero` irreducible for this definition, otherwise `simps`
-- will unfold it in the statement of the lemma it generates.
/-- `coe` as a bundled morphism -/
@[to_additive "`coe` as a bundled morphism", simps apply]
def coeMulHom [Mul α] : α →ₙ* WithOne α where
  toFun := coe
  map_mul' x y := rfl
#align with_one.coe_mul_hom WithOne.coeMulHom

end

section lift

variable [Mul α] [MulOneClass β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homorphism. -/
@[to_additive "Lift an add_semigroup homomorphism `f` to a bundled add_monoid homorphism."]
def lift : (α →ₙ* β) ≃ (WithOne α →* β) where
  toFun f :=
    { toFun := fun x => Option.casesOn x 1 f, map_one' := rfl,
      map_mul' := fun x y =>
        (WithOne.cases_on x
            (by
              rw [one_mul]
              exact (one_mul _).symm))
          fun x =>
          (WithOne.cases_on y
              (by
                rw [mul_one]
                exact (mul_one _).symm))
            fun y => f.map_mul x y }
  invFun F := F.toMulHom.comp coeMulHom
  left_inv f := MulHom.ext fun x => rfl
  right_inv F := MonoidHom.ext fun x => (WithOne.cases_on x F.map_one.symm) fun x => rfl
#align with_one.lift WithOne.lift

variable (f : α →ₙ* β)

@[simp, to_additive]
theorem lift_coe (x : α) : lift f x = f x :=
  rfl
#align with_one.lift_coe WithOne.lift_coe

@[simp, to_additive]
theorem lift_one : lift f 1 = 1 :=
  rfl
#align with_one.lift_one WithOne.lift_one

@[to_additive]
theorem lift_unique (f : WithOne α →* β) : f = lift (f.toMulHom.comp coeMulHom) :=
  (lift.apply_symm_apply f).symm
#align with_one.lift_unique WithOne.lift_unique

end lift

section Map

variable [Mul α] [Mul β] [Mul γ]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `with_one α` to `with_one β` -/
@[to_additive
      "Given an additive map from `α → β` returns an add_monoid homomorphism\n  from `with_zero α` to `with_zero β`"]
def map (f : α →ₙ* β) : WithOne α →* WithOne β :=
  lift (coeMulHom.comp f)
#align with_one.map WithOne.map

@[simp, to_additive]
theorem map_coe (f : α →ₙ* β) (a : α) : map f (a : WithOne α) = f a :=
  lift_coe _ _
#align with_one.map_coe WithOne.map_coe

@[simp, to_additive]
theorem map_id : map (MulHom.id α) = MonoidHom.id (WithOne α) := by
  ext
  induction x using WithOne.cases_on <;> rfl
#align with_one.map_id WithOne.map_id

@[to_additive]
theorem map_map (f : α →ₙ* β) (g : β →ₙ* γ) (x) : map g (map f x) = map (g.comp f) x := by
  induction x using WithOne.cases_on <;> rfl
#align with_one.map_map WithOne.map_map

@[simp, to_additive]
theorem map_comp (f : α →ₙ* β) (g : β →ₙ* γ) : map (g.comp f) = (map g).comp (map f) :=
  MonoidHom.ext fun x => (map_map f g x).symm
#align with_one.map_comp WithOne.map_comp

/-- A version of `equiv.option_congr` for `with_one`. -/
@[to_additive "A version of `equiv.option_congr` for `with_zero`.", simps apply]
def _root_.mul_equiv.with_one_congr (e : α ≃* β) : WithOne α ≃* WithOne β :=
  { map e.toMulHom with toFun := map e.toMulHom, invFun := map e.symm.toMulHom,
    left_inv := fun x =>
      (map_map _ _ _).trans <| by
        induction x using WithOne.cases_on <;>
          · simp
            ,
    right_inv := fun x =>
      (map_map _ _ _).trans <| by
        induction x using WithOne.cases_on <;>
          · simp
             }
#align with_one._root_.mul_equiv.with_one_congr with_one._root_.mul_equiv.with_one_congr

@[simp]
theorem _root_.mul_equiv.with_one_congr_refl : (MulEquiv.refl α).withOneCongr = MulEquiv.refl _ :=
  MulEquiv.to_monoid_hom_injective map_id
#align with_one._root_.mul_equiv.with_one_congr_refl with_one._root_.mul_equiv.with_one_congr_refl

@[simp]
theorem _root_.mul_equiv.with_one_congr_symm (e : α ≃* β) : e.withOneCongr.symm = e.symm.withOneCongr :=
  rfl
#align with_one._root_.mul_equiv.with_one_congr_symm with_one._root_.mul_equiv.with_one_congr_symm

@[simp]
theorem _root_.mul_equiv.with_one_congr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
    e₁.withOneCongr.trans e₂.withOneCongr = (e₁.trans e₂).withOneCongr :=
  MulEquiv.to_monoid_hom_injective (map_comp _ _).symm
#align with_one._root_.mul_equiv.with_one_congr_trans with_one._root_.mul_equiv.with_one_congr_trans

end Map

@[simp, norm_cast, to_additive]
theorem coe_mul [Mul α] (a b : α) : ((a * b : α) : WithOne α) = a * b :=
  rfl
#align with_one.coe_mul WithOne.coe_mul

@[simp, norm_cast, to_additive]
theorem coe_inv [Inv α] (a : α) : ((a⁻¹ : α) : WithOne α) = a⁻¹ :=
  rfl
#align with_one.coe_inv WithOne.coe_inv

end WithOne

namespace WithZero

instance [one : One α] : One (WithZero α) :=
  { one with }

@[simp, norm_cast]
theorem coe_one [One α] : ((1 : α) : WithZero α) = 1 :=
  rfl
#align with_zero.coe_one WithZero.coe_one

instance [Mul α] : MulZeroClass (WithZero α) :=
  { WithZero.hasZero with mul := fun o₁ o₂ => o₁.bind fun a => Option.map (fun b => a * b) o₂, zero_mul := fun a => rfl,
    mul_zero := fun a => by cases a <;> rfl }

@[simp, norm_cast]
theorem coe_mul {α : Type u} [Mul α] {a b : α} : ((a * b : α) : WithZero α) = a * b :=
  rfl
#align with_zero.coe_mul WithZero.coe_mul

@[simp]
theorem zero_mul {α : Type u} [Mul α] (a : WithZero α) : 0 * a = 0 :=
  rfl
#align with_zero.zero_mul WithZero.zero_mul

@[simp]
theorem mul_zero {α : Type u} [Mul α] (a : WithZero α) : a * 0 = 0 := by cases a <;> rfl
#align with_zero.mul_zero WithZero.mul_zero

instance [Mul α] : NoZeroDivisors (WithZero α) :=
  ⟨by
    rintro (a | a) (b | b) h
    exacts[Or.inl rfl, Or.inl rfl, Or.inr rfl, Option.noConfusion h]⟩

instance [Semigroup α] : SemigroupWithZero (WithZero α) :=
  { WithZero.mulZeroClass with
    mul_assoc := fun a b c =>
      match a, b, c with
      | none, _, _ => rfl
      | some a, none, _ => rfl
      | some a, some b, none => rfl
      | some a, some b, some c => congr_arg some (mul_assoc _ _ _) }

instance [CommSemigroup α] : CommSemigroup (WithZero α) :=
  { WithZero.semigroupWithZero with
    mul_comm := fun a b =>
      match a, b with
      | none, _ => (mul_zero _).symm
      | some a, none => rfl
      | some a, some b => congr_arg some (mul_comm _ _) }

instance [MulOneClass α] : MulZeroOneClass (WithZero α) :=
  { WithZero.mulZeroClass, WithZero.hasOne with
    one_mul := fun a =>
      match a with
      | none => rfl
      | some a => congr_arg some <| one_mul _,
    mul_one := fun a =>
      match a with
      | none => rfl
      | some a => congr_arg some <| mul_one _ }

instance [One α] [Pow α ℕ] : Pow (WithZero α) ℕ :=
  ⟨fun x n =>
    match x, n with
    | none, 0 => 1
    | none, n + 1 => 0
    | some x, n => ↑(x ^ n)⟩

@[simp, norm_cast]
theorem coe_pow [One α] [Pow α ℕ] {a : α} (n : ℕ) : ↑(a ^ n : α) = (↑a ^ n : WithZero α) :=
  rfl
#align with_zero.coe_pow WithZero.coe_pow

instance [Monoid α] : MonoidWithZero (WithZero α) :=
  { WithZero.mulZeroOneClass, WithZero.semigroupWithZero with npow := fun n x => x ^ n,
    npow_zero' := fun x =>
      match x with
      | none => rfl
      | some x => congr_arg some <| pow_zero _,
    npow_succ' := fun n x =>
      match x with
      | none => rfl
      | some x => congr_arg some <| pow_succ _ _ }

instance [CommMonoid α] : CommMonoidWithZero (WithZero α) :=
  { WithZero.monoidWithZero, WithZero.commSemigroup with }

/-- Given an inverse operation on `α` there is an inverse operation
  on `with_zero α` sending `0` to `0`-/
instance [Inv α] : Inv (WithZero α) :=
  ⟨fun a => Option.map Inv.inv a⟩

@[simp, norm_cast]
theorem coe_inv [Inv α] (a : α) : ((a⁻¹ : α) : WithZero α) = a⁻¹ :=
  rfl
#align with_zero.coe_inv WithZero.coe_inv

@[simp]
theorem inv_zero [Inv α] : (0 : WithZero α)⁻¹ = 0 :=
  rfl
#align with_zero.inv_zero WithZero.inv_zero

instance [HasInvolutiveInv α] : HasInvolutiveInv (WithZero α) :=
  { WithZero.hasInv with
    inv_inv := fun a => (Option.map_map _ _ _).trans <| by simp_rw [inv_comp_inv, Option.map_id, id] }

instance [InvOneClass α] : InvOneClass (WithZero α) :=
  { WithZero.hasOne, WithZero.hasInv with inv_one := show ((1⁻¹ : α) : WithZero α) = 1 by simp }

instance [Div α] : Div (WithZero α) :=
  ⟨fun o₁ o₂ => o₁.bind fun a => Option.map (fun b => a / b) o₂⟩

@[norm_cast]
theorem coe_div [Div α] (a b : α) : ↑(a / b : α) = (a / b : WithZero α) :=
  rfl
#align with_zero.coe_div WithZero.coe_div

instance [One α] [Pow α ℤ] : Pow (WithZero α) ℤ :=
  ⟨fun x n =>
    match x, n with
    | none, Int.ofNat 0 => 1
    | none, Int.ofNat (Nat.succ n) => 0
    | none, Int.negSucc n => 0
    | some x, n => ↑(x ^ n)⟩

@[simp, norm_cast]
theorem coe_zpow [DivInvMonoid α] {a : α} (n : ℤ) : ↑(a ^ n : α) = (↑a ^ n : WithZero α) :=
  rfl
#align with_zero.coe_zpow WithZero.coe_zpow

instance [DivInvMonoid α] : DivInvMonoid (WithZero α) :=
  { WithZero.hasDiv, WithZero.hasInv, WithZero.monoidWithZero with
    div_eq_mul_inv := fun a b =>
      match a, b with
      | none, _ => rfl
      | some a, none => rfl
      | some a, some b => congr_arg some (div_eq_mul_inv _ _),
    zpow := fun n x => x ^ n,
    zpow_zero' := fun x =>
      match x with
      | none => rfl
      | some x => congr_arg some <| zpow_zero _,
    zpow_succ' := fun n x =>
      match x with
      | none => rfl
      | some x => congr_arg some <| DivInvMonoid.zpow_succ' _ _,
    zpow_neg' := fun n x =>
      match x with
      | none => rfl
      | some x => congr_arg some <| DivInvMonoid.zpow_neg' _ _ }

instance [DivInvOneMonoid α] : DivInvOneMonoid (WithZero α) :=
  { WithZero.divInvMonoid, WithZero.invOneClass with }

instance [DivisionMonoid α] : DivisionMonoid (WithZero α) :=
  { WithZero.divInvMonoid, WithZero.hasInvolutiveInv with
    mul_inv_rev := fun a b =>
      match a, b with
      | none, none => rfl
      | none, some b => rfl
      | some a, none => rfl
      | some a, some b => congr_arg some <| mul_inv_rev _ _,
    inv_eq_of_mul := fun a b =>
      match a, b with
      | none, none => fun _ => rfl
      | none, some b => by contradiction
      | some a, none => by contradiction
      | some a, some b => fun h => congr_arg some <| inv_eq_of_mul_eq_one_right <| Option.some_injective _ h }

instance [DivisionCommMonoid α] : DivisionCommMonoid (WithZero α) :=
  { WithZero.divisionMonoid, WithZero.commSemigroup with }

section Group

variable [Group α]

/-- if `G` is a group then `with_zero G` is a group with zero. -/
instance : GroupWithZero (WithZero α) :=
  { WithZero.monoidWithZero, WithZero.divInvMonoid, WithZero.nontrivial with inv_zero := inv_zero,
    mul_inv_cancel := fun a ha => by
      lift a to α using ha
      norm_cast
      apply mul_right_inv }

end Group

instance [CommGroup α] : CommGroupWithZero (WithZero α) :=
  { WithZero.groupWithZero, WithZero.commMonoidWithZero with }

instance [AddMonoidWithOne α] : AddMonoidWithOne (WithZero α) :=
  { WithZero.addMonoid, WithZero.hasOne with natCast := fun n => if n = 0 then 0 else (n.cast : α),
    nat_cast_zero := rfl,
    nat_cast_succ := fun n => by
      cases n
      show (((1 : ℕ) : α) : WithZero α) = 0 + 1
      · rw [Nat.cast_one, coe_one, zero_add]

      show (((n + 2 : ℕ) : α) : WithZero α) = ((n + 1 : ℕ) : α) + 1
      · rw [Nat.cast_succ, coe_add, coe_one]
         }

instance [Semiring α] : Semiring (WithZero α) :=
  { WithZero.addMonoidWithOne, WithZero.addCommMonoid, WithZero.mulZeroClass, WithZero.monoidWithZero with
    left_distrib := fun a b c => by
      cases' a with a
      · rfl

      cases' b with b <;> cases' c with c <;> try rfl
      exact congr_arg some (left_distrib _ _ _),
    right_distrib := fun a b c => by
      cases' c with c
      · change (a + b) * 0 = a * 0 + b * 0
        simp

      cases' a with a <;> cases' b with b <;> try rfl
      exact congr_arg some (right_distrib _ _ _) }

/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
def unitsWithZeroEquiv [Group α] : (WithZero α)ˣ ≃* α where
  toFun a := unzero a.NeZero
  invFun a := Units.mk0 a coe_ne_zero
  left_inv _ := Units.ext <| by simpa only [coe_unzero]
  right_inv _ := rfl
  map_mul' _ _ := coe_inj.mp <| by simpa only [coe_unzero, coe_mul]
#align with_zero.units_with_zero_equiv WithZero.unitsWithZeroEquiv

end WithZero
