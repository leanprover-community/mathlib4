/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.Logic.Pairwise
import Mathlib.Algebra.Hom.GroupInstances
import Mathlib.Data.Pi.Algebra
import Mathlib.Data.Set.Function

#align_import algebra.group.pi from "leanprover-community/mathlib"@"e4bc74cbaf429d706cb9140902f7ca6c431e75a4"

/-!
# Pi instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/

/-
  Porting notes:

  See this Zulip discussion: [https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/not.20porting.20pi_instance]

  * This file now includes the pi instances for `AddMonoidWithOne` and `AddGroupWithOne`
  * This file relied on the `pi_instance` tactic, which was not available at the time of porting.
    The comment `--pi_instance` is inserted before all fields which were previously derived by
    `pi_instance`.
  * This file previously gave data fields explicitly. Now previously-defined instances are sourced
    via `with` as much as possible.
-/

universe u v w

variable {ι α : Type*}

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i j : I)

@[to_additive]
theorem Set.preimage_one {α β : Type*} [One β] (s : Set β) [Decidable ((1 : β) ∈ s)] :
    (1 : α → β) ⁻¹' s = if (1 : β) ∈ s then Set.univ else ∅ :=
  Set.preimage_const 1 s
#align set.preimage_one Set.preimage_one
#align set.preimage_zero Set.preimage_zero

namespace Pi

@[to_additive]
instance semigroup [∀ i, Semigroup <| f i] : Semigroup (∀ i : I, f i) :=
  { mul := (· * ·)
    --pi_instance
    mul_assoc := by intros; ext; exact mul_assoc _ _ _ }
                    -- ⊢ a✝ * b✝ * c✝ = a✝ * (b✝ * c✝)
                            -- ⊢ (a✝ * b✝ * c✝) x✝ = (a✝ * (b✝ * c✝)) x✝
                                 -- 🎉 no goals
#align pi.semigroup Pi.semigroup
#align pi.add_semigroup Pi.addSemigroup

@[to_additive]
instance commSemigroup [∀ i, CommSemigroup <| f i] : CommSemigroup (∀ i : I, f i) :=
  { semigroup with
    --pi_instance
    mul_comm := by intros; ext; exact mul_comm _ _
                   -- ⊢ a✝ * b✝ = b✝ * a✝
                           -- ⊢ (a✝ * b✝) x✝ = (b✝ * a✝) x✝
                                -- 🎉 no goals
  }
#align pi.comm_semigroup Pi.commSemigroup
#align pi.add_comm_semigroup Pi.addCommSemigroup

@[to_additive]
instance mulOneClass [∀ i, MulOneClass <| f i] : MulOneClass (∀ i : I, f i) :=
  { one := (1 : ∀ i, f i)
    mul := (· * ·)
    --pi_instance
    one_mul := by intros; ext; exact one_mul _
                  -- ⊢ 1 * a✝ = a✝
                          -- ⊢ (1 * a✝) x✝ = a✝ x✝
                               -- 🎉 no goals
    mul_one := by intros; ext; exact mul_one _
                  -- ⊢ a✝ * 1 = a✝
                          -- ⊢ (a✝ * 1) x✝ = a✝ x✝
                               -- 🎉 no goals
  }
#align pi.mul_one_class Pi.mulOneClass
#align pi.add_zero_class Pi.addZeroClass

@[to_additive]
instance invOneClass [∀ i, InvOneClass <| f i] : InvOneClass (∀ i : I, f i) :=
  { one := (1 : ∀ i, f i)
    inv := (· ⁻¹)
    inv_one := by intros; ext; exact inv_one }
                  -- ⊢ 1⁻¹ = 1
                          -- ⊢ 1⁻¹ x✝ = OfNat.ofNat 1 x✝
                               -- 🎉 no goals

@[to_additive]
instance monoid [∀ i, Monoid <| f i] : Monoid (∀ i : I, f i) :=
  { semigroup, mulOneClass with
    npow := fun n x i => x i ^ n
    --pi_instance
    npow_zero := by intros; ext; exact Monoid.npow_zero _
                    -- ⊢ (fun n x i => x i ^ n) 0 x✝ = 1
                            -- ⊢ (fun n x i => x i ^ n) 0 x✝¹ x✝ = OfNat.ofNat 1 x✝
                                 -- 🎉 no goals
    npow_succ := by intros; ext; exact Monoid.npow_succ _ _
                    -- ⊢ (fun n x i => x i ^ n) (n✝ + 1) x✝ = x✝ * (fun n x i => x i ^ n) n✝ x✝
                            -- ⊢ (fun n x i => x i ^ n) (n✝ + 1) x✝¹ x✝ = (x✝¹ * (fun n x i => x i ^ n) n✝ x✝ …
                                 -- 🎉 no goals
  }
#align pi.monoid Pi.monoid
#align pi.add_monoid Pi.addMonoid

instance addMonoidWithOne [∀ i, AddMonoidWithOne <| f i] : AddMonoidWithOne (∀ i : I, f i) :=
  { addMonoid with
    natCast := fun n _ => n
    natCast_zero := funext fun _ => AddMonoidWithOne.natCast_zero
    natCast_succ := fun n => funext fun _ => AddMonoidWithOne.natCast_succ n
  }

@[to_additive]
instance commMonoid [∀ i, CommMonoid <| f i] : CommMonoid (∀ i : I, f i) :=
  { monoid, commSemigroup with }
#align pi.comm_monoid Pi.commMonoid
#align pi.add_comm_monoid Pi.addCommMonoid

@[to_additive Pi.subNegMonoid]
instance divInvMonoid [∀ i, DivInvMonoid <| f i] : DivInvMonoid (∀ i : I, f i) :=
  { monoid with
    inv := Inv.inv
    div := Div.div
    zpow := fun z x i => x i ^ z
    --pi_instance
    div_eq_mul_inv := by intros; ext; exact div_eq_mul_inv _ _
                         -- ⊢ a✝ / b✝ = a✝ * b✝⁻¹
                                 -- ⊢ (a✝ / b✝) x✝ = (a✝ * b✝⁻¹) x✝
                                      -- 🎉 no goals
    zpow_zero' := by intros; ext; exact DivInvMonoid.zpow_zero' _
                     -- ⊢ (fun z x i => x i ^ z) 0 a✝ = 1
                             -- ⊢ (fun z x i => x i ^ z) 0 a✝ x✝ = OfNat.ofNat 1 x✝
                                  -- 🎉 no goals
    zpow_succ' := by intros; ext; exact DivInvMonoid.zpow_succ' _ _
                     -- ⊢ (fun z x i => x i ^ z) (Int.ofNat (Nat.succ n✝)) a✝ = a✝ * (fun z x i => x i …
                             -- ⊢ (fun z x i => x i ^ z) (Int.ofNat (Nat.succ n✝)) a✝ x✝ = (a✝ * (fun z x i => …
                                  -- 🎉 no goals
    zpow_neg' := by intros; ext; exact DivInvMonoid.zpow_neg' _ _
                    -- ⊢ (fun z x i => x i ^ z) (Int.negSucc n✝) a✝ = ((fun z x i => x i ^ z) (↑(Nat. …
                            -- ⊢ (fun z x i => x i ^ z) (Int.negSucc n✝) a✝ x✝ = ((fun z x i => x i ^ z) (↑(N …
                                 -- 🎉 no goals
  }

@[to_additive Pi.subNegZeroMonoid]
instance divInvOneMonoid [∀ i, DivInvOneMonoid <| f i] : DivInvOneMonoid (∀ i : I, f i) :=
  { divInvMonoid with
    inv_one := by ext; exact inv_one }
                  -- ⊢ 1⁻¹ x✝ = OfNat.ofNat 1 x✝
                       -- 🎉 no goals

@[to_additive]
instance involutiveInv [∀ i, InvolutiveInv <| f i] : InvolutiveInv (∀ i, f i) :=
  { inv := Inv.inv
    --pi_instance
    inv_inv := by intros; ext; exact inv_inv _
                  -- ⊢ x✝⁻¹⁻¹ = x✝
                          -- ⊢ x✝¹⁻¹⁻¹ x✝ = x✝¹ x✝
                               -- 🎉 no goals
  }

@[to_additive Pi.subtractionMonoid]
instance divisionMonoid [∀ i, DivisionMonoid <| f i] : DivisionMonoid (∀ i, f i) :=
  { divInvMonoid, involutiveInv with
    --pi_instance
    mul_inv_rev := by intros; ext; exact mul_inv_rev _ _
                      -- ⊢ (a✝ * b✝)⁻¹ = b✝⁻¹ * a✝⁻¹
                              -- ⊢ (a✝ * b✝)⁻¹ x✝ = (b✝⁻¹ * a✝⁻¹) x✝
                                   -- 🎉 no goals
    inv_eq_of_mul := by
      intros _ _ h; ext; exact DivisionMonoid.inv_eq_of_mul _ _ (congrFun h _)
      -- ⊢ a✝⁻¹ = b✝
                    -- ⊢ a✝⁻¹ x✝ = b✝ x✝
                         -- 🎉 no goals
  }

@[to_additive Pi.subtractionCommMonoid]
instance [∀ i, DivisionCommMonoid <| f i] : DivisionCommMonoid (∀ i, f i) :=
  { divisionMonoid, commSemigroup with }

@[to_additive]
instance group [∀ i, Group <| f i] : Group (∀ i : I, f i) :=
  { divInvMonoid with
    --pi_instance
    mul_left_inv := by intros; ext; exact mul_left_inv _
                       -- ⊢ a✝⁻¹ * a✝ = 1
                               -- ⊢ (a✝⁻¹ * a✝) x✝ = OfNat.ofNat 1 x✝
                                    -- 🎉 no goals
    }
#align pi.group Pi.group
#align pi.add_group Pi.addGroup

instance addGroupWithOne [∀ i, AddGroupWithOne <| f i] : AddGroupWithOne (∀ i : I, f i) :=
  { addGroup, addMonoidWithOne with
    intCast := fun z _ => z
    intCast_ofNat := fun n => funext fun _ => AddGroupWithOne.intCast_ofNat n
    intCast_negSucc := fun n => funext fun _ => AddGroupWithOne.intCast_negSucc n
  }

@[to_additive]
instance commGroup [∀ i, CommGroup <| f i] : CommGroup (∀ i : I, f i) :=
  { group, commMonoid with }
#align pi.comm_group Pi.commGroup
#align pi.add_comm_group Pi.addCommGroup

@[to_additive]
instance leftCancelSemigroup [∀ i, LeftCancelSemigroup <| f i] :
    LeftCancelSemigroup (∀ i : I, f i) :=
  { semigroup with
    --pi_instance
    mul_left_cancel := by
      intros _ _ _ h; ext; exact LeftCancelSemigroup.mul_left_cancel _ _ _ (congr_fun h _);
      -- ⊢ b✝ = c✝
                      -- ⊢ b✝ x✝ = c✝ x✝
                           -- 🎉 no goals
  }
#align pi.left_cancel_semigroup Pi.leftCancelSemigroup
#align pi.add_left_cancel_semigroup Pi.addLeftCancelSemigroup

@[to_additive]
instance rightCancelSemigroup [∀ i, RightCancelSemigroup <| f i] :
    RightCancelSemigroup (∀ i : I, f i) :=
  { semigroup with
    --pi_instance
    mul_right_cancel := by
      intros _ _ _ h; ext; exact RightCancelSemigroup.mul_right_cancel _ _ _ (congr_fun h _)
      -- ⊢ a✝ = c✝
                      -- ⊢ a✝ x✝ = c✝ x✝
                           -- 🎉 no goals
  }
#align pi.right_cancel_semigroup Pi.rightCancelSemigroup
#align pi.add_right_cancel_semigroup Pi.addRightCancelSemigroup

@[to_additive]
instance leftCancelMonoid [∀ i, LeftCancelMonoid <| f i] : LeftCancelMonoid (∀ i : I, f i) :=
  { leftCancelSemigroup, monoid with }
#align pi.left_cancel_monoid Pi.leftCancelMonoid
#align pi.add_left_cancel_monoid Pi.addLeftCancelMonoid

@[to_additive]
instance rightCancelMonoid [∀ i, RightCancelMonoid <| f i] : RightCancelMonoid (∀ i : I, f i) :=
  { rightCancelSemigroup, monoid with }
#align pi.right_cancel_monoid Pi.rightCancelMonoid
#align pi.add_right_cancel_monoid Pi.addRightCancelMonoid

@[to_additive]
instance cancelMonoid [∀ i, CancelMonoid <| f i] : CancelMonoid (∀ i : I, f i) :=
  { leftCancelMonoid, rightCancelMonoid with }
#align pi.cancel_monoid Pi.cancelMonoid
#align pi.add_cancel_monoid Pi.addCancelMonoid

@[to_additive]
instance cancelCommMonoid [∀ i, CancelCommMonoid <| f i] : CancelCommMonoid (∀ i : I, f i) :=
  { leftCancelMonoid, commMonoid with }
#align pi.cancel_comm_monoid Pi.cancelCommMonoid
#align pi.add_cancel_comm_monoid Pi.addCancelCommMonoid

instance mulZeroClass [∀ i, MulZeroClass <| f i] : MulZeroClass (∀ i : I, f i) :=
  { zero := (0 : ∀ i, f i)
    mul := (· * ·)
    --pi_instance
    zero_mul := by intros; ext; exact zero_mul _
                   -- ⊢ 0 * a✝ = 0
                           -- ⊢ (0 * a✝) x✝ = OfNat.ofNat 0 x✝
                                -- 🎉 no goals
    mul_zero := by intros; ext; exact mul_zero _
                   -- ⊢ a✝ * 0 = 0
                           -- ⊢ (a✝ * 0) x✝ = OfNat.ofNat 0 x✝
                                -- 🎉 no goals
}
#align pi.mul_zero_class Pi.mulZeroClass

instance mulZeroOneClass [∀ i, MulZeroOneClass <| f i] : MulZeroOneClass (∀ i : I, f i) :=
  { mulZeroClass, mulOneClass with }
#align pi.mul_zero_one_class Pi.mulZeroOneClass

instance monoidWithZero [∀ i, MonoidWithZero <| f i] : MonoidWithZero (∀ i : I, f i) :=
  { monoid, mulZeroClass with }
#align pi.monoid_with_zero Pi.monoidWithZero

instance commMonoidWithZero [∀ i, CommMonoidWithZero <| f i] : CommMonoidWithZero (∀ i : I, f i) :=
  { monoidWithZero, commMonoid with }
#align pi.comm_monoid_with_zero Pi.commMonoidWithZero

instance semigroupWithZero [∀ i, SemigroupWithZero <| f i] : SemigroupWithZero (∀ i : I, f i) :=
  { semigroup, mulZeroClass with }
#align pi.semigroup_with_zero Pi.semigroupWithZero

end Pi

namespace MulHom

@[to_additive]
theorem coe_mul {M N} {_ : Mul M} {_ : CommSemigroup N} (f g : M →ₙ* N) : (f * g : M → N) =
  fun x => f x * g x := rfl
#align mul_hom.coe_mul MulHom.coe_mul
#align add_hom.coe_add AddHom.coe_add

end MulHom

section MulHom

/-- A family of MulHom's `f a : γ →ₙ* β a` defines a MulHom `Pi.mulHom f : γ →ₙ* Π a, β a`
given by `Pi.mulHom f x b = f b x`. -/
@[to_additive (attr := simps)
  "A family of AddHom's `f a : γ → β a` defines an AddHom `Pi.addHom f : γ → Π a, β a` given by
  `Pi.addHom f x b = f b x`."]
def Pi.mulHom {γ : Type w} [∀ i, Mul (f i)] [Mul γ] (g : ∀ i, γ →ₙ* f i) : γ →ₙ* ∀ i, f i where
  toFun x i := g i x
  map_mul' x y := funext fun i => (g i).map_mul x y
#align pi.mul_hom Pi.mulHom
#align pi.add_hom Pi.addHom
#align pi.mul_hom_apply Pi.mulHom_apply
#align pi.add_hom_apply Pi.addHom_apply

@[to_additive]
theorem Pi.mulHom_injective {γ : Type w} [Nonempty I] [∀ i, Mul (f i)] [Mul γ] (g : ∀ i, γ →ₙ* f i)
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (Pi.mulHom g) := fun x y h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((Function.funext_iff.mp h : _) i)
#align pi.mul_hom_injective Pi.mulHom_injective
#align pi.add_hom_injective Pi.addHom_injective

/-- A family of monoid homomorphisms `f a : γ →* β a` defines a monoid homomorphism
`Pi.monoidHom f : γ →* Π a, β a` given by `Pi.monoidHom f x b = f b x`. -/
@[to_additive (attr := simps)
  "A family of additive monoid homomorphisms `f a : γ →+ β a` defines a monoid homomorphism
  `Pi.addMonoidHom f : γ →+ Π a, β a` given by `Pi.addMonoidHom f x b = f b x`."]
def Pi.monoidHom {γ : Type w} [∀ i, MulOneClass (f i)] [MulOneClass γ] (g : ∀ i, γ →* f i) :
    γ →* ∀ i, f i :=
  { Pi.mulHom fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }
#align pi.monoid_hom Pi.monoidHom
#align pi.add_monoid_hom Pi.addMonoidHom
#align pi.monoid_hom_apply Pi.monoidHom_apply
#align pi.add_monoid_hom_apply Pi.addMonoidHom_apply

@[to_additive]
theorem Pi.monoidHom_injective {γ : Type w} [Nonempty I] [∀ i, MulOneClass (f i)] [MulOneClass γ]
    (g : ∀ i, γ →* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (Pi.monoidHom g) :=
  Pi.mulHom_injective (fun i => (g i).toMulHom) hg
#align pi.monoid_hom_injective Pi.monoidHom_injective
#align pi.add_monoid_hom_injective Pi.addMonoidHom_injective

variable (f) [(i : I) → Mul (f i)]

/-- Evaluation of functions into an indexed collection of semigroups at a point is a semigroup
homomorphism.
This is `Function.eval i` as a `MulHom`. -/
@[to_additive (attr := simps)
  "Evaluation of functions into an indexed collection of additive semigroups at a point is an
  additive semigroup homomorphism. This is `Function.eval i` as an `AddHom`."]
def Pi.evalMulHom (i : I) : (∀ i, f i) →ₙ* f i where
  toFun g := g i
  map_mul' _ _ := Pi.mul_apply _ _ i
#align pi.eval_mul_hom Pi.evalMulHom
#align pi.eval_add_hom Pi.evalAddHom
#align pi.eval_mul_hom_apply Pi.evalMulHom_apply
#align pi.eval_add_hom_apply Pi.evalAddHom_apply

/-- `Function.const` as a `MulHom`. -/
@[to_additive (attr := simps) "`Function.const` as an `AddHom`."]
def Pi.constMulHom (α β : Type*) [Mul β] :
    β →ₙ* α → β where
  toFun := Function.const α
  map_mul' _ _ := rfl
#align pi.const_mul_hom Pi.constMulHom
#align pi.const_add_hom Pi.constAddHom
#align pi.const_mul_hom_apply Pi.constMulHom_apply
#align pi.const_add_hom_apply Pi.constAddHom_apply

/-- Coercion of a `MulHom` into a function is itself a `MulHom`.

See also `MulHom.eval`. -/
@[to_additive (attr := simps) "Coercion of an `AddHom` into a function is itself an `AddHom`.

See also `AddHom.eval`."]
def MulHom.coeFn (α β : Type*) [Mul α] [CommSemigroup β] :
    (α →ₙ* β) →ₙ* α → β where
  toFun g := g
  map_mul' _ _ := rfl
#align mul_hom.coe_fn MulHom.coeFn
#align add_hom.coe_fn AddHom.coeFn
#align mul_hom.coe_fn_apply MulHom.coeFn_apply
#align add_hom.coe_fn_apply AddHom.coeFn_apply

/-- Semigroup homomorphism between the function spaces `I → α` and `I → β`, induced by a semigroup
homomorphism `f` between `α` and `β`. -/
@[to_additive (attr := simps) "Additive semigroup homomorphism between the function spaces `I → α`
and `I → β`, induced by an additive semigroup homomorphism `f` between `α` and `β`"]
protected def MulHom.compLeft {α β : Type*} [Mul α] [Mul β] (f : α →ₙ* β) (I : Type*) :
    (I → α) →ₙ* I → β where
  toFun h := f ∘ h
  map_mul' _ _ := by ext; simp
                     -- ⊢ (fun h => ↑f ∘ h) (x✝² * x✝¹) x✝ = ((fun h => ↑f ∘ h) x✝² * (fun h => ↑f ∘ h …
                          -- 🎉 no goals
#align mul_hom.comp_left MulHom.compLeft
#align add_hom.comp_left AddHom.compLeft
#align mul_hom.comp_left_apply MulHom.compLeft_apply
#align add_hom.comp_left_apply AddHom.compLeft_apply

end MulHom

section MonoidHom

variable (f) [(i : I) → MulOneClass (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism.
This is `Function.eval i` as a `MonoidHom`. -/
@[to_additive (attr := simps) "Evaluation of functions into an indexed collection of additive
monoids at a point is an additive monoid homomorphism. This is `Function.eval i` as an
`AddMonoidHom`."]
def Pi.evalMonoidHom (i : I) : (∀ i, f i) →* f i where
  toFun g := g i
  map_one' := Pi.one_apply i
  map_mul' _ _ := Pi.mul_apply _ _ i
#align pi.eval_monoid_hom Pi.evalMonoidHom
#align pi.eval_add_monoid_hom Pi.evalAddMonoidHom
#align pi.eval_monoid_hom_apply Pi.evalMonoidHom_apply
#align pi.eval_add_monoid_hom_apply Pi.evalAddMonoidHom_apply

/-- `Function.const` as a `MonoidHom`. -/
@[to_additive (attr := simps) "`Function.const` as an `AddMonoidHom`."]
def Pi.constMonoidHom (α β : Type*) [MulOneClass β] : β →* α → β where
  toFun := Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl
#align pi.const_monoid_hom Pi.constMonoidHom
#align pi.const_add_monoid_hom Pi.constAddMonoidHom
#align pi.const_monoid_hom_apply Pi.constMonoidHom_apply
#align pi.const_add_monoid_hom_apply Pi.constAddMonoidHom_apply

/-- Coercion of a `MonoidHom` into a function is itself a `MonoidHom`.

See also `MonoidHom.eval`. -/
@[to_additive (attr := simps) "Coercion of an `AddMonoidHom` into a function is itself
an `AddMonoidHom`.

See also `AddMonoidHom.eval`."]
def MonoidHom.coeFn (α β : Type*) [MulOneClass α] [CommMonoid β] : (α →* β) →* α → β where
  toFun g := g
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_hom.coe_fn MonoidHom.coeFn
#align add_monoid_hom.coe_fn AddMonoidHom.coeFn
#align monoid_hom.coe_fn_apply MonoidHom.coeFn_apply
#align add_monoid_hom.coe_fn_apply AddMonoidHom.coeFn_apply

/-- Monoid homomorphism between the function spaces `I → α` and `I → β`, induced by a monoid
homomorphism `f` between `α` and `β`. -/
@[to_additive (attr := simps)
  "Additive monoid homomorphism between the function spaces `I → α` and `I → β`, induced by an
  additive monoid homomorphism `f` between `α` and `β`"]
protected def MonoidHom.compLeft {α β : Type*} [MulOneClass α] [MulOneClass β] (f : α →* β)
    (I : Type*) : (I → α) →* I → β where
  toFun h := f ∘ h
  map_one' := by ext; dsimp; simp
                 -- ⊢ (fun h => ↑f ∘ h) 1 x✝ = OfNat.ofNat 1 x✝
                      -- ⊢ ↑f 1 = 1
                             -- 🎉 no goals
  map_mul' _ _ := by ext; simp
                     -- ⊢ OneHom.toFun { toFun := fun h => ↑f ∘ h, map_one' := (_ : (fun h => ↑f ∘ h)  …
                          -- 🎉 no goals
#align monoid_hom.comp_left MonoidHom.compLeft
#align add_monoid_hom.comp_left AddMonoidHom.compLeft
#align monoid_hom.comp_left_apply MonoidHom.compLeft_apply
#align add_monoid_hom.comp_left_apply AddMonoidHom.compLeft_apply

end MonoidHom

section Single

variable [DecidableEq I]

open Pi

variable (f)

/-- The one-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `OneHom` version of `Pi.mulSingle`. -/
@[to_additive
      "The zero-preserving homomorphism including a single value into a dependent family of values,
      as functions supported at a point.

      This is the `ZeroHom` version of `Pi.single`."]
def OneHom.single [∀ i, One <| f i] (i : I) : OneHom (f i) (∀ i, f i) where
  toFun := mulSingle i
  map_one' := mulSingle_one i
#align one_hom.single OneHom.single
#align zero_hom.single ZeroHom.single

@[to_additive (attr := simp)]
theorem OneHom.single_apply [∀ i, One <| f i] (i : I) (x : f i) :
    OneHom.single f i x = mulSingle i x :=
  rfl
#align one_hom.single_apply OneHom.single_apply
#align zero_hom.single_apply ZeroHom.single_apply

/-- The monoid homomorphism including a single monoid into a dependent family of additive monoids,
as functions supported at a point.

This is the `MonoidHom` version of `Pi.mulSingle`. -/
@[to_additive
      "The additive monoid homomorphism including a single additive monoid into a dependent family
      of additive monoids, as functions supported at a point.

      This is the `AddMonoidHom` version of `Pi.single`."]
def MonoidHom.single [∀ i, MulOneClass <| f i] (i : I) : f i →* ∀ i, f i :=
  { OneHom.single f i with map_mul' := mulSingle_op₂ (fun _ => (· * ·)) (fun _ => one_mul _) _ }
#align monoid_hom.single MonoidHom.single
#align add_monoid_hom.single AddMonoidHom.single

@[to_additive (attr := simp)]
theorem MonoidHom.single_apply [∀ i, MulOneClass <| f i] (i : I) (x : f i) :
    MonoidHom.single f i x = mulSingle i x :=
  rfl
#align monoid_hom.single_apply MonoidHom.single_apply
#align add_monoid_hom.single_apply AddMonoidHom.single_apply

/-- The multiplicative homomorphism including a single `MulZeroClass`
into a dependent family of `MulZeroClass`es, as functions supported at a point.

This is the `MulHom` version of `Pi.single`. -/
@[simps]
def MulHom.single [∀ i, MulZeroClass <| f i] (i : I) : f i →ₙ* ∀ i, f i where
  toFun := Pi.single i
  map_mul' := Pi.single_op₂ (fun _ => (· * ·)) (fun _ => zero_mul _) _
#align mul_hom.single MulHom.single
#align mul_hom.single_apply MulHom.single_apply

variable {f}

@[to_additive]
theorem Pi.mulSingle_sup [∀ i, SemilatticeSup (f i)] [∀ i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊔ y) = Pi.mulSingle i x ⊔ Pi.mulSingle i y :=
  Function.update_sup _ _ _ _
#align pi.mul_single_sup Pi.mulSingle_sup
#align pi.single_sup Pi.single_sup

@[to_additive]
theorem Pi.mulSingle_inf [∀ i, SemilatticeInf (f i)] [∀ i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊓ y) = Pi.mulSingle i x ⊓ Pi.mulSingle i y :=
  Function.update_inf _ _ _ _
#align pi.mul_single_inf Pi.mulSingle_inf
#align pi.single_inf Pi.single_inf

@[to_additive]
theorem Pi.mulSingle_mul [∀ i, MulOneClass <| f i] (i : I) (x y : f i) :
    mulSingle i (x * y) = mulSingle i x * mulSingle i y :=
  (MonoidHom.single f i).map_mul x y
#align pi.mul_single_mul Pi.mulSingle_mul
#align pi.single_add Pi.single_add

@[to_additive]
theorem Pi.mulSingle_inv [∀ i, Group <| f i] (i : I) (x : f i) :
    mulSingle i x⁻¹ = (mulSingle i x)⁻¹ :=
  (MonoidHom.single f i).map_inv x
#align pi.mul_single_inv Pi.mulSingle_inv
#align pi.single_neg Pi.single_neg

@[to_additive]
theorem Pi.single_div [∀ i, Group <| f i] (i : I) (x y : f i) :
    mulSingle i (x / y) = mulSingle i x / mulSingle i y :=
  (MonoidHom.single f i).map_div x y
#align pi.single_div Pi.single_div
#align pi.single_sub Pi.single_sub

theorem Pi.single_mul [∀ i, MulZeroClass <| f i] (i : I) (x y : f i) :
    single i (x * y) = single i x * single i y :=
  (MulHom.single f i).map_mul x y
#align pi.single_mul Pi.single_mul

theorem Pi.single_mul_left_apply [∀ i, MulZeroClass <| f i] (a : f i) :
    Pi.single i (a * x i) j = Pi.single i a j * x j :=
  (Pi.apply_single (fun i => (· * x i)) (fun _ => zero_mul _) _ _ _).symm
#align pi.single_mul_left_apply Pi.single_mul_left_apply

theorem Pi.single_mul_right_apply [∀ i, MulZeroClass <| f i] (a : f i) :
    Pi.single i (x i * a) j = x j * Pi.single i a j :=
  (Pi.apply_single (fun i => (· * ·) (x i)) (fun _ => mul_zero _) _ _ _).symm
#align pi.single_mul_right_apply Pi.single_mul_right_apply

theorem Pi.single_mul_left [∀ i, MulZeroClass <| f i] (a : f i) :
    Pi.single i (a * x i) = Pi.single i a * x :=
  funext fun _ => Pi.single_mul_left_apply _ _ _ _
#align pi.single_mul_left Pi.single_mul_left

theorem Pi.single_mul_right [∀ i, MulZeroClass <| f i] (a : f i) :
    Pi.single i (x i * a) = x * Pi.single i a :=
  funext fun _ => Pi.single_mul_right_apply _ _ _ _
#align pi.single_mul_right Pi.single_mul_right

/-- The injection into a pi group at different indices commutes.

For injections of commuting elements at the same index, see `Commute.map` -/
@[to_additive
      "The injection into an additive pi group at different indices commutes.

      For injections of commuting elements at the same index, see `AddCommute.map`"]
theorem Pi.mulSingle_commute [∀ i, MulOneClass <| f i] :
    Pairwise fun i j => ∀ (x : f i) (y : f j), Commute (mulSingle i x) (mulSingle j y) := by
  intro i j hij x y; ext k
  -- ⊢ Commute (mulSingle i x) (mulSingle j y)
                     -- ⊢ (mulSingle i x * mulSingle j y) k = (mulSingle j y * mulSingle i x) k
  by_cases h1 : i = k;
  -- ⊢ (mulSingle i x * mulSingle j y) k = (mulSingle j y * mulSingle i x) k
  · subst h1
    -- ⊢ (mulSingle i x * mulSingle j y) i = (mulSingle j y * mulSingle i x) i
    simp [hij]
    -- 🎉 no goals
  by_cases h2 : j = k;
  -- ⊢ (mulSingle i x * mulSingle j y) k = (mulSingle j y * mulSingle i x) k
  · subst h2
    -- ⊢ (mulSingle i x * mulSingle j y) j = (mulSingle j y * mulSingle i x) j
    simp [hij]
    -- 🎉 no goals
  simp [h1, h2]
  -- 🎉 no goals
#align pi.mul_single_commute Pi.mulSingle_commute
#align pi.single_commute Pi.single_commute

/-- The injection into a pi group with the same values commutes. -/
@[to_additive "The injection into an additive pi group with the same values commutes."]
theorem Pi.mulSingle_apply_commute [∀ i, MulOneClass <| f i] (x : ∀ i, f i) (i j : I) :
    Commute (mulSingle i (x i)) (mulSingle j (x j)) := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  -- ⊢ Commute (mulSingle i (x i)) (mulSingle i (x i))
  · rfl
    -- 🎉 no goals
  · exact Pi.mulSingle_commute hij _ _
    -- 🎉 no goals
#align pi.mul_single_apply_commute Pi.mulSingle_apply_commute
#align pi.single_apply_commute Pi.single_apply_commute

@[to_additive]
theorem Pi.update_eq_div_mul_mulSingle [∀ i, Group <| f i] (g : ∀ i : I, f i) (x : f i) :
    Function.update g i x = g / mulSingle i (g i) * mulSingle i x := by
  ext j
  -- ⊢ Function.update g i x j = (g / mulSingle i (g i) * mulSingle i x) j
  rcases eq_or_ne i j with (rfl | h)
  -- ⊢ Function.update g i x i = (g / mulSingle i (g i) * mulSingle i x) i
  · simp
    -- 🎉 no goals
  · simp [Function.update_noteq h.symm, h]
    -- 🎉 no goals
#align pi.update_eq_div_mul_single Pi.update_eq_div_mul_mulSingle
#align pi.update_eq_sub_add_single Pi.update_eq_div_mul_mulSingle

@[to_additive]
theorem Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle {M : Type*} [CommMonoid M]
    {k l m n : I} {u v : M} (hu : u ≠ 1) (hv : v ≠ 1) :
    (mulSingle k u : I → M) * mulSingle l v = mulSingle m u * mulSingle n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n := by
  refine' ⟨fun h => _, _⟩
  -- ⊢ k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n
  · have hk := congr_fun h k
    -- ⊢ k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n
    have hl := congr_fun h l
    -- ⊢ k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n
    have hm := (congr_fun h m).symm
    -- ⊢ k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n
    have hn := (congr_fun h n).symm
    -- ⊢ k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n
    simp only [mul_apply, mulSingle_apply, if_pos rfl] at hk hl hm hn
    -- ⊢ k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n
    rcases eq_or_ne k m with (rfl | hkm)
    -- ⊢ k = k ∧ l = n ∨ u = v ∧ k = n ∧ l = k ∨ u * v = 1 ∧ k = l ∧ k = n
    · refine' Or.inl ⟨rfl, not_ne_iff.mp fun hln => (hv _).elim⟩
      -- ⊢ v = 1
      rcases eq_or_ne k l with (rfl | hkl)
      -- ⊢ v = 1
      · rwa [if_neg hln.symm, if_neg hln.symm, one_mul, one_mul] at hn
        -- 🎉 no goals
      · rwa [if_neg hkl.symm, if_neg hln, one_mul, one_mul] at hl
        -- 🎉 no goals
    · rcases eq_or_ne m n with (rfl | hmn)
      -- ⊢ k = m ∧ l = m ∨ u = v ∧ k = m ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = m
      · rcases eq_or_ne k l with (rfl | hkl)
        -- ⊢ k = m ∧ k = m ∨ u = v ∧ k = m ∧ k = m ∨ u * v = 1 ∧ k = k ∧ m = m
        · rw [if_neg hkm.symm, if_neg hkm.symm, one_mul, if_pos rfl] at hm
          -- ⊢ k = m ∧ k = m ∨ u = v ∧ k = m ∧ k = m ∨ u * v = 1 ∧ k = k ∧ m = m
          exact Or.inr (Or.inr ⟨hm, rfl, rfl⟩)
          -- 🎉 no goals
        · simp only [if_neg hkm, if_neg hkl, mul_one] at hk
          -- ⊢ k = m ∧ l = m ∨ u = v ∧ k = m ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = m
          dsimp at hk
          -- ⊢ k = m ∧ l = m ∨ u = v ∧ k = m ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = m
          contradiction
          -- 🎉 no goals
      · rw [if_neg hkm.symm, if_neg hmn, one_mul, mul_one] at hm
        -- ⊢ k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hm.symm hu)).1
        -- ⊢ k = m ∧ m = n ∨ u = v ∧ k = n ∧ m = m ∨ u * v = 1 ∧ k = m ∧ m = n
        rw [if_neg hkm, if_neg hkm, one_mul, mul_one] at hk
        -- ⊢ k = m ∧ m = n ∨ u = v ∧ k = n ∧ m = m ∨ u * v = 1 ∧ k = m ∧ m = n
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hk.symm hu)).1
        -- ⊢ k = m ∧ m = k ∨ u = v ∧ k = k ∧ m = m ∨ u * v = 1 ∧ k = m ∧ m = k
        exact Or.inr (Or.inl ⟨hk.trans (if_pos rfl), rfl, rfl⟩)
        -- 🎉 no goals
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h, rfl, rfl⟩)
    · rfl
      -- 🎉 no goals
    · apply mul_comm
      -- 🎉 no goals
    · simp_rw [← Pi.mulSingle_mul, h, mulSingle_one]
      -- 🎉 no goals
#align pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle
#align pi.single_add_single_eq_single_add_single Pi.single_add_single_eq_single_add_single

end Single

namespace Function

@[to_additive (attr := simp)]
theorem update_one [∀ i, One (f i)] [DecidableEq I] (i : I) : update (1 : ∀ i, f i) i 1 = 1 :=
  update_eq_self i (1 : (a : I) → f a)
#align function.update_one Function.update_one
#align function.update_zero Function.update_zero

@[to_additive]
theorem update_mul [∀ i, Mul (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun _ => (· * ·)) f₁ f₂ i x₁ x₂ j).symm
#align function.update_mul Function.update_mul
#align function.update_add Function.update_add

@[to_additive]
theorem update_inv [∀ i, Inv (f i)] [DecidableEq I] (f₁ : ∀ i, f i) (i : I) (x₁ : f i) :
    update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹ :=
  funext fun j => (apply_update (fun _ => Inv.inv) f₁ i x₁ j).symm
#align function.update_inv Function.update_inv
#align function.update_neg Function.update_neg

@[to_additive]
theorem update_div [∀ i, Div (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun _ => (· / ·)) f₁ f₂ i x₁ x₂ j).symm
#align function.update_div Function.update_div
#align function.update_sub Function.update_sub

variable [One α] [Nonempty ι] {a : α}

@[to_additive (attr := simp)]
theorem const_eq_one : const ι a = 1 ↔ a = 1 :=
  @const_inj _ _ _ _ 1
#align function.const_eq_one Function.const_eq_one
#align function.const_eq_zero Function.const_eq_zero

@[to_additive]
theorem const_ne_one : const ι a ≠ 1 ↔ a ≠ 1 :=
  Iff.not const_eq_one
#align function.const_ne_one Function.const_ne_one
#align function.const_ne_zero Function.const_ne_zero

end Function

section Piecewise

@[to_additive]
theorem Set.piecewise_mul [∀ i, Mul (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
  s.piecewise_op₂ f₁ _ _ _ fun _ => (· * ·)
#align set.piecewise_mul Set.piecewise_mul
#align set.piecewise_add Set.piecewise_add

@[to_additive]
theorem Set.piecewise_inv [∀ i, Inv (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ g₁ : ∀ i, f i) :
    s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹ :=
  s.piecewise_op f₁ g₁ fun _ x => x⁻¹
#align set.piecewise_inv Set.piecewise_inv
#align set.piecewise_neg Set.piecewise_neg

@[to_additive]
theorem Set.piecewise_div [∀ i, Div (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
  s.piecewise_op₂ f₁ _ _ _ fun _ => (· / ·)
#align set.piecewise_div Set.piecewise_div
#align set.piecewise_sub Set.piecewise_sub

end Piecewise

section Extend

variable {η : Type v} (R : Type w) (s : ι → η)

/-- `Function.extend s f 1` as a bundled hom. -/
@[to_additive (attr := simps) Function.ExtendByZero.hom "`Function.extend s f 0` as a bundled hom."]
noncomputable def Function.ExtendByOne.hom [MulOneClass R] :
    (ι → R) →* η → R where
  toFun f := Function.extend s f 1
  map_one' := Function.extend_one s
  map_mul' f g := by simpa using Function.extend_mul s f g 1 1
                     -- 🎉 no goals
#align function.extend_by_one.hom Function.ExtendByOne.hom
#align function.extend_by_zero.hom Function.ExtendByZero.hom
#align function.extend_by_one.hom_apply Function.ExtendByOne.hom_apply
#align function.extend_by_zero.hom_apply Function.ExtendByZero.hom_apply

end Extend

namespace Pi

variable [DecidableEq I] [∀ i, Preorder (f i)] [∀ i, One (f i)]

@[to_additive]
theorem mulSingle_mono : Monotone (Pi.mulSingle i : f i → ∀ i, f i) :=
  Function.update_mono
#align pi.mul_single_mono Pi.mulSingle_mono
#align pi.single_mono Pi.single_mono

@[to_additive]
theorem mulSingle_strictMono : StrictMono (Pi.mulSingle i : f i → ∀ i, f i) :=
  Function.update_strictMono
#align pi.mul_single_strict_mono Pi.mulSingle_strictMono
#align pi.single_strict_mono Pi.single_strictMono

end Pi
