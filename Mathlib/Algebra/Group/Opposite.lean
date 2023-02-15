/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.group.opposite
! leanprover-community/mathlib commit 655994e298904d7e5bbd1e18c95defd7b543eb94
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.Group.Commute
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Algebra.Opposites
import Mathlib.Data.Int.Cast.Defs

/-!
# Group structures on the multiplicative and additive opposites
-/


universe u v

variable (α : Type u)

namespace MulOpposite

/-!
### Additive structures on `αᵐᵒᵖ`
-/


instance [AddSemigroup α] : AddSemigroup αᵐᵒᵖ :=
  unop_injective.addSemigroup _ fun _ _ => rfl

instance [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup αᵐᵒᵖ :=
  unop_injective.addLeftCancelSemigroup _ fun _ _ => rfl

instance [AddRightCancelSemigroup α] : AddRightCancelSemigroup αᵐᵒᵖ :=
  unop_injective.addRightCancelSemigroup _ fun _ _ => rfl

instance [AddCommSemigroup α] : AddCommSemigroup αᵐᵒᵖ :=
  unop_injective.addCommSemigroup _ fun _ _ => rfl

instance [AddZeroClass α] : AddZeroClass αᵐᵒᵖ :=
  unop_injective.addZeroClass _ (by exact rfl) fun _ _ => rfl

instance [AddMonoid α] : AddMonoid αᵐᵒᵖ :=
  unop_injective.addMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [AddMonoidWithOne α] : AddMonoidWithOne αᵐᵒᵖ :=
  { instAddMonoidMulOpposite α, instOneMulOpposite α with
    natCast := fun n => op n,
    natCast_zero := show op ((0 : ℕ) : α) = 0 by simp,
    natCast_succ := show ∀ n, op ((n + 1 : ℕ) : α) = op ((n : ℕ) : α) + 1 by simp }

instance [AddCommMonoid α] : AddCommMonoid αᵐᵒᵖ :=
  unop_injective.addCommMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [SubNegMonoid α] : SubNegMonoid αᵐᵒᵖ :=
  unop_injective.subNegMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [AddGroup α] : AddGroup αᵐᵒᵖ :=
  unop_injective.addGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) fun _ _ => rfl

instance [AddGroupWithOne α] : AddGroupWithOne αᵐᵒᵖ :=
  { instAddMonoidWithOneMulOpposite α, instAddGroupMulOpposite α with
    intCast := fun n => op n,
    intCast_ofNat := fun n => show op ((n : ℤ) : α) = op (n : α) by rw [Int.cast_ofNat],
    intCast_negSucc := fun n =>
      show op _ = op (-unop (op ((n + 1 : ℕ) : α))) by simp }

instance [AddCommGroup α] : AddCommGroup αᵐᵒᵖ :=
  unop_injective.addCommGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-!
### Multiplicative structures on `αᵐᵒᵖ`

We also generate additive structures on `αᵃᵒᵖ` using `to_additive`
-/


@[to_additive]
instance [Semigroup α] : Semigroup αᵐᵒᵖ :=
  { instMulMulOpposite α with
    mul_assoc := fun x y z => unop_injective <| Eq.symm <| mul_assoc (unop z) (unop y) (unop x) }

@[to_additive]
instance [RightCancelSemigroup α] : LeftCancelSemigroup αᵐᵒᵖ :=
  { instSemigroupMulOpposite α with
    mul_left_cancel := fun _ _ _ H => unop_injective <| mul_right_cancel <| op_injective H }

@[to_additive]
instance [LeftCancelSemigroup α] : RightCancelSemigroup αᵐᵒᵖ :=
  { instSemigroupMulOpposite α with
    mul_right_cancel := fun _ _ _ H => unop_injective <| mul_left_cancel <| op_injective H }

@[to_additive]
instance [CommSemigroup α] : CommSemigroup αᵐᵒᵖ :=
  { instSemigroupMulOpposite α with
    mul_comm := fun x y => unop_injective <| mul_comm (unop y) (unop x) }

@[to_additive]
instance [MulOneClass α] : MulOneClass αᵐᵒᵖ :=
  { instMulMulOpposite α, instOneMulOpposite α with
    one_mul := fun x => unop_injective <| mul_one <| unop x,
    mul_one := fun x => unop_injective <| one_mul <| unop x }

@[to_additive]
instance [Monoid α] : Monoid αᵐᵒᵖ :=
  { instSemigroupMulOpposite α, instMulOneClassMulOpposite α with
    npow := fun n x => op <| x.unop ^ n,
    npow_zero := fun x => unop_injective <| Monoid.npow_zero x.unop,
    npow_succ := fun n x => unop_injective <| pow_succ' x.unop n }

@[to_additive]
instance [RightCancelMonoid α] : LeftCancelMonoid αᵐᵒᵖ :=
  { instLeftCancelSemigroupMulOpposite α, instMonoidMulOpposite α with }

@[to_additive]
instance [LeftCancelMonoid α] : RightCancelMonoid αᵐᵒᵖ :=
  { instRightCancelSemigroupMulOpposite α, instMonoidMulOpposite α with }

@[to_additive]
instance [CancelMonoid α] : CancelMonoid αᵐᵒᵖ :=
  { instRightCancelMonoidMulOpposite α, instLeftCancelMonoidMulOpposite α with }

@[to_additive]
instance [CommMonoid α] : CommMonoid αᵐᵒᵖ :=
  { instMonoidMulOpposite α, instCommSemigroupMulOpposite α with }

@[to_additive]
instance [CancelCommMonoid α] : CancelCommMonoid αᵐᵒᵖ :=
  { instCancelMonoidMulOpposite α, instCommMonoidMulOpposite α with }

@[to_additive AddOpposite.subNegMonoid]
instance [DivInvMonoid α] : DivInvMonoid αᵐᵒᵖ :=
  { instMonoidMulOpposite α, instInvMulOpposite α with
    zpow := fun n x => op <| x.unop ^ n,
    zpow_zero' := fun x => unop_injective <| DivInvMonoid.zpow_zero' x.unop,
    zpow_succ' := fun n x => unop_injective <| by
      simp only [Int.ofNat_eq_coe]
      rw [unop_op, zpow_ofNat, pow_succ', unop_mul, unop_op, zpow_ofNat],
    zpow_neg' := fun z x => unop_injective <| DivInvMonoid.zpow_neg' z x.unop }

@[to_additive AddOpposite.subtractionMonoid]
instance [DivisionMonoid α] : DivisionMonoid αᵐᵒᵖ :=
  { instDivInvMonoidMulOpposite α, instInvolutiveInvMulOpposite α with
    mul_inv_rev := fun _ _ => unop_injective <| mul_inv_rev _ _,
    inv_eq_of_mul := fun _ _ h => unop_injective <| inv_eq_of_mul_eq_one_left <| congr_arg unop h }

@[to_additive AddOpposite.subtractionCommMonoid]
instance [DivisionCommMonoid α] : DivisionCommMonoid αᵐᵒᵖ :=
  { instDivisionMonoidMulOpposite α, instCommSemigroupMulOpposite α with }

@[to_additive]
instance [Group α] : Group αᵐᵒᵖ :=
  { instDivInvMonoidMulOpposite α with
    mul_left_inv := fun x => unop_injective <| mul_inv_self <| unop x }

@[to_additive]
instance [CommGroup α] : CommGroup αᵐᵒᵖ :=
  { instGroupMulOpposite α, instCommMonoidMulOpposite α with }

variable {α}

@[to_additive (attr := simp)]
theorem unop_div [DivInvMonoid α] (x y : αᵐᵒᵖ) : unop (x / y) = (unop y)⁻¹ * unop x :=
  rfl
#align mul_opposite.unop_div MulOpposite.unop_div
#align add_opposite.unop_sub AddOpposite.unop_sub

@[to_additive (attr := simp)]
theorem op_div [DivInvMonoid α] (x y : α) : op (x / y) = (op y)⁻¹ * op x := by simp [div_eq_mul_inv]
#align mul_opposite.op_div MulOpposite.op_div
#align add_opposite.op_sub AddOpposite.op_sub

@[to_additive (attr := simp)]
theorem semiconjBy_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y :=
  by simp only [SemiconjBy, ← op_mul, op_inj, eq_comm]
#align mul_opposite.semiconj_by_op MulOpposite.semiconjBy_op
#align add_opposite.semiconj_by_op AddOpposite.semiconjBy_op

@[to_additive (attr := simp, nolint simpComm)]
theorem semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} :
    SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, semiconjBy_op]
#align mul_opposite.semiconj_by_unop MulOpposite.semiconjBy_unop
#align add_opposite.semiconj_by_unop AddOpposite.semiconjBy_unop

attribute [nolint simpComm] AddOpposite.semiconjBy_unop

@[to_additive]
theorem _root_.SemiconjBy.op [Mul α] {a x y : α} (h : SemiconjBy a x y) :
    SemiconjBy (op a) (op y) (op x) :=
  semiconjBy_op.2 h
#align semiconj_by.op SemiconjBy.op
#align add_semiconj_by.op AddSemiconjBy.op

@[to_additive]
theorem _root_.SemiconjBy.unop [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y) :
    SemiconjBy (unop a) (unop y) (unop x) :=
  semiconjBy_unop.2 h
#align semiconj_by.unop SemiconjBy.unop
#align add_semiconj_by.unop AddSemiconjBy.unop

@[to_additive]
theorem _root_.Commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) :=
  SemiconjBy.op h
#align commute.op Commute.op
#align add_commute.op AddCommute.op

@[to_additive]
theorem Commute.unop [Mul α] {x y : αᵐᵒᵖ} (h : Commute x y) : Commute (unop x) (unop y) :=
  h.unop
#align mul_opposite.commute.unop MulOpposite.Commute.unop
#align add_opposite.commute.unop AddOpposite.Commute.unop

@[to_additive (attr := simp)]
theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y :=
  semiconjBy_op
#align mul_opposite.commute_op MulOpposite.commute_op
#align add_opposite.commute_op AddOpposite.commute_op

@[to_additive (attr := simp, nolint simpComm)]
theorem commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x y :=
  semiconjBy_unop
#align mul_opposite.commute_unop MulOpposite.commute_unop
#align add_opposite.commute_unop AddOpposite.commute_unop

attribute [nolint simpComm] AddOpposite.commute_unop

/-- The function `MulOpposite.op` is an additive equivalence. -/
@[simps! (config := { fullyApplied := false, simpRhs := true })]
def opAddEquiv [Add α] : α ≃+ αᵐᵒᵖ :=
  { opEquiv with map_add' := fun _ _ => rfl }
#align mul_opposite.op_add_equiv MulOpposite.opAddEquiv
#align mul_opposite.op_add_equiv_symm_apply MulOpposite.opAddEquiv_symmApply

@[simp]
theorem opAddEquiv_toEquiv [Add α] : (opAddEquiv : α ≃+ αᵐᵒᵖ).toEquiv = opEquiv := rfl

#align mul_opposite.op_add_equiv_to_equiv MulOpposite.opAddEquiv_toEquiv

end MulOpposite

/-!
### Multiplicative structures on `αᵃᵒᵖ`
-/


namespace AddOpposite

instance [Semigroup α] : Semigroup αᵃᵒᵖ :=
  unop_injective.semigroup _ fun _ _ => rfl

instance [LeftCancelSemigroup α] : LeftCancelSemigroup αᵃᵒᵖ :=
  unop_injective.leftCancelSemigroup _ fun _ _ => rfl

instance [RightCancelSemigroup α] : RightCancelSemigroup αᵃᵒᵖ :=
  unop_injective.rightCancelSemigroup _ fun _ _ => rfl

instance [CommSemigroup α] : CommSemigroup αᵃᵒᵖ :=
  unop_injective.commSemigroup _ fun _ _ => rfl

instance [MulOneClass α] : MulOneClass αᵃᵒᵖ :=
  unop_injective.mulOneClass _ (by exact rfl) fun _ _ => rfl

instance {β} [Pow α β] : Pow αᵃᵒᵖ β where pow a b := op (unop a ^ b)

@[simp]
theorem op_pow {β} [Pow α β] (a : α) (b : β) : op (a ^ b) = op a ^ b :=
  rfl
#align add_opposite.op_pow AddOpposite.op_pow

@[simp]
theorem unop_pow {β} [Pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b :=
  rfl
#align add_opposite.unop_pow AddOpposite.unop_pow

instance [Monoid α] : Monoid αᵃᵒᵖ :=
  unop_injective.monoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [CommMonoid α] : CommMonoid αᵃᵒᵖ :=
  unop_injective.commMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [DivInvMonoid α] : DivInvMonoid αᵃᵒᵖ :=
  unop_injective.divInvMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [Group α] : Group αᵃᵒᵖ :=
  unop_injective.group _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) fun _ _ => rfl

instance [CommGroup α] : CommGroup αᵃᵒᵖ :=
  unop_injective.commGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) fun _ _ => rfl

variable {α}

/-- The function `AddOpposite.op` is a multiplicative equivalence. -/
@[simps! (config := { fullyApplied := false, simpRhs := true })]
def opMulEquiv [Mul α] : α ≃* αᵃᵒᵖ :=
  { opEquiv with map_mul' := fun _ _ => rfl }
#align add_opposite.op_mul_equiv AddOpposite.opMulEquiv
#align add_opposite.op_mul_equiv_symm_apply AddOpposite.opMulEquiv_symmApply

@[simp]
theorem opMulEquiv_toEquiv [Mul α] : (opMulEquiv : α ≃* αᵃᵒᵖ).toEquiv = opEquiv :=
  rfl
#align add_opposite.op_mul_equiv_to_equiv AddOpposite.opMulEquiv_toEquiv

end AddOpposite

open MulOpposite

/-- Inversion on a group is a `MulEquiv` to the opposite group. When `G` is commutative, there is
`MulEquiv.inv`. -/
@[to_additive (attr := simps! (config := { fullyApplied := false, simpRhs := true }))
      "Negation on an additive group is an `AddEquiv` to the opposite group. When `G`
      is commutative, there is `AddEquiv.inv`."]
def MulEquiv.inv' (G : Type _) [DivisionMonoid G] : G ≃* Gᵐᵒᵖ :=
  { (Equiv.inv G).trans opEquiv with map_mul' := fun x y => unop_injective <| mul_inv_rev x y }
#align mul_equiv.inv' MulEquiv.inv'
#align add_equiv.neg' AddEquiv.neg'
#align mul_equiv.inv'_symm_apply MulEquiv.inv'_symmApply
#align add_equiv.inv'_symm_apply AddEquiv.neg'_symmApply

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := { fullyApplied := false }))
      "An additive semigroup homomorphism `f : AddHom M N` such that `f x` additively
      commutes with `f y` for all `x, y` defines an additive semigroup homomorphism to `Sᵃᵒᵖ`."]
def MulHom.toOpposite {M N : Type _} [Mul M] [Mul N] (f : M →ₙ* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →ₙ* Nᵐᵒᵖ where
  toFun := op ∘ f
  map_mul' x y := by simp [(hf x y).eq]
#align mul_hom.to_opposite MulHom.toOpposite
#align add_hom.to_opposite AddHom.toOpposite
#align mul_hom.to_opposite_apply MulHom.toOpposite_apply
#align add_hom.to_opposite_apply AddHom.toOpposite_apply

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := { fullyApplied := false }))
      "An additive semigroup homomorphism `f : AddHom M N` such that `f x` additively
      commutes with `f y` for all `x`, `y` defines an additive semigroup homomorphism from `Mᵃᵒᵖ`."]
def MulHom.fromOpposite {M N : Type _} [Mul M] [Mul N] (f : M →ₙ* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →ₙ* N where
  toFun := f ∘ MulOpposite.unop
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq
#align mul_hom.from_opposite MulHom.fromOpposite
#align add_hom.from_opposite AddHom.fromOpposite
#align mul_hom.from_opposite_apply MulHom.fromOpposite_apply
#align add_hom.from_opposite_apply AddHom.fromOpposite_apply

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := { fullyApplied := false }))
      "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
      with `f y` for all `x, y` defines an additive monoid homomorphism to `Sᵃᵒᵖ`."]
def MonoidHom.toOpposite {M N : Type _} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →* Nᵐᵒᵖ where
  toFun := op ∘ f
  map_one' := congrArg op f.map_one
  map_mul' x y := by simp [(hf x y).eq]
#align monoid_hom.to_opposite MonoidHom.toOpposite
#align add_monoid_hom.to_opposite AddMonoidHom.toOpposite
#align monoid_hom.to_opposite_apply MonoidHom.toOpposite_apply
#align add_monoid_hom.to_opposite_apply AddMonoidHom.toOpposite_apply

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := { fullyApplied := false }))
      "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
      with `f y` for all `x`, `y` defines an additive monoid homomorphism from `Mᵃᵒᵖ`."]
def MonoidHom.fromOpposite {M N : Type _} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →* N where
  toFun := f ∘ MulOpposite.unop
  map_one' := f.map_one
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq
#align monoid_hom.from_opposite MonoidHom.fromOpposite
#align add_monoid_hom.from_opposite AddMonoidHom.fromOpposite
#align monoid_hom.from_opposite_apply MonoidHom.fromOpposite_apply
#align add_monoid_hom.from_opposite_apply AddMonoidHom.fromOpposite_apply

/-- The units of the opposites are equivalent to the opposites of the units. -/
@[to_additive
      "The additive units of the additive opposites are equivalent to the additive opposites
      of the additive units."]
def Units.opEquiv {M} [Monoid M] : Mᵐᵒᵖˣ ≃* Mˣᵐᵒᵖ where
  toFun u := op ⟨unop u, unop ↑u⁻¹, op_injective u.4, op_injective u.3⟩
  invFun := MulOpposite.rec' fun u => ⟨op ↑u, op ↑u⁻¹, unop_injective <| u.4, unop_injective u.3⟩
  map_mul' x y := unop_injective <| Units.ext <| rfl
  left_inv x := Units.ext <| by simp
  right_inv x := unop_injective <| Units.ext <| rfl
#align units.op_equiv Units.opEquiv
#align add_units.op_equiv AddUnits.opEquiv

@[to_additive (attr := simp)]
theorem Units.coe_unop_opEquiv {M} [Monoid M] (u : Mᵐᵒᵖˣ) :
    ((Units.opEquiv u).unop : M) = unop (u : Mᵐᵒᵖ) :=
  rfl
#align units.coe_unop_op_equiv Units.coe_unop_opEquiv
#align add_units.coe_unop_op_equiv AddUnits.coe_unop_opEquiv

@[to_additive (attr := simp)]
theorem Units.coe_opEquiv_symm {M} [Monoid M] (u : Mˣᵐᵒᵖ) :
    (Units.opEquiv.symm u : Mᵐᵒᵖ) = op (u.unop : M) :=
  rfl
#align units.coe_op_equiv_symm Units.coe_opEquiv_symm
#align add_units.coe_op_equiv_symm AddUnits.coe_opEquiv_symm

/-- A semigroup homomorphism `M →ₙ* N` can equivalently be viewed as a semigroup homomorphism
`Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive (attr := simps)
      "An additive semigroup homomorphism `AddHom M N` can equivalently be viewed as an
      additive semigroup homomorphism `AddHom Mᵃᵒᵖ Nᵃᵒᵖ`. This is the action of the
      (fully faithful)`ᵃᵒᵖ`-functor on morphisms."]
def MulHom.op {M N} [Mul M] [Mul N] : (M →ₙ* N) ≃ (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop,
      map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op,
      map_mul' := fun x y => congrArg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }
  left_inv _ := rfl
  right_inv _ := rfl
#align mul_hom.op MulHom.op
#align add_hom.op AddHom.op
#align mul_hom.op_symm_apply_apply MulHom.op_symm_apply_apply
#align mul_hom.op_apply_apply MulHom.op_apply_apply
#align add_hom.op_symm_apply_apply AddHom.op_symm_apply_apply
#align add_hom.op_apply_apply AddHom.op_apply_apply

/-- The 'unopposite' of a semigroup homomorphism `Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. Inverse to `MulHom.op`. -/
@[to_additive (attr := simp)
      "The 'unopposite' of an additive semigroup homomorphism `Mᵃᵒᵖ →ₙ+ Nᵃᵒᵖ`. Inverse
      to `AddHom.op`."]
def MulHom.unop {M N} [Mul M] [Mul N] : (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) ≃ (M →ₙ* N) :=
  MulHom.op.symm
#align mul_hom.unop MulHom.unop
#align add_hom.unop AddHom.unop

/-- An additive semigroup homomorphism `AddHom M N` can equivalently be viewed as an additive
homomorphism `AddHom Mᵐᵒᵖ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on
morphisms. -/
@[simps]
def AddHom.mulOp {M N} [Add M] [Add N] : AddHom M N ≃ AddHom Mᵐᵒᵖ Nᵐᵒᵖ where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ MulOpposite.unop,
      map_add' := fun x y => unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := MulOpposite.unop ∘ f ∘ MulOpposite.op,
      map_add' :=
        fun x y => congrArg MulOpposite.unop (f.map_add (MulOpposite.op x) (MulOpposite.op y)) }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_hom.mul_op AddHom.mulOp
#align add_hom.mul_op_symm_apply_apply AddHom.mulOp_symm_apply_apply
#align add_hom.mul_op_apply_apply AddHom.mulOp_apply_apply

/-- The 'unopposite' of an additive semigroup hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`AddHom.mul_op`. -/
@[simp]
def AddHom.mulUnop {α β} [Add α] [Add β] : AddHom αᵐᵒᵖ βᵐᵒᵖ ≃ AddHom α β :=
  AddHom.mulOp.symm
#align add_hom.mul_unop AddHom.mulUnop

/-- A monoid homomorphism `M →* N` can equivalently be viewed as a monoid homomorphism
`Mᵐᵒᵖ →* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive (attr := simps)
      "An additive monoid homomorphism `M →+ N` can equivalently be viewed as an
      additive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. This is the action of the (fully faithful)
      `ᵃᵒᵖ`-functor on morphisms."]
def MonoidHom.op {M N} [MulOneClass M] [MulOneClass N] : (M →* N) ≃ (Mᵐᵒᵖ →* Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop, map_one' := congrArg MulOpposite.op f.map_one,
      map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op, map_one' := congrArg unop f.map_one,
      map_mul' := fun x y => congrArg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }
  left_inv _ := rfl
  right_inv _ := rfl
#align monoid_hom.op MonoidHom.op
#align add_monoid_hom.op AddMonoidHom.op
#align monoid_hom.op_apply_apply MonoidHom.op_apply_apply
#align monoid_hom.op_symm_apply_apply MonoidHom.op_symm_apply_apply
#align add_monoid_hom.op_apply_apply AddMonoidHom.op_apply_apply
#align add_monoid_hom.op_symm_apply_apply AddMonoidHom.op_symm_apply_apply

/-- The 'unopposite' of a monoid homomorphism `Mᵐᵒᵖ →* Nᵐᵒᵖ`. Inverse to `MonoidHom.op`. -/
@[to_additive (attr := simp)
      "The 'unopposite' of an additive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. Inverse to
      `AddMonoidHom.op`."]
def MonoidHom.unop {M N} [MulOneClass M] [MulOneClass N] : (Mᵐᵒᵖ →* Nᵐᵒᵖ) ≃ (M →* N) :=
  MonoidHom.op.symm
#align monoid_hom.unop MonoidHom.unop
#align add_monoid_hom.unop AddMonoidHom.unop

/-- An additive homomorphism `M →+ N` can equivalently be viewed as an additive homomorphism
`Mᵐᵒᵖ →+ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def AddMonoidHom.mulOp {M N} [AddZeroClass M] [AddZeroClass N] : (M →+ N) ≃ (Mᵐᵒᵖ →+  Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ MulOpposite.unop, map_zero' := unop_injective f.map_zero,
      map_add' := fun x y => unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := MulOpposite.unop ∘ f ∘ MulOpposite.op,
      map_zero' := congrArg MulOpposite.unop f.map_zero,
      map_add' :=
        fun x y => congrArg MulOpposite.unop (f.map_add (MulOpposite.op x) (MulOpposite.op y)) }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.mul_op AddMonoidHom.mulOp
#align add_monoid_hom.mul_op_symm_apply_apply AddMonoidHom.mulOp_symm_apply_apply
#align add_monoid_hom.mul_op_apply_apply AddMonoidHom.mulOp_apply_apply

/-- The 'unopposite' of an additive monoid hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`AddMonoidHom.mul_op`. -/
@[simp]
def AddMonoidHom.mulUnop {α β} [AddZeroClass α] [AddZeroClass β] : (αᵐᵒᵖ →+ βᵐᵒᵖ) ≃ (α →+ β) :=
  AddMonoidHom.mulOp.symm
#align add_monoid_hom.mul_unop AddMonoidHom.mulUnop

/-- A iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
def AddEquiv.mulOp {α β} [Add α] [Add β] : α ≃+ β ≃ (αᵐᵒᵖ ≃+ βᵐᵒᵖ) where
  toFun f := opAddEquiv.symm.trans (f.trans opAddEquiv)
  invFun f := opAddEquiv.trans (f.trans opAddEquiv.symm)
  left_inv _ := rfl
  right_inv _ := rfl
#align add_equiv.mul_op AddEquiv.mulOp
#align add_equiv.mul_op_apply AddEquiv.mulOp_apply
#align add_equiv.mul_op_symm_apply AddEquiv.mulOp_symm_apply

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `AddEquiv.mul_op`. -/
@[simp]
def AddEquiv.mulUnop {α β} [Add α] [Add β] : αᵐᵒᵖ ≃+ βᵐᵒᵖ ≃ (α ≃+ β) :=
  AddEquiv.mulOp.symm
#align add_equiv.mul_unop AddEquiv.mulUnop

/-- A iso `α ≃* β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. -/
@[to_additive (attr := simps) "A iso `α ≃+ β` can equivalently be viewed as an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`."]
def MulEquiv.op {α β} [Mul α] [Mul β] : α ≃* β ≃ (αᵐᵒᵖ ≃* βᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop, invFun := MulOpposite.op ∘ f.symm ∘ unop,
      left_inv := fun x => unop_injective (f.symm_apply_apply x.unop),
      right_inv := fun x => unop_injective (f.apply_symm_apply x.unop),
      map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op, invFun := unop ∘ f.symm ∘ MulOpposite.op,
      left_inv := fun x => by simp,
      right_inv := fun x => by simp,
      map_mul' := fun x y => congr_arg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }
  left_inv _ := rfl
  right_inv _ := rfl
#align mul_equiv.op MulEquiv.op
#align add_equiv.op AddEquiv.op
#align mul_equiv.op_symm_apply_symm_apply MulEquiv.op_symm_apply_symmApply
#align mul_equiv.op_apply_apply MulEquiv.op_apply_apply
#align mul_equiv.op_apply_symm_apply MulEquiv.op_apply_symmApply
#align mul_equiv.op_symm_apply_apply MulEquiv.op_symm_apply_apply
#align add_equiv.op_symm_apply_symm_apply AddEquiv.op_symm_apply_symmApply
#align add_equiv.op_apply_apply AddEquiv.op_apply_apply
#align add_equiv.op_apply_symm_apply AddEquiv.op_apply_symmApply
#align add_equiv.op_symm_apply_apply AddEquiv.op_symm_apply_apply

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. Inverse to `MulEquiv.op`. -/
@[to_additive (attr := simp)
  "The 'unopposite' of an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`. Inverse to `AddEquiv.op`."]
def MulEquiv.unop {α β} [Mul α] [Mul β] : αᵐᵒᵖ ≃* βᵐᵒᵖ ≃ (α ≃* β) :=
  MulEquiv.op.symm
#align mul_equiv.unop MulEquiv.unop
#align add_equiv.unop AddEquiv.unop

section Ext

/-- This ext lemma changes equalities on `αᵐᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will apply
to an equality of `α →+ β` such as `Finsupp.addHom_ext'`. -/
@[ext]
theorem AddMonoidHom.mul_op_ext {α β} [AddZeroClass α] [AddZeroClass β] (f g : αᵐᵒᵖ →+ β)
    (h :
      f.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom =
        g.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom) :
    f = g :=
  AddMonoidHom.ext <| MulOpposite.rec fun x => (FunLike.congr_fun h : _) x
#align add_monoid_hom.mul_op_ext AddMonoidHom.mul_op_ext

end Ext
