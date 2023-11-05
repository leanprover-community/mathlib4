/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Opposites
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread

#align_import algebra.group.opposite from "leanprover-community/mathlib"@"0372d31fb681ef40a687506bc5870fd55ebc8bb9"

/-!
# Group structures on the multiplicative and additive opposites
-/


universe u v

variable (α : Type u)

namespace MulOpposite

/-!
### Additive structures on `αᵐᵒᵖ`
-/

@[to_additive]
instance natCast [NatCast α] : NatCast αᵐᵒᵖ :=
  ⟨fun n => op n⟩

@[to_additive]
instance intCast [IntCast α] : IntCast αᵐᵒᵖ :=
  ⟨fun n => op n⟩

instance addSemigroup [AddSemigroup α] : AddSemigroup αᵐᵒᵖ :=
  unop_injective.addSemigroup _ fun _ _ => rfl

instance addLeftCancelSemigroup [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup αᵐᵒᵖ :=
  unop_injective.addLeftCancelSemigroup _ fun _ _ => rfl

instance addRightCancelSemigroup [AddRightCancelSemigroup α] : AddRightCancelSemigroup αᵐᵒᵖ :=
  unop_injective.addRightCancelSemigroup _ fun _ _ => rfl

instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup αᵐᵒᵖ :=
  unop_injective.addCommSemigroup _ fun _ _ => rfl

instance addZeroClass [AddZeroClass α] : AddZeroClass αᵐᵒᵖ :=
  unop_injective.addZeroClass _ (by exact rfl) fun _ _ => rfl

instance addMonoid [AddMonoid α] : AddMonoid αᵐᵒᵖ :=
  unop_injective.addMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

instance addCommMonoid [AddCommMonoid α] : AddCommMonoid αᵐᵒᵖ :=
  unop_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance addMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne αᵐᵒᵖ :=
  { MulOpposite.addMonoid α, MulOpposite.one α, MulOpposite.natCast _ with
    natCast_zero := show op ((0 : ℕ) : α) = 0 by rw [Nat.cast_zero, op_zero]
    natCast_succ := show ∀ n, op ((n + 1 : ℕ) : α) = op ↑(n : ℕ) + 1 by simp }

instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵐᵒᵖ :=
  { MulOpposite.addMonoidWithOne α, MulOpposite.addCommMonoid α with }

instance subNegMonoid [SubNegMonoid α] : SubNegMonoid αᵐᵒᵖ :=
  unop_injective.subNegMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance addGroup [AddGroup α] : AddGroup αᵐᵒᵖ :=
  unop_injective.addGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) fun _ _ => rfl

instance addCommGroup [AddCommGroup α] : AddCommGroup αᵐᵒᵖ :=
  unop_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance addGroupWithOne [AddGroupWithOne α] : AddGroupWithOne αᵐᵒᵖ :=
  { MulOpposite.addMonoidWithOne α, MulOpposite.addGroup α with
    intCast := fun n => op n,
    intCast_ofNat := fun n => show op ((n : ℤ) : α) = op (n : α) by rw [Int.cast_ofNat],
    intCast_negSucc := fun n =>
      show op _ = op (-unop (op ((n + 1 : ℕ) : α))) by simp }

instance addCommGroupWithOne [AddCommGroupWithOne α] : AddCommGroupWithOne αᵐᵒᵖ :=
  { MulOpposite.addGroupWithOne α, MulOpposite.addCommGroup α with }

/-!
### Multiplicative structures on `αᵐᵒᵖ`

We also generate additive structures on `αᵃᵒᵖ` using `to_additive`
-/


@[to_additive]
instance isRightCancelMul [Mul α] [IsLeftCancelMul α] : IsRightCancelMul αᵐᵒᵖ where
  mul_right_cancel _ _ _ h := unop_injective <| mul_left_cancel <| op_injective h

@[to_additive]
instance isLeftCancelMul [Mul α] [IsRightCancelMul α] : IsLeftCancelMul αᵐᵒᵖ where
  mul_left_cancel _ _ _ h := unop_injective <| mul_right_cancel <| op_injective h

@[to_additive]
instance semigroup [Semigroup α] : Semigroup αᵐᵒᵖ where
  mul_assoc x y z := unop_injective <| Eq.symm <| mul_assoc (unop z) (unop y) (unop x)

@[to_additive]
instance leftCancelSemigroup [RightCancelSemigroup α] : LeftCancelSemigroup αᵐᵒᵖ where
  mul_left_cancel _ _ _ := mul_left_cancel

@[to_additive]
instance rightCancelSemigroup [LeftCancelSemigroup α] : RightCancelSemigroup αᵐᵒᵖ where
  mul_right_cancel _ _ _ := mul_right_cancel

@[to_additive]
instance commSemigroup [CommSemigroup α] : CommSemigroup αᵐᵒᵖ where
  mul_comm x y := unop_injective <| mul_comm (unop y) (unop x)

@[to_additive]
instance mulOneClass [MulOneClass α] : MulOneClass αᵐᵒᵖ :=
  { MulOpposite.mul α, MulOpposite.one α with
    one_mul := fun x => unop_injective <| mul_one <| unop x,
    mul_one := fun x => unop_injective <| one_mul <| unop x }

@[to_additive]
instance monoid [Monoid α] : Monoid αᵐᵒᵖ :=
  { MulOpposite.semigroup α, MulOpposite.mulOneClass α with
    npow := fun n x => op <| x.unop ^ n,
    npow_zero := fun x => unop_injective <| Monoid.npow_zero x.unop,
    npow_succ := fun n x => unop_injective <| pow_succ' x.unop n }

@[to_additive]
instance leftCancelMonoid [RightCancelMonoid α] : LeftCancelMonoid αᵐᵒᵖ :=
  { MulOpposite.leftCancelSemigroup α, MulOpposite.monoid α with }

@[to_additive]
instance rightCancelMonoid [LeftCancelMonoid α] : RightCancelMonoid αᵐᵒᵖ :=
  { MulOpposite.rightCancelSemigroup α, MulOpposite.monoid α with }

@[to_additive]
instance cancelMonoid [CancelMonoid α] : CancelMonoid αᵐᵒᵖ :=
  { MulOpposite.rightCancelMonoid α, MulOpposite.leftCancelMonoid α with }

@[to_additive]
instance commMonoid [CommMonoid α] : CommMonoid αᵐᵒᵖ :=
  { MulOpposite.monoid α, MulOpposite.commSemigroup α with }

@[to_additive]
instance cancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid αᵐᵒᵖ :=
  { MulOpposite.cancelMonoid α, MulOpposite.commMonoid α with }

@[to_additive AddOpposite.subNegMonoid]
instance divInvMonoid [DivInvMonoid α] : DivInvMonoid αᵐᵒᵖ :=
  { MulOpposite.monoid α, MulOpposite.inv α with
    zpow := fun n x => op <| x.unop ^ n,
    zpow_zero' := fun x => unop_injective <| DivInvMonoid.zpow_zero' x.unop,
    zpow_succ' := fun n x => unop_injective <| by
      simp only [Int.ofNat_eq_coe]
      rw [unop_op, zpow_ofNat, pow_succ', unop_mul, unop_op, zpow_ofNat],
    zpow_neg' := fun z x => unop_injective <| DivInvMonoid.zpow_neg' z x.unop }

@[to_additive AddOpposite.subtractionMonoid]
instance divisionMonoid [DivisionMonoid α] : DivisionMonoid αᵐᵒᵖ :=
  { MulOpposite.divInvMonoid α, MulOpposite.involutiveInv α with
    mul_inv_rev := fun _ _ => unop_injective <| mul_inv_rev _ _,
    inv_eq_of_mul := fun _ _ h => unop_injective <| inv_eq_of_mul_eq_one_left <| congr_arg unop h }

@[to_additive AddOpposite.subtractionCommMonoid]
instance divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid αᵐᵒᵖ :=
  { MulOpposite.divisionMonoid α, MulOpposite.commSemigroup α with }

@[to_additive]
instance group [Group α] : Group αᵐᵒᵖ :=
  { MulOpposite.divInvMonoid α with
    mul_left_inv := fun x => unop_injective <| mul_inv_self <| unop x }

@[to_additive]
instance commGroup [CommGroup α] : CommGroup αᵐᵒᵖ :=
  { MulOpposite.group α, MulOpposite.commMonoid α with }

variable {α}
@[to_additive (attr := simp, norm_cast)]
theorem op_natCast [NatCast α] (n : ℕ) : op (n : α) = n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem op_intCast [IntCast α] (n : ℤ) : op (n : α) = n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem unop_natCast [NatCast α] (n : ℕ) : unop (n : αᵐᵒᵖ) = n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem unop_intCast [IntCast α] (n : ℤ) : unop (n : αᵐᵒᵖ) = n :=
  rfl

@[to_additive (attr := simp)]
theorem unop_div [DivInvMonoid α] (x y : αᵐᵒᵖ) : unop (x / y) = (unop y)⁻¹ * unop x :=
  rfl

@[to_additive (attr := simp)]
theorem op_div [DivInvMonoid α] (x y : α) : op (x / y) = (op y)⁻¹ * op x := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
theorem semiconjBy_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y :=
  by simp only [SemiconjBy, ← op_mul, op_inj, eq_comm]

@[to_additive (attr := simp, nolint simpComm)]
theorem semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} :
    SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, semiconjBy_op]

attribute [nolint simpComm] AddOpposite.semiconjBy_unop

@[to_additive]
theorem _root_.SemiconjBy.op [Mul α] {a x y : α} (h : SemiconjBy a x y) :
    SemiconjBy (op a) (op y) (op x) :=
  semiconjBy_op.2 h

@[to_additive]
theorem _root_.SemiconjBy.unop [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y) :
    SemiconjBy (unop a) (unop y) (unop x) :=
  semiconjBy_unop.2 h

@[to_additive]
theorem _root_.Commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) :=
  SemiconjBy.op h

@[to_additive]
theorem Commute.unop [Mul α] {x y : αᵐᵒᵖ} (h : Commute x y) : Commute (unop x) (unop y) :=
  h.unop

@[to_additive (attr := simp)]
theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y :=
  semiconjBy_op

@[to_additive (attr := simp, nolint simpComm)]
theorem commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x y :=
  semiconjBy_unop

attribute [nolint simpComm] AddOpposite.commute_unop

/-- The function `MulOpposite.op` is an additive equivalence. -/
@[simps! (config := { fullyApplied := false, simpRhs := true }) apply symm_apply]
def opAddEquiv [Add α] : α ≃+ αᵐᵒᵖ :=
  { opEquiv with map_add' := fun _ _ => rfl }

@[simp]
theorem opAddEquiv_toEquiv [Add α] : ((opAddEquiv : α ≃+ αᵐᵒᵖ) : α ≃ αᵐᵒᵖ) = opEquiv := rfl

end MulOpposite

/-!
### Multiplicative structures on `αᵃᵒᵖ`
-/


namespace AddOpposite

instance semigroup [Semigroup α] : Semigroup αᵃᵒᵖ :=
  unop_injective.semigroup _ fun _ _ => rfl

instance leftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup αᵃᵒᵖ :=
  unop_injective.leftCancelSemigroup _ fun _ _ => rfl

instance rightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup αᵃᵒᵖ :=
  unop_injective.rightCancelSemigroup _ fun _ _ => rfl

instance commSemigroup [CommSemigroup α] : CommSemigroup αᵃᵒᵖ :=
  unop_injective.commSemigroup _ fun _ _ => rfl

instance mulOneClass [MulOneClass α] : MulOneClass αᵃᵒᵖ :=
  unop_injective.mulOneClass _ (by exact rfl) fun _ _ => rfl

instance pow {β} [Pow α β] : Pow αᵃᵒᵖ β where pow a b := op (unop a ^ b)

@[simp]
theorem op_pow {β} [Pow α β] (a : α) (b : β) : op (a ^ b) = op a ^ b :=
  rfl

@[simp]
theorem unop_pow {β} [Pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b :=
  rfl

instance monoid [Monoid α] : Monoid αᵃᵒᵖ :=
  unop_injective.monoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

instance commMonoid [CommMonoid α] : CommMonoid αᵃᵒᵖ :=
  unop_injective.commMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

instance divInvMonoid [DivInvMonoid α] : DivInvMonoid αᵃᵒᵖ :=
  unop_injective.divInvMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance group [Group α] : Group αᵃᵒᵖ :=
  unop_injective.group _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance commGroup [CommGroup α] : CommGroup αᵃᵒᵖ :=
  unop_injective.commGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

-- NOTE: `addMonoidWithOne α → addMonoidWithOne αᵃᵒᵖ` does not hold
instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵃᵒᵖ :=
  { AddOpposite.addCommMonoid α, AddOpposite.one, AddOpposite.natCast α with
    natCast_zero := show op ((0 : ℕ) : α) = 0 by rw [Nat.cast_zero, op_zero]
    natCast_succ := show ∀ n, op ((n + 1 : ℕ) : α) = op ↑(n : ℕ) + 1 by simp [add_comm] }

instance addCommGroupWithOne [AddCommGroupWithOne α] : AddCommGroupWithOne αᵃᵒᵖ :=
  { AddOpposite.addCommMonoidWithOne α, AddOpposite.addCommGroup α, AddOpposite.intCast α with
    intCast_ofNat := λ _ ↦ congr_arg op $ Int.cast_ofNat _
    intCast_negSucc := λ _ ↦ congr_arg op $ Int.cast_negSucc _ }

variable {α}

/-- The function `AddOpposite.op` is a multiplicative equivalence. -/
@[simps! (config := { fullyApplied := false, simpRhs := true })]
def opMulEquiv [Mul α] : α ≃* αᵃᵒᵖ :=
  { opEquiv with map_mul' := fun _ _ => rfl }

@[simp]
theorem opMulEquiv_toEquiv [Mul α] : ((opMulEquiv : α ≃* αᵃᵒᵖ) : α ≃ αᵃᵒᵖ) = opEquiv :=
  rfl

end AddOpposite

open MulOpposite

/-- Inversion on a group is a `MulEquiv` to the opposite group. When `G` is commutative, there is
`MulEquiv.inv`. -/
@[to_additive (attr := simps! (config := { fullyApplied := false, simpRhs := true }))
      "Negation on an additive group is an `AddEquiv` to the opposite group. When `G`
      is commutative, there is `AddEquiv.inv`."]
def MulEquiv.inv' (G : Type*) [DivisionMonoid G] : G ≃* Gᵐᵒᵖ :=
  { (Equiv.inv G).trans opEquiv with map_mul' := fun x y => unop_injective <| mul_inv_rev x y }

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := { fullyApplied := false }))
      "An additive semigroup homomorphism `f : AddHom M N` such that `f x` additively
      commutes with `f y` for all `x, y` defines an additive semigroup homomorphism to `Sᵃᵒᵖ`."]
def MulHom.toOpposite {M N : Type*} [Mul M] [Mul N] (f : M →ₙ* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →ₙ* Nᵐᵒᵖ where
  toFun := op ∘ f
  map_mul' x y := by simp [(hf x y).eq]

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := { fullyApplied := false }))
      "An additive semigroup homomorphism `f : AddHom M N` such that `f x` additively
      commutes with `f y` for all `x`, `y` defines an additive semigroup homomorphism from `Mᵃᵒᵖ`."]
def MulHom.fromOpposite {M N : Type*} [Mul M] [Mul N] (f : M →ₙ* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →ₙ* N where
  toFun := f ∘ MulOpposite.unop
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := { fullyApplied := false }))
      "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
      with `f y` for all `x, y` defines an additive monoid homomorphism to `Sᵃᵒᵖ`."]
def MonoidHom.toOpposite {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →* Nᵐᵒᵖ where
  toFun := op ∘ f
  map_one' := congrArg op f.map_one
  map_mul' x y := by simp [(hf x y).eq]

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := { fullyApplied := false }))
      "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
      with `f y` for all `x`, `y` defines an additive monoid homomorphism from `Mᵃᵒᵖ`."]
def MonoidHom.fromOpposite {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →* N where
  toFun := f ∘ MulOpposite.unop
  map_one' := f.map_one
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq

/-- The units of the opposites are equivalent to the opposites of the units. -/
@[to_additive
      "The additive units of the additive opposites are equivalent to the additive opposites
      of the additive units."]
def Units.opEquiv {M} [Monoid M] : Mᵐᵒᵖˣ ≃* Mˣᵐᵒᵖ where
  toFun u := op ⟨unop u, unop ↑u⁻¹, op_injective u.4, op_injective u.3⟩
  invFun := MulOpposite.rec' fun u => ⟨op ↑u, op ↑u⁻¹, unop_injective <| u.4, unop_injective u.3⟩
  map_mul' x y := unop_injective <| Units.ext <| rfl
  left_inv x := Units.ext <| by simp
  right_inv x := unop_injective <| Units.ext <| by rfl

@[to_additive (attr := simp)]
theorem Units.coe_unop_opEquiv {M} [Monoid M] (u : Mᵐᵒᵖˣ) :
    ((Units.opEquiv u).unop : M) = unop (u : Mᵐᵒᵖ) :=
  rfl

@[to_additive (attr := simp)]
theorem Units.coe_opEquiv_symm {M} [Monoid M] (u : Mˣᵐᵒᵖ) :
    (Units.opEquiv.symm u : Mᵐᵒᵖ) = op (u.unop : M) :=
  rfl

@[to_additive]
nonrec theorem IsUnit.op {M} [Monoid M] {m : M} (h : IsUnit m) : IsUnit (op m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨Units.opEquiv.symm (op u), rfl⟩

@[to_additive]
nonrec theorem IsUnit.unop {M} [Monoid M] {m : Mᵐᵒᵖ} (h : IsUnit m) : IsUnit (unop m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨unop (Units.opEquiv u), rfl⟩

@[to_additive (attr := simp)]
theorem isUnit_op {M} [Monoid M] {m : M} : IsUnit (op m) ↔ IsUnit m :=
  ⟨IsUnit.unop, IsUnit.op⟩

@[to_additive (attr := simp)]
theorem isUnit_unop {M} [Monoid M] {m : Mᵐᵒᵖ} : IsUnit (unop m) ↔ IsUnit m :=
  ⟨IsUnit.op, IsUnit.unop⟩

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

/-- The 'unopposite' of a semigroup homomorphism `Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. Inverse to `MulHom.op`. -/
@[to_additive (attr := simp)
      "The 'unopposite' of an additive semigroup homomorphism `Mᵃᵒᵖ →ₙ+ Nᵃᵒᵖ`. Inverse
      to `AddHom.op`."]
def MulHom.unop {M N} [Mul M] [Mul N] : (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) ≃ (M →ₙ* N) :=
  MulHom.op.symm

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

/-- The 'unopposite' of an additive semigroup hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`AddHom.mul_op`. -/
@[simp]
def AddHom.mulUnop {α β} [Add α] [Add β] : AddHom αᵐᵒᵖ βᵐᵒᵖ ≃ AddHom α β :=
  AddHom.mulOp.symm

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

/-- The 'unopposite' of a monoid homomorphism `Mᵐᵒᵖ →* Nᵐᵒᵖ`. Inverse to `MonoidHom.op`. -/
@[to_additive (attr := simp)
      "The 'unopposite' of an additive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. Inverse to
      `AddMonoidHom.op`."]
def MonoidHom.unop {M N} [MulOneClass M] [MulOneClass N] : (Mᵐᵒᵖ →* Nᵐᵒᵖ) ≃ (M →* N) :=
  MonoidHom.op.symm

/-- A monoid is isomorphic to the opposite of its opposite. -/
@[to_additive (attr := simps!)
      "A additive monoid is isomorphic to the opposite of its opposite."]
def MulEquiv.opOp (M : Type*) [Mul M] : M ≃* Mᵐᵒᵖᵐᵒᵖ where
  __ := MulOpposite.opEquiv.trans MulOpposite.opEquiv
  map_mul' _ _ := rfl

/-- An additive homomorphism `M →+ N` can equivalently be viewed as an additive homomorphism
`Mᵐᵒᵖ →+ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def AddMonoidHom.mulOp {M N} [AddZeroClass M] [AddZeroClass N] : (M →+ N) ≃ (Mᵐᵒᵖ →+ Nᵐᵒᵖ) where
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

/-- The 'unopposite' of an additive monoid hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`AddMonoidHom.mul_op`. -/
@[simp]
def AddMonoidHom.mulUnop {α β} [AddZeroClass α] [AddZeroClass β] : (αᵐᵒᵖ →+ βᵐᵒᵖ) ≃ (α →+ β) :=
  AddMonoidHom.mulOp.symm

/-- An iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
def AddEquiv.mulOp {α β} [Add α] [Add β] : α ≃+ β ≃ (αᵐᵒᵖ ≃+ βᵐᵒᵖ) where
  toFun f := opAddEquiv.symm.trans (f.trans opAddEquiv)
  invFun f := opAddEquiv.trans (f.trans opAddEquiv.symm)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `AddEquiv.mul_op`. -/
@[simp]
def AddEquiv.mulUnop {α β} [Add α] [Add β] : αᵐᵒᵖ ≃+ βᵐᵒᵖ ≃ (α ≃+ β) :=
  AddEquiv.mulOp.symm

/-- An iso `α ≃* β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. -/
@[to_additive (attr := simps)
  "An iso `α ≃+ β` can equivalently be viewed as an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`."]
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

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. Inverse to `MulEquiv.op`. -/
@[to_additive (attr := simp)
  "The 'unopposite' of an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`. Inverse to `AddEquiv.op`."]
def MulEquiv.unop {α β} [Mul α] [Mul β] : αᵐᵒᵖ ≃* βᵐᵒᵖ ≃ (α ≃* β) :=
  MulEquiv.op.symm

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
  AddMonoidHom.ext <| MulOpposite.rec' fun x => (FunLike.congr_fun h : _) x

end Ext
