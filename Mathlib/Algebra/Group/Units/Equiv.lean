/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Hom

#align_import algebra.hom.equiv.units.basic from "leanprover-community/mathlib"@"a95b16cbade0f938fc24abd05412bde1e84bab9b"

/-!
# Multiplicative and additive equivalence acting on units.
-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

variable {F α β A B M N P Q G H : Type*}

/-- A group is isomorphic to its group of units. -/
@[to_additive (attr := simps apply_val symm_apply)
"An additive group is isomorphic to its group of additive units"]
def toUnits [Group G] : G ≃* Gˣ where
  toFun x := ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩
  invFun x := x
  left_inv _ := rfl
  right_inv _ := Units.ext rfl
  map_mul' _ _ := Units.ext rfl
#align to_units toUnits
#align to_add_units toAddUnits

#align coe_to_units val_toUnits_apply
#align coe_to_add_units val_toAddUnits_apply

@[to_additive (attr := simp)]
lemma toUnits_val_apply {G : Type*} [Group G] (x : Gˣ) : toUnits (x : G) = x := by
  simp_rw [MulEquiv.apply_eq_iff_symm_apply, toUnits_symm_apply]

namespace Units

variable [Monoid M] [Monoid N] [Monoid P]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom,
    left_inv := fun u => ext <| h.left_inv u,
    right_inv := fun u => ext <| h.right_inv u }
#align units.map_equiv Units.mapEquiv

@[simp]
theorem mapEquiv_symm (h : M ≃* N) : (mapEquiv h).symm = mapEquiv h.symm :=
  rfl
#align units.map_equiv_symm Units.mapEquiv_symm

@[simp]
theorem coe_mapEquiv (h : M ≃* N) (x : Mˣ) : (mapEquiv h x : N) = h x :=
  rfl
#align units.coe_map_equiv Units.coe_mapEquiv

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive (attr := simps (config := .asFn) apply)
  "Left addition of an additive unit is a permutation of the underlying type."]
def mulLeft (u : Mˣ) : Equiv.Perm M where
  toFun x := u * x
  invFun x := u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left
#align units.mul_left Units.mulLeft
#align add_units.add_left AddUnits.addLeft
#align units.mul_left_apply Units.mulLeft_apply
#align add_units.add_left_apply AddUnits.addLeft_apply

@[to_additive (attr := simp)]
theorem mulLeft_symm (u : Mˣ) : u.mulLeft.symm = u⁻¹.mulLeft :=
  Equiv.ext fun _ => rfl
#align units.mul_left_symm Units.mulLeft_symm
#align add_units.add_left_symm AddUnits.addLeft_symm

@[to_additive]
theorem mulLeft_bijective (a : Mˣ) : Function.Bijective ((a * ·) : M → M) :=
  (mulLeft a).bijective
#align units.mul_left_bijective Units.mulLeft_bijective
#align add_units.add_left_bijective AddUnits.addLeft_bijective

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive (attr := simps (config := .asFn) apply)
"Right addition of an additive unit is a permutation of the underlying type."]
def mulRight (u : Mˣ) : Equiv.Perm M where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u
#align units.mul_right Units.mulRight
#align add_units.add_right AddUnits.addRight
#align units.mul_right_apply Units.mulRight_apply
#align add_units.add_right_apply AddUnits.addRight_apply

@[to_additive (attr := simp)]
theorem mulRight_symm (u : Mˣ) : u.mulRight.symm = u⁻¹.mulRight :=
  Equiv.ext fun _ => rfl
#align units.mul_right_symm Units.mulRight_symm
#align add_units.add_right_symm AddUnits.addRight_symm

@[to_additive]
theorem mulRight_bijective (a : Mˣ) : Function.Bijective ((· * a) : M → M) :=
  (mulRight a).bijective
#align units.mul_right_bijective Units.mulRight_bijective
#align add_units.add_right_bijective AddUnits.addRight_bijective

end Units

namespace Equiv

section Group

variable [Group G]

/-- Left multiplication in a `Group` is a permutation of the underlying type. -/
@[to_additive "Left addition in an `AddGroup` is a permutation of the underlying type."]
protected def mulLeft (a : G) : Perm G :=
  (toUnits a).mulLeft
#align equiv.mul_left Equiv.mulLeft
#align equiv.add_left Equiv.addLeft

@[to_additive (attr := simp)]
theorem coe_mulLeft (a : G) : ⇑(Equiv.mulLeft a) = (a * ·) :=
  rfl
#align equiv.coe_mul_left Equiv.coe_mulLeft
#align equiv.coe_add_left Equiv.coe_addLeft

-- Porting note: we don't put `@[simp]` on the additive version;
-- mysteriously simp can already prove that one (although not the multiplicative one)!
/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this.",
  simp, nolint simpNF]
theorem mulLeft_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G → G) = (a⁻¹ * ·) :=
  rfl
#align equiv.mul_left_symm_apply Equiv.mulLeft_symm_apply
#align equiv.add_left_symm_apply Equiv.addLeft_symm_apply

@[to_additive (attr := simp)]
theorem mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ :=
  ext fun _ => rfl
#align equiv.mul_left_symm Equiv.mulLeft_symm
#align equiv.add_left_symm Equiv.addLeft_symm

@[to_additive]
theorem _root_.Group.mulLeft_bijective (a : G) : Function.Bijective (a * ·) :=
  (Equiv.mulLeft a).bijective
#align group.mul_left_bijective Group.mulLeft_bijective
#align add_group.add_left_bijective AddGroup.addLeft_bijective

/-- Right multiplication in a `Group` is a permutation of the underlying type. -/
@[to_additive "Right addition in an `AddGroup` is a permutation of the underlying type."]
protected def mulRight (a : G) : Perm G :=
  (toUnits a).mulRight
#align equiv.mul_right Equiv.mulRight
#align equiv.add_right Equiv.addRight

@[to_additive (attr := simp)]
theorem coe_mulRight (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a :=
  rfl
#align equiv.coe_mul_right Equiv.coe_mulRight
#align equiv.coe_add_right Equiv.coe_addRight

@[to_additive (attr := simp)]
theorem mulRight_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ :=
  ext fun _ => rfl
#align equiv.mul_right_symm Equiv.mulRight_symm
#align equiv.add_right_symm Equiv.addRight_symm

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this.",
  simp, nolint simpNF]
theorem mulRight_symm_apply (a : G) : ((Equiv.mulRight a).symm : G → G) = fun x => x * a⁻¹ :=
  rfl
#align equiv.mul_right_symm_apply Equiv.mulRight_symm_apply
#align equiv.add_right_symm_apply Equiv.addRight_symm_apply

@[to_additive]
theorem _root_.Group.mulRight_bijective (a : G) : Function.Bijective (· * a) :=
  (Equiv.mulRight a).bijective
#align group.mul_right_bijective Group.mulRight_bijective
#align add_group.add_right_bijective AddGroup.addRight_bijective

/-- A version of `Equiv.mulLeft a b⁻¹` that is defeq to `a / b`. -/
@[to_additive (attr := simps) " A version of `Equiv.addLeft a (-b)` that is defeq to `a - b`. "]
protected def divLeft (a : G) : G ≃ G where
  toFun b := a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]
#align equiv.div_left Equiv.divLeft
#align equiv.sub_left Equiv.subLeft
#align equiv.div_left_apply Equiv.divLeft_apply
#align equiv.div_left_symm_apply Equiv.divLeft_symm_apply
#align equiv.sub_left_apply Equiv.subLeft_apply
#align equiv.sub_left_symm_apply Equiv.subLeft_symm_apply

@[to_additive]
theorem divLeft_eq_inv_trans_mulLeft (a : G) :
    Equiv.divLeft a = (Equiv.inv G).trans (Equiv.mulLeft a) :=
  ext fun _ => div_eq_mul_inv _ _
#align equiv.div_left_eq_inv_trans_mul_left Equiv.divLeft_eq_inv_trans_mulLeft
#align equiv.sub_left_eq_neg_trans_add_left Equiv.subLeft_eq_neg_trans_addLeft

/-- A version of `Equiv.mulRight a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive (attr := simps) " A version of `Equiv.addRight (-a) b` that is defeq to `b - a`. "]
protected def divRight (a : G) : G ≃ G where
  toFun b := b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]
#align equiv.div_right Equiv.divRight
#align equiv.sub_right Equiv.subRight
#align equiv.div_right_symm_apply Equiv.divRight_symm_apply
#align equiv.div_right_apply Equiv.divRight_apply
#align equiv.sub_right_symm_apply Equiv.subRight_symm_apply
#align equiv.sub_right_apply Equiv.subRight_apply

@[to_additive]
theorem divRight_eq_mulRight_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹ :=
  ext fun _ => div_eq_mul_inv _ _
#align equiv.div_right_eq_mul_right_inv Equiv.divRight_eq_mulRight_inv
#align equiv.sub_right_eq_add_right_neg Equiv.subRight_eq_addRight_neg

end Group

end Equiv

variable (α) in
/-- The `αˣ` type is equivalent to a subtype of `α × α`. -/
@[simps]
def unitsEquivProdSubtype [Monoid α] : αˣ ≃ {p : α × α // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} where
  toFun u := ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩
  invFun p := Units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext <| Prod.ext rfl rfl
#align units_equiv_prod_subtype unitsEquivProdSubtype
#align units_equiv_prod_subtype_apply_coe unitsEquivProdSubtype_apply_coe

-- Porting note: we don't put `@[simp]` on the additive version;
-- mysteriously simp can already prove that one (although not the multiplicative one)!
-- Porting note: `@[simps apply]` removed because right now it's generating lemmas which
-- aren't in simp normal form (they contain a `toFun`)
/-- In a `DivisionCommMonoid`, `Equiv.inv` is a `MulEquiv`. There is a variant of this
`MulEquiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[to_additive (attr := simps apply)
  "When the `AddGroup` is commutative, `Equiv.neg` is an `AddEquiv`."]
def MulEquiv.inv (G : Type*) [DivisionCommMonoid G] : G ≃* G :=
  { Equiv.inv G with toFun := Inv.inv, invFun := Inv.inv, map_mul' := mul_inv }
#align mul_equiv.inv MulEquiv.inv
#align add_equiv.neg AddEquiv.neg
#align mul_equiv.inv_apply MulEquiv.inv_apply
#align add_equiv.neg_apply AddEquiv.neg_apply

@[to_additive (attr := simp)]
theorem MulEquiv.inv_symm (G : Type*) [DivisionCommMonoid G] :
    (MulEquiv.inv G).symm = MulEquiv.inv G :=
  rfl
#align mul_equiv.inv_symm MulEquiv.inv_symm
-- Porting note: no `add_equiv.neg_symm` in `mathlib3`

@[to_additive]
protected
theorem MulEquiv.map_isUnit_iff {M N} [Monoid M] [Monoid N] [EquivLike F M N] [MonoidHomClass F M N]
    (f : F) {m : M} : IsUnit (f m) ↔ IsUnit m :=
  isUnit_map_of_leftInverse (MonoidHom.inverse (f : M →* N) (EquivLike.inv f)
    (EquivLike.left_inv f) <| EquivLike.right_inv f) (EquivLike.left_inv f)
