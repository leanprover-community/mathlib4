/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Hom

/-!
# Multiplicative and additive equivalence acting on units.
-/

assert_not_exists MonoidWithZero DenselyOrdered

variable {F α M N G : Type*}

/-- A group is isomorphic to its group of units. -/
@[to_additive (attr := simps apply_val symm_apply)
"An additive group is isomorphic to its group of additive units"]
def toUnits [Group G] : G ≃* Gˣ where
  toFun x := ⟨x, x⁻¹, mul_inv_cancel _, inv_mul_cancel _⟩
  invFun x := x
  map_mul' _ _ := Units.ext rfl

@[to_additive (attr := simp)]
lemma toUnits_val_apply {G : Type*} [Group G] (x : Gˣ) : toUnits (x : G) = x := by
  simp_rw [MulEquiv.apply_eq_iff_symm_apply, toUnits_symm_apply]

namespace Units

variable [Monoid M] [Monoid N]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom,
    left_inv := fun u => ext <| h.left_inv u,
    right_inv := fun u => ext <| h.right_inv u }

@[simp]
theorem mapEquiv_symm (h : M ≃* N) : (mapEquiv h).symm = mapEquiv h.symm :=
  rfl

@[simp]
theorem coe_mapEquiv (h : M ≃* N) (x : Mˣ) : (mapEquiv h x : N) = h x :=
  rfl

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive (attr := simps -fullyApplied apply)
  "Left addition of an additive unit is a permutation of the underlying type."]
def mulLeft (u : Mˣ) : Equiv.Perm M where
  toFun x := u * x
  invFun x := u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left

@[to_additive (attr := simp)]
theorem mulLeft_symm (u : Mˣ) : u.mulLeft.symm = u⁻¹.mulLeft :=
  Equiv.ext fun _ => rfl

@[to_additive]
theorem mulLeft_bijective (a : Mˣ) : Function.Bijective ((a * ·) : M → M) :=
  (mulLeft a).bijective

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive (attr := simps -fullyApplied apply)
"Right addition of an additive unit is a permutation of the underlying type."]
def mulRight (u : Mˣ) : Equiv.Perm M where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u

@[to_additive (attr := simp)]
theorem mulRight_symm (u : Mˣ) : u.mulRight.symm = u⁻¹.mulRight :=
  Equiv.ext fun _ => rfl

@[to_additive]
theorem mulRight_bijective (a : Mˣ) : Function.Bijective ((· * a) : M → M) :=
  (mulRight a).bijective

end Units

namespace Equiv

section Group

variable [Group G]

/-- Left multiplication in a `Group` is a permutation of the underlying type. -/
@[to_additive "Left addition in an `AddGroup` is a permutation of the underlying type."]
protected def mulLeft (a : G) : Perm G :=
  (toUnits a).mulLeft

@[to_additive (attr := simp)]
theorem coe_mulLeft (a : G) : ⇑(Equiv.mulLeft a) = (a * ·) :=
  rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[to_additive (attr := simp) "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mulLeft_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G → G) = (a⁻¹ * ·) :=
  rfl

@[to_additive (attr := simp)]
theorem mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ :=
  ext fun _ => rfl

@[to_additive]
theorem _root_.Group.mulLeft_bijective (a : G) : Function.Bijective (a * ·) :=
  (Equiv.mulLeft a).bijective

/-- Right multiplication in a `Group` is a permutation of the underlying type. -/
@[to_additive "Right addition in an `AddGroup` is a permutation of the underlying type."]
protected def mulRight (a : G) : Perm G :=
  (toUnits a).mulRight

@[to_additive (attr := simp)]
theorem coe_mulRight (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a :=
  rfl

@[to_additive (attr := simp)]
theorem mulRight_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ :=
  ext fun _ => rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[to_additive (attr := simp) "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mulRight_symm_apply (a : G) : ((Equiv.mulRight a).symm : G → G) = fun x => x * a⁻¹ :=
  rfl

@[to_additive]
theorem _root_.Group.mulRight_bijective (a : G) : Function.Bijective (· * a) :=
  (Equiv.mulRight a).bijective

/-- A version of `Equiv.mulLeft a b⁻¹` that is defeq to `a / b`. -/
@[to_additive (attr := simps) " A version of `Equiv.addLeft a (-b)` that is defeq to `a - b`. "]
protected def divLeft (a : G) : G ≃ G where
  toFun b := a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
theorem divLeft_eq_inv_trans_mulLeft (a : G) :
    Equiv.divLeft a = (Equiv.inv G).trans (Equiv.mulLeft a) :=
  ext fun _ => div_eq_mul_inv _ _

/-- A version of `Equiv.mulRight a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive (attr := simps) " A version of `Equiv.addRight (-a) b` that is defeq to `b - a`. "]
protected def divRight (a : G) : G ≃ G where
  toFun b := b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
theorem divRight_eq_mulRight_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹ :=
  ext fun _ => div_eq_mul_inv _ _

end Group

end Equiv

variable (α) in
/-- The `αˣ` type is equivalent to a subtype of `α × α`. -/
@[simps]
def unitsEquivProdSubtype [Monoid α] : αˣ ≃ {p : α × α // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} where
  toFun u := ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩
  invFun p := Units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2

/-- In a `DivisionCommMonoid`, `Equiv.inv` is a `MulEquiv`. There is a variant of this
`MulEquiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[to_additive (attr := simps apply)
  "When the `AddGroup` is commutative, `Equiv.neg` is an `AddEquiv`."]
def MulEquiv.inv (G : Type*) [DivisionCommMonoid G] : G ≃* G :=
  { Equiv.inv G with toFun := Inv.inv, invFun := Inv.inv, map_mul' := mul_inv }

@[to_additive (attr := simp)]
theorem MulEquiv.inv_symm (G : Type*) [DivisionCommMonoid G] :
    (MulEquiv.inv G).symm = MulEquiv.inv G :=
  rfl

section EquivLike
variable [Monoid M] [Monoid N] [EquivLike F M N] [MulEquivClass F M N] (f : F) {x : M}

-- Higher priority to take over the non-additivisable `isUnit_map_iff`
@[to_additive (attr := simp high)]
lemma MulEquiv.isUnit_map : IsUnit (f x) ↔ IsUnit x where
  mp hx := by
    simpa using hx.map <| MonoidHom.mk ⟨EquivLike.inv f, EquivLike.injective f <| by simp⟩
      fun x y ↦ EquivLike.injective f <| by simp
  mpr := .map f

@[instance] theorem isLocalHom_equiv : IsLocalHom f where map_nonunit := by simp

end EquivLike
