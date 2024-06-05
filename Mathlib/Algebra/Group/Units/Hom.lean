/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Units

#align_import algebra.hom.units from "leanprover-community/mathlib"@"a07d750983b94c530ab69a726862c2ab6802b38c"

/-!
# Monoid homomorphisms and units

This file allows to lift monoid homomorphisms to group homomorphisms of their units subgroups. It
also contains unrelated results about `Units` that depend on `MonoidHom`.

## Main declarations

* `Units.map`: Turn a homomorphism from `α` to `β` monoids into a homomorphism from `αˣ` to `βˣ`.
* `MonoidHom.toHomUnits`: Turn a homomorphism from a group `α` to `β` into a homomorphism from
  `α` to `βˣ`.
-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

open Function

universe u v w

section MonoidHomClass

/-- If two homomorphisms from a division monoid to a monoid are equal at a unit `x`, then they are
equal at `x⁻¹`. -/
@[to_additive
  "If two homomorphisms from a subtraction monoid to an additive monoid are equal at an
  additive unit `x`, then they are equal at `-x`."]
theorem IsUnit.eq_on_inv {F G N} [DivisionMonoid G] [Monoid N] [FunLike F G N]
    [MonoidHomClass F G N] {x : G} (hx : IsUnit x) (f g : F) (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  left_inv_eq_right_inv (map_mul_eq_one f hx.inv_mul_cancel)
    (h.symm ▸ map_mul_eq_one g (hx.mul_inv_cancel))
#align is_unit.eq_on_inv IsUnit.eq_on_inv
#align is_add_unit.eq_on_neg IsAddUnit.eq_on_neg

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[to_additive
    "If two homomorphism from an additive group to an additive monoid are equal at `x`,
    then they are equal at `-x`."]
theorem eq_on_inv {F G M} [Group G] [Monoid M] [FunLike F G M] [MonoidHomClass F G M]
    (f g : F) {x : G} (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  (Group.isUnit x).eq_on_inv f g h
#align eq_on_inv eq_on_inv
#align eq_on_neg eq_on_neg

end MonoidHomClass

namespace Units

variable {α : Type*} {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

/-- The group homomorphism on units induced by a `MonoidHom`. -/
@[to_additive "The additive homomorphism on `AddUnit`s induced by an `AddMonoidHom`."]
def map (f : M →* N) : Mˣ →* Nˣ :=
  MonoidHom.mk'
    (fun u => ⟨f u.val, f u.inv,
      by rw [← f.map_mul, u.val_inv, f.map_one],
      by rw [← f.map_mul, u.inv_val, f.map_one]⟩)
    fun x y => ext (f.map_mul x y)
#align units.map Units.map
#align add_units.map AddUnits.map

@[to_additive (attr := simp)]
theorem coe_map (f : M →* N) (x : Mˣ) : ↑(map f x) = f x := rfl
#align units.coe_map Units.coe_map
#align add_units.coe_map AddUnits.coe_map

@[to_additive (attr := simp)]
theorem coe_map_inv (f : M →* N) (u : Mˣ) : ↑(map f u)⁻¹ = f ↑u⁻¹ := rfl
#align units.coe_map_inv Units.coe_map_inv
#align add_units.coe_map_neg AddUnits.coe_map_neg

@[to_additive (attr := simp)]
theorem map_comp (f : M →* N) (g : N →* P) : map (g.comp f) = (map g).comp (map f) := rfl
#align units.map_comp Units.map_comp
#align add_units.map_comp AddUnits.map_comp

@[to_additive]
lemma map_injective {f : M →* N} (hf : Function.Injective f) :
    Function.Injective (map f) := fun _ _ e => ext (hf (congr_arg val e))

variable (M)

@[to_additive (attr := simp)]
theorem map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ := by ext; rfl
#align units.map_id Units.map_id
#align add_units.map_id AddUnits.map_id

/-- Coercion `Mˣ → M` as a monoid homomorphism. -/
@[to_additive "Coercion `AddUnits M → M` as an AddMonoid homomorphism."]
def coeHom : Mˣ →* M where
  toFun := Units.val; map_one' := val_one; map_mul' := val_mul
#align units.coe_hom Units.coeHom
#align add_units.coe_hom AddUnits.coeHom

variable {M}

@[to_additive (attr := simp)]
theorem coeHom_apply (x : Mˣ) : coeHom M x = ↑x := rfl
#align units.coe_hom_apply Units.coeHom_apply
#align add_units.coe_hom_apply AddUnits.coeHom_apply

section DivisionMonoid

variable [DivisionMonoid α]

@[to_additive (attr := simp, norm_cast)]
theorem val_zpow_eq_zpow_val : ∀ (u : αˣ) (n : ℤ), ((u ^ n : αˣ) : α) = (u : α) ^ n :=
  (Units.coeHom α).map_zpow
#align units.coe_zpow Units.val_zpow_eq_zpow_val
#align add_units.coe_zsmul AddUnits.val_zsmul_eq_zsmul_val

@[to_additive (attr := simp)]
theorem _root_.map_units_inv {F : Type*} [FunLike F M α] [MonoidHomClass F M α]
    (f : F) (u : Units M) :
    f ↑u⁻¹ = (f u)⁻¹ := ((f : M →* α).comp (Units.coeHom M)).map_inv u
#align map_units_inv map_units_inv
#align map_add_units_neg map_addUnits_neg

end DivisionMonoid

/-- If a map `g : M → Nˣ` agrees with a homomorphism `f : M →* N`, then
this map is a monoid homomorphism too. -/
@[to_additive
  "If a map `g : M → AddUnits N` agrees with a homomorphism `f : M →+ N`, then this map
  is an AddMonoid homomorphism too."]
def liftRight (f : M →* N) (g : M → Nˣ) (h : ∀ x, ↑(g x) = f x) : M →* Nˣ where
  toFun := g
  map_one' := by ext; rw [h 1]; exact f.map_one
  map_mul' x y := Units.ext <| by simp only [h, val_mul, f.map_mul]
#align units.lift_right Units.liftRight
#align add_units.lift_right AddUnits.liftRight

@[to_additive (attr := simp)]
theorem coe_liftRight {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    (liftRight f g h x : N) = f x := h x
#align units.coe_lift_right Units.coe_liftRight
#align add_units.coe_lift_right AddUnits.coe_liftRight

@[to_additive (attr := simp)]
theorem mul_liftRight_inv {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    f x * ↑(liftRight f g h x)⁻¹ = 1 := by
  rw [Units.mul_inv_eq_iff_eq_mul, one_mul, coe_liftRight]
#align units.mul_lift_right_inv Units.mul_liftRight_inv
#align add_units.add_lift_right_neg AddUnits.add_liftRight_neg

@[to_additive (attr := simp)]
theorem liftRight_inv_mul {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    ↑(liftRight f g h x)⁻¹ * f x = 1 := by
  rw [Units.inv_mul_eq_iff_eq_mul, mul_one, coe_liftRight]
#align units.lift_right_inv_mul Units.liftRight_inv_mul
#align add_units.lift_right_neg_add AddUnits.liftRight_neg_add

end Units

namespace MonoidHom

/-- If `f` is a homomorphism from a group `G` to a monoid `M`,
then its image lies in the units of `M`,
and `f.toHomUnits` is the corresponding monoid homomorphism from `G` to `Mˣ`. -/
@[to_additive
  "If `f` is a homomorphism from an additive group `G` to an additive monoid `M`,
  then its image lies in the `AddUnits` of `M`,
  and `f.toHomUnits` is the corresponding homomorphism from `G` to `AddUnits M`."]
def toHomUnits {G M : Type*} [Group G] [Monoid M] (f : G →* M) : G →* Mˣ :=
  Units.liftRight f (fun g => ⟨f g, f g⁻¹, map_mul_eq_one f (mul_inv_self _),
    map_mul_eq_one f (inv_mul_self _)⟩)
    fun _ => rfl
#align monoid_hom.to_hom_units MonoidHom.toHomUnits
#align add_monoid_hom.to_hom_add_units AddMonoidHom.toHomAddUnits

@[to_additive (attr := simp)]
theorem coe_toHomUnits {G M : Type*} [Group G] [Monoid M] (f : G →* M) (g : G) :
    (f.toHomUnits g : M) = f g := rfl
#align monoid_hom.coe_to_hom_units MonoidHom.coe_toHomUnits
#align add_monoid_hom.coe_to_hom_add_units AddMonoidHom.coe_toHomAddUnits

end MonoidHom

namespace IsUnit

variable {F G α M N : Type*} [FunLike F M N] [FunLike G N M]

section Monoid

variable [Monoid M] [Monoid N]

@[to_additive]
theorem map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x) := by
  rcases h with ⟨y, rfl⟩; exact (Units.map (f : M →* N) y).isUnit
#align is_unit.map IsUnit.map
#align is_add_unit.map IsAddUnit.map

@[to_additive]
theorem of_leftInverse [MonoidHomClass G N M] {f : F} {x : M} (g : G)
    (hfg : Function.LeftInverse g f) (h : IsUnit (f x)) : IsUnit x := by
  simpa only [hfg x] using h.map g
#align is_unit.of_left_inverse IsUnit.of_leftInverse
#align is_add_unit.of_left_inverse IsAddUnit.of_leftInverse

@[to_additive]
theorem _root_.isUnit_map_of_leftInverse [MonoidHomClass F M N] [MonoidHomClass G N M]
    {f : F} {x : M} (g : G) (hfg : Function.LeftInverse g f) :
    IsUnit (f x) ↔ IsUnit x := ⟨of_leftInverse g hfg, map _⟩
#align is_unit_map_of_left_inverse isUnit_map_of_leftInverse
#align is_add_unit_map_of_left_inverse isAddUnit_map_of_leftInverse

/-- If a homomorphism `f : M →* N` sends each element to an `IsUnit`, then it can be lifted
to `f : M →* Nˣ`. See also `Units.liftRight` for a computable version. -/
@[to_additive
  "If a homomorphism `f : M →+ N` sends each element to an `IsAddUnit`, then it can be
  lifted to `f : M →+ AddUnits N`. See also `AddUnits.liftRight` for a computable version."]
noncomputable def liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) : M →* Nˣ :=
  (Units.liftRight f fun x => (hf x).unit) fun _ => rfl
#align is_unit.lift_right IsUnit.liftRight
#align is_add_unit.lift_right IsAddUnit.liftRight

@[to_additive]
theorem coe_liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) (x) :
    (IsUnit.liftRight f hf x : N) = f x := rfl
#align is_unit.coe_lift_right IsUnit.coe_liftRight
#align is_add_unit.coe_lift_right IsAddUnit.coe_liftRight

@[to_additive (attr := simp)]
theorem mul_liftRight_inv (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    f x * ↑(IsUnit.liftRight f h x)⁻¹ = 1 := Units.mul_liftRight_inv (by intro; rfl) x
#align is_unit.mul_lift_right_inv IsUnit.mul_liftRight_inv
#align is_add_unit.add_lift_right_neg IsAddUnit.add_liftRight_neg

@[to_additive (attr := simp)]
theorem liftRight_inv_mul (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    ↑(IsUnit.liftRight f h x)⁻¹ * f x = 1 := Units.liftRight_inv_mul (by intro; rfl) x
#align is_unit.lift_right_inv_mul IsUnit.liftRight_inv_mul
#align is_add_unit.lift_right_neg_add IsAddUnit.liftRight_neg_add

end Monoid
end IsUnit
