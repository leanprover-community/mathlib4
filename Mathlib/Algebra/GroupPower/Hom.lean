/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Power as a monoid hom
-/

variable {α : Type*}

section CommMonoid
variable [CommMonoid α]

/-- The `n`th power map on a commutative monoid for a natural `n`, considered as a morphism of
monoids. -/
@[to_additive (attr := simps) "Multiplication by a natural `n` on a commutative additive monoid,
considered as a morphism of additive monoids."]
def powMonoidHom (n : ℕ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_pow _
  map_mul' a b := mul_pow a b n
#align pow_monoid_hom powMonoidHom
#align nsmul_add_monoid_hom nsmulAddMonoidHom
#align pow_monoid_hom_apply powMonoidHom_apply
#align nsmul_add_monoid_hom_apply nsmulAddMonoidHom_apply

end CommMonoid

section DivisionCommMonoid
variable [DivisionCommMonoid α]

/-- The `n`-th power map (for an integer `n`) on a commutative group, considered as a group
homomorphism. -/
@[to_additive (attr := simps) "Multiplication by an integer `n` on a commutative additive group,
considered as an additive group homomorphism."]
def zpowGroupHom (n : ℤ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n
#align zpow_group_hom zpowGroupHom
#align zsmul_add_group_hom zsmulAddGroupHom
#align zpow_group_hom_apply zpowGroupHom_apply
#align zsmul_add_group_hom_apply zsmulAddGroupHom_apply

end DivisionCommMonoid
