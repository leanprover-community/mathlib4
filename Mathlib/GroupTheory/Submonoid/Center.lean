/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.GroupTheory.Subsemigroup.Center

/-!
# Centers of monoids

## Main definitions

* `Submonoid.center`: the center of a monoid
* `AddSubmonoid.center`: the center of an additive monoid

We provide `Subgroup.center`, `AddSubgroup.center`, `Subsemiring.center`, and `Subring.center` in
other files.
-/

-- Guard against import creep
assert_not_exists Finset

namespace Submonoid

section MulOneClass

variable (M : Type*) [MulOneClass M]

/-- The center of a multiplication with unit `M` is the set of elements that commute with everything
in `M` -/
@[to_additive
      "The center of an addition with zero `M` is the set of elements that commute with everything
      in `M`"]
def center : Submonoid M where
  carrier := Set.center M
  one_mem' := Set.one_mem_center
  mul_mem' := Set.mul_mem_center

@[to_additive]
theorem coe_center : ↑(center M) = Set.center M :=
  rfl

@[to_additive (attr := simp) AddSubmonoid.center_toAddSubsemigroup]
theorem center_toSubsemigroup : (center M).toSubsemigroup = Subsemigroup.center M :=
  rfl

variable {M}

/-- The center of a multiplication with unit is commutative and associative.

This is not an instance as it forms an non-defeq diamond with `Submonoid.toMonoid` in the `npow`
field. -/
@[to_additive "The center of an addition with zero is commutative and associative."]
abbrev center.commMonoid' : CommMonoid (center M) :=
  { (center M).toMulOneClass, Subsemigroup.center.commSemigroup with }

end MulOneClass

section Monoid

variable {M} [Monoid M]

/-- The center of a monoid is commutative. -/
@[to_additive]
instance center.commMonoid : CommMonoid (center M) :=
  { (center M).toMonoid, Subsemigroup.center.commSemigroup with }

-- no instance diamond, unlike the primed version
example : center.commMonoid.toMonoid = Submonoid.toMonoid (center M) := by
  with_reducible_and_instances rfl

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] : Decidable (a ∈ center M) :=
  decidable_of_iff' _ mem_center_iff



/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smulCommClass_left : SMulCommClass (center M) M M where
  smul_comm m x y := Commute.left_comm (m.prop.comm x) y

/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smulCommClass_right : SMulCommClass M (center M) M :=
  SMulCommClass.symm _ _ _

/-! Note that `smulCommClass (center M) (center M) M` is already implied by
`Submonoid.smulCommClass_right` -/

example : SMulCommClass (center M) (center M) M := by infer_instance

end Monoid

section

variable (M : Type*) [CommMonoid M]

@[simp]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)

end

end Submonoid

variable (M)

/-- For a monoid, the units of the center inject into the center of the units. This is not an
equivalence in general; one case when it is is for groups with zero, which is covered in
`centerUnitsEquivUnitsCenter`. -/
@[to_additive (attr := simps! apply_coe_val)
  "For an additive monoid, the units of the center inject into the center of the units."]
def unitsCenterToCenterUnits [Monoid M] : (Submonoid.center M)ˣ →* Submonoid.center (Mˣ) :=
  (Units.map (Submonoid.center M).subtype).codRestrict _ <|
      fun u ↦ Submonoid.mem_center_iff.mpr <|
        fun r ↦ Units.ext <| by
        rw [Units.val_mul, Units.coe_map, Submonoid.coe_subtype, Units.val_mul, Units.coe_map,
          Submonoid.coe_subtype, u.1.prop.comm r]

@[to_additive]
theorem unitsCenterToCenterUnits_injective [Monoid M] :
    Function.Injective (unitsCenterToCenterUnits M) :=
  fun _a _b h => Units.ext <| Subtype.ext <| congr_arg (Units.val ∘ Subtype.val) h

section congr

variable {M} {N : Type*}

@[to_additive] theorem _root_.MulEquivClass.apply_mem_center {F} [EquivLike F M N] [Mul M] [Mul N]
    [MulEquivClass F M N] (e : F) {x : M} (hx : x ∈ Set.center M) : e x ∈ Set.center N := by
  let e := MulEquivClass.toMulEquiv e
  show e x ∈ Set.center N
  constructor <;>
  (intros; apply e.symm.injective;
    simp only [map_mul, e.symm_apply_apply, (isMulCentral_iff _).mp hx])

@[to_additive] theorem _root_.MulEquivClass.apply_mem_center_iff {F} [EquivLike F M N]
    [Mul M] [Mul N] [MulEquivClass F M N] (e : F) {x : M} :
    e x ∈ Set.center N ↔ x ∈ Set.center M :=
  ⟨(by simpa using MulEquivClass.apply_mem_center (MulEquivClass.toMulEquiv e).symm ·),
    MulEquivClass.apply_mem_center e⟩

/-- The center of isomorphic magmas are isomorphic. -/
@[to_additive (attr := simps) "The center of isomorphic additive magmas are isomorphic."]
def Subsemigroup.centerCongr [Mul M] [Mul N] (e : M ≃* N) : center M ≃* center N where
  toFun r := ⟨e r, MulEquivClass.apply_mem_center e r.2⟩
  invFun s := ⟨e.symm s, MulEquivClass.apply_mem_center e.symm s.2⟩
  left_inv _ := Subtype.ext (e.left_inv _)
  right_inv _ := Subtype.ext (e.right_inv _)
  map_mul' _ _ := Subtype.ext (map_mul ..)

/-- The center of isomorphic monoids are isomorphic. -/
@[to_additive (attr := simps!) "The center of isomorphic additive monoids are isomorphic."]
def Submonoid.centerCongr [MulOneClass M] [MulOneClass N] (e : M ≃* N) : center M ≃* center N :=
  Subsemigroup.centerCongr e

@[to_additive] theorem MulOpposite.op_mem_center_iff [Mul M] {x : M} :
    op x ∈ Set.center Mᵐᵒᵖ ↔ x ∈ Set.center M := by
  simp_rw [Set.mem_center_iff, isMulCentral_iff, MulOpposite.forall, ← op_mul, op_inj]; aesop

@[to_additive] theorem MulOpposite.unop_mem_center_iff [Mul M] {x : Mᵐᵒᵖ} :
    unop x ∈ Set.center M ↔ x ∈ Set.center Mᵐᵒᵖ :=
  op_mem_center_iff.symm

/-- The center of a magma is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps)
"The center of an additive magma is isomorphic to the center of its opposite."]
def Subsemigroup.centerToMulOpposite [Mul M] : center M ≃* center Mᵐᵒᵖ where
  toFun r := ⟨_, MulOpposite.op_mem_center_iff.mpr r.2⟩
  invFun r := ⟨_, MulOpposite.unop_mem_center_iff.mpr r.2⟩
  map_mul' r _ := Subtype.ext (congr_arg MulOpposite.op <| r.2.1 _)

/-- The center of a monoid is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps!)
"The center of an additive monoid is isomorphic to the center of its opposite. "]
def Submonoid.centerToMulOpposite [MulOneClass M] : center M ≃* center Mᵐᵒᵖ :=
  Subsemigroup.centerToMulOpposite

end congr
