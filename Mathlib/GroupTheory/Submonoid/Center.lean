/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.GroupTheory.Subsemigroup.Center

/-!
# Centers of monoids

## Main definitions

* `Submonoid.center`: the center of a monoid
* `AddSubmonoid.center`: the center of an additive monoid

We provide `Subgroup.center`, `AddSubgroup.center`, `Subsemiring.center`, and `Subring.center` in
other files.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Finset

namespace Submonoid

section MulOneClass

variable (M : Type*) [MulOneClass M]

/-- The center of a multiplication with unit `M` is the set of elements that commute with everything
in `M` -/
@[to_additive
/-- The center of an addition with zero `M` is the set of elements that commute with everything in
`M` -/]
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

@[to_additive]
instance (priority := low) : CommMonoid (Center M) where
  mul_assoc := Center.mul_assoc'

variable {M N} [MulOneClass N]

@[to_additive]
protected theorem center_prod {N : Type*} [MulOneClass N] :
    center (M × N) = prod (center M) (center N) :=
  SetLike.coe_injective Set.center_prod

@[to_additive]
protected theorem center_pi {ι : Type*} {M : ι → Type*} [Π i, MulOneClass (M i)] :
    center (Π i, M i) = pi .univ fun i ↦ center (M i) :=
  SetLike.coe_injective Set.center_pi

@[to_additive]
theorem map_center_le_center {F} [FunLike F M N] [MonoidHomClass F M N] {f : F}
    (hf : Function.Surjective f) : map f (center M) ≤ center N :=
  Set.image_center_subset hf

@[to_additive]
theorem comap_center_le_center {F} [FunLike F M N] [MonoidHomClass F M N] {f : F}
    (hf : Function.Injective f) : comap f (center N) ≤ center M :=
  Set.preimage_center_subset hf

@[to_additive (attr := simp)]
theorem map_center_eq {F} [EquivLike F M N] [MulEquivClass F M N] (f : F) :
    map f (center M) = center N :=
  SetLike.coe_injective (Set.image_center_eq f)

end MulOneClass

section Monoid

variable {M} [Monoid M]

@[to_additive]
instance : CommMonoid (Center M) :=
  {toMonoid := inferInstanceAs <| Monoid (center M), mul_comm}

@[to_additive (attr := simp)]
lemma _root_.Center.coe_npow (a : Center M) (n : ℕ) : (a ^ n).val = a.val ^ n := rfl

instance {M α : Type*} [Monoid M] [MulAction M α] : MulAction (Center M) α :=
  inferInstanceAs <| MulAction (center M) α

@[simp]
lemma _root_.Center.coe_smul {M α : Type*} [Monoid M] [MulAction M α] (z : Center M)
    (a : α) : z • a = z.val • a := rfl

instance {M α : Type*} [Monoid M] [MulAction M α] : SMulCommClass (Center M) M α where
  smul_comm c r v := by simp [smul_smul, Center.comm]

instance {M α : Type*} [Monoid M] [MulAction M α] : SMulCommClass M (Center M) α :=
  SMulCommClass.symm (Center M) M α

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
equivalence in general; one case where this holds is for groups with zero, which is covered in
`centerUnitsEquivUnitsCenter`. -/
@[to_additive (attr := simps! apply_coe_val)
  /-- For an additive monoid, the units of the center inject into the center of the units. -/]
def unitsCenterToCenterUnits [Monoid M] : (Submonoid.center M)ˣ →* Submonoid.center (Mˣ) :=
  (Units.map (Submonoid.center M).subtype).codRestrict _ <|
      fun u ↦ Submonoid.mem_center_iff.mpr <|
        fun r ↦ Units.ext <| by
        rw [Units.val_mul, Units.coe_map, Submonoid.coe_subtype, Units.val_mul, Units.coe_map,
          Submonoid.coe_subtype, u.1.prop.comm r]

@[to_additive]
theorem unitsCenterToCenterUnits_injective [Monoid M] :
    Function.Injective (unitsCenterToCenterUnits M) :=
  fun _a _b h => Units.ext <| Subtype.ext congr((Units.val ∘ Subtype.val) $h)

section congr

variable {M} {N : Type*}

/-- The center of isomorphic magmas are isomorphic. -/
@[to_additive (attr := simps!, deprecated "use `MulEquiv.toCenter` instead" (since := "2026-10-27"))
/-- The center of isomorphic additive magmas are isomorphic. -/]
def Subsemigroup.centerCongr [Mul M] [Mul N] (e : M ≃* N) : center M ≃* center N := e.toCenter

/-- The center of isomorphic monoids are isomorphic. -/
@[to_additive (attr := simps!, deprecated "use `MulEquiv.toCenter` instead" (since := "2026-10-27"))
/-- The center of isomorphic additive monoids are isomorphic. -/]
def Submonoid.centerCongr [MulOneClass M] [MulOneClass N] (e : M ≃* N) : center M ≃* center N :=
  e.toCenter

@[to_additive] theorem MulOpposite.op_mem_center_iff [Mul M] {x : M} :
    op x ∈ Set.center Mᵐᵒᵖ ↔ x ∈ Set.center M := by
  simp_rw [Set.mem_center_iff, isMulCentral_iff, MulOpposite.forall, ← op_mul, op_inj]; aesop

@[to_additive] theorem MulOpposite.unop_mem_center_iff [Mul M] {x : Mᵐᵒᵖ} :
    unop x ∈ Set.center M ↔ x ∈ Set.center Mᵐᵒᵖ :=
  op_mem_center_iff.symm

/-- The center of a magma is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps)]
def Center.toMulOpposite [Mul M] : Center M ≃* Center Mᵐᵒᵖ where
  toFun r := Center.mk _ (MulOpposite.op_mem_center_iff.mpr r.2)
  invFun r := Center.mk _ (MulOpposite.unop_mem_center_iff.mpr r.2)
  map_mul' r _ := Subtype.ext congr(MulOpposite.op $(r.2.1 _))

/-- The center of a magma is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps!,
deprecated "use `Center.toMulOpposite` instead" (since := "2026-10-27"))
/-- The center of an additive magma is isomorphic to the center of its opposite. -/]
def Subsemigroup.centerToMulOpposite [Mul M] : center M ≃* center Mᵐᵒᵖ := Center.toMulOpposite

/-- The center of a monoid is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps!,
deprecated "use `Center.toMulOpposite` instead" (since := "2026-10-27"))
/-- The center of an additive monoid is isomorphic to the center of its opposite. -/]
def Submonoid.centerToMulOpposite [MulOneClass M] : center M ≃* center Mᵐᵒᵖ := Center.toMulOpposite

end congr
