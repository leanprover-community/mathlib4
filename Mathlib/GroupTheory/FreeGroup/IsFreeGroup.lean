/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Eric Wieser, Joachim Breitner
-/
import Mathlib.GroupTheory.FreeGroup.Basic

#align_import group_theory.is_free_group from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Free groups structures on arbitrary types

This file defines a type class for type that are free groups, together with the usual operations.
The type class can be instantiated by providing an isomorphism to the canonical free group, or by
proving that the universal property holds.

For the explicit construction of free groups, see `GroupTheory/FreeGroup`.

## Main definitions

* `IsFreeGroup G` - a typeclass to indicate that `G` is free over some generators
* `IsFreeGroup.of` - the canonical injection of `G`'s generators into `G`
* `IsFreeGroup.lift` - the universal property of the free group

## Main results

* `IsFreeGroup.toFreeGroup` - any free group with generators `A` is equivalent to `FreeGroup A`.
* `IsFreeGroup.unique_lift` - the universal property of a free group
* `IsFreeGroup.ofUniqueLift` - constructing `IsFreeGroup` from the universal property

-/


universe u


/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4:
#[`MulEquiv] [] -/
/- Porting Note regarding the comment above:
The mathlib3 version makes `G` explicit in `IsFreeGroup.MulEquiv`. -/

/-- `IsFreeGroup G` means that `G` isomorphic to a free group. -/
class IsFreeGroup (G : Type u) [Group G] where
  /-- The generators of a free group. -/
  Generators : Type u
  /-- The multiplicative equivalence between "the" free group on the generators, and
  the given group `G`.
  Note: `IsFreeGroup.MulEquiv'` should not be used directly.
  `IsFreeGroup.MulEquiv` should be used instead because it makes `G` an explicit variable.-/
  MulEquiv' : FreeGroup Generators ≃* G
#align is_free_group IsFreeGroup

instance (X : Type*) : IsFreeGroup (FreeGroup X) where
  Generators := X
  MulEquiv' := MulEquiv.refl _

namespace IsFreeGroup

variable (G : Type*) [Group G] [IsFreeGroup G]

/-- Any free group is isomorphic to "the" free group. -/
def MulEquiv : FreeGroup (Generators G) ≃* G := IsFreeGroup.MulEquiv'

/-- Any free group is isomorphic to "the" free group. -/
@[simps!]
def toFreeGroup : G ≃* FreeGroup (Generators G) :=
  (MulEquiv G).symm
#align is_free_group.to_free_group IsFreeGroup.toFreeGroup
#align is_free_group.to_free_group_apply IsFreeGroup.toFreeGroup_apply
#align is_free_group.to_free_group_symm_apply IsFreeGroup.toFreeGroup_symm_apply

variable {G}

/-- The canonical injection of G's generators into G -/
def of : Generators G → G :=
  (MulEquiv G).toFun ∘ FreeGroup.of
#align is_free_group.of IsFreeGroup.of

@[simp]
theorem of_eq_freeGroup_of {A : Type u} : @of (FreeGroup A) _ _ = FreeGroup.of :=
  rfl
#align is_free_group.of_eq_free_group_of IsFreeGroup.of_eq_freeGroup_of

variable {H : Type*} [Group H]

/-- The equivalence between functions on the generators and group homomorphisms from a free group
given by those generators. -/
def lift : (Generators G → H) ≃ (G →* H) :=
  FreeGroup.lift.trans
    { toFun := fun f => f.comp (MulEquiv G).symm.toMonoidHom
      invFun := fun f => f.comp (MulEquiv G).toMonoidHom
      left_inv := fun f => by
        ext
        simp
      right_inv := fun f => by
        ext
        simp }
#align is_free_group.lift IsFreeGroup.lift

@[simp]
theorem lift'_eq_freeGroup_lift {A : Type u} : @lift (FreeGroup A) _ _ H _ = FreeGroup.lift :=
  rfl
#align is_free_group.lift'_eq_free_group_lift IsFreeGroup.lift'_eq_freeGroup_lift

@[simp]
theorem lift_of (f : Generators G → H) (a : Generators G) : lift f (of a) = f a :=
  congr_fun (lift.symm_apply_apply f) a
#align is_free_group.lift_of IsFreeGroup.lift_of

@[simp]
theorem lift_symm_apply (f : G →* H) (a : Generators G) : (lift.symm f) a = f (of a) :=
  rfl
#align is_free_group.lift_symm_apply IsFreeGroup.lift_symm_apply

@[ext 1050] --Porting note: increased priority, but deliberately less than for example
--`FreeProduct.ext_hom`
theorem ext_hom ⦃f g : G →* H⦄ (h : ∀ a : Generators G, f (of a) = g (of a)) : f = g :=
  lift.symm.injective (funext h)
#align is_free_group.ext_hom IsFreeGroup.ext_hom

/-- The universal property of a free group: A function from the generators of `G` to another
group extends in a unique way to a homomorphism from `G`.

Note that since `IsFreeGroup.lift` is expressed as a bijection, it already
expresses the universal property.  -/
theorem unique_lift (f : Generators G → H) : ∃! F : G →* H, ∀ a, F (of a) = f a := by
  simpa only [Function.funext_iff] using lift.symm.bijective.existsUnique f
#align is_free_group.unique_lift IsFreeGroup.unique_lift

/-- If a group satisfies the universal property of a free group, then it is a free group, where
the universal property is expressed as in `IsFreeGroup.lift` and its properties. -/
def ofLift {G : Type u} [Group G] (X : Type u) (of : X → G)
    (lift : ∀ {H : Type u} [Group H], (X → H) ≃ (G →* H))
    (lift_of : ∀ {H : Type u} [Group H], ∀ (f : X → H) (a), lift f (of a) = f a) : IsFreeGroup G
    where
  Generators := X
  MulEquiv' :=
    MonoidHom.toMulEquiv (FreeGroup.lift of) (lift FreeGroup.of)
      (by
        apply FreeGroup.ext_hom; intro x
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, FreeGroup.lift.of,
          lift_of])
      (by
        let lift_symm_of : ∀ {H : Type u} [Group H], ∀ (f : G →* H) (a), lift.symm f a = f (of a) :=
          by intro H _ f a; simp [← lift_of (lift.symm f)]
        apply lift.symm.injective; ext x
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, FreeGroup.lift.of,
          lift_of, lift_symm_of])
#align is_free_group.of_lift IsFreeGroup.ofLift

/-- If a group satisfies the universal property of a free group, then it is a free group, where
the universal property is expressed as in `IsFreeGroup.unique_lift`.  -/
noncomputable def ofUniqueLift {G : Type u} [Group G] (X : Type u) (of : X → G)
    (h : ∀ {H : Type u} [Group H] (f : X → H), ∃! F : G →* H, ∀ a, F (of a) = f a) :
    IsFreeGroup G :=
  let lift {H : Type u} [Group H] : (X → H) ≃ (G →* H) :=
    { toFun := fun f => Classical.choose (h f)
      invFun := fun F => F ∘ of
      left_inv := fun f => funext (Classical.choose_spec (h f)).left
      right_inv := fun F => ((Classical.choose_spec (h (F ∘ of))).right F fun _ => rfl).symm }
  let lift_of {H : Type u} [Group H] (f : X → H) (a : X) : lift f (of a) = f a :=
    congr_fun (lift.symm_apply_apply f) a
  ofLift X of @lift @lift_of
#align is_free_group.of_unique_lift IsFreeGroup.ofUniqueLift

/-- Being a free group transports across group isomorphisms. -/
def ofMulEquiv {H : Type _} [Group H] (h : G ≃* H) : IsFreeGroup H
    where
  Generators := Generators G
  MulEquiv' := (MulEquiv G).trans h
#align is_free_group.of_mul_equiv IsFreeGroup.ofMulEquiv

end IsFreeGroup
