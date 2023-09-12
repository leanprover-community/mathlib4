/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# The additive monoid on the skeleton of a category with binary biproducts

## Main results:

* `Skeleton.instAddCommMonoid`

-/

namespace CategoryTheory

universe v u

section
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

open Limits

/-- Transport `Limits.IsZero` along an equivalence. -/
theorem Limits.IsZero.transport (e : C ≌ D) {x : C} (hx : IsZero x) : IsZero (e.functor.obj x) where
  unique_to X := hx.unique_to (e.inverse.obj X) |>.map fun u => {
    default := e.functor.map u.default ≫ e.counit.app _
    uniq := fun Y => by
      dsimp only
      have h := u.uniq (e.unit.app _ ≫ e.inverse.map Y)
      rw [←h]
      simp_rw [Functor.map_comp, Equivalence.fun_inv_map, Functor.id_obj, Category.assoc,
        Equivalence.counit_app_functor, ←Functor.map_comp_assoc, Iso.inv_hom_id_app,
        Functor.id_obj, Functor.comp_obj, Category.comp_id, Iso.hom_inv_id_app, Functor.id_obj,
        Functor.map_id, Category.id_comp]
  }
  unique_from X := hx.unique_from (e.inverse.obj X) |>.map fun u => {
    default := e.counitInv.app _ ≫ e.functor.map u.default
    uniq := fun Y => by
      dsimp only
      have h := u.uniq (e.inverse.map Y ≫ e.unitInv.app _)
      rw [←h]
      simp_rw [Functor.map_comp, Equivalence.fun_inv_map, Functor.id_obj, Category.assoc,
        Equivalence.counitInv_functor_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]
  }

/-- Transport `Limits.HasZeroObject` along an equivalence. -/
theorem Limits.HasZeroObject.transport (e : C ≌ D) [Limits.HasZeroObject C] :
    Limits.HasZeroObject D where
  zero := let ⟨_Z, hZ⟩ := Limits.HasZeroObject.zero (C := C); ⟨_, Limits.IsZero.transport e hZ⟩

/-- Transport `Limits.HasZeroMorphisms` along an equivalence. -/
def Limits.HasZeroMorphisms.transport (e : C ≌ D) [Limits.HasZeroMorphisms C] :
    Limits.HasZeroMorphisms D where
  Zero X Y := ⟨e.counitInv.app _ ≫ e.functor.map 0 ≫ e.counit.app _⟩
  zero_comp X {Y Z} f := show (_ ≫ _ ≫ _) ≫ _ = _ ≫ _ ≫ _ by
    sorry
  comp_zero {X Y} Z f := show _ ≫ (_ ≫ _ ≫ _) = _ ≫ _ ≫ _ by
    sorry

/-- Transport `Limits.HasBinaryBiproduct` along an equivalence. -/
theorem Limits.HasBinaryBiproduct.transport
    (e : C ≌ D) [Limits.HasZeroMorphisms C] {X Y : D}
    [Limits.HasBinaryBiproduct (e.inverse.obj X) (e.inverse.obj Y)]
    [Limits.HasZeroMorphisms D] :
    Limits.HasBinaryBiproduct X Y where
  exists_binary_biproduct :=
    (Limits.HasBinaryBiproduct.exists_binary_biproduct
      (P := e.inverse.obj X) (Q := e.inverse.obj Y)).map fun d =>
      { bicone := sorry
        isBilimit := sorry }

end

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C] [Limits.HasBinaryBiproducts C] [Limits.HasZeroObject C]

/-- If `C` is monoidal and skeletal, it is a monoid.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def addCommMonoidOfSkeletal (hC : Skeletal C) : AddCommMonoid C where
  add X Y := (X ⊞ Y : C)
  toZero := CategoryTheory.Limits.HasZeroObject.zero' _
  zero_add X := hC ⟨(Limits.isoZeroBiprod (Limits.isZero_zero _)).symm⟩
  add_zero X := hC ⟨(Limits.isoBiprodZero (Limits.isZero_zero _)).symm⟩
  add_assoc X Y Z := hC ⟨Limits.biprod.associator X Y Z⟩
  add_comm X Y := hC ⟨Limits.biprod.braiding X Y⟩

instance : Limits.HasZeroObject (Skeleton C) :=
  Limits.HasZeroObject.transport (skeletonEquivalence C).symm

noncomputable instance : Limits.HasZeroMorphisms (Skeleton C) :=
  Limits.HasZeroMorphisms.transport (skeletonEquivalence C).symm

instance (X Y : Skeleton C) : Limits.HasBinaryBiproduct X Y :=
  Limits.HasBinaryBiproduct.transport (skeletonEquivalence C).symm

noncomputable instance : Limits.HasBinaryBiproducts (Skeleton C) where
  has_binary_biproduct := inferInstance
/--
The skeleton of a category with biproducts can be viewed as an additive monoid, where the addition
is given by the biproduct, and satisfies the monoid axioms since it is a skeleton.
-/
noncomputable instance Skeleton.instAddCommMonoid : AddCommMonoid (Skeleton C) :=
  addCommMonoidOfSkeletal (skeletonIsSkeleton _).skel
