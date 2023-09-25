/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# The additive monoid on the skeleton of a category with binary biproducts

## Main results:

* `Skeleton.instAddCommMonoid`

-/

namespace CategoryTheory

universe v u v' u'

section
variable {C D : Type u} {E : Type u'} [Category.{v} C] [Category.{v} D] [Category.{v'} E]

open Limits

/-- Transport `Limits.IsZero` along an equivalence. -/
theorem Limits.IsZero.transport (e : C ≌ D) {x : C} (hx : IsZero x) : IsZero (e.functor.obj x) where
  unique_to X := hx.unique_to (e.inverse.obj X) |>.map <|
    fun u => @Equiv.unique _ _ u (e.toAdjunction.homEquiv _ _)
  unique_from X := hx.unique_from (e.inverse.obj X) |>.map <|
    fun u => @Equiv.unique _ _ u (e.symm.toAdjunction.homEquiv _ _).symm

/-- Transport `Limits.HasZeroObject` along an equivalence. -/
theorem Limits.HasZeroObject.transport (e : C ≌ D) [Limits.HasZeroObject C] :
    Limits.HasZeroObject D where
  zero := let ⟨_Z, hZ⟩ := Limits.HasZeroObject.zero (C := C); ⟨_, Limits.IsZero.transport e hZ⟩

attribute [pp_dot] Equivalence.toAdjunction

/-- Transport `Limits.HasZeroMorphisms` along an equivalence. -/
def Limits.HasZeroMorphisms.transport (e : C ≌ D) [Limits.HasZeroMorphisms C] :
    Limits.HasZeroMorphisms D where
  Zero X Y := ⟨e.counitInv.app _ ≫ e.functor.map 0 ≫ e.counit.app _⟩
  zero_comp X {Y Z} f := show (_ ≫ _ ≫ _) ≫ _ = _ ≫ _ ≫ _ by
    conv_rhs => rw [←zero_comp _ (e.inverse.map f)]
    simp_rw [Functor.map_comp, e.fun_inv_map, Category.assoc, Iso.inv_hom_id_app, Functor.id_obj,
      Category.comp_id]
  comp_zero {X Y} f Z := show _ ≫ (_ ≫ _ ≫ _) = _ ≫ _ ≫ _ by
    conv_rhs => rw [←comp_zero (e.inverse.map f)]
    simp_rw [Functor.map_comp, e.fun_inv_map, ←Category.assoc, Iso.inv_hom_id_app, Functor.id_obj,
      Category.id_comp]


@[simp]
theorem toAdjunction_unit {e : C ≌ D} :
    e.toAdjunction.unit = e.unit :=
  rfl

@[simp]
theorem toAdjunction_counit {e : C ≌ D} :
    e.toAdjunction.counit = e.counit :=
  rfl

#check IsEquivalence

#check Functor.mapCone


/-- Transport a binary bicone along an equivalence.

See also `CategoryTheory.Functor.mapBinaryBicone` -/
@[simps]
def Limits.Cone.transport (e : C ≌ D) (F : E ⥤ C) (c : Cone (F ⋙ e.functor)) :
    Cone F where
  pt := e.inverse.obj c.pt
  π :=
    { app := fun Y => e.inverse.map (c.π.app Y) ≫ e.unitInv.app (F.obj Y)
      naturality := @fun X Y f => by
        have := c.π.naturality f
        aesop_cat }

/-- Transport a cone along a functor. See also `CategoryTheory.Functor.mapCone` -/
@[simps!]
def Functor.comapCone (e : C ⥤ D) [IsEquivalence e] (F : E ⥤ C) (c : Cone (F ⋙ e)) :
    Cone F :=
  Limits.Cone.transport e.asEquivalence F c

/-- Transport a binary bicone along an equivalence.

See also `CategoryTheory.Functor.mapBinaryBicone` -/
@[simps]
def Limits.BinaryBicone.transport [Limits.HasZeroMorphisms C]  [Limits.HasZeroMorphisms D]
  (e : C ≌ D) {X Y : D} (b : BinaryBicone (e.inverse.obj X) (e.inverse.obj Y)) :
    BinaryBicone X Y where
  pt := e.functor.obj b.pt
  fst := (e.toAdjunction.homEquiv _ _).symm b.fst
  snd := (e.toAdjunction.homEquiv _ _).symm b.snd
  inl := (e.symm.toAdjunction.homEquiv _ _) b.inl
  inr := (e.symm.toAdjunction.homEquiv _ _) b.inr
  inl_fst := by
    simp only [Equivalence.symm_functor, Equivalence.symm_inverse, Adjunction.homEquiv_unit, Functor.id_obj,
      Functor.comp_obj, Adjunction.homEquiv_counit, Category.assoc]
    slice_lhs 2 3 => rw [←Functor.map_comp, b.inl_fst, Functor.map_id]
    simp only [toAdjunction_unit, toAdjunction_counit]
    rw [Equivalence.unit, Equivalence.symm_unitIso]
    simp
  inl_snd := by
    simp only [Equivalence.symm_functor, Equivalence.symm_inverse, Adjunction.homEquiv_unit, Functor.id_obj,
      Functor.comp_obj, Adjunction.homEquiv_counit, Category.assoc]
    slice_lhs 2 3 => rw [←Functor.map_comp, b.inl_snd, Functor.map_zero]
    simp only [toAdjunction_unit, toAdjunction_counit]
    rw [Equivalence.unit, Equivalence.symm_unitIso]
    simp
  inr_fst := by
    simp only [Equivalence.symm_functor, Equivalence.symm_inverse, Adjunction.homEquiv_unit, Functor.id_obj,
      Functor.comp_obj, Adjunction.homEquiv_counit, Category.assoc]
    slice_lhs 2 3 => rw [←Functor.map_comp, b.inr_fst, Functor.map_zero]
    simp only [toAdjunction_unit, toAdjunction_counit]
    rw [Equivalence.unit, Equivalence.symm_unitIso]
    simp
  inr_snd := by
    simp only [Equivalence.symm_functor, Equivalence.symm_inverse, Adjunction.homEquiv_unit, Functor.id_obj,
      Functor.comp_obj, Adjunction.homEquiv_counit, Category.assoc]
    slice_lhs 2 3 => rw [←Functor.map_comp, b.inr_snd, Functor.map_id]
    simp only [toAdjunction_unit, toAdjunction_counit]
    rw [Equivalence.unit, Equivalence.symm_unitIso]
    simp

@[simp]
theorem Limits.BinaryBicone.transport_toCone [Limits.HasZeroMorphisms C]
    [Limits.HasZeroMorphisms D]
    (e : C ≌ D) {X Y : D} (b : BinaryBicone (e.inverse.obj X) (e.inverse.obj Y)) :
    (b.transport e).toCone =
      (BinaryFan.mk (P := e.functor.obj b.pt)
            (e.functor.map b.fst ≫ e.counit.app X)
            (e.functor.map b.snd ≫ e.counit.app Y)) :=
  rfl

@[simps!]
def Functor.mapBinaryBiconeInv [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (e : D ⥤ C) [IsEquivalence e] {X Y : D} (b : BinaryBicone (e.obj X) (e.obj Y)) :
    BinaryBicone X Y :=
  Limits.BinaryBicone.transport e.asEquivalence.symm b


@[simp]
theorem Functor.mapBinaryBiconeInv_toCone [Limits.HasZeroMorphisms C]
  [Limits.HasZeroMorphisms D]
    (e : D ⥤ C) [IsEquivalence e] {X Y : D} (b : BinaryBicone (e.obj X) (e.obj Y)) :
    (e.mapBinaryBiconeInv b).toCone =
      (e.mapConeInv <|
        letI := b.toCone
        letI := (pairComp X Y e).symm
        sorry)
      -- (BinaryFan.mk (P := e.inv.obj b.pt)
      --       (e.inv.map b.fst ≫ e.asEquivalence.unitInv.app X)
      --       (e.inv.map b.snd ≫ e.asEquivalence.unitInv.app Y))
            := rfl

def Limits.BinaryBiproductData.transport [Limits.HasZeroMorphisms C]  [Limits.HasZeroMorphisms D]
  (e : C ≌ D) {X Y : D} (b : BinaryBiproductData (e.inverse.obj X) (e.inverse.obj Y)) :
    BinaryBiproductData X Y where
      bicone := b.bicone.transport e
      isBilimit := {
        isLimit := CategoryTheory.Limits.HasLimit.isoOfEquivalence e _
        isColimit := mkCofanColimit  _ _ _ _
      }

/-- Transport `Limits.HasBinaryBiproduct` along an equivalence. -/
theorem Limits.HasBinaryBiproduct.transport
    (e : C ≌ D) [Limits.HasZeroMorphisms C] {X Y : D}
    [Limits.HasBinaryBiproduct (e.inverse.obj X) (e.inverse.obj Y)]
    [Limits.HasZeroMorphisms D] :
    Limits.HasBinaryBiproduct X Y where
  exists_binary_biproduct :=
    (Limits.HasBinaryBiproduct.exists_binary_biproduct
      (P := e.inverse.obj X) (Q := e.inverse.obj Y)).map fun d =>
      d.transport e

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
