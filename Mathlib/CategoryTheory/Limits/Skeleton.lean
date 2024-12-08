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

section Skeletal

variable {C : Type u} [Category.{v} C]
variable [Limits.HasZeroMorphisms C] [Limits.HasBinaryBiproducts C] [Limits.HasZeroObject C]

/-- If `C` has binary biproducts and is skeletal, it is a commutative additive monoid.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def addCommMonoidOfSkeletal (hC : Skeletal C) : AddCommMonoid C where
  add X Y := (X ⊞ Y : C)
  toZero := CategoryTheory.Limits.HasZeroObject.zero' _
  zero_add X := hC ⟨(Limits.isoZeroBiprod (Limits.isZero_zero _)).symm⟩
  add_zero X := hC ⟨(Limits.isoBiprodZero (Limits.isZero_zero _)).symm⟩
  add_assoc X Y Z := hC ⟨Limits.biprod.associator X Y Z⟩
  add_comm X Y := hC ⟨Limits.biprod.braiding X Y⟩

end Skeletal

/-! TODO: surely we have all this stuff somewhere? -/
section Transport
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
  zero X Y := ⟨e.counitInv.app _ ≫ e.functor.map 0 ≫ e.counit.app _⟩
  zero_comp X {Y Z} f := show (_ ≫ _ ≫ _) ≫ _ = _ ≫ _ ≫ _ by
    conv_rhs => rw [← zero_comp _ (e.inverse.map f)]
    simp_rw [Functor.map_comp, e.fun_inv_map, Category.assoc, Iso.inv_hom_id_app, Functor.id_obj,
      Category.comp_id]
  comp_zero {X Y} f Z := show _ ≫ (_ ≫ _ ≫ _) = _ ≫ _ ≫ _ by
    conv_rhs => rw [← comp_zero (e.inverse.map f)]
    simp_rw [Functor.map_comp, e.fun_inv_map, ← Category.assoc, Iso.inv_hom_id_app, Functor.id_obj,
      Category.id_comp]


@[simp]
theorem toAdjunction_unit {e : C ≌ D} :
    e.toAdjunction.unit = e.unit :=
  rfl

@[simp]
theorem toAdjunction_counit {e : C ≌ D} :
    e.toAdjunction.counit = e.counit :=
  rfl


@[simp]
theorem adjunction_unit {e : C ⥤ D} [IsEquivalence e] :
    e.adjunction.unit = e.asEquivalence.unit :=
  rfl

@[simp]
theorem adjunction_counit {e : C ⥤ D} [IsEquivalence e] :
    e.adjunction.counit = e.asEquivalence.counit :=
  rfl

@[simp]
theorem asEquivalence_inv {e : C ⥤ D} [IsEquivalence e] :
    e.inv.asEquivalence = e.asEquivalence.symm := rfl



/-- Transport a binary bicone along an equivalence.

See also `CategoryTheory.Functor.mapBinaryBicone` -/
example (e : C ≌ D) (F : E ⥤ C) (c : Cone (F ⋙ e.functor)) :
    Cone F :=
  Functor.mapConeInv e.functor c

#check CategoryTheory.Functor.mapBinaryBicone

/-- Transport a binary bicone along an equivalence.
An inverse to `Functor.mapBinaryBicone`.

See also `CategoryTheory.Functor.mapBinaryBicone` -/
@[simps]
def Functor.mapBinaryBiconeInv [Limits.HasZeroMorphisms C]  [Limits.HasZeroMorphisms D]
    (e : D ⥤ C) [IsEquivalence e] {X Y : D} (b : BinaryBicone (e.obj X) (e.obj Y)) :
    BinaryBicone X Y where
  pt := e.inv.obj b.pt
  fst := (e.inv.adjunction.homEquiv _ _).symm b.fst
  snd := (e.inv.adjunction.homEquiv _ _).symm b.snd
  inl := (e.adjunction.homEquiv _ _) b.inl
  inr := (e.adjunction.homEquiv _ _) b.inr
  inl_fst := by
    simp only [Equivalence.symm_functor, Equivalence.symm_inverse, Adjunction.homEquiv_unit,
      Functor.id_obj, Functor.comp_obj, Adjunction.homEquiv_counit, Category.assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, b.inl_fst, Functor.map_id]
    simp only [adjunction_unit, adjunction_counit, asEquivalence_inv, Category.id_comp]
    rw [Equivalence.counit, Equivalence.unit, Equivalence.symm_counitIso]
    simp
  inl_snd := by
    simp only [Equivalence.symm_functor, Equivalence.symm_inverse, Adjunction.homEquiv_unit,
      Functor.id_obj, Functor.comp_obj, Adjunction.homEquiv_counit, Category.assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, b.inl_snd, Functor.map_zero]
    simp only [adjunction_unit, adjunction_counit, asEquivalence_inv, Category.id_comp]
    rw [Equivalence.counit, Equivalence.unit, Equivalence.symm_counitIso]
    simp
  inr_fst := by
    simp only [Equivalence.symm_functor, Equivalence.symm_inverse, Adjunction.homEquiv_unit,
      Functor.id_obj, Functor.comp_obj, Adjunction.homEquiv_counit, Category.assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, b.inr_fst, Functor.map_zero]
    simp only [adjunction_unit, adjunction_counit, asEquivalence_inv, Category.id_comp]
    rw [Equivalence.counit, Equivalence.unit, Equivalence.symm_counitIso]
    simp
  inr_snd := by
    simp only [Equivalence.symm_functor, Equivalence.symm_inverse, Adjunction.homEquiv_unit,
      Functor.id_obj, Functor.comp_obj, Adjunction.homEquiv_counit, Category.assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, b.inr_snd, Functor.map_id]
    simp only [adjunction_unit, adjunction_counit, asEquivalence_inv, Category.id_comp]
    rw [Equivalence.counit, Equivalence.unit, Equivalence.symm_counitIso]
    simp

@[simp]
theorem Functor.mapBinaryBiconeInv_toCone' [Limits.HasZeroMorphisms C]
    [Limits.HasZeroMorphisms D]
    (e : D ⥤ C) [IsEquivalence e] {X Y : D} (b : BinaryBicone (e.obj X) (e.obj Y)) :
    (e.mapBinaryBiconeInv b).toCone =
      (BinaryFan.mk (P := e.inv.obj b.pt)
            (e.inv.map b.fst ≫ IsEquivalence.counitIso.hom.app X)
            (e.inv.map b.snd ≫ IsEquivalence.counitIso.hom.app Y)) :=
  rfl

theorem Functor.mapBinaryBiconeInv_toCone [Limits.HasZeroMorphisms C]
    [Limits.HasZeroMorphisms D]
    (e : D ⥤ C) [IsEquivalence e] {X Y : D} (b : BinaryBicone (e.obj X) (e.obj Y)) :
    (e.mapBinaryBiconeInv b).toCone =
      (e.mapConeInv <| (Cones.postcompose (pairComp X Y e).symm.hom).obj b.toCone) := by
  simp
  sorry

theorem Functor.mapBinaryBiconeInv_toCocone [Limits.HasZeroMorphisms C]
    [Limits.HasZeroMorphisms D]
    (e : D ⥤ C) [IsEquivalence e] {X Y : D} (b : BinaryBicone (e.obj X) (e.obj Y)) :
    (e.mapBinaryBiconeInv b).toCocone =
      (e.mapCoconeInv <| (Cocones.precompose (pairComp X Y e).hom).obj b.toCocone) := by
  sorry

/-- Transport `Limits.BinaryBicone.IsBilimit` along an equivalence. -/
def Limits.BinaryBicone.IsBilimit.transport [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (e : D ⥤ C) [IsEquivalence e] {X Y : D} {b : BinaryBicone (e.obj X) (e.obj Y)} (hb : b.IsBilimit) :
    (e.mapBinaryBiconeInv b).IsBilimit where
  isColimit := by
    rw [Functor.mapBinaryBiconeInv_toCocone]
    have := hb.isColimit
    sorry
    -- letI := hb.isColimit.map
    -- letI := e.mapCocone <| (Cocones.precompose (pairComp X Y e).hom).obj b.toCocone
    -- sorry -- mkCofanColimit _ _ _ _
  isLimit := by
    rw [Functor.mapBinaryBiconeInv_toCone]
    have := hb.isLimit
    sorry

/-- Transport `Limits.BinaryBiproductData` along an equivalence. -/
def Limits.BinaryBiproductData.transport [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (e : D ⥤ C) [IsEquivalence e] {X Y : D} (b : BinaryBiproductData (e.obj X) (e.obj Y)) :
    BinaryBiproductData X Y where
      bicone := e.mapBinaryBiconeInv b.bicone
      isBilimit := b.isBilimit.transport e

/-- Transport `Limits.HasBinaryBiproduct` along an equivalence. -/
theorem Limits.HasBinaryBiproduct.transport
    (e : D ⥤ C) [IsEquivalence e] [Limits.HasZeroMorphisms C] {X Y : D}
    [Limits.HasBinaryBiproduct (e.obj X) (e.obj Y)]
    [Limits.HasZeroMorphisms D] :
    Limits.HasBinaryBiproduct X Y where
  exists_binary_biproduct :=
    Limits.HasBinaryBiproduct.exists_binary_biproduct.map fun d =>
      d.transport e

end Transport

section Skeleton

variable {C : Type u} [Category.{v} C]
variable [Limits.HasZeroMorphisms C] [Limits.HasBinaryBiproducts C] [Limits.HasZeroObject C]

instance : Limits.HasZeroObject (Skeleton C) :=
  Limits.HasZeroObject.transport (skeletonEquivalence C).symm

noncomputable instance : Limits.HasZeroMorphisms (Skeleton C) :=
  Limits.HasZeroMorphisms.transport (skeletonEquivalence C).symm

instance (X Y : Skeleton C) : Limits.HasBinaryBiproduct X Y :=
  Limits.HasBinaryBiproduct.transport (skeletonEquivalence C).functor

noncomputable instance : Limits.HasBinaryBiproducts (Skeleton C) where
  has_binary_biproduct := inferInstance

/--
The skeleton of a category with biproducts can be viewed as an additive monoid, where the addition
is given by the biproduct, and satisfies the monoid axioms since it is a skeleton.
-/
noncomputable instance Skeleton.instAddCommMonoid : AddCommMonoid (Skeleton C) :=
  addCommMonoidOfSkeletal (skeletonIsSkeleton _).skel

end Skeleton
