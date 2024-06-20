/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.RingTheory.LocalProperties

/-!

# Affine morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is affine if the preimage of affine opens are affine.

## TODO
- Show that affine morphisms are Zariski-local at the target.
- Show that affine morphisms are stable under base change.

-/

universe v u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes `X ⟶ Y` is affine if the preimages of affine open sets are affine. -/
@[mk_iff]
class IsAffineHom {X Y : Scheme} (f : X ⟶ Y) : Prop where
  isAffine_preimage : ∀ U : Opens Y, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U)

/-- The preimage of an affine open as an `Scheme.affine_opens`. -/
@[simps]
def affinePreimage {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f] (U : Y.affineOpens) :
    X.affineOpens :=
⟨f ⁻¹ᵁ U.1, IsAffineHom.isAffine_preimage _ U.prop⟩

instance (priority := 900) [IsIso f] : IsAffineHom f :=
⟨fun _ hU ↦ hU.map_isIso f⟩

instance (priority := 900) [IsAffineHom f] : QuasiCompact f :=
(quasiCompact_iff_forall_affine f).mpr (fun U hU ↦ (IsAffineHom.isAffine_preimage U hU).isCompact)

instance [IsAffineHom f] [IsAffineHom g] : IsAffineHom (f ≫ g) := by
  constructor
  intros U hU
  rw [Scheme.comp_val_base, Opens.map_comp_obj]
  apply IsAffineHom.isAffine_preimage
  apply IsAffineHom.isAffine_preimage
  exact hU

instance : MorphismProperty.IsMultiplicative @IsAffineHom where
  id_mem := inferInstance
  comp_mem _ _ _ _ := inferInstance

/-- The `AffineTargetMorphismProperty` corresponding to affine morphisms. -/
def IsAffineHom.affineProperty : AffineTargetMorphismProperty :=
fun X _ _ _  ↦ IsAffine X

@[simp] lemma IsAffineHom.affineProperty_toProperty :
  AffineTargetMorphismProperty.toProperty IsAffineHom.affineProperty f ↔
    IsAffine Y ∧ IsAffine X := by
  delta AffineTargetMorphismProperty.toProperty IsAffineHom.affineProperty; simp

lemma isAffineHom_iff_affineProperty :
    IsAffineHom f ↔ targetAffineLocally IsAffineHom.affineProperty f :=
(isAffineHom_iff f).trans ⟨fun H U ↦ H U U.prop, fun H U hU ↦ H ⟨U, hU⟩⟩

lemma isAffineHom_eq_affineProperty :
    @IsAffineHom = targetAffineLocally IsAffineHom.affineProperty := by
  ext; exact isAffineHom_iff_affineProperty _

instance {X : Scheme} (r : X.presheaf.obj (op ⊤)) :
    IsAffineHom (Scheme.ιOpens (X.basicOpen r)) := by
  constructor
  intros U hU
  fapply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (Scheme.ιOpens _)).mp
  convert hU.basicOpenIsAffine (X.presheaf.map (homOfLE le_top).op r)
  rw [X.basicOpen_res]
  ext1
  refine Set.image_preimage_eq_inter_range.trans ?_
  erw [Subtype.range_coe]
  rfl

end AlgebraicGeometry
