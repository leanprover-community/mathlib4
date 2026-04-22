/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Preservation of biproducts

We define the image of a (binary) bicone under a functor that preserves zero morphisms and define
classes `PreservesBiproduct` and `PreservesBinaryBiproduct`. We then

* show that a functor that preserves biproducts of a two-element type preserves binary biproducts,
* construct the comparison morphisms between the image of a biproduct and the biproduct of the
  images and show that one composite is the identity,
* give the canonical isomorphism between the image of a biproduct and the biproduct of the images
  in case that the biproduct is preserved.

-/

@[expose] public section


universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section HasZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace Functor

section Map

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁}

set_option backward.isDefEq.respectTransparency false in
/-- The image of a bicone under a functor. -/
@[simps]
def mapBicone {f : J → C} (b : Bicone f) : Bicone (F.obj ∘ f) where
  pt := F.obj b.pt
  π j := F.map (b.π j)
  ι j := F.map (b.ι j)
  ι_π j j' := by
    rw [← F.map_comp]
    split_ifs with h
    · subst h
      simp only [bicone_ι_π_self, CategoryTheory.Functor.map_id, eqToHom_refl]; dsimp
    · rw [bicone_ι_π_ne _ h, F.map_zero]

theorem mapBicone_whisker {K : Type w₂} {g : K ≃ J} {f : J → C} (c : Bicone f) :
    F.mapBicone (c.whisker g) = (F.mapBicone c).whisker g :=
  rfl

end Bicone

/-- The image of a binary bicone under a functor. -/
@[simps!]
def mapBinaryBicone {X Y : C} (b : BinaryBicone X Y) : BinaryBicone (F.obj X) (F.obj Y) :=
  (BinaryBicones.functoriality _ _ F).obj b

end Map

end Functor

open CategoryTheory.Functor

namespace Limits

section Bicone

variable {J : Type w₁} {K : Type w₂}

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
bilimit bicone over `F.obj ∘ f`. -/
class PreservesBiproduct (f : J → C) (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {b : Bicone f}, b.IsBilimit → Nonempty (F.mapBicone b).IsBilimit

attribute [inherit_doc PreservesBiproduct] PreservesBiproduct.preserves

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
bilimit bicone over `F.obj ∘ f`. -/
def isBilimitOfPreserves {f : J → C} (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesBiproduct f F]
    {b : Bicone f} (hb : b.IsBilimit) : (F.mapBicone b).IsBilimit :=
  (PreservesBiproduct.preserves hb).some

variable (J)

/-- A functor `F` preserves biproducts of shape `J` if it preserves biproducts of `f` for every
`f : J → C`. -/
class PreservesBiproductsOfShape (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {f : J → C}, PreservesBiproduct f F

attribute [inherit_doc PreservesBiproductsOfShape] PreservesBiproductsOfShape.preserves

attribute [instance 100] PreservesBiproductsOfShape.preserves

end Bicone

/-- A functor `F` preserves finite biproducts if it preserves biproducts of shape `J`
whenever `J` is a finite type. -/
class PreservesFiniteBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {J : Type} [Finite J], PreservesBiproductsOfShape J F

attribute [inherit_doc PreservesFiniteBiproducts] PreservesFiniteBiproducts.preserves
attribute [instance 100] PreservesFiniteBiproducts.preserves

/-- A functor `F` preserves biproducts if it preserves biproducts of any shape `J` of size `w`.
The usual notion of preservation of biproducts is recovered by choosing `w` to be the universe
of the morphisms of `C`. -/
class PreservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {J : Type w₁}, PreservesBiproductsOfShape J F

attribute [inherit_doc PreservesBiproducts] PreservesBiproducts.preserves

attribute [instance 100] PreservesBiproducts.preserves

/-- Preserving biproducts at a bigger universe level implies preserving biproducts at a
smaller universe level. -/
lemma preservesBiproducts_shrink (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproducts.{max w₁ w₂} F] : PreservesBiproducts.{w₁} F :=
  ⟨fun {_} =>
    ⟨fun {_} =>
      ⟨fun {b} ib =>
        ⟨((F.mapBicone b).whiskerIsBilimitIff _).toFun
          (isBilimitOfPreserves F ((b.whiskerIsBilimitIff Equiv.ulift.{w₂}).invFun ib))⟩⟩⟩⟩

instance (priority := 100) preservesFiniteBiproductsOfPreservesBiproducts (F : C ⥤ D)
    [PreservesZeroMorphisms F] [PreservesBiproducts.{w₁} F] : PreservesFiniteBiproducts F where
  preserves {J} _ := by letI := preservesBiproducts_shrink.{0} F; infer_instance

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
`X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
class PreservesBinaryBiproduct (X Y : C) (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {b : BinaryBicone X Y}, b.IsBilimit → Nonempty ((F.mapBinaryBicone b).IsBilimit)

attribute [inherit_doc PreservesBinaryBiproduct] PreservesBinaryBiproduct.preserves

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
`X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
def isBinaryBilimitOfPreserves {X Y : C} (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBinaryBiproduct X Y F] {b : BinaryBicone X Y} (hb : b.IsBilimit) :
    (F.mapBinaryBicone b).IsBilimit :=
  (PreservesBinaryBiproduct.preserves hb).some

/-- A functor `F` preserves binary biproducts if it preserves the binary biproduct of `X` and `Y`
for all `X` and `Y`. -/
class PreservesBinaryBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {X Y : C}, PreservesBinaryBiproduct X Y F := by infer_instance

attribute [inherit_doc PreservesBinaryBiproducts] PreservesBinaryBiproducts.preserves

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
lemma preservesBinaryBiproduct_of_preservesBiproduct (F : C ⥤ D)
    [PreservesZeroMorphisms F] (X Y : C) [PreservesBiproduct (pairFunction X Y) F] :
    PreservesBinaryBiproduct X Y F where
  preserves {b} hb := ⟨{
      isLimit :=
        IsLimit.ofIsoLimit
            ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isLimit) <|
          Cone.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp
      isColimit :=
        IsColimit.ofIsoColimit
            ((IsColimit.precomposeInvEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isColimit) <|
          Cocone.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp }⟩

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
lemma preservesBinaryBiproducts_of_preservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproductsOfShape WalkingPair F] : PreservesBinaryBiproducts F where
  preserves {X} Y := preservesBinaryBiproduct_of_preservesBiproduct F X Y

attribute [instance 100] PreservesBinaryBiproducts.preserves

end Limits

open CategoryTheory.Limits

namespace Functor

section Bicone

variable {J : Type w₁} (F : C ⥤ D) (f : J → C) [HasBiproduct f]

section

variable [HasBiproduct (F.obj ∘ f)]

/-- As for products, any functor between categories with biproducts gives rise to a morphism
`F.obj (⨁ f) ⟶ ⨁ (F.obj ∘ f)`. -/
def biproductComparison : F.obj (⨁ f) ⟶ ⨁ F.obj ∘ f :=
  biproduct.lift fun j => F.map (biproduct.π f j)

@[reassoc (attr := simp)]
theorem biproductComparison_π (j : J) :
    biproductComparison F f ≫ biproduct.π _ j = F.map (biproduct.π f j) :=
  biproduct.lift_π _ _

/-- As for coproducts, any functor between categories with biproducts gives rise to a morphism
`⨁ (F.obj ∘ f) ⟶ F.obj (⨁ f)` -/
def biproductComparison' : ⨁ F.obj ∘ f ⟶ F.obj (⨁ f) :=
  biproduct.desc fun j => F.map (biproduct.ι f j)

@[reassoc (attr := simp)]
theorem ι_biproductComparison' (j : J) :
    biproduct.ι _ j ≫ biproductComparison' F f = F.map (biproduct.ι f j) :=
  biproduct.ι_desc _ _

variable [PreservesZeroMorphisms F]

set_option backward.isDefEq.respectTransparency false in
/-- The composition `biproductComparison' F f ≫ biproductComparison F f` is the identity. -/
@[reassoc (attr := simp)]
theorem biproductComparison'_comp_biproductComparison :
    biproductComparison' F f ≫ biproductComparison F f = 𝟙 (⨁ F.obj ∘ f) := by
  classical
    ext
    simp [biproduct.ι_π, ← Functor.map_comp, eqToHom_map]

/-- `biproductComparison F f` is a split epimorphism. -/
@[simps]
def splitEpiBiproductComparison : SplitEpi (biproductComparison F f) where
  section_ := biproductComparison' F f
  id := by simp

instance : IsSplitEpi (biproductComparison F f) :=
  IsSplitEpi.mk' (splitEpiBiproductComparison F f)

/-- `biproductComparison' F f` is a split monomorphism. -/
@[simps]
def splitMonoBiproductComparison' : SplitMono (biproductComparison' F f) where
  retraction := biproductComparison F f
  id := by simp

instance : IsSplitMono (biproductComparison' F f) :=
  IsSplitMono.mk' (splitMonoBiproductComparison' F f)

end

variable [PreservesZeroMorphisms F] [PreservesBiproduct f F]

instance hasBiproduct_of_preserves : HasBiproduct (F.obj ∘ f) :=
  HasBiproduct.mk
    { bicone := F.mapBicone (biproduct.bicone f)
      isBilimit := isBilimitOfPreserves _ (biproduct.isBilimit _) }

/-- This instance applies more often than `hasBiproduct_of_preserves`, but the discrimination
tree key matches a lot more (since it does not look through lambdas). -/
instance (priority := low) hasBiproduct_of_preserves' : HasBiproduct fun i => F.obj (f i) :=
  HasBiproduct.mk
    { bicone := F.mapBicone (biproduct.bicone f)
      isBilimit := isBilimitOfPreserves _ (biproduct.isBilimit _) }

/-- If `F` preserves a biproduct, we get a definitionally nice isomorphism
`F.obj (⨁ f) ≅ ⨁ (F.obj ∘ f)`. -/
abbrev mapBiproduct : F.obj (⨁ f) ≅ ⨁ F.obj ∘ f :=
  biproduct.uniqueUpToIso _ (isBilimitOfPreserves _ (biproduct.isBilimit _))

theorem mapBiproduct_hom :
    (mapBiproduct F f).hom = biproduct.lift fun j => F.map (biproduct.π f j) := rfl

theorem mapBiproduct_inv :
    (mapBiproduct F f).inv = biproduct.desc fun j => F.map (biproduct.ι f j) := rfl

end Bicone

variable (F : C ⥤ D) (X Y : C) [HasBinaryBiproduct X Y]

section

variable [HasBinaryBiproduct (F.obj X) (F.obj Y)]

/-- As for products, any functor between categories with binary biproducts gives rise to a
morphism `F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y`. -/
def biprodComparison : F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y :=
  biprod.lift (F.map biprod.fst) (F.map biprod.snd)

@[reassoc (attr := simp)]
theorem biprodComparison_fst : biprodComparison F X Y ≫ biprod.fst = F.map biprod.fst :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
theorem biprodComparison_snd : biprodComparison F X Y ≫ biprod.snd = F.map biprod.snd :=
  biprod.lift_snd _ _

/-- As for coproducts, any functor between categories with binary biproducts gives rise to a
morphism `F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)`. -/
def biprodComparison' : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y) :=
  biprod.desc (F.map biprod.inl) (F.map biprod.inr)

@[reassoc (attr := simp)]
theorem inl_biprodComparison' : biprod.inl ≫ biprodComparison' F X Y = F.map biprod.inl :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
theorem inr_biprodComparison' : biprod.inr ≫ biprodComparison' F X Y = F.map biprod.inr :=
  biprod.inr_desc _ _

variable [PreservesZeroMorphisms F]

/-- The composition `biprodComparison' F X Y ≫ biprodComparison F X Y` is the identity. -/
@[reassoc (attr := simp)]
theorem biprodComparison'_comp_biprodComparison :
    biprodComparison' F X Y ≫ biprodComparison F X Y = 𝟙 (F.obj X ⊞ F.obj Y) := by
  ext <;> simp [← Functor.map_comp]

/-- `biprodComparison F X Y` is a split epi. -/
@[simps]
def splitEpiBiprodComparison : SplitEpi (biprodComparison F X Y) where
  section_ := biprodComparison' F X Y
  id := by simp

instance : IsSplitEpi (biprodComparison F X Y) :=
  IsSplitEpi.mk' (splitEpiBiprodComparison F X Y)

/-- `biprodComparison' F X Y` is a split mono. -/
@[simps]
def splitMonoBiprodComparison' : SplitMono (biprodComparison' F X Y) where
  retraction := biprodComparison F X Y
  id := by simp

instance : IsSplitMono (biprodComparison' F X Y) :=
  IsSplitMono.mk' (splitMonoBiprodComparison' F X Y)

end

variable [PreservesZeroMorphisms F] [PreservesBinaryBiproduct X Y F]

instance hasBinaryBiproduct_of_preserves : HasBinaryBiproduct (F.obj X) (F.obj Y) :=
  HasBinaryBiproduct.mk
    { bicone := F.mapBinaryBicone (BinaryBiproduct.bicone X Y)
      isBilimit := isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _) }

/-- If `F` preserves a binary biproduct, we get a definitionally nice isomorphism
`F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y`. -/
abbrev mapBiprod : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _))

theorem mapBiprod_hom : (mapBiprod F X Y).hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd) :=
  rfl

theorem mapBiprod_inv : (mapBiprod F X Y).inv = biprod.desc (F.map biprod.inl) (F.map biprod.inr) :=
  rfl

end Functor

namespace Limits

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁} (f : J → C) [HasBiproduct f] [PreservesBiproduct f F] {W : C}

theorem biproduct.map_lift_mapBiprod (g : ∀ j, W ⟶ f j) :
    F.map (biproduct.lift g) ≫ (F.mapBiproduct f).hom = biproduct.lift fun j => F.map (g j) := by
  ext j
  dsimp only [Function.comp_def]
  simp only [mapBiproduct_hom, Category.assoc, biproduct.lift_π, ← F.map_comp]

theorem biproduct.mapBiproduct_inv_map_desc (g : ∀ j, f j ⟶ W) :
    (F.mapBiproduct f).inv ≫ F.map (biproduct.desc g) = biproduct.desc fun j => F.map (g j) := by
  ext j
  dsimp only [Function.comp_def]
  simp only [mapBiproduct_inv, ← Category.assoc, biproduct.ι_desc, ← F.map_comp]

set_option backward.isDefEq.respectTransparency false in
theorem biproduct.mapBiproduct_hom_desc (g : ∀ j, f j ⟶ W) :
    ((F.mapBiproduct f).hom ≫ biproduct.desc fun j => F.map (g j)) = F.map (biproduct.desc g) := by
  rw [← biproduct.mapBiproduct_inv_map_desc, Iso.hom_inv_id_assoc]

end Bicone

section BinaryBicone

variable (X Y : C) [HasBinaryBiproduct X Y] [PreservesBinaryBiproduct X Y F] {W : C}

theorem biprod.map_lift_mapBiprod (f : W ⟶ X) (g : W ⟶ Y) :
    F.map (biprod.lift f g) ≫ (F.mapBiprod X Y).hom = biprod.lift (F.map f) (F.map g) := by
  ext <;> simp [mapBiprod, ← F.map_comp]

theorem biprod.lift_mapBiprod (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift (F.map f) (F.map g) ≫ (F.mapBiprod X Y).inv = F.map (biprod.lift f g) := by
  rw [← biprod.map_lift_mapBiprod, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem biprod.mapBiprod_inv_map_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).inv ≫ F.map (biprod.desc f g) = biprod.desc (F.map f) (F.map g) := by
  ext <;> simp [mapBiprod, ← F.map_comp]

theorem biprod.mapBiprod_hom_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).hom ≫ biprod.desc (F.map f) (F.map g) = F.map (biprod.desc f g) := by
  rw [← biprod.mapBiprod_inv_map_desc, Iso.hom_inv_id_assoc]

end BinaryBicone

end Limits

end HasZeroMorphisms

end CategoryTheory
