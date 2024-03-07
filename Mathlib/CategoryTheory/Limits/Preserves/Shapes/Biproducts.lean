/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

#align_import category_theory.limits.preserves.shapes.biproducts from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Preservation of biproducts

We define the image of a (binary) bicone under a functor that preserves zero morphisms and define
classes `PreservesBiproduct` and `PreservesBinaryBiproduct`. We then

* show that a functor that preserves biproducts of a two-element type preserves binary biproducts,
* construct the comparison morphisms between the image of a biproduct and the biproduct of the
  images and show that the biproduct is preserved if one of them is an isomorphism,
* give the canonical isomorphism between the image of a biproduct and the biproduct of the images
  in case that the biproduct is preserved.

-/


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
#align category_theory.functor.map_bicone CategoryTheory.Functor.mapBicone

theorem mapBicone_whisker {K : Type w₂} {g : K ≃ J} {f : J → C} (c : Bicone f) :
    F.mapBicone (c.whisker g) = (F.mapBicone c).whisker g :=
  rfl
#align category_theory.functor.map_bicone_whisker CategoryTheory.Functor.mapBicone_whisker

end Bicone

/-- The image of a binary bicone under a functor. -/
@[simps!]
def mapBinaryBicone {X Y : C} (b : BinaryBicone X Y) : BinaryBicone (F.obj X) (F.obj Y) :=
  (BinaryBicones.functoriality _ _ F).obj b
#align category_theory.functor.map_binary_bicone CategoryTheory.Functor.mapBinaryBicone

end Map

end Functor

open CategoryTheory.Functor

namespace Limits

section Bicone

variable {J : Type w₁} {K : Type w₂}

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
    bilimit bicone over `F.obj ∘ f`. -/
class PreservesBiproduct (f : J → C) (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {b : Bicone f}, b.IsBilimit → (F.mapBicone b).IsBilimit
#align category_theory.limits.preserves_biproduct CategoryTheory.Limits.PreservesBiproduct

attribute [inherit_doc PreservesBiproduct] PreservesBiproduct.preserves

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
    bilimit bicone over `F.obj ∘ f`. -/
def isBilimitOfPreserves {f : J → C} (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesBiproduct f F]
    {b : Bicone f} (hb : b.IsBilimit) : (F.mapBicone b).IsBilimit :=
  PreservesBiproduct.preserves hb
#align category_theory.limits.is_bilimit_of_preserves CategoryTheory.Limits.isBilimitOfPreserves

variable (J)

/-- A functor `F` preserves biproducts of shape `J` if it preserves biproducts of `f` for every
    `f : J → C`. -/
class PreservesBiproductsOfShape (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {f : J → C}, PreservesBiproduct f F
#align category_theory.limits.preserves_biproducts_of_shape CategoryTheory.Limits.PreservesBiproductsOfShape

attribute [inherit_doc PreservesBiproductsOfShape] PreservesBiproductsOfShape.preserves

attribute [instance 100] PreservesBiproductsOfShape.preserves

end Bicone

/-- A functor `F` preserves finite biproducts if it preserves biproducts of shape `J` whenever
    `J` is a fintype. -/
class PreservesFiniteBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {J : Type} [Fintype J], PreservesBiproductsOfShape J F
#align category_theory.limits.preserves_finite_biproducts CategoryTheory.Limits.PreservesFiniteBiproducts

attribute [inherit_doc PreservesFiniteBiproducts] PreservesFiniteBiproducts.preserves

attribute [instance 100] PreservesFiniteBiproducts.preserves

/-- A functor `F` preserves biproducts if it preserves biproducts of any shape `J` of size `w`.
    The usual notion of preservation of biproducts is recovered by choosing `w` to be the universe
    of the morphisms of `C`. -/
class PreservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {J : Type w₁}, PreservesBiproductsOfShape J F
#align category_theory.limits.preserves_biproducts CategoryTheory.Limits.PreservesBiproducts

attribute [inherit_doc PreservesBiproducts] PreservesBiproducts.preserves

attribute [instance 100] PreservesBiproducts.preserves

/-- Preserving biproducts at a bigger universe level implies preserving biproducts at a
smaller universe level. -/
def preservesBiproductsShrink (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproducts.{max w₁ w₂} F] : PreservesBiproducts.{w₁} F :=
  ⟨fun {_} =>
    ⟨fun {_} =>
      ⟨fun {b} ib =>
        ((F.mapBicone b).whiskerIsBilimitIff _).toFun
          (isBilimitOfPreserves F ((b.whiskerIsBilimitIff Equiv.ulift.{w₂}).invFun ib))⟩⟩⟩
#align category_theory.limits.preserves_biproducts_shrink CategoryTheory.Limits.preservesBiproductsShrink

instance (priority := 100) preservesFiniteBiproductsOfPreservesBiproducts (F : C ⥤ D)
    [PreservesZeroMorphisms F] [PreservesBiproducts.{w₁} F] : PreservesFiniteBiproducts F where
  preserves {J} _ := by letI := preservesBiproductsShrink.{0} F; infer_instance
#align category_theory.limits.preserves_finite_biproducts_of_preserves_biproducts CategoryTheory.Limits.preservesFiniteBiproductsOfPreservesBiproducts

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
    `X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
class PreservesBinaryBiproduct (X Y : C) (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {b : BinaryBicone X Y}, b.IsBilimit → (F.mapBinaryBicone b).IsBilimit
#align category_theory.limits.preserves_binary_biproduct CategoryTheory.Limits.PreservesBinaryBiproduct

attribute [inherit_doc PreservesBinaryBiproduct] PreservesBinaryBiproduct.preserves

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
    `X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
def isBinaryBilimitOfPreserves {X Y : C} (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBinaryBiproduct X Y F] {b : BinaryBicone X Y} (hb : b.IsBilimit) :
    (F.mapBinaryBicone b).IsBilimit :=
  PreservesBinaryBiproduct.preserves hb
#align category_theory.limits.is_binary_bilimit_of_preserves CategoryTheory.Limits.isBinaryBilimitOfPreserves

/-- A functor `F` preserves binary biproducts if it preserves the binary biproduct of `X` and `Y`
    for all `X` and `Y`. -/
class PreservesBinaryBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {X Y : C}, PreservesBinaryBiproduct X Y F := by infer_instance
#align category_theory.limits.preserves_binary_biproducts CategoryTheory.Limits.PreservesBinaryBiproducts

attribute [inherit_doc PreservesBinaryBiproducts] PreservesBinaryBiproducts.preserves

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
def preservesBinaryBiproductOfPreservesBiproduct (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C)
    [PreservesBiproduct (pairFunction X Y) F] : PreservesBinaryBiproduct X Y F where
  preserves {b} hb :=
    { isLimit :=
        IsLimit.ofIsoLimit
            ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isLimit) <|
          Cones.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp
      isColimit :=
        IsColimit.ofIsoColimit
            ((IsColimit.precomposeInvEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isColimit) <|
          Cocones.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp }
#align category_theory.limits.preserves_binary_biproduct_of_preserves_biproduct CategoryTheory.Limits.preservesBinaryBiproductOfPreservesBiproduct

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
def preservesBinaryBiproductsOfPreservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproductsOfShape WalkingPair F] : PreservesBinaryBiproducts F where
  preserves {X} Y := preservesBinaryBiproductOfPreservesBiproduct F X Y
#align category_theory.limits.preserves_binary_biproducts_of_preserves_biproducts CategoryTheory.Limits.preservesBinaryBiproductsOfPreservesBiproducts

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
#align category_theory.functor.biproduct_comparison CategoryTheory.Functor.biproductComparison

@[reassoc (attr := simp)]
theorem biproductComparison_π (j : J) :
    biproductComparison F f ≫ biproduct.π _ j = F.map (biproduct.π f j) :=
  biproduct.lift_π _ _
#align category_theory.functor.biproduct_comparison_π CategoryTheory.Functor.biproductComparison_π

/-- As for coproducts, any functor between categories with biproducts gives rise to a morphism
    `⨁ (F.obj ∘ f) ⟶ F.obj (⨁ f)` -/
def biproductComparison' : ⨁ F.obj ∘ f ⟶ F.obj (⨁ f) :=
  biproduct.desc fun j => F.map (biproduct.ι f j)
#align category_theory.functor.biproduct_comparison' CategoryTheory.Functor.biproductComparison'

@[reassoc (attr := simp)]
theorem ι_biproductComparison' (j : J) :
    biproduct.ι _ j ≫ biproductComparison' F f = F.map (biproduct.ι f j) :=
  biproduct.ι_desc _ _
#align category_theory.functor.ι_biproduct_comparison' CategoryTheory.Functor.ι_biproductComparison'

variable [PreservesZeroMorphisms F]

/-- The composition in the opposite direction is equal to the identity if and only if `F` preserves
    the biproduct, see `preservesBiproduct_of_monoBiproductComparison`.  -/
@[reassoc (attr := simp)]
theorem biproductComparison'_comp_biproductComparison :
    biproductComparison' F f ≫ biproductComparison F f = 𝟙 (⨁ F.obj ∘ f) := by
  classical
    ext
    simp [biproduct.ι_π, ← Functor.map_comp, eqToHom_map]
#align category_theory.functor.biproduct_comparison'_comp_biproduct_comparison CategoryTheory.Functor.biproductComparison'_comp_biproductComparison

/-- `biproduct_comparison F f` is a split epimorphism. -/
@[simps]
def splitEpiBiproductComparison : SplitEpi (biproductComparison F f) where
  section_ := biproductComparison' F f
  id := by aesop
#align category_theory.functor.split_epi_biproduct_comparison CategoryTheory.Functor.splitEpiBiproductComparison

instance : IsSplitEpi (biproductComparison F f) :=
  IsSplitEpi.mk' (splitEpiBiproductComparison F f)

/-- `biproduct_comparison' F f` is a split monomorphism. -/
@[simps]
def splitMonoBiproductComparison' : SplitMono (biproductComparison' F f) where
  retraction := biproductComparison F f
  id := by aesop
#align category_theory.functor.split_mono_biproduct_comparison' CategoryTheory.Functor.splitMonoBiproductComparison'

instance : IsSplitMono (biproductComparison' F f) :=
  IsSplitMono.mk' (splitMonoBiproductComparison' F f)

end

variable [PreservesZeroMorphisms F] [PreservesBiproduct f F]

instance hasBiproduct_of_preserves : HasBiproduct (F.obj ∘ f) :=
  HasBiproduct.mk
    { bicone := F.mapBicone (biproduct.bicone f)
      isBilimit := PreservesBiproduct.preserves (biproduct.isBilimit _) }
#align category_theory.functor.has_biproduct_of_preserves CategoryTheory.Functor.hasBiproduct_of_preserves

/-- If `F` preserves a biproduct, we get a definitionally nice isomorphism
    `F.obj (⨁ f) ≅ ⨁ (F.obj ∘ f)`. -/
@[simp]
def mapBiproduct : F.obj (⨁ f) ≅ ⨁ F.obj ∘ f :=
  biproduct.uniqueUpToIso _ (PreservesBiproduct.preserves (biproduct.isBilimit _))
#align category_theory.functor.map_biproduct CategoryTheory.Functor.mapBiproduct

theorem mapBiproduct_hom :
    haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
    (mapBiproduct F f).hom = biproduct.lift fun j => F.map (biproduct.π f j) := rfl
#align category_theory.functor.map_biproduct_hom CategoryTheory.Functor.mapBiproduct_hom

theorem mapBiproduct_inv :
    haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
    (mapBiproduct F f).inv = biproduct.desc fun j => F.map (biproduct.ι f j) := rfl
#align category_theory.functor.map_biproduct_inv CategoryTheory.Functor.mapBiproduct_inv

end Bicone

variable (F : C ⥤ D) (X Y : C) [HasBinaryBiproduct X Y]

section

variable [HasBinaryBiproduct (F.obj X) (F.obj Y)]

/-- As for products, any functor between categories with binary biproducts gives rise to a
    morphism `F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y`. -/
def biprodComparison : F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y :=
  biprod.lift (F.map biprod.fst) (F.map biprod.snd)
#align category_theory.functor.biprod_comparison CategoryTheory.Functor.biprodComparison

@[reassoc (attr := simp)]
theorem biprodComparison_fst : biprodComparison F X Y ≫ biprod.fst = F.map biprod.fst :=
  biprod.lift_fst _ _
#align category_theory.functor.biprod_comparison_fst CategoryTheory.Functor.biprodComparison_fst

@[reassoc (attr := simp)]
theorem biprodComparison_snd : biprodComparison F X Y ≫ biprod.snd = F.map biprod.snd :=
  biprod.lift_snd _ _
#align category_theory.functor.biprod_comparison_snd CategoryTheory.Functor.biprodComparison_snd

/-- As for coproducts, any functor between categories with binary biproducts gives rise to a
    morphism `F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)`. -/
def biprodComparison' : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y) :=
  biprod.desc (F.map biprod.inl) (F.map biprod.inr)
#align category_theory.functor.biprod_comparison' CategoryTheory.Functor.biprodComparison'

@[reassoc (attr := simp)]
theorem inl_biprodComparison' : biprod.inl ≫ biprodComparison' F X Y = F.map biprod.inl :=
  biprod.inl_desc _ _
#align category_theory.functor.inl_biprod_comparison' CategoryTheory.Functor.inl_biprodComparison'

@[reassoc (attr := simp)]
theorem inr_biprodComparison' : biprod.inr ≫ biprodComparison' F X Y = F.map biprod.inr :=
  biprod.inr_desc _ _
#align category_theory.functor.inr_biprod_comparison' CategoryTheory.Functor.inr_biprodComparison'

variable [PreservesZeroMorphisms F]

/-- The composition in the opposite direction is equal to the identity if and only if `F` preserves
    the biproduct, see `preservesBinaryBiproduct_of_monoBiprodComparison`. -/
@[reassoc (attr := simp)]
theorem biprodComparison'_comp_biprodComparison :
    biprodComparison' F X Y ≫ biprodComparison F X Y = 𝟙 (F.obj X ⊞ F.obj Y) := by
  ext <;> simp [← Functor.map_comp]
#align category_theory.functor.biprod_comparison'_comp_biprod_comparison CategoryTheory.Functor.biprodComparison'_comp_biprodComparison

/-- `biprodComparison F X Y` is a split epi. -/
@[simps]
def splitEpiBiprodComparison : SplitEpi (biprodComparison F X Y) where
  section_ := biprodComparison' F X Y
  id := by aesop
#align category_theory.functor.split_epi_biprod_comparison CategoryTheory.Functor.splitEpiBiprodComparison

instance : IsSplitEpi (biprodComparison F X Y) :=
  IsSplitEpi.mk' (splitEpiBiprodComparison F X Y)

/-- `biprodComparison' F X Y` is a split mono. -/
@[simps]
def splitMonoBiprodComparison' : SplitMono (biprodComparison' F X Y) where
  retraction := biprodComparison F X Y
  id := by aesop
#align category_theory.functor.split_mono_biprod_comparison' CategoryTheory.Functor.splitMonoBiprodComparison'

instance : IsSplitMono (biprodComparison' F X Y) :=
  IsSplitMono.mk' (splitMonoBiprodComparison' F X Y)

end

variable [PreservesZeroMorphisms F] [PreservesBinaryBiproduct X Y F]

instance hasBinaryBiproduct_of_preserves : HasBinaryBiproduct (F.obj X) (F.obj Y) :=
  HasBinaryBiproduct.mk
    { bicone := F.mapBinaryBicone (BinaryBiproduct.bicone X Y)
      isBilimit := PreservesBinaryBiproduct.preserves (BinaryBiproduct.isBilimit _ _) }
#align category_theory.functor.has_binary_biproduct_of_preserves CategoryTheory.Functor.hasBinaryBiproduct_of_preserves

/-- If `F` preserves a binary biproduct, we get a definitionally nice isomorphism
    `F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y`. -/
@[simp]
def mapBiprod : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  biprod.uniqueUpToIso _ _ (PreservesBinaryBiproduct.preserves (BinaryBiproduct.isBilimit _ _))
#align category_theory.functor.map_biprod CategoryTheory.Functor.mapBiprod

theorem mapBiprod_hom : (mapBiprod F X Y).hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd) :=
  rfl
#align category_theory.functor.map_biprod_hom CategoryTheory.Functor.mapBiprod_hom

theorem mapBiprod_inv : (mapBiprod F X Y).inv = biprod.desc (F.map biprod.inl) (F.map biprod.inr) :=
  rfl
#align category_theory.functor.map_biprod_inv CategoryTheory.Functor.mapBiprod_inv

end Functor

namespace Limits

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁} (f : J → C) [HasBiproduct f] [PreservesBiproduct f F] {W : C}

theorem biproduct.map_lift_mapBiprod (g : ∀ j, W ⟶ f j) :
    -- Porting note: twice we need haveI to tell Lean about hasBiproduct_of_preserves F f
    haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
    F.map (biproduct.lift g) ≫ (F.mapBiproduct f).hom = biproduct.lift fun j => F.map (g j) := by
  ext j
  dsimp only [Function.comp_def]
  haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
  simp only [mapBiproduct_hom, Category.assoc, biproduct.lift_π, ← F.map_comp]
#align category_theory.limits.biproduct.map_lift_map_biprod CategoryTheory.Limits.biproduct.map_lift_mapBiprod

theorem biproduct.mapBiproduct_inv_map_desc (g : ∀ j, f j ⟶ W) :
    -- Porting note: twice we need haveI to tell Lean about hasBiproduct_of_preserves F f
    haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
    (F.mapBiproduct f).inv ≫ F.map (biproduct.desc g) = biproduct.desc fun j => F.map (g j) := by
  ext j
  dsimp only [Function.comp_def]
  haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
  simp only [mapBiproduct_inv, ← Category.assoc, biproduct.ι_desc ,← F.map_comp]
#align category_theory.limits.biproduct.map_biproduct_inv_map_desc CategoryTheory.Limits.biproduct.mapBiproduct_inv_map_desc

theorem biproduct.mapBiproduct_hom_desc (g : ∀ j, f j ⟶ W) :
    ((F.mapBiproduct f).hom ≫ biproduct.desc fun j => F.map (g j)) = F.map (biproduct.desc g) := by
  rw [← biproduct.mapBiproduct_inv_map_desc, Iso.hom_inv_id_assoc]
#align category_theory.limits.biproduct.map_biproduct_hom_desc CategoryTheory.Limits.biproduct.mapBiproduct_hom_desc

end Bicone

section BinaryBicone

variable (X Y : C) [HasBinaryBiproduct X Y] [PreservesBinaryBiproduct X Y F] {W : C}

theorem biprod.map_lift_mapBiprod (f : W ⟶ X) (g : W ⟶ Y) :
    F.map (biprod.lift f g) ≫ (F.mapBiprod X Y).hom = biprod.lift (F.map f) (F.map g) := by
  ext <;> simp [mapBiprod, ← F.map_comp]
#align category_theory.limits.biprod.map_lift_map_biprod CategoryTheory.Limits.biprod.map_lift_mapBiprod

theorem biprod.lift_mapBiprod (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift (F.map f) (F.map g) ≫ (F.mapBiprod X Y).inv = F.map (biprod.lift f g) := by
  rw [← biprod.map_lift_mapBiprod, Category.assoc, Iso.hom_inv_id, Category.comp_id]
#align category_theory.limits.biprod.lift_map_biprod CategoryTheory.Limits.biprod.lift_mapBiprod

theorem biprod.mapBiprod_inv_map_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).inv ≫ F.map (biprod.desc f g) = biprod.desc (F.map f) (F.map g) := by
  ext <;> simp [mapBiprod, ← F.map_comp]
#align category_theory.limits.biprod.map_biprod_inv_map_desc CategoryTheory.Limits.biprod.mapBiprod_inv_map_desc

theorem biprod.mapBiprod_hom_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).hom ≫ biprod.desc (F.map f) (F.map g) = F.map (biprod.desc f g) := by
  rw [← biprod.mapBiprod_inv_map_desc, Iso.hom_inv_id_assoc]
#align category_theory.limits.biprod.map_biprod_hom_desc CategoryTheory.Limits.biprod.mapBiprod_hom_desc

end BinaryBicone

end Limits

end HasZeroMorphisms

end CategoryTheory
