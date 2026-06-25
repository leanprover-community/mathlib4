/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.FullSubcategory
public import Mathlib.Algebra.Homology.ModelCategory.Injective
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences
public import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject

/-!
# The injective derivability structure

Let `C` be an abelian category with enough injectives.
In this file, we define a localizer morphism `CochainComplex.Plus.localizerMorphism`
(relatively to quasi-isomorphisms) which is given by the (fully faithful) functor
`CochainComplex.Plus (InjectiveObject C) ⥤ CochainComplex.Plus C`, and we show
that it is a right derivability structure. (The proof proceeds by showing that
up to equivalences of categories, this functor is the inclusion of the full
subcategory of fibrant objects in the model category `CochainComplex.Plus C`.)

TODO(@joelriou): obtain similar results for the bounded below homotopy category.

-/

@[expose] public section

open HomotopicalAlgebra CategoryTheory Limits ZeroObject Category

variable (C : Type*) [Category* C] [Abelian C]

namespace CochainComplex.Plus

/-- The localizer morphism (relatively to quasi-isomorphisms) that is
given by the "inclusion functor"
`CochainComplex.Plus (InjectiveObject C) ⥤ CochainComplex.Plus C`. -/
@[simps]
def localizerMorphism :
    LocalizerMorphism ((quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus)
      (quasiIso C) where
  functor := (InjectiveObject.ι C).mapCochainComplexPlus
  map := by rfl

instance : (localizerMorphism C).IsInduced where
  inverseImage_eq := rfl

instance (K : Plus (InjectiveObject C)) (n : ℤ) :
    Injective (K.obj.X n).obj :=
  (K.obj.X n).property

variable [EnoughInjectives C]

open modelCategoryQuillen

instance (K : FibrantObject (Plus C)) (n : ℤ) :
    Injective (K.obj.obj.X n) := by
  obtain ⟨K, hK⟩ := K
  rw [fibrantObjects, modelCategoryQuillen.isFibrant_iff] at hK
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence between `CochainComplex.Plus (InjectiveObject C)`
and the category of fibrant object in `CochainComplex.Plus C` for the
Quillen model category structure. -/
def fibrantObjectEquivalence :
    Plus (InjectiveObject C) ≌ FibrantObject (Plus C) where
  functor := ObjectProperty.lift _ (InjectiveObject.ι C).mapCochainComplexPlus (fun K ↦ by
    dsimp [fibrantObjects]
    rw [modelCategoryQuillen.isFibrant_iff]
    intro n
    dsimp
    infer_instance)
  inverse := ObjectProperty.lift _
    (HomologicalComplex.liftFunctorObjectProperty _ (FibrantObject.ι ⋙ Plus.ι C)
      (fun K n ↦ by dsimp; infer_instance)) (by
        rintro ⟨⟨K, n, hn⟩, _⟩
        refine ⟨n, ?_⟩
        rw [isStrictlyGE_iff]
        intro i hi
        rw [IsZero.iff_id_eq_zero]
        ext
        apply (K.isZero_of_isStrictlyGE n i hi).eq_of_tgt)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The localizer morphism (relatively to quasi-isomorphisms) that is
given by the equivalence of categories
`CochainComplex.Plus (InjectiveObject C) ≌ FibrantObject (CochainComplex.Plus C)`. -/
@[simps]
def fibrantObjectLocalizerMorphism :
    LocalizerMorphism ((quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus)
      (weakEquivalences (FibrantObject (Plus C))) where
  functor := (fibrantObjectEquivalence C).functor
  map := by rfl

instance : (fibrantObjectLocalizerMorphism C).IsInduced where
  inverseImage_eq := rfl

set_option backward.defeqAttrib.useBackward true in
instance : (fibrantObjectLocalizerMorphism C).functor.IsEquivalence := by
  dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : (localizerMorphism C).IsRightDerivabilityStructure := by
  rw [LocalizerMorphism.isRightDerivabilityStructure_iff_of_equivalences
    (T := localizerMorphism C) (B := FibrantObject.localizerMorphism (Plus C))
    (R := .id _) (L := fibrantObjectLocalizerMorphism C) (Iso.refl _)]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : (localizerMorphism C).arrow.HasRightResolutions := by
  rw [LocalizerMorphism.hasRightResolutions_arrow_iff_of_equivalences
    (T := localizerMorphism C) (B := FibrantObject.localizerMorphism (Plus C))
    (R := .id _) (L := fibrantObjectLocalizerMorphism C) (Iso.refl _)]
  infer_instance

end CochainComplex.Plus
