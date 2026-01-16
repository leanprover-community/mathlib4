/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor

/-!
# The K-injective derivability structure

-/

@[expose] public section

universe w

open CategoryTheory Abelian Limits ZeroObject

variable (C : Type*) [Category C] [Abelian C]
  [HasDerivedCategory.{w} C]
  {H : Type*} [Category H]

namespace CategoryTheory.Abelian

class HasKInjectiveResolutions : Prop where
  exists_isKInjective (K : CochainComplex C ℤ) :
    ∃ (L : CochainComplex C ℤ) (i : K ⟶ L), Mono i ∧ L.IsKInjective

end CategoryTheory.Abelian

namespace CochainComplex

variable [HasKInjectiveResolutions C]

abbrev KInjectives :=
  ObjectProperty.FullSubcategory (fun (K : CochainComplex C ℤ) ↦ K.IsKInjective)

namespace KInjectives

variable {C} in
abbrev ι : KInjectives C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

def quasiIso : MorphismProperty (KInjectives C) :=
  (HomologicalComplex.quasiIso C (.up ℤ)).inverseImage ι

def localizerMorphism :
    LocalizerMorphism (KInjectives.quasiIso C) (HomologicalComplex.quasiIso C (.up ℤ)) where
  functor := ι
  map := by rfl

--instance : (localizerMorphism C).IsRightDerivabilityStructure := sorry

end KInjectives

end CochainComplex
