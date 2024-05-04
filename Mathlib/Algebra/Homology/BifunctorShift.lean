/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.TotalComplexShift

/-!
# Behavior of the action of a bifunctor on cochain complexes with respect to shifts

In this file, given cochain complexes `K₁ : CochainComplex C₁ ℤ`, `K₂ : CochainComplex C₂ ℤ` and
a functor `F : C₁ ⥤ C₂ ⥤ D`, we define an isomorphism of cochain complexes in `D`:
- `CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x` of type
`mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧` for `x : ℤ`.
- `CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F y` of type
`mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧` for `y : ℤ`.

## TODO

- obtain various compatibilities

-/

open CategoryTheory Limits

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

namespace CochainComplex

section

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]

/-- The condition that `((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂` has
a total cochain complex. -/
abbrev HasMapBifunctor := HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)

/-- Given `K₁ : CochainComplex C₁ ℤ`, `K₂ : CochainComplex C₂ ℤ`,
a bifunctor `F : C₁ ⥤ C₂ ⥤ D`, this `mapBifunctor K₁ K₂ F : CochainComplex D ℤ`
is the total complex of the bicomplex obtained by applying `F` to `K₁` and `K₂`. -/
noncomputable abbrev mapBifunctor [HasMapBifunctor K₁ K₂ F] : CochainComplex D ℤ :=
  HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ)

/-- The inclusion of a summand `(F.obj (K₁.X n₁)).obj (K₂.X n₂) ⟶ (mapBifunctor K₁ K₂ F).X n`
of the total cochain complex when `n₁ + n₂ = n`. -/
noncomputable abbrev ιMapBifunctor [HasMapBifunctor K₁ K₂ F] (n₁ n₂ n : ℤ) (h : n₁ + n₂ = n) :
    (F.obj (K₁.X n₁)).obj (K₂.X n₂) ⟶ (mapBifunctor K₁ K₂ F).X n :=
  HomologicalComplex.ιMapBifunctor K₁ K₂ F _ _ _ _ h

end

section

variable [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms] (x : ℤ)
  [HasMapBifunctor K₁ K₂ F] [HasMapBifunctor (K₁⟦x⟧) K₂ F]
  [HomologicalComplex₂.HasTotal ((HomologicalComplex₂.shiftFunctor₁ D x).obj
    (((F.mapBifunctorHomologicalComplex _ _ ).obj K₁).obj K₂)) (ComplexShape.up ℤ)]

/-- Auxiliary definition for `mapBifunctorShift₁Iso`. -/
def mapBifunctorHomologicalComplexShift₁Iso :
    ((F.mapBifunctorHomologicalComplex _ _).obj (K₁⟦x⟧)).obj K₂ ≅
    (HomologicalComplex₂.shiftFunctor₁ D x).obj
      (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂) :=
  HomologicalComplex.Hom.isoOfComponents (fun i₁ => Iso.refl _)

/-- The canonical isomorphism `mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧`.
This isomorphism does not involve signs. -/
noncomputable def mapBifunctorShift₁Iso :
    mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧ :=
  HomologicalComplex₂.total.mapIso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x) _ ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₁Iso x

end

section

variable [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive] (y : ℤ)
  [HasMapBifunctor K₁ K₂ F] [HasMapBifunctor K₁ (K₂⟦y⟧) F]
  [HomologicalComplex₂.HasTotal
    ((HomologicalComplex₂.shiftFunctor₂ D y).obj
      (((F.mapBifunctorHomologicalComplex _ _ ).obj K₁).obj K₂)) (ComplexShape.up ℤ)]

/-- Auxiliary definition for `mapBifunctorShift₂Iso`. -/
def mapBifunctorHomologicalComplexShift₂Iso :
    ((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj (K₂⟦y⟧) ≅
    (HomologicalComplex₂.shiftFunctor₂ D y).obj
      (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents (fun i₂ => Iso.refl _))

/-- The canonical isomorphism `mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧`.
This isomorphism involves signs: on the summand `(F.obj (K₁.X p)).obj (K₂.X q)`, it is given
by the multiplication by `(p * y).negOnePow`. -/
noncomputable def mapBifunctorShift₂Iso :
    mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧ :=
  HomologicalComplex₂.total.mapIso
    (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y) (ComplexShape.up ℤ) ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₂Iso y

end

end CochainComplex
