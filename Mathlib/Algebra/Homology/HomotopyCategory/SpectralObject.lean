/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Triangulated.SpectralObject

/-!
# The spectral object with values in the homotopy category

Let `C` be an additive category. In this file, we show that the
mapping cone defines a spectral object with values in the homotopy
category of `ℤ`-indexed cochain complexes `C` that is indexed
by the category `CochainComplex C ℤ`.
(It follows that to any functor `ι ⥤ CochainComplex C ℤ` (e.g. a filtered
complex), there is an associated spectral object indexed by `ι`.)

-/

@[expose] public section

namespace HomotopyCategory

open CategoryTheory Limits Triangulated CochainComplex.mappingCone

variable (C : Type*) [Category* C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The functor `ComposableArrows (CochainComplex C ℤ) 1 ⥤ CochainComplex C ℤ` which
sends a morphism of cochain complexes to its mapping cone. -/
@[simps]
noncomputable def composableArrowsFunctor :
    ComposableArrows (CochainComplex C ℤ) 1 ⥤ CochainComplex C ℤ where
  obj f := CochainComplex.mappingCone (f.map' 0 1)
  map φ := map _ _ (φ.app 0) (φ.app 1) (ComposableArrows.naturality' φ 0 1)
  map_id _ := map_id _
  map_comp _ _ := map_comp _ _ _ _ _ _ _ _ _

/-- The spectral object with values in `(HomotopyCategory C (.up ℤ)` that
is indexed by `CochainComplex C ℤ`. -/
@[simps]
noncomputable def spectralObjectMappingCone :
    SpectralObject (HomotopyCategory C (ComplexShape.up ℤ)) (CochainComplex C ℤ) where
  ω₁ := composableArrowsFunctor C ⋙ HomotopyCategory.quotient _ _
  δ'.app D := ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
    (CochainComplex.mappingConeCompTriangle (D.map' 0 1) (D.map' 1 2))).mor₃
  δ'.naturality D₁ D₂ φ := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D₁
    obtain ⟨_, _, _, f', g', rfl⟩ := ComposableArrows.mk₂_surjective D₂
    have eq := CochainComplex.mappingConeCompTriangle_mor₃_naturality f g f' g' φ
    dsimp [ComposableArrows.Precomp.map] at eq ⊢
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    simp [eq]
  distinguished' D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D
    exact HomotopyCategory.mappingConeCompTriangleh_distinguished f g

end HomotopyCategory
