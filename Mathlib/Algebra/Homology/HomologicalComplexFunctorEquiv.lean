/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive

/-!
# Homological complexes in the category of functors
-/

open CategoryTheory Limits

namespace HomologicalComplex

variable (C : Type*) [Category C] [HasZeroMorphisms C]
    {ι : Type*} (c : ComplexShape ι) (J : Type*) [Category J]

namespace functorEquivalence

@[simps]
def functor : HomologicalComplex (J ⥤ C) c ⥤ (J ⥤ HomologicalComplex C c) where
  obj K :=
    { obj j := (((evaluation J C).obj j).mapHomologicalComplex c).obj K
      map {j j'} f := (NatTrans.mapHomologicalComplex ((evaluation J C).map f) c).app K }
  map {K K'} φ :=
    { app j := (((evaluation J C).obj j).mapHomologicalComplex c).map φ }

@[simps]
def inverse : (J ⥤ HomologicalComplex C c) ⥤ HomologicalComplex (J ⥤ C) c where
  obj F :=
    { X j := F ⋙ eval C c j
      d i j := whiskerLeft F (dNatTrans C c i j)
      shape i j hij := by
        ext K
        exact (F.obj K).shape i j hij
      d_comp_d' := by intros; ext; dsimp; simp }
  map {F G} τ :=
    { f j := whiskerRight τ (eval C c j)
      comm' := by intros; ext; dsimp; simp }

end functorEquivalence

@[simps]
def functorEquivalence :
    HomologicalComplex (J ⥤ C) c ≌ (J ⥤ HomologicalComplex C c) where
  functor := functorEquivalence.functor C c J
  inverse := functorEquivalence.inverse C c J
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end HomologicalComplex
