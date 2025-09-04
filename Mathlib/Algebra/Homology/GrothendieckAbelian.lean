/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Generator.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Homological complexes in a Grothendieck abelian category

Let `c : ComplexShape ι` be a complex shape with no loop, and
such that `Small.{w} ι`. Then, if `C` is a Grothendieck abelian
category (with `IsGrothendieckAbelian.{w} C`), the category
`HomologicalComplex C c` is Grothendieck abelian.

-/

universe w w' t v u

open CategoryTheory Limits

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] {ι : Type t} (c : ComplexShape ι)

section HasZeroMorphisms

variable [HasZeroMorphisms C]

instance locallySmall [LocallySmall.{w} C] [Small.{w} ι] :
    LocallySmall.{w} (HomologicalComplex C c) where
  hom_small K L := by
    let emb (f : K ⟶ L) (i : Shrink.{w} ι) := (equivShrink.{w} _) (f.f ((equivShrink _).symm i))
    have hemb : Function.Injective emb := fun f g h ↦ by
      ext i
      obtain ⟨i, rfl⟩ := (equivShrink.{w} _).symm.surjective i
      simpa [emb] using congr_fun h i
    apply small_of_injective hemb

instance [HasFilteredColimitsOfSize.{w, w'} C] :
    HasFilteredColimitsOfSize.{w, w'} (HomologicalComplex C c) where
  HasColimitsOfShape J _ _ := by infer_instance

instance hasExactColimitsOfShape (J : Type w) [Category.{w'} J] [HasFiniteLimits C]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    HasExactColimitsOfShape J (HomologicalComplex C c) where
  preservesFiniteLimits :=
    ⟨fun K _ _ ↦ ⟨fun {F} ↦ ⟨fun hc ↦ ⟨isLimitOfEval _ _ (fun i ↦ by
      let e := preservesColimitNatIso (J := J) (eval C c i)
      exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerLeft F e) _).1
        (IsLimit.ofIsoLimit
          (isLimitOfPreserves ((Functor.whiskeringRight J _ _).obj (eval C c i) ⋙ colim) hc)
          (Cones.ext (e.symm.app _) (fun k ↦ (NatIso.naturality_2 e.symm _).symm))))⟩⟩⟩⟩

instance ab5OfSize [HasFilteredColimitsOfSize.{w', w} C] [HasFiniteLimits C]
    [AB5OfSize.{w', w} C] :
    AB5OfSize.{w', w} (HomologicalComplex C c) where
  ofShape J _ _ := by infer_instance

end HasZeroMorphisms

instance isGrothendieckAbelian [Abelian C] [IsGrothendieckAbelian.{w} C]
    [c.HasNoLoop] [Small.{w} ι] :
    IsGrothendieckAbelian.{w} (HomologicalComplex C c) where
  hasSeparator := by
    have : HasCoproductsOfShape ι C :=
      hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} ι)).symm
    infer_instance

end HomologicalComplex
