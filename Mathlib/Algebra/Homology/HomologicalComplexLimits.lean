/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Limits and colimits in the category of homological complexes

In this file, it is shown that if a category `C` has (co)limits of shape `J`,
then it is also the case of the categories `HomologicalComplex C c`,
and the evaluation functors `eval C c i : HomologicalComplex C c ⥤ C`
commute to these.

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C ι J : Type*} [Category C] [Category J] {c : ComplexShape ι} [HasZeroMorphisms C]

section

variable (F : J ⥤ HomologicalComplex C c)

/-- A cone in `HomologicalComplex C c` is limit if the induced cones obtained
by applying `eval C c i : HomologicalComplex C c ⥤ C` for all `i` are limit. -/
def isLimitOfEval (s : Cone F)
    (hs : ∀ (i : ι), IsLimit ((eval C c i).mapCone s)) : IsLimit s where
  lift t :=
    { f := fun i => (hs i).lift ((eval C c i).mapCone t)
      comm' := fun i i' _ => by
        apply IsLimit.hom_ext (hs i')
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCone t)
        simp only [Functor.mapCone_π_app, eval_map] at eq
        simp only [Functor.mapCone_π_app, eval_map, assoc]
        rw [eq i', ← Hom.comm, reassoc_of% (eq i), Hom.comm] }
  fac t j := by
    ext i
    apply (hs i).fac
  uniq t m hm := by
    ext i
    apply (hs i).uniq ((eval C c i).mapCone t)
    intro j
    dsimp
    simp only [← comp_f, hm]

variable [∀ (n : ι), HasLimit (F ⋙ eval C c n)]

/-- A cone for a functor `F : J ⥤ HomologicalComplex C c` which is given in degree `n` by
the limit `F ⋙ eval C c n`. -/
@[simps]
noncomputable def coneOfHasLimitEval : Cone F where
  pt :=
    { X := fun n => limit (F ⋙ eval C c n)
      d := fun n m => limMap { app := fun j => (F.obj j).d n m }
      shape := fun {n m} h => by
        ext j
        rw [limMap_π]
        dsimp
        rw [(F.obj j).shape _ _ h, comp_zero, zero_comp] }
  π :=
    { app := fun j => { f := fun n => limit.π _ j }
      naturality := fun i j φ => by
        ext n
        dsimp
        erw [limit.w, id_comp] }

/-- The cone `coneOfHasLimitEval F` is limit. -/
noncomputable def isLimitConeOfHasLimitEval : IsLimit (coneOfHasLimitEval F) :=
  isLimitOfEval _ _ (fun _ => limit.isLimit _)

instance : HasLimit F := ⟨⟨⟨_, isLimitConeOfHasLimitEval F⟩⟩⟩

noncomputable instance (n : ι) : PreservesLimit F (eval C c n) :=
  preservesLimitOfPreservesLimitCone (isLimitConeOfHasLimitEval F) (limit.isLimit _)

end

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (HomologicalComplex C c) := ⟨inferInstance⟩

noncomputable instance [HasLimitsOfShape J C] (n : ι) :
  PreservesLimitsOfShape J (eval C c n) := ⟨inferInstance⟩

instance [HasFiniteLimits C] : HasFiniteLimits (HomologicalComplex C c) :=
  ⟨fun _ _ => inferInstance⟩

noncomputable instance [HasFiniteLimits C] (n : ι) :
  PreservesFiniteLimits (eval C c n) := ⟨fun _ _ _ => inferInstance⟩

instance [HasFiniteLimits C] {K L : HomologicalComplex C c} (φ : K ⟶ L) [Mono φ] (n : ι) :
    Mono (φ.f n) := by
  change Mono ((HomologicalComplex.eval C c n).map φ)
  infer_instance

section

variable (F : J ⥤ HomologicalComplex C c)

/-- A cocone in `HomologicalComplex C c` is colimit if the induced cocones obtained
by applying `eval C c i : HomologicalComplex C c ⥤ C` for all `i` are colimit. -/
def isColimitOfEval (s : Cocone F)
    (hs : ∀ (i : ι), IsColimit ((eval C c i).mapCocone s)) : IsColimit s where
  desc t :=
    { f := fun i => (hs i).desc ((eval C c i).mapCocone t)
      comm' := fun i i' _ => by
        apply IsColimit.hom_ext (hs i)
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCocone t)
        simp only [Functor.mapCocone_ι_app, eval_map] at eq
        simp only [Functor.mapCocone_ι_app, eval_map, assoc]
        rw [reassoc_of% (eq i), Hom.comm_assoc, eq i', Hom.comm] }
  fac t j := by
    ext i
    apply (hs i).fac
  uniq t m hm := by
    ext i
    apply (hs i).uniq ((eval C c i).mapCocone t)
    intro j
    dsimp
    simp only [← comp_f, hm]


variable [∀ (n : ι), HasColimit (F ⋙ HomologicalComplex.eval C c n)]

/-- A cocone for a functor `F : J ⥤ HomologicalComplex C c` which is given in degree `n` by
the colimit of `F ⋙ eval C c n`. -/
@[simps]
noncomputable def coconeOfHasColimitEval : Cocone F where
  pt :=
    { X := fun n => colimit (F ⋙ eval C c n)
      d := fun n m => colimMap { app := fun j => (F.obj j).d n m }
      shape := fun {n m} h => by
        ext j
        rw [ι_colimMap]
        dsimp
        rw [(F.obj j).shape _ _ h, zero_comp, comp_zero] }
  ι :=
    { app := fun j => { f := fun n => colimit.ι (F ⋙ eval C c n) j }
      naturality := fun i j φ => by
        ext n
        dsimp
        erw [colimit.w (F ⋙ eval C c n) φ, comp_id] }

/-- The cocone `coconeOfHasLimitEval F` is colimit. -/
noncomputable def isColimitCoconeOfHasColimitEval : IsColimit (coconeOfHasColimitEval F) :=
  isColimitOfEval _ _ (fun _ => colimit.isColimit _)

instance : HasColimit F := ⟨⟨⟨_, isColimitCoconeOfHasColimitEval F⟩⟩⟩

noncomputable instance (n : ι) : PreservesColimit F (eval C c n) :=
  preservesColimitOfPreservesColimitCocone (isColimitCoconeOfHasColimitEval F)
    (colimit.isColimit _)

end

instance [HasColimitsOfShape J C] : HasColimitsOfShape J (HomologicalComplex C c) := ⟨inferInstance⟩

noncomputable instance [HasColimitsOfShape J C] (n : ι) :
  PreservesColimitsOfShape J (eval C c n) := ⟨inferInstance⟩

instance [HasFiniteColimits C] : HasFiniteColimits (HomologicalComplex C c) :=
  ⟨fun _ _ => inferInstance⟩

noncomputable instance [HasFiniteColimits C] (n : ι) :
  PreservesFiniteColimits (eval C c n) := ⟨fun _ _ _ => inferInstance⟩

instance [HasFiniteColimits C] {K L : HomologicalComplex C c} (φ : K ⟶ L) [Epi φ] (n : ι) :
    Epi (φ.f n) := by
  change Epi ((HomologicalComplex.eval C c n).map φ)
  infer_instance

/-- A functor `D ⥤ HomologicalComplex C c` preserves limits of shape `J`
if for any `i`, `G ⋙ eval C c i` does. -/
def preservesLimitsOfShapeOfEval {D : Type*} [Category D]
    (G : D ⥤ HomologicalComplex C c)
    (_ : ∀ (i : ι), PreservesLimitsOfShape J (G ⋙ eval C c i)) :
    PreservesLimitsOfShape J G :=
  ⟨fun {_} => ⟨fun hs ↦ isLimitOfEval _ _
    (fun i => isLimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩

/-- A functor `D ⥤ HomologicalComplex C c` preserves colimits of shape `J`
if for any `i`, `G ⋙ eval C c i` does. -/
def preservesColimitsOfShapeOfEval {D : Type*} [Category D]
    (G : D ⥤ HomologicalComplex C c)
    (_ : ∀ (i : ι), PreservesColimitsOfShape J (G ⋙ eval C c i)) :
    PreservesColimitsOfShape J G :=
  ⟨fun {_} => ⟨fun hs ↦ isColimitOfEval _ _
    (fun i => isColimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩

end HomologicalComplex
