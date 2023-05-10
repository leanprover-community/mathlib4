import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C : Type _} {ι J : Type _} [Category C] [Category J] {c : ComplexShape ι}
  [HasZeroMorphisms C] (F : J ⥤ HomologicalComplex C c)

section

variable [∀ (n : ι), HasLimit (F ⋙ eval C c n)]

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

noncomputable def isLimitConeOfHasLimitEval : IsLimit (coneOfHasLimitEval F) where
  lift := fun s =>
    { f := fun n => limit.lift _ ((eval C c n).mapCone s) }
  uniq s m hm := by
    ext1 n
    refine' limit.hom_ext (fun j => _)
    simp only [limit.lift_π, Functor.mapCone_π_app, ← hm, eval_map, comp_f,
      coneOfHasLimitEval_π_app_f]

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

section

variable [∀ (n : ι), HasColimit (F ⋙ HomologicalComplex.eval C c n)]

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

noncomputable def isColimitCoconeOfHasColimitEval : IsColimit (coconeOfHasColimitEval F) where
  desc := fun s => { f := fun n => colimit.desc _ ((eval C c n).mapCocone s) }
  uniq s m hm := by
    ext1 n
    refine' colimit.hom_ext (fun j => _)
    simp only [colimit.ι_desc, Functor.mapCocone_ι_app, ← hm, eval_map, comp_f,
      coconeOfHasColimitEval_ι_app_f]

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

end HomologicalComplex
