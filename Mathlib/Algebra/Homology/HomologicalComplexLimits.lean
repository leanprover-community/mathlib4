import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.LibrarySearch


open CategoryTheory Category Limits

namespace CategoryTheory.Limits

variable {J C D : Type _} [Category J] [Category C] [Category D]
  [HasZeroMorphisms C] [HasZeroObject C]
  [HasZeroMorphisms D] [HasZeroObject D]
  (F : J ⥤ C) (hF : IsZero F) (G : C ⥤ D) (hG : IsZero G)

def IsLimit.ofIsZero (c : Cone F) (hc : IsZero c.pt) : IsLimit c where
  lift _ := 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_tgt _ _
  uniq _ _ _ := hc.eq_of_tgt _ _

def preservesLimitsOfShapeOfIsZero : PreservesLimitsOfShape J G :=
  ⟨fun {_} => ⟨fun hc => by
    rw [Functor.isZero_iff] at hG
    apply IsLimit.ofIsZero
    . rw [Functor.isZero_iff]
      intro X
      apply hG
    . apply hG⟩⟩

def IsColimit.ofIsZero (c : Cocone F) (hc : IsZero c.pt) : IsColimit c where
  desc _ := 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_src _ _
  uniq _ _ _ := hc.eq_of_src _ _

def preservesColimitsOfShapeOfIsZero : PreservesColimitsOfShape J G :=
  ⟨fun {_} => ⟨fun hc => by
    rw [Functor.isZero_iff] at hG
    apply IsColimit.ofIsZero
    . rw [Functor.isZero_iff]
      intro X
      apply hG
    . apply hG⟩⟩

end CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type _} {ι J : Type _} [Category C] [Category J] {c : ComplexShape ι}
  [HasZeroMorphisms C] (F : J ⥤ HomologicalComplex C c)

variable (C c)

noncomputable def singleCompEvalIsoSelf [HasZeroObject C] [DecidableEq ι] (i : ι) : single C c i ⋙ eval C c i ≅ 𝟭 _ :=
  NatIso.ofComponents (fun A => singleObjXSelf C c i A) (by aesop_cat)

lemma isZeroSingleCompEval [HasZeroObject C] [DecidableEq ι] (i j : ι) (h : i ≠ j) :
    IsZero (single C c i ⋙ eval C c j) := by
  rw [Functor.isZero_iff]
  intro A
  dsimp
  rw [if_neg (Ne.symm h)]
  apply Limits.isZero_zero

variable {C c}

section

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

noncomputable def isLimitConeOfHasLimitEval : IsLimit (coneOfHasLimitEval F) := by
  apply isLimitOfEval
  intro i
  exact limit.isLimit _

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

noncomputable def isColimitCoconeOfHasColimitEval : IsColimit (coconeOfHasColimitEval F) := by
  apply isColimitOfEval
  intro i
  exact colimit.isColimit _

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

def preservesLimitsOfShapeOfEval {D : Type _} [Category D]
    (G : D ⥤ HomologicalComplex C c) [HasLimitsOfShape J C]
    (_ : ∀ (i : ι), PreservesLimitsOfShape J (G ⋙ eval C c i)) :
    PreservesLimitsOfShape J G :=
  ⟨fun {_} => ⟨fun hs =>  isLimitOfEval _ _
    (fun i => isLimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩

def preservesColimitsOfShapeOfEval {D : Type _} [Category D]
    (G : D ⥤ HomologicalComplex C c) [HasColimitsOfShape J C]
    (_ : ∀ (i : ι), PreservesColimitsOfShape J (G ⋙ eval C c i)) :
    PreservesColimitsOfShape J G :=
  ⟨fun {_} => ⟨fun hs =>  isColimitOfEval _ _
    (fun i => isColimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩

section

variable [HasZeroObject C] [DecidableEq ι]

noncomputable instance [HasLimitsOfShape J C] (i : ι) :
    PreservesLimitsOfShape J (single C c i) :=
  preservesLimitsOfShapeOfEval _ (fun j => by
    by_cases i = j
    . subst h
      exact preservesLimitsOfShapeOfNatIso (singleCompEvalIsoSelf C c i).symm
    . exact preservesLimitsOfShapeOfIsZero _ (isZeroSingleCompEval C c _ _ h))

noncomputable instance [HasColimitsOfShape J C] (i : ι) :
    PreservesColimitsOfShape J (single C c i) :=
  preservesColimitsOfShapeOfEval _ (fun j => by
    by_cases i = j
    . subst h
      exact preservesColimitsOfShapeOfNatIso (singleCompEvalIsoSelf C c i).symm
    . exact preservesColimitsOfShapeOfIsZero _ (isZeroSingleCompEval C c _ _ h))

noncomputable instance [HasFiniteLimits C] (i : ι) :
    PreservesFiniteLimits (single C c i) := ⟨by intros ; infer_instance⟩

noncomputable instance [HasFiniteColimits C] (i : ι) :
    PreservesFiniteColimits (single C c i) := ⟨by intros ; infer_instance⟩

end

end HomologicalComplex
