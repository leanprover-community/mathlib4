/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Coproducts in the category of Ind-objects

We show that if `C` has finite coproducts, then `Ind C` has small coproducts. It is shown elsewhere
that the functor `C ⥤ Inc C` preserves finite coproducts if `C` has finite colimits. It is not true
that the functors `C ⥤ Ind C` or `Ind C ⥤ Cᵒᵖ ⥤ Type v` preserves coproducts in general.
-/

universe w v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

variable {J : Type v} [SmallCategory J] [IsFiltered J]

noncomputable def Ind.yonedaYonedaColimit
  (F : J ⥤ Ind C) :
    Ind.yoneda.op ⋙ yoneda.obj (colimit F) ≅ Ind.yoneda.op ⋙ colimit (F ⋙ yoneda) :=
  Functor.fullyFaithfulCancelRight uliftFunctor.{u} <| calc
    (Ind.yoneda.op ⋙ yoneda.obj (colimit F)) ⋙ uliftFunctor.{u} ≅
        Ind.yoneda.op ⋙ yoneda.obj (colimit F) ⋙ uliftFunctor.{u} := Functor.associator _ _ _
    _ ≅ Ind.yoneda.op ⋙ (Ind.inclusion C).op ⋙ yoneda.obj ((Ind.inclusion C).obj (colimit F)) :=
        isoWhiskerLeft Ind.yoneda.op
          ((Functor.FullyFaithful.ofFullyFaithful (Ind.inclusion C)).homNatIsoMaxRight _).symm
    _ ≅ (Ind.yoneda ⋙ Ind.inclusion C).op ⋙ yoneda.obj ((Ind.inclusion C).obj (colimit F)) :=
        Iso.refl _
    _ ≅ yoneda.op ⋙ yoneda.obj ((Ind.inclusion C).obj (colimit F)) :=
        isoWhiskerRight (NatIso.op Ind.yonedaCompInclusion.symm) _
    _ ≅ yoneda.op ⋙ yoneda.obj (colimit (F ⋙ Ind.inclusion C)) :=
        isoWhiskerLeft yoneda.op (yoneda.mapIso (preservesColimitIso _ _))
    _ ≅ yoneda.op ⋙ colimit ((F ⋙ Ind.inclusion C) ⋙ yoneda) :=
        CategoryTheory.yonedaYonedaColimit _
    _ ≅ (Ind.yoneda ⋙ Ind.inclusion C).op ⋙ colimit ((F ⋙ Ind.inclusion C) ⋙ yoneda) :=
        isoWhiskerRight (NatIso.op Ind.yonedaCompInclusion) _
    _ ≅ Ind.yoneda.op ⋙ (Ind.inclusion C).op ⋙ colimit ((F ⋙ Ind.inclusion C) ⋙ yoneda) :=
        Iso.refl _
    _ ≅ Ind.yoneda.op ⋙ colimit ((F ⋙ Ind.inclusion C) ⋙
          yoneda ⋙ (whiskeringLeft _ _ _).obj (Ind.inclusion C).op) :=
        isoWhiskerLeft Ind.yoneda.op (colimitCompWhiskeringLeftIsoCompColimit _ _).symm
    _ ≅ Ind.yoneda.op ⋙ colimit (F ⋙ (Ind.inclusion C ⋙
          yoneda ⋙ (whiskeringLeft _ _ _).obj (Ind.inclusion C).op)) :=
        Iso.refl _
    _ ≅ Ind.yoneda.op ⋙ colimit (F ⋙ yoneda ⋙
          (CategoryTheory.whiskeringRight _ _ _).obj uliftFunctor.{u}) :=
        isoWhiskerLeft Ind.yoneda.op (HasColimit.isoOfNatIso
          (isoWhiskerLeft F
            (Functor.FullyFaithful.ofFullyFaithful
              (Ind.inclusion C)).compYonedaCompWhiskeringLeftMaxRight))
    _ ≅ Ind.yoneda.op ⋙ colimit ((F ⋙ yoneda) ⋙
          (CategoryTheory.whiskeringRight _ _ _).obj uliftFunctor.{u}) :=
        Iso.refl _
    _ ≅ _ := isoWhiskerLeft Ind.yoneda.op (colimitCompWhiskeringRightIsoColimitComp _ _)

end


section

variable {α : Type v} [Finite α] {I : α → Type v} [∀ s, SmallCategory (I s)] [∀ s, IsFiltered (I s)]
variable  (F : ∀ s, I s ⥤ C) [HasColimitsOfShape (Discrete α) C]

-- This is the λ in my notes
@[simps!]
noncomputable def pointwiseCoproduct : (∀ s, I s) ⥤ C where
  obj i := ∐ (fun s => (F s).obj (i s))
  map f := Sigma.map (fun s => (F s).map (f s))

section step1

variable (i : ∀ s, I s)

-- noncomputable def collection : α → Ind C := fun s => Ind.yoneda.obj ((F s).obj (i s))

-- -- Could be streamlined using a `Cofan.map` definition
-- noncomputable def cofan : Cofan (collection F i) :=
--   Cofan.mk (Ind.yoneda.obj (∐ fun s => (F s).obj (i s)))
--     (fun s => Ind.yoneda.map (Sigma.ι (fun s => (F s).obj (i s)) s))

noncomputable def collection00 : α → C := fun s => (F s).obj (i s)

noncomputable def cofan00 : Cofan (collection00 F i) :=
  Cofan.mk (∐ fun s => (F s).obj (i s))
    (fun s => Sigma.ι (fun s => (F s).obj (i s)) s)

noncomputable def stepM (X : C) : IsLimit (Fan.map (yoneda.obj X) _ ((cofan00 F i).op)) :=
  Cofan.isColimitYonedaEquiv _ _ (coproductIsCoproduct _) X

noncomputable def step0000 {J : Type v} [SmallCategory J] [IsFiltered J] (G : J ⥤ C) (j : J) :
    IsLimit
      (Fan.map (Ind.yoneda.op ⋙
       (G ⋙ Ind.yoneda ⋙ yoneda).flip ⋙ (evaluation _ _).obj j) _ (cofan00 F i).op) := by
  refine Fan.isLimitMapCongr _ _ _ (Iso.symm ?_) _ (stepM F i (G.obj j))

  calc
    Ind.yoneda.op ⋙ (G ⋙ Ind.yoneda ⋙ yoneda).flip ⋙ (evaluation J (Type v)).obj j ≅
      (Ind.yoneda.op ⋙ coyoneda ⋙
        (whiskeringLeft _ _ _).obj Ind.yoneda) ⋙
        (whiskeringLeft _ _ _).obj G ⋙ (evaluation J (Type v)).obj j
      -- (Ind.yoneda.op ⋙ yoneda ⋙ _ ⋙ (evaluation J (Type v)).obj j)
      := Iso.refl _
    _ ≅ coyoneda ⋙ (whiskeringLeft _ _ _).obj G ⋙ (evaluation J (Type v)).obj j
      := isoWhiskerRight (Functor.FullyFaithful.compCoyonedaSmall
        (Functor.FullyFaithful.ofFullyFaithful _))
        ((whiskeringLeft _ _ _).obj G ⋙ (evaluation J (Type v)).obj j)
    _ ≅ yoneda.obj (G.obj j) := Iso.refl _


noncomputable def step000 {J : Type v} [SmallCategory J] [IsFiltered J] (G : J ⥤ C) (j : J) :
    IsLimit
      (Fan.map (Ind.yoneda.op ⋙ (G ⋙ Ind.yoneda ⋙ yoneda).flip ⋙ (evaluation _ _).obj j) _ (cofan00 F i).op) :=
  step0000 F i G j

noncomputable def step00 {J : Type v} [SmallCategory J] [IsFiltered J] (G : J ⥤ C) :
    IsLimit (Fan.map (Ind.yoneda.op ⋙ (G ⋙ Ind.yoneda ⋙ yoneda).flip) _ (cofan00 F i).op) := by
  apply evaluationJointlyReflectsLimits
  intro j
  refine (Fan.isLimitMapConeEquiv _ _ _).symm ?_
  exact step000 F i G j

  -- refine Fan.isLimitMapCongr _ _ _ _ _ (stepM F i (G.obj j))


noncomputable def step01 {J : Type v} [SmallCategory J] [IsFiltered J] (G : J ⥤ C) :
    IsLimit (Fan.map colim _ (Fan.map (Ind.yoneda.op ⋙ (G ⋙ Ind.yoneda ⋙ yoneda).flip) _ (cofan00 F i).op)) :=
  isLimitFanMapOfIsLimit _ _ _ (step00 F i G)

noncomputable def step02 {J : Type v} [SmallCategory J] [IsFiltered J] (G : J ⥤ C) :
    IsLimit (Fan.map (Ind.yoneda.op ⋙ (G ⋙ Ind.yoneda ⋙ yoneda).flip ⋙ colim) _ (cofan00 F i).op) :=
  step01 F i G

noncomputable def step03 {J : Type v} [SmallCategory J] [IsFiltered J] (G : J ⥤ C) :
    IsLimit (Fan.map (Ind.yoneda.op ⋙ colimit (G ⋙ Ind.yoneda ⋙ yoneda)) _ (cofan00 F i).op) := by
  refine Fan.isLimitMapCongr _ _ _ ?_ _ (step02 F i G)
  exact isoWhiskerLeft _ (colimitIsoFlipCompColim _).symm

noncomputable def step04 {J : Type v} [SmallCategory J] [IsFiltered J] (G : J ⥤ C) :
    IsLimit (Fan.map (Ind.yoneda.op ⋙ colimit (G ⋙ Ind.yoneda ⋙ yoneda)) _ (cofan00 F i).op) := by
  exact step03 F i G
  -- sorry

noncomputable def step044 {J : Type v} [SmallCategory J] [IsFiltered J] (G : J ⥤ C) :
    IsLimit (Fan.map
      (Ind.yoneda.op ⋙ yoneda.obj (colimit (G ⋙ Ind.yoneda))) _ (cofan00 F i).op) := by
  refine Fan.isLimitMapCongr _ _ _ ?_ _ (step04 F i G)
  exact (Ind.yonedaYonedaColimit (G ⋙ Ind.yoneda)).symm

noncomputable def step045 {J : Type v} [SmallCategory J] [IsFiltered J] (G : J ⥤ C) :
    IsLimit (Fan.map (Ind.yoneda.op ⋙ yoneda.obj (colimit (G ⋙ Ind.yoneda))) _ (cofan00 F i).op) :=
  step044 F i G

noncomputable def step05 {J : Type v} [SmallCategory J] [IsFiltered J] (G : J ⥤ C) :
    IsLimit (Fan.map (Ind.yoneda.op ⋙ yoneda.obj (colimit (G ⋙ Ind.yoneda))) _ (cofan00 F i).op) := by
  exact step045 F i G

  noncomputable def step1 : IsColimit (Cofan.map Ind.yoneda _ (cofan00 F i)) := by
  refine (Cofan.isColimitYonedaEquiv _ (Cofan.map Ind.yoneda _ (cofan00 F i))).symm ?_
  intro L
  change IsLimit (Fan.map (Ind.yoneda.op ⋙ yoneda.obj L) _ (cofan00 F i).op)
  refine Fan.isLimitMapCongr _ _ _ ?_ _ (step05 F i L.2.presentation.F)
  refine isoWhiskerLeft _ (yoneda.mapIso ?_)
  have hInc : (Ind.inclusion C).FullyFaithful := .ofFullyFaithful _
  refine hInc.isoEquiv.symm ?_
  refine preservesColimitIso _ _ ≪≫ ?_
  refine HasColimit.isoOfNatIso (Functor.associator _ _ _) ≪≫ ?_
  refine HasColimit.isoOfNatIso (isoWhiskerLeft _ Ind.yonedaCompInclusion) ≪≫ ?_
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) L.2.presentation.isColimit

-- instance : HasColimit (Discrete.functor (collection F i)) :=
--   ⟨_, step1 F i⟩

-- noncomputable def step1iso : ∐ collection F i ≅ Ind.yoneda.obj (∐ fun s => (F s).obj (i s)) :=
--   IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (step1 F i)

end step1

section step15

noncomputable def collection15 : α → (∀ s, I s) ⥤ Ind C := fun s => Pi.eval I s ⋙ F s ⋙ Ind.yoneda

noncomputable def collection15CompEvaluation (i : ∀ s, I s) :
    Discrete.functor (collection15 F) ⋙ (evaluation _ _).obj i ≅
      Discrete.functor (collection00 (fun s => F s ⋙ Ind.yoneda) i) :=
  Discrete.compNatIsoDiscrete _ _

noncomputable def cofan15 : Cofan (collection15 F) :=
  Cofan.mk (pointwiseCoproduct F ⋙ Ind.yoneda) (fun s =>
    ((Functor.associator _ _ _).inv ≫ whiskerRight
        { app := fun i => Sigma.ι (fun s => (F s).obj (i s)) s } Ind.yoneda))

noncomputable def step15 : IsColimit (cofan15 F) := by
  apply evaluationJointlyReflectsColimits
  intro i
  let t := step1 F i
  let t' := (IsColimit.precomposeHomEquiv (collection15CompEvaluation F i) _).symm t
  refine IsColimit.ofIsoColimit t' (Cocones.ext (Iso.refl _))

end step15

section step2

noncomputable def collection2 : α → Ind C := fun s => colimit (Pi.eval I s ⋙ F s ⋙ Ind.yoneda)

noncomputable def collection15CompColim :
    Discrete.functor (collection15 F) ⋙ colim ≅ Discrete.functor (collection2 F) :=
  Discrete.compNatIsoDiscrete _ _

noncomputable def cofan2 : Cofan (collection2 F) :=
  Cofan.mk (colimit (pointwiseCoproduct F ⋙ Ind.yoneda))
    (fun s => colimMap ((Functor.associator _ _ _).inv ≫ whiskerRight
        { app := fun i => Sigma.ι (fun s => (F s).obj (i s)) s } Ind.yoneda))

noncomputable def step2 : IsColimit (cofan2 F) := by
  let t := PreservesColimit.preserves (F := colim) (step15 F)
  let t' := (IsColimit.precomposeInvEquiv (collection15CompColim F) _).symm t
  refine IsColimit.ofIsoColimit t' (Cocones.ext (Iso.refl _) ?_)
  intro ⟨j⟩
  simp [collection15CompColim, collection15, cofan15, cofan2]
  exact Category.id_comp _

theorem hasColimit_collection2 : HasColimit (Discrete.functor (collection2 F)) :=
  ⟨_, step2 F⟩

end step2

end

section

variable {α : Type v} [Finite α] [HasColimitsOfShape (Discrete α) C]

instance final (f : α → Ind C) : HasColimit (Discrete.functor f) := by
  -- Evil evil defeq abuse here........
  let I : α → Type v := fun s => (f s).2.presentation.I
  let F : ∀ s, I s ⥤ C := fun s => (f s).2.presentation.F
  let q : ∀ s, collection2 F s ≅ f s := by
    intro s
    dsimp [collection2]
    refine (Functor.Final.colimitIso (Pi.eval I s) (F s ⋙ Ind.yoneda)) ≪≫ ?_
    have hInc : (Ind.inclusion C).FullyFaithful := .ofFullyFaithful _
    refine hInc.isoEquiv.symm ?_
    refine preservesColimitIso _ _ ≪≫ ?_
    refine HasColimit.isoOfNatIso (Functor.associator _ _ _) ≪≫ ?_
    refine HasColimit.isoOfNatIso (isoWhiskerLeft (F s) Ind.yonedaCompInclusion) ≪≫ ?_
    exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (f s).2.presentation.isColimit
  suffices Discrete.functor f ≅ Discrete.functor (collection2 F) by
    have _ := hasColimit_collection2 F
    apply hasColimitOfIso this
  apply Discrete.natIso
  exact fun s => (q s.as).symm

theorem done : HasColimitsOfShape (Discrete α) (Ind C) where
  has_colimit _ := hasColimitOfIso (Discrete.natIsoFunctor)

#print axioms done

end

end CategoryTheory.Limits
