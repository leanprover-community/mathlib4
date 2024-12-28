/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.SmallObject.Construction
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.CategoryTheory.MorphismProperty.IsSmall
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Cardinals that are suitable for the small object argument

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/

universe w v v' u u'

lemma Cardinal.zero_lt_ord_iff (κ : Cardinal.{w}) : 0 < κ.ord ↔ κ ≠ 0 := by
  constructor
  · intro h h'
    simp only [h', ord_zero, lt_self_iff_false] at h
  · intro h
    by_contra!
    exact h (ord_eq_zero.1 (le_antisymm this (Ordinal.zero_le _)))

noncomputable def Cardinal.IsRegular.orderBotOrdToType
    {κ : Cardinal.{w}} (hκ : κ.IsRegular) : OrderBot κ.ord.toType :=
  Ordinal.toTypeOrderBotOfPos (by
    rw [Cardinal.zero_lt_ord_iff]
    rintro rfl
    apply Cardinal.aleph0_ne_zero.{w}
    simpa using hκ.aleph0_le)

namespace CategoryTheory

open Category

noncomputable instance (o : Ordinal.{w}) : SuccOrder o.toType :=
  SuccOrder.ofLinearWellFoundedLT o.toType

open Limits SmallObject

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (I : MorphismProperty C)

section

variable (J : Type u') [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

lemma transfiniteCompositionsOfShape_pushouts_coproducts_le_rlp_llp :
    (coproducts.{w} I).pushouts.transfiniteCompositionsOfShape J ≤ I.rlp.llp := by
  simpa using transfiniteCompositionsOfShape_le_rlp_llp (coproducts.{w} I).pushouts J

lemma retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_rlp_llp :
    ((coproducts.{w} I).pushouts.transfiniteCompositionsOfShape J).retracts ≤ I.rlp.llp := by
  rw [le_llp_iff_le_rlp, retracts_rlp, ← le_llp_iff_le_rlp]
  apply transfiniteCompositionsOfShape_pushouts_coproducts_le_rlp_llp

end

lemma transfiniteCompositions_pushouts_coproducts_le_rlp_llp :
    (transfiniteCompositions.{w} (coproducts.{w} I).pushouts) ≤ I.rlp.llp := by
  simpa using transfiniteCompositions_le_rlp_llp (coproducts.{w} I).pushouts

lemma retracts_transfiniteComposition_pushouts_coproducts_le_rlp_llp :
    (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts ≤ I.rlp.llp := by
  rw [le_llp_iff_le_rlp, retracts_rlp, ← le_llp_iff_le_rlp]
  apply transfiniteCompositions_pushouts_coproducts_le_rlp_llp

class IsCardinalForSmallObjectArgument (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.toType] : Prop where
  isSmall : IsSmall.{w} I := by infer_instance
  locallySmall : LocallySmall.{w} C := by infer_instance
  hasPushouts : HasPushouts C := by infer_instance
  hasCoproducts : HasCoproducts.{w} C := by infer_instance
  hasIterationOfShape : HasIterationOfShape C κ.ord.toType
  preservesColimit :
      ∀ {A B : C} (i : A ⟶ B) (_ : I i)
      (F : κ.ord.toType ⥤ C) [F.IsWellOrderContinuous]
      (_ : ∀ (j : _) (_ : ¬IsMax j),
        (coproducts.{w} I).pushouts (F.map (homOfLE (Order.le_succ j)))),
      PreservesColimit F (coyoneda.obj (Opposite.op A))

end MorphismProperty

namespace SmallObject

open MorphismProperty

variable (I : MorphismProperty C)

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.toType]
  [I.IsCardinalForSmallObjectArgument κ]

include I κ

lemma isSmall : IsSmall.{w} I :=
  IsCardinalForSmallObjectArgument.isSmall κ

lemma locallySmall : LocallySmall.{w} C :=
  IsCardinalForSmallObjectArgument.locallySmall I κ

lemma hasIterationOfShape : HasIterationOfShape C κ.ord.toType :=
  IsCardinalForSmallObjectArgument.hasIterationOfShape I

lemma hasPushouts : HasPushouts C :=
  IsCardinalForSmallObjectArgument.hasPushouts I κ

lemma hasCoproducts : HasCoproducts.{w} C :=
  IsCardinalForSmallObjectArgument.hasCoproducts I κ

lemma preservesColimit_coyoneda_obj
    {A B : C} (i : A ⟶ B) (hi : I i)
    (F : κ.ord.toType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ (j : κ.ord.toType) (_ : ¬IsMax j),
      (coproducts.{w} I).pushouts (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F (coyoneda.obj (Opposite.op A)) :=
  IsCardinalForSmallObjectArgument.preservesColimit i hi F hF

lemma small_functorObjIndex {X Y : C} (p : X ⟶ Y) :
    Small.{w} (FunctorObjIndex I.homFamily p) := by
  have := locallySmall I κ
  have := isSmall I κ
  let φ : FunctorObjIndex I.homFamily p →
    Σ (i : Shrink.{w} I.toSet),
      Shrink.{w} ((((equivShrink _).symm i).1.left ⟶ X) ×
        (((equivShrink _).symm i).1.right ⟶ Y)) :=
        fun x ↦ ⟨equivShrink _ x.i, equivShrink _
          (⟨eqToHom (by simp) ≫ x.t, eqToHom (by simp) ≫ x.b⟩)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨i₁, t₁, b₁, _⟩ ⟨i₂, t₂, b₂, _⟩ h
    obtain rfl : i₁ = i₂ := by simpa using congr_arg Sigma.fst h
    simpa [cancel_epi, φ] using h
  exact small_of_injective hφ

lemma hasColimitsOfShape_discrete (X Y : C) (p : X ⟶ Y) :
    HasColimitsOfShape
      (Discrete (FunctorObjIndex I.homFamily p)) C := by
  have := small_functorObjIndex I κ p
  have := hasCoproducts I κ
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} _)).symm

noncomputable def succStruct : SuccStruct (Arrow C ⥤ Arrow C) :=
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  SuccStruct.ofNatTrans (ε I.homFamily)

noncomputable def iterationFunctor : κ.ord.toType ⥤ Arrow C ⥤ Arrow C :=
  have := hasIterationOfShape I κ
  (succStruct I κ).iterationFunctor κ.ord.toType

instance : (iterationFunctor I κ).IsWellOrderContinuous := by
  dsimp [iterationFunctor]
  infer_instance

instance (f : Arrow C) :
    (iterationFunctor I κ ⋙ (evaluation _ _).obj f).IsWellOrderContinuous := by
  have := hasIterationOfShape I κ
  infer_instance

noncomputable def iteration : Arrow C ⥤ Arrow C :=
  have := hasIterationOfShape I κ
  (succStruct I κ).iteration κ.ord.toType

noncomputable def iterationCocone : Cocone (iterationFunctor I κ) :=
  have := hasIterationOfShape I κ
  (succStruct I κ).iterationCocone κ.ord.toType

@[simp]
lemma iterationCocone_pt : (iterationCocone I κ).pt = iteration I κ := rfl

@[reassoc (attr := simp)]
lemma iterationCocone_w_app_app_left
    (f : Arrow C) {j₁ j₂ : κ.ord.toType} (g : j₁ ⟶ j₂) :
    (((iterationFunctor I κ).map g).app f).left ≫ (((iterationCocone I κ).ι.app j₂).app f).left =
      (((iterationCocone I κ).ι.app j₁).app f).left := by
  rw [← Arrow.comp_left, ← NatTrans.comp_app, Cocone.w]

noncomputable def isColimitIterationCocone : IsColimit (iterationCocone I κ) :=
  have := hasIterationOfShape I κ
  colimit.isColimit _

noncomputable def ιIteration : 𝟭 _ ⟶ iteration I κ :=
  have := hasIterationOfShape I κ
  (succStruct I κ).ιIteration κ.ord.toType

def propArrow : MorphismProperty (Arrow C) := fun _ _ f ↦
  (coproducts.{w} I).pushouts f.left ∧ (isomorphisms C) f.right

lemma succStruct_prop_le_propArrow :
    (succStruct I κ).prop ≤ (propArrow.{w} I).functorCategory (Arrow C) := by
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  intro _ _ _ ⟨F⟩ f
  constructor
  · have := small_functorObjIndex I κ (F.obj f).hom
    nth_rw 1 [← I.ofHoms_homFamily]
    apply pushouts_mk _ (functorObj_isPushout I.homFamily (F.obj f).hom)
    exact coproducts_of_small _ _
      (colimitsOfShape_colimMap _ _ (by rintro ⟨j⟩; constructor))
  · rw [MorphismProperty.isomorphisms.iff]
    dsimp [succStruct]
    infer_instance

lemma transfiniteCompositionOfShape_succStruct_prop_ιIteration :
    (succStruct I κ).prop.transfiniteCompositionsOfShape κ.ord.toType (ιIteration I κ) := by
  have := hasIterationOfShape I κ
  apply SuccStruct.transfiniteCompositionOfShape_ιIteration

lemma transfiniteCompositionOfShape_propArrow_ιIteration :
    ((propArrow.{w} I).functorCategory (Arrow C)).transfiniteCompositionsOfShape
      κ.ord.toType (ιIteration I κ) :=
  monotone_transfiniteCompositionsOfShape _ (succStruct_prop_le_propArrow I κ) _
    (transfiniteCompositionOfShape_succStruct_prop_ιIteration I κ)

instance : IsStableUnderTransfiniteComposition.{w} (isomorphisms C) := sorry

instance isIso_ιIteration_app_right (f : Arrow C) :
    IsIso ((ιIteration I κ).app f).right := by
  have := hasIterationOfShape I κ
  suffices (isomorphisms _).transfiniteCompositionsOfShape κ.ord.toType
      (((evaluation _ (Arrow C)).obj f ⋙ Arrow.rightFunc).map (ιIteration I κ)) from
    (isomorphisms C).transfiniteCompositionsOfShape_le κ.ord.toType _ this
  apply transfiniteCompositionsOfShape_map_of_preserves
  apply monotone_transfiniteCompositionsOfShape _ _ _
    (transfiniteCompositionOfShape_propArrow_ιIteration I κ)
  intro _ _ _ h
  exact (h f).2

instance (f : Arrow C) (j : κ.ord.toType) :
    IsIso (((iterationCocone I κ).ι.app j).app f) :=
  sorry

instance : IsIso (whiskerRight (ιIteration I κ) Arrow.rightFunc) := by
  rw [NatTrans.isIso_iff_isIso_app]
  dsimp
  infer_instance

lemma transfiniteCompositionsOfShape_ιIteration_app_left (f : Arrow C) :
    (coproducts.{w} I).pushouts.transfiniteCompositionsOfShape κ.ord.toType
      ((ιIteration I κ).app f).left := by
  have := hasIterationOfShape I κ
  change (coproducts.{w} I).pushouts.transfiniteCompositionsOfShape κ.ord.toType
    (((evaluation _ (Arrow C)).obj f ⋙ Arrow.leftFunc).map (ιIteration I κ))
  apply transfiniteCompositionsOfShape_map_of_preserves
  apply monotone_transfiniteCompositionsOfShape _ _ _
    (transfiniteCompositionOfShape_propArrow_ιIteration I κ)
  intro _ _ _ h
  exact (h f).1

def iterationFunctorObjSuccObjLeftIso (f : Arrow C) (j : κ.ord.toType) (hj : ¬ IsMax j) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    (((iterationFunctor I κ).obj (Order.succ j)).obj f).left ≅
        functorObj I.homFamily (((iterationFunctor I κ).obj j).obj f).hom := by
  sorry

@[reassoc (attr := simp)]
def ιFunctorObj_iterationFunctorObjSuccObjLeftIso_inv
    (f : Arrow C) (j : κ.ord.toType) (hj : ¬ IsMax j) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    ιFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj f).hom ≫
      (iterationFunctorObjSuccObjLeftIso I κ f j hj).inv =
        (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).left := by
  sorry

lemma hasRightLiftingProperty_iteration_obj_hom (f : Arrow C) {A B : C} (i : A ⟶ B) (hi : I i):
    HasLiftingProperty i ((iteration I κ).obj f).hom := ⟨by
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  have := hasIterationOfShape I κ
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  intro g b sq
  have : PreservesColimit (iterationFunctor I κ ⋙
    ((evaluation (Arrow C) (Arrow C)).obj f ⋙ Arrow.leftFunc))
      (coyoneda.obj (Opposite.op A)) :=
    preservesColimit_coyoneda_obj I κ i hi _
      (fun j hj ↦ (succStruct_prop_le_propArrow I κ _
        ((succStruct I κ).prop_iterationFunctor_map_succ j hj) f).1)
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (((evaluation _ _).obj f ⋙ Arrow.leftFunc) ⋙
      coyoneda.obj (Opposite.op A)) (isColimitIterationCocone I κ)) g
  dsimp at g b t ht
  let x : FunctorObjIndex I.homFamily (((iterationFunctor I κ).obj j).obj f).hom :=
    { i := ⟨Arrow.mk i, hi⟩
      t := t
      b := b ≫ (inv (((iterationCocone I κ).ι.app j).app f)).right
      w := by
        have := (((iterationCocone I κ).ι.app j).app f).w
        dsimp at this
        rw [← cancel_mono (((iterationCocone I κ).ι.app j).app f).right, assoc, assoc, assoc,
          ← Arrow.comp_right, IsIso.inv_hom_id, Arrow.id_right, ← this,
          reassoc_of% ht]
        simp [comp_id, homFamily, sq.w] }
  exact ⟨⟨{
    l := Sigma.ι (functorObjTgtFamily _ _) x ≫ ρFunctorObj _ _ ≫
          (iterationFunctorObjSuccObjLeftIso I κ f j (not_isMax j)).inv ≫
          (((iterationCocone I κ).ι.app (Order.succ j)).app f).left
    fac_left := by
      have := x.comm
      dsimp [homFamily_apply] at this ⊢
      simp [reassoc_of% this, ← ht]
    fac_right := by
      dsimp
      simp only [assoc]
      simp only [assoc, Arrow.w_mk_right, Functor.id_obj, Arrow.mk_right]
      sorry }⟩⟩⟩
    /-
    exact ⟨⟨{
      l := Sigma.ι (functorObjTgtFamily _ _) x ≫ ρFunctorObj _ _ ≫
        (inductiveSystemForgetObjSuccIso f J p j (not_isMax j)).inv ≫
        (inductiveSystemForgetCocone f J p).ι.app (Order.succ j)
      fac_left := by
        erw [x.comm_assoc]
        simp [← ht, ιFunctorObj_inductiveSystemForgetObjSuccIso_inv_assoc]
      fac_right := by simp }⟩⟩-/

noncomputable def functorialFactorizationData :
    FunctorialFactorizationData I.rlp.llp I.rlp where
  Z := iteration I κ ⋙ Arrow.leftFunc
  i := whiskerRight (ιIteration I κ) Arrow.leftFunc
  p := whiskerLeft (iteration I κ) Arrow.leftToRight ≫
    inv (whiskerRight (ιIteration I κ) Arrow.rightFunc)
  hi f := by
    apply I.transfiniteCompositionsOfShape_pushouts_coproducts_le_rlp_llp κ.ord.toType
    apply transfiniteCompositionsOfShape_ιIteration_app_left
  hp f := by
    apply RespectsIso.postcomp
    apply hasRightLiftingProperty_iteration_obj_hom

lemma hasFunctorialFactorization :
    HasFunctorialFactorization I.rlp.llp I.rlp where
  nonempty_functorialFactorizationData :=
    ⟨functorialFactorizationData I κ⟩

/-- If `κ` is a suitable cardinal for the small object argument for `I : MorphismProperty C`,
then the class `I.rlp.llp` is exactly the class of morphisms that are retracts
of transfinite compositions (of shape `κ.ord.toType`) of pushouts of coproducts
of maps in `I`.  -/
lemma rlp_llp_of_isCardinalForSmallObjectArgument' :
    I.rlp.llp = (transfiniteCompositionsOfShape
      (coproducts.{w} I).pushouts κ.ord.toType).retracts := by
  refine le_antisymm ?_
    (retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_rlp_llp I κ.ord.toType)
  -- reintroduce obj, ιObj, πObj...
  sorry
  /-apply le_antisymm
  · intro X Y f hf
    replace hf := hf _ (rlp_πObject I κ f)
    have sq : CommSq (ιObject I κ f) f (πObject I κ f) (𝟙 _) := ⟨by simp⟩
    refine ⟨_, _, _, ?_, transfiniteCompositionsOfShape_ιObject I κ f⟩
    -- this is a particular case of the retract argument
    exact
      { i := Arrow.homMk (u := 𝟙 X) (v := sq.lift) (by simp)
        r := Arrow.homMk (u := 𝟙 X) (v := πObject I κ f) (by simp) }
  · rw [le_llp_iff_le_rlp, retracts_rlp, ← le_llp_iff_le_rlp]
    (coproducts.{w} I).pushouts κ.ord.toType-/


/-- If `κ` is a suitable cardinal for the small object argument for `I : MorphismProperty C`,
then the class `I.rlp.llp` is exactly the class of morphisms that are retracts
of transfinite compositions of pushouts of coproducts of maps in `I`.  -/
lemma rlp_llp_of_isCardinalForSmallObjectArgument :
    I.rlp.llp =
      (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts := by
  refine le_antisymm ?_
    (retracts_transfiniteComposition_pushouts_coproducts_le_rlp_llp I)
  rw [rlp_llp_of_isCardinalForSmallObjectArgument' I κ]
  apply monotone_retracts
  apply transfiniteCompositionsOfShape_le_transfiniteCompositions

/-
variable (Y) in
noncomputable def transfiniteIterationFunctor : Over Y ⥤ Over Y :=
  have := hasIterationOfShape I κ
  have := hasPushouts I κ
  have := hasColimitsOfShape_discrete I κ
  ((functor I.homFamily Y).transfiniteIteration (ε _ Y) κ.ord.toType)

variable (Y) in
noncomputable def ιTransfiniteIterationFunctor : 𝟭 _ ⟶ transfiniteIterationFunctor I κ Y :=
  have := hasIterationOfShape I κ
  have := hasPushouts I κ
  have := hasColimitsOfShape_discrete I κ
  ((functor I.homFamily Y).ιTransfiniteIteration (ε _ Y) κ.ord.toType)

noncomputable def object : C := ((transfiniteIterationFunctor I κ Y).obj (Over.mk p)).left

noncomputable def ιObject : X ⟶ object I κ p :=
  ((ιTransfiniteIterationFunctor I κ Y).app (Over.mk p)).left

noncomputable def πObject : object I κ p ⟶ Y :=
  ((transfiniteIterationFunctor I κ Y).obj (Over.mk p)).hom

@[reassoc (attr := simp)]
lemma ιObject_πObject : ιObject I κ p ≫ πObject I κ p = p := by
  simp [ιObject, πObject]

lemma transfiniteCompositionsOfShape_ιObject :
    (coproducts.{w} I).pushouts.transfiniteCompositionsOfShape κ.ord.toType
      (ιObject I κ p) := by
  have := hasIterationOfShape I κ
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  have := isSmall I κ
  have := locallySmall I κ
  simpa only [ofHoms_homFamily] using
    transfiniteCompositionsOfShape_ιObj (f := homFamily I) (J := κ.ord.toType) (p := p)

lemma rlp_πObject : I.rlp (πObject I κ p) := by
  have := Cardinal.noMaxOrder (isRegular I κ).aleph0_le
  have := hasIterationOfShape I κ
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  have := isSmall I κ
  have := locallySmall I κ
  have (i : I.toSet) : PreservesColimit (inductiveSystemForget I.homFamily κ.ord.toType p)
      (coyoneda.obj (Opposite.op i.1.left)) :=
    preservesColimit_coyoneda_obj I κ i.1.hom i.2 _ (fun j hj ↦ by
      refine (arrow_mk_iso_iff _
        ((Over.forget _).mapArrow.mapIso
          (Functor.transfiniteIterationMapLeSuccAppArrowIso _ _ j hj _))).2 ?_
      simpa using coproducts_pushouts_ιFunctorObj (homFamily I) _)
  intro _ _ _ hi
  rw [← ofHoms_homFamily I] at hi
  obtain ⟨i⟩ := hi
  apply hasLiftingProperty_πObj

@[simps]
noncomputable def mapFactorizationData : MapFactorizationData I.rlp.llp I.rlp p where
  i := ιObject I κ p
  p := πObject I κ p
  hi := by
    simpa using transfiniteCompositionsOfShape_le_rlp_llp _ _ _
      (transfiniteCompositionsOfShape_ιObject I κ p)
  hp := rlp_πObject I κ p

/-- Variant of `rlp_llp` which shows it suffices to consider transfinite compositions
indexed by `κ.ord.toType`. -/
lemma rlp_llp' :
    I.rlp.llp =
      ((coproducts.{w} I).pushouts.transfiniteCompositionsOfShape κ.ord.toType).retracts := by
  apply le_antisymm
  · intro X Y f hf
    replace hf := hf _ (rlp_πObject I κ f)
    have sq : CommSq (ιObject I κ f) f (πObject I κ f) (𝟙 _) := ⟨by simp⟩
    refine ⟨_, _, _, ?_, transfiniteCompositionsOfShape_ιObject I κ f⟩
    -- this is a particular case of the retract argument
    exact
      { i := Arrow.homMk (u := 𝟙 X) (v := sq.lift) (by simp)
        r := Arrow.homMk (u := 𝟙 X) (v := πObject I κ f) (by simp) }
  · rw [le_llp_iff_le_rlp, retracts_rlp, ← le_llp_iff_le_rlp]
    simpa using transfiniteCompositionsOfShape_le_rlp_llp
      (coproducts.{w} I).pushouts κ.ord.toType

end

section

variable [HasSmallObjectArgument I]

lemma hasFactorization : HasFactorization I.rlp.llp I.rlp where
  nonempty_mapFactorizationData p := ⟨mapFactorizationData I I.smallObjectκ p⟩

lemma rlp_llp :
    I.rlp.llp =
      (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts := by
  apply le_antisymm
  · rw [rlp_llp' I I.smallObjectκ]
    apply monotone_retracts
    apply transfiniteCompositionsOfShape_le_transfiniteCompositions
  · rw [le_llp_iff_le_rlp, retracts_rlp, ← le_llp_iff_le_rlp]
    simpa using transfiniteCompositions_le_rlp_llp.{w} (coproducts.{w} I).pushouts

end-/

end

end SmallObject

end CategoryTheory
