/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.SmallObject.Construction
import Mathlib.CategoryTheory.SmallObject.Iteration.Iteration
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.CategoryTheory.MorphismProperty.IsSmall
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Morphism properties which admits a small object argument

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

noncomputable instance (o : Ordinal.{w}) : SuccOrder o.toType :=
  SuccOrder.ofLinearWellFoundedLT o.toType

open Limits SmallObject

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (I : MorphismProperty C)

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

class HasSmallObjectArgument : Prop where
  exists_cardinal : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.toType),
    IsCardinalForSmallObjectArgument I κ

variable [HasSmallObjectArgument.{w} I]

noncomputable def smallObjectκ : Cardinal.{w} :=
  (HasSmallObjectArgument.exists_cardinal (I := I)).choose

instance smallObjectκ_isRegular : Fact I.smallObjectκ.IsRegular :=
  (HasSmallObjectArgument.exists_cardinal (I := I)).choose_spec.choose

noncomputable instance : OrderBot I.smallObjectκ.ord.toType :=
  (HasSmallObjectArgument.exists_cardinal (I := I)).choose_spec.choose_spec.choose

instance isCardinalForSmallObjectArgument_smallObjectκ :
    IsCardinalForSmallObjectArgument.{w} I I.smallObjectκ :=
  (HasSmallObjectArgument.exists_cardinal (I := I)).choose_spec.choose_spec.choose_spec

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
variable (f : Arrow C)

instance (f : Arrow C) :
    (iterationFunctor I κ ⋙ (evaluation _ _).obj f).IsWellOrderContinuous := by
  have := hasIterationOfShape I κ
  infer_instance

instance (f : Arrow C) :
    (iterationFunctor I κ ⋙ (evaluation _ _).obj f ⋙ Arrow.leftFunc).IsWellOrderContinuous := by
  have := hasIterationOfShape I κ
  change ((iterationFunctor I κ ⋙ (evaluation _ _).obj f) ⋙
    Arrow.leftFunc).IsWellOrderContinuous
  infer_instance

instance (f : Arrow C) :
    (iterationFunctor I κ ⋙ (evaluation _ _).obj f ⋙ Arrow.rightFunc).IsWellOrderContinuous := by
  have := hasIterationOfShape I κ
  change ((iterationFunctor I κ ⋙ (evaluation _ _).obj f) ⋙
    Arrow.rightFunc).IsWellOrderContinuous
  infer_instance

noncomputable def iteration : Arrow C ⥤ Arrow C :=
  have := hasIterationOfShape I κ
  (succStruct I κ).iteration κ.ord.toType

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
      κ.ord.toType (ιIteration I κ) := by
  sorry

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
