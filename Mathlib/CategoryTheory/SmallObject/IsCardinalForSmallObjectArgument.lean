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
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Cardinals that are suitable for the small object argument

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/

universe w v v' u u'

namespace CategoryTheory

open Category HomotopicalAlgebra

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
  hasIterationOfShape : HasIterationOfShape κ.ord.toType C
  preservesColimit {A B X Y : C} (i : A ⟶ B) (_ : I i) (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.toType) ↦ I.homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A))
  /-- TODO: replace `preservesColimits'` by `preservesColimit` -/
  preservesColimit' :
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

lemma hasIterationOfShape : HasIterationOfShape κ.ord.toType C :=
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
  IsCardinalForSmallObjectArgument.preservesColimit' i hi F hF

lemma hasColimitsOfShape_discrete (X Y : C) (p : X ⟶ Y) :
    HasColimitsOfShape
      (Discrete (FunctorObjIndex I.homFamily p)) C := by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasCoproducts I κ
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} _)).symm

@[simps! (config := .lemmasOnly)]
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

noncomputable def attachCellsOfSuccStructProp
    {F G : Arrow C ⥤ Arrow C} {φ : F ⟶ G}
    (h : (succStruct I κ).prop φ) (f : Arrow C) :
    AttachCells.{w} I.homFamily (φ.app f).left :=
  have := locallySmall I κ
  have := isSmall I κ
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  AttachCells.ofArrowIso (attachCellsιFunctorObjOfSmall _ _)
    ((Functor.mapArrow ((evaluation _ _).obj f ⋙
      Arrow.leftFunc)).mapIso h.arrowIso.symm)

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

@[reassoc (attr := simp)]
lemma iterationCocone_w_app_app_right
    (f : Arrow C) {j₁ j₂ : κ.ord.toType} (g : j₁ ⟶ j₂) :
    (((iterationFunctor I κ).map g).app f).right ≫
      (((iterationCocone I κ).ι.app j₂).app f).right =
      (((iterationCocone I κ).ι.app j₁).app f).right := by
  rw [← Arrow.comp_right, ← NatTrans.comp_app, Cocone.w]

@[nolint unusedHavesSuffices]
noncomputable def isColimitIterationCocone : IsColimit (iterationCocone I κ) :=
  have := hasIterationOfShape I κ
  colimit.isColimit _

noncomputable def ιIteration : 𝟭 _ ⟶ iteration I κ :=
  have := hasIterationOfShape I κ
  (succStruct I κ).ιIteration κ.ord.toType

noncomputable def transfiniteCompositionOfShapeSuccStructPropιIteration :
    (succStruct I κ).prop.TransfiniteCompositionOfShape κ.ord.toType (ιIteration I κ) :=
  have := hasIterationOfShape I κ
  (succStruct I κ).transfiniteCompositionOfShapeιIteration κ.ord.toType

noncomputable def relativeCellComplexιIterationAppLeft (f : Arrow C) :
    RelativeCellComplex.{w} (fun (_ : κ.ord.toType) ↦ I.homFamily)
      ((ιIteration I κ).app f).left := by
  have := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  exact
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.leftFunc)
    attachCells j hj :=
      attachCellsOfSuccStructProp I κ (h.map_mem j hj) f }

def propArrow : MorphismProperty (Arrow C) := fun _ _ f ↦
  (coproducts.{w} I).pushouts f.left ∧ (isomorphisms C) f.right

lemma succStruct_prop_le_propArrow :
    (succStruct I κ).prop ≤ (propArrow.{w} I).functorCategory (Arrow C) := by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  intro _ _ _ ⟨F⟩ f
  constructor
  · nth_rw 1 [← I.ofHoms_homFamily]
    apply pushouts_mk _ (functorObj_isPushout I.homFamily (F.obj f).hom)
    exact coproducts_of_small _ _
      (colimitsOfShape_colimMap _ _ (by rintro ⟨j⟩; constructor))
  · rw [MorphismProperty.isomorphisms.iff]
    dsimp [succStruct]
    infer_instance

noncomputable def transfiniteCompositionOfShapePropArrowιIteration :
    ((propArrow.{w} I).functorCategory (Arrow C)).TransfiniteCompositionOfShape
      κ.ord.toType (ιIteration I κ) :=
  (transfiniteCompositionOfShapeSuccStructPropιIteration I κ).ofLE
    (succStruct_prop_le_propArrow I κ)

omit κ in
lemma propArrow_functorCategory_arrow_le (f : Arrow C) :
    (propArrow I).functorCategory (Arrow C) ≤
      (isomorphisms C).inverseImage
        ((evaluation (Arrow C) (Arrow C)).obj f ⋙ Arrow.rightFunc) := by
  intro _ _ _ h
  exact (h f).2

lemma isEventuallyConstantFrom_bot_iterationFunctor_evaluation_right (f : Arrow C) :
    (iterationFunctor I κ ⋙
      (evaluation _ (Arrow C)).obj f ⋙ Arrow.rightFunc).IsEventuallyConstantFrom ⊥ := by
  intro j φ
  have := hasIterationOfShape I κ
  suffices (isomorphisms _).transfiniteCompositionsOfShape (Set.Iic j)
      (((evaluation _ (Arrow C)).obj f ⋙ Arrow.rightFunc).map
      ((iterationFunctor I κ).map φ)) from
    (isomorphisms C).transfiniteCompositionsOfShape_le _ _ this
  apply transfiniteCompositionsOfShape_map_of_preserves
  exact transfiniteCompositionsOfShape_monotone _
    (propArrow_functorCategory_arrow_le I f) _
    ((transfiniteCompositionOfShapePropArrowιIteration I κ).iic j).mem

instance isIso_ιIteration_app_right (f : Arrow C) :
    IsIso ((ιIteration I κ).app f).right := by
  have := hasIterationOfShape I κ
  suffices (isomorphisms _).transfiniteCompositionsOfShape κ.ord.toType
      (((evaluation _ (Arrow C)).obj f ⋙ Arrow.rightFunc).map (ιIteration I κ)) from
    (isomorphisms C).transfiniteCompositionsOfShape_le κ.ord.toType _ this
  apply transfiniteCompositionsOfShape_map_of_preserves
  exact transfiniteCompositionsOfShape_monotone _
    (propArrow_functorCategory_arrow_le I f) _
    (transfiniteCompositionOfShapePropArrowιIteration I κ).mem

instance (f : Arrow C) (j : κ.ord.toType) :
    IsIso (((iterationCocone I κ).ι.app j).app f).right :=
  have := hasIterationOfShape I κ
  (isEventuallyConstantFrom_bot_iterationFunctor_evaluation_right
    I κ f).isIso_ι_of_isColimit'
      (isColimitOfPreserves ((evaluation _ _).obj f ⋙ Arrow.rightFunc)
        (isColimitIterationCocone I κ)) j (homOfLE bot_le)

noncomputable def iterationFunctorObjSuccObjLeftIso
    (f : Arrow C) (j : κ.ord.toType) (hj : ¬ IsMax j) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    (((iterationFunctor I κ).obj (Order.succ j)).obj f).left ≅
        functorObj I.homFamily (((iterationFunctor I κ).obj j).obj f).hom :=
  have := hasIterationOfShape I κ
  Arrow.leftFunc.mapIso (((succStruct I κ).iterationFunctorObjSuccIso j hj).app f)

@[reassoc]
lemma ιFunctorObj_iterationFunctorObjSuccObjLeftIso_inv
    (f : Arrow C) (j : κ.ord.toType) (hj : ¬ IsMax j) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    ιFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj f).hom ≫
      (iterationFunctorObjSuccObjLeftIso I κ f j hj).inv =
        (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).left := by
  have := hasIterationOfShape I κ
  exact ((evaluation _ _).obj f ⋙ Arrow.leftFunc).congr_map
    ((succStruct I κ).iterationFunctor_map_succ j hj).symm

lemma πFunctorObj_iterationCocone_ι_app_app_right
    (f : Arrow C) (j : κ.ord.toType) (hj : ¬ IsMax j) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    πFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj f).hom ≫
        (((iterationCocone I κ).ι.app j).app f).right =
      (iterationFunctorObjSuccObjLeftIso I κ f j hj).inv ≫
        (((iterationFunctor I κ).obj (Order.succ j)).obj f).hom ≫
        ((((iterationCocone I κ).ι.app (Order.succ j)).app f)).right := by
  have := hasIterationOfShape I κ
  simp [iterationFunctorObjSuccObjLeftIso, iterationFunctor,
    succStruct_succ_obj_hom I κ, ← (iterationCocone I κ).w (homOfLE (Order.le_succ j)),
    (succStruct I κ).iterationFunctor_map_succ j hj, succStruct_toSucc_app_right]

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
  dsimp at t ht
  obtain ⟨l, hl₁, hl₂⟩ := ιFunctorObj_extension (f := I.homFamily) (i := ⟨i, hi⟩)
    (πX := (((iterationFunctor I κ).obj j).obj f).hom) t
    (b ≫ inv (((iterationCocone I κ).ι.app j).app f).right) (⟨by
      have := (((iterationCocone I κ).ι.app j).app f).w
      dsimp at this
      rw [← cancel_mono (((iterationCocone I κ).ι.app j).app f).right, assoc, assoc, assoc,
        IsIso.inv_hom_id]
      dsimp
      rw [comp_id, ← sq.w, ← this, ← reassoc_of% ht] ⟩)
  dsimp at l hl₁
  exact ⟨⟨{
    l := l ≫ (iterationFunctorObjSuccObjLeftIso I κ f j (not_isMax j)).inv ≫
        (((iterationCocone I κ).ι.app (Order.succ j)).app f).left
    fac_left := by
      rw [reassoc_of% hl₁, ← ht, ιFunctorObj_iterationFunctorObjSuccObjLeftIso_inv_assoc,
        iterationCocone_w_app_app_left]
    fac_right := by
      rw [← cancel_mono (inv (((iterationCocone I κ).ι.app j).app f).right),
        assoc, assoc, assoc, ← hl₂,
        ← cancel_mono ((((iterationCocone I κ).ι.app j).app f).right),
        assoc, assoc, assoc, assoc, assoc, IsIso.inv_hom_id, comp_id,
        πFunctorObj_iterationCocone_ι_app_app_right _ _ _ _ (not_isMax j)]
      dsimp
      rw [Arrow.w_mk_right] }⟩⟩⟩

section

variable {X Y : C} (f : X ⟶ Y)

noncomputable def obj : C := ((iteration I κ).obj (Arrow.mk f)).left

noncomputable def ιObj : X ⟶ obj I κ f := ((ιIteration I κ).app (Arrow.mk f)).left

noncomputable def πObj : obj I κ f ⟶ Y :=
  ((iteration I κ).obj (Arrow.mk f)).hom ≫ inv ((ιIteration I κ).app f).right

@[reassoc (attr := simp)]
lemma ιObj_πObj : ιObj I κ f ≫ πObj I κ f = f := by
  simp [ιObj, πObj]

/-- The map `ιObj I κ f` is a relative `I`-cell complex. -/
noncomputable def relativeCellComplexιObj :
    RelativeCellComplex.{w} (fun (_ : κ.ord.toType) ↦ I.homFamily)
      (ιObj I κ f) :=
  relativeCellComplexιIterationAppLeft I κ (Arrow.mk f)

lemma transfiniteCompositionsOfShape_ιObj :
    (coproducts.{w} I).pushouts.transfiniteCompositionsOfShape κ.ord.toType
      (ιObj I κ f) :=
  ⟨((relativeCellComplexιObj I κ f).transfiniteCompositionOfShape).ofLE
    (by simp)⟩

lemma llp_rlp_ιObj : I.rlp.llp (ιObj I κ f) := by
  apply I.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp κ.ord.toType
  apply transfiniteCompositionsOfShape_ιObj

lemma hasRightLiftingProperty_πObj {A B : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y) :
    HasLiftingProperty i (πObj I κ f) := by
  dsimp [πObj]
  have := hasRightLiftingProperty_iteration_obj_hom I κ (Arrow.mk f) i hi
  infer_instance

lemma rlp_πObj : I.rlp (πObj I κ f) :=
  fun _ _ _ hi ↦ hasRightLiftingProperty_πObj _ _ _ hi _

end

section

noncomputable def objMap {f g : Arrow C} (φ : f ⟶ g) : obj I κ f.hom ⟶ obj I κ g.hom :=
  ((iteration I κ).map φ).left

@[simp]
lemma objMap_id (f : Arrow C) : objMap I κ (𝟙 f) = 𝟙 _ := by
  simp only [objMap, Functor.map_id]
  rfl

@[reassoc, simp]
lemma objMap_comp {f g h : Arrow C} (φ : f ⟶ g) (ψ : g ⟶ h) :
    objMap I κ (φ ≫ ψ) = objMap I κ φ ≫ objMap I κ ψ := by
  simp only [objMap, Functor.map_comp]
  rfl

@[reassoc (attr := simp)]
lemma ιObj_naturality {f g : Arrow C} (φ : f ⟶ g) :
    ιObj I κ f.hom ≫ objMap I κ φ = φ.left ≫ ιObj I κ g.hom :=
  Arrow.leftFunc.congr_map ((ιIteration I κ).naturality φ).symm

@[reassoc (attr := simp)]
lemma πObj_naturality {f g : Arrow C} (φ : f ⟶ g) :
    objMap I κ φ ≫ πObj I κ g.hom = πObj I κ f.hom ≫ φ.right := by
  let e₁ := asIso ((ιIteration I κ).app (Arrow.mk f.hom)).right
  let e₂ := asIso ((ιIteration I κ).app (Arrow.mk g.hom)).right
  change _ ≫ _ ≫ e₂.inv = (_ ≫ e₁.inv) ≫ _
  have h₁ := ((iteration I κ).map φ).w =≫ e₂.inv
  have h₂ : φ.right ≫ e₂.hom = e₁.hom ≫ ((iteration I κ).map φ).right :=
    ((whiskerRight (ιIteration I κ) Arrow.rightFunc).naturality φ)
  dsimp at h₁
  rw [assoc] at h₁
  apply h₁.trans
  simp only [← cancel_mono e₂.hom, assoc, e₂.inv_hom_id, h₂, e₁.inv_hom_id_assoc]
  rw [← assoc]
  apply comp_id

end

@[simps]
noncomputable def functorialFactorizationData :
    FunctorialFactorizationData I.rlp.llp I.rlp where
  Z :=
    { obj f := obj I κ f.hom
      map φ := objMap I κ φ }
  i := { app f := ιObj I κ f.hom }
  p := { app f := πObj I κ f.hom }
  hi f := llp_rlp_ιObj I κ f.hom
  hp f := rlp_πObj I κ f.hom

lemma hasFunctorialFactorization :
    HasFunctorialFactorization I.rlp.llp I.rlp where
  nonempty_functorialFactorizationData :=
    ⟨functorialFactorizationData I κ⟩

/-- If `κ` is a suitable cardinal for the small object argument for `I : MorphismProperty C`,
then the class `I.rlp.llp` is exactly the class of morphisms that are retracts
of transfinite compositions (of shape `κ.ord.toType`) of pushouts of coproducts
of maps in `I`.  -/
lemma llp_rlp_of_isCardinalForSmallObjectArgument' :
    I.rlp.llp = (transfiniteCompositionsOfShape
      (coproducts.{w} I).pushouts κ.ord.toType).retracts := by
  refine le_antisymm ?_
    (retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp I κ.ord.toType)
  intro X Y f hf
  have sq : CommSq (ιObj I κ f) f (πObj I κ f) (𝟙 _) := ⟨by simp⟩
  have := hf _ (rlp_πObj I κ f)
  refine ⟨_, _, _, ?_, transfiniteCompositionsOfShape_ιObj I κ f⟩
  exact
    { i := Arrow.homMk (𝟙 _) sq.lift
      r := Arrow.homMk (𝟙 _) (πObj I κ f) }

/-- If `κ` is a suitable cardinal for the small object argument for `I : MorphismProperty C`,
then the class `I.rlp.llp` is exactly the class of morphisms that are retracts
of transfinite compositions of pushouts of coproducts of maps in `I`.  -/
lemma llp_rlp_of_isCardinalForSmallObjectArgument :
    I.rlp.llp =
      (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts := by
  refine le_antisymm ?_
    (retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp I)
  rw [llp_rlp_of_isCardinalForSmallObjectArgument' I κ]
  apply retracts_monotone
  apply transfiniteCompositionsOfShape_le_transfiniteCompositions

end

end SmallObject

end CategoryTheory
