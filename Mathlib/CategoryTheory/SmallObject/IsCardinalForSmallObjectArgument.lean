/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Construction
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Cardinals that are suitable for the small object argument

In this file, given a class of morphisms `I : MorphismProperty C` and
a regular cardinal `κ : Cardinal.{w}`, we define a typeclass
`IsCardinalForSmallObjectArgument I κ` which requires certain
smallness properties (`I` is `w`-small, `C` is locally `w`-small),
the existence of certain colimits (pushouts, coproducts of size `w`,
and the condition `HasIterationOfShape κ.ord.ToType C` about the
existence of colimits indexed by limit ordinal smaller than or equal
to `κ.ord`), and the technical assumption that if `A` is the
a morphism in `I`, then the functor `Hom(A, _)` should commute
with the filtering colimits corresponding to relative
`I`-cell complexes. (This last condition shall hold when `κ`
is the successor of an infinite cardinal `c` such that all these objects `A` are `c`-presentable,
see `Mathlib/CategoryTheory/Presentable/Basic.lean`.)

Given `I : MorphismProperty C`, we shall say that `I` permits
the small object argument if there exists `κ` such that
`IsCardinalForSmallObjectArgument I κ` holds. See the file
`Mathlib/CategoryTheory/SmallObject/Basic.lean` for the definition of this typeclass
`HasSmallObjectArgument` and an outline of the proof.

## Main results

Assuming `IsCardinalForSmallObjectArgument I κ`, any morphism `f : X ⟶ Y`
is factored as `ιObj I κ f ≫ πObj I κ f = f`. It is shown that `ιObj I κ f`
is a relative `I`-cell complex (see `SmallObject.relativeCellComplexιObj`)
and that `πObj I κ f` has the right lifting property with respect to `I`
(see `SmallObject.rlp_πObj`). This construction is obtained by
iterating to the power `κ.ord.ToType` the functor `Arrow C ⥤ Arrow C` defined
in the file `Mathlib/CategoryTheory/SmallObject/Construction.lean`.
This factorization is functorial in `f`
and gives the property `HasFunctorialFactorization I.rlp.llp I.rlp`.
Finally, the lemma `llp_rlp_of_isCardinalForSmallObjectArgument`
(and its primed version) shows that the morphisms in `I.rlp.llp` are exactly
the retracts of the transfinite compositions (of shape `κ.ord.ToType`) of
pushouts of coproducts of morphisms in `I`.

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Category HomotopicalAlgebra Limits SmallObject

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)

namespace MorphismProperty

/-- Given `I : MorphismProperty C` and a regular cardinal `κ : Cardinal.{w}`,
this property asserts the technical conditions which allow to proceed
to the small object argument by doing a construction by transfinite
induction indexed by the well-ordered type `κ.ord.ToType`. -/
class IsCardinalForSmallObjectArgument (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType] : Prop where
  isSmall : IsSmall.{w} I := by infer_instance
  locallySmall : LocallySmall.{w} C := by infer_instance
  hasPushouts : HasPushouts C := by infer_instance
  hasCoproducts : HasCoproducts.{w} C := by infer_instance
  hasIterationOfShape : HasIterationOfShape κ.ord.ToType C := by infer_instance
  preservesColimit {A B X Y : C} (i : A ⟶ B) (_ : I i) (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ I.homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A))

end MorphismProperty

namespace SmallObject

open MorphismProperty

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

include I κ

lemma isSmall : IsSmall.{w} I :=
  IsCardinalForSmallObjectArgument.isSmall κ

lemma locallySmall : LocallySmall.{w} C :=
  IsCardinalForSmallObjectArgument.locallySmall I κ

lemma hasIterationOfShape : HasIterationOfShape κ.ord.ToType C :=
  IsCardinalForSmallObjectArgument.hasIterationOfShape I

lemma hasPushouts : HasPushouts C :=
  IsCardinalForSmallObjectArgument.hasPushouts I κ

lemma hasCoproducts : HasCoproducts.{w} C :=
  IsCardinalForSmallObjectArgument.hasCoproducts I κ

lemma preservesColimit {A B X Y : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ I.homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) :=
  IsCardinalForSmallObjectArgument.preservesColimit i hi f hf

lemma hasColimitsOfShape_discrete (X Y : C) (p : X ⟶ Y) :
    HasColimitsOfShape
      (Discrete (FunctorObjIndex I.homFamily p)) C := by
  haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasCoproducts I κ
  exact hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm

/-- The successor structure on `Arrow C ⥤ Arrow C` corresponding
to the iterations of the natural transformation
`ε : 𝟭 (Arrow C) ⟶ SmallObject.functor I.homFamily`
(see the file `SmallObject.Construction`). -/
noncomputable def succStruct : SuccStruct (Arrow C ⥤ Arrow C) :=
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  SuccStruct.ofNatTrans (ε I.homFamily)

/-- For the successor structure `succStruct I κ` on `Arrow C ⥤ Arrow C`,
the morphism from an object to its successor induces
morphisms in `C` which consists in attaching `I`-cells. -/
noncomputable def attachCellsOfSuccStructProp
    {F G : Arrow C ⥤ Arrow C} {φ : F ⟶ G}
    (h : (succStruct I κ).prop φ) (f : Arrow C) :
    AttachCells.{w} I.homFamily (φ.app f).left :=
  haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  AttachCells.ofArrowIso (attachCellsιFunctorObjOfSmall _ _)
    ((Functor.mapArrow ((evaluation _ _).obj f ⋙
      Arrow.leftFunc)).mapIso h.arrowIso.symm)

/-- The class of morphisms in `Arrow C` which on the left side are
pushouts of coproducts of morphisms in `I`, and which are
isomorphisms on the right side. -/
def propArrow : MorphismProperty (Arrow C) := fun _ _ f ↦
  (coproducts.{w} I).pushouts f.left ∧ (isomorphisms C) f.right

lemma succStruct_prop_le_propArrow :
    (succStruct I κ).prop ≤ (propArrow.{w} I).functorCategory (Arrow C) := by
  haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  intro _ _ _ ⟨F⟩ f
  constructor
  · nth_rw 1 [← I.ofHoms_homFamily]
    apply pushouts_mk _ (functorObj_isPushout I.homFamily (F.obj f).hom)
    exact coproducts_of_small _ _ (colimitsOfShape_colimMap _ (by rintro ⟨j⟩; constructor))
  · rw [MorphismProperty.isomorphisms.iff]
    dsimp [succStruct]
    infer_instance

/-- The functor `κ.ord.ToType ⥤ Arrow C ⥤ Arrow C` corresponding to the
iterations of the successor structure `succStruct I κ`. -/
noncomputable def iterationFunctor : κ.ord.ToType ⥤ Arrow C ⥤ Arrow C :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).iterationFunctor κ.ord.ToType

/-- The colimit of `iterationFunctor I κ`. -/
noncomputable def iteration : Arrow C ⥤ Arrow C :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).iteration κ.ord.ToType

/-- The natural "inclusion" `𝟭 (Arrow C) ⟶ iteration I κ`. -/
noncomputable def ιIteration : 𝟭 _ ⟶ iteration I κ :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).ιIteration κ.ord.ToType

/-- The morphism `ιIteration I κ` is a transfinite composition of shape
`κ.ord.ToType` of morphisms satisfying `(succStruct I κ).prop`. -/
noncomputable def transfiniteCompositionOfShapeSuccStructPropιIteration :
    (succStruct I κ).prop.TransfiniteCompositionOfShape κ.ord.ToType (ιIteration I κ) :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).transfiniteCompositionOfShapeιIteration κ.ord.ToType

@[simp]
lemma transfiniteCompositionOfShapeSuccStructPropιIteration_F :
    (transfiniteCompositionOfShapeSuccStructPropιIteration I κ).F =
      iterationFunctor I κ :=
  rfl

/-- For any `f : Arrow C`, the map `((ιIteration I κ).app f).right` is
a transfinite composition of isomorphisms. -/
noncomputable def transfiniteCompositionOfShapeιIterationAppRight (f : Arrow C) :
    (isomorphisms C).TransfiniteCompositionOfShape κ.ord.ToType
      ((ιIteration I κ).app f).right :=
  haveI := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.rightFunc)
    map_mem j hj := ((succStruct_prop_le_propArrow I κ _ (h.map_mem j hj)) f).2 }

instance (f : Arrow C) : IsIso ((ιIteration I κ).app f).right :=
  (transfiniteCompositionOfShapeιIterationAppRight I κ f).isIso

instance {j₁ j₂ : κ.ord.ToType} (φ : j₁ ⟶ j₂) (f : Arrow C) :
    IsIso (((iterationFunctor I κ).map φ).app f).right :=
  inferInstanceAs (IsIso ((transfiniteCompositionOfShapeιIterationAppRight I κ f).F.map φ))

set_option backward.isDefEq.respectTransparency false in
/-- For any `f : Arrow C`, the object `((iteration I κ).obj f).right`
identifies to `f.right`. -/
@[simps! hom]
noncomputable def iterationObjRightIso (f : Arrow C) :
    f.right ≅ ((iteration I κ).obj f).right :=
  asIso ((ιIteration I κ).app f).right

set_option backward.isDefEq.respectTransparency false in
/-- For any `f : Arrow C` and `j : κ.ord.ToType`, the object
`(((iterationFunctor I κ).obj j).obj f).right` identifies to `f.right`. -/
noncomputable def iterationFunctorObjObjRightIso (f : Arrow C) (j : κ.ord.ToType) :
    (((iterationFunctor I κ).obj j).obj f).right ≅ f.right :=
  asIso ((transfiniteCompositionOfShapeιIterationAppRight I κ f).incl.app j) ≪≫
    (iterationObjRightIso I κ f).symm

@[reassoc (attr := simp)]
lemma iterationFunctorObjObjRightIso_ιIteration_app_right (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorObjObjRightIso I κ f j).hom ≫ ((ιIteration I κ).app f).right =
      (transfiniteCompositionOfShapeιIterationAppRight I κ f).incl.app j := by
  simp [iterationFunctorObjObjRightIso, iterationObjRightIso]

lemma prop_iterationFunctor_map_succ (j : κ.ord.ToType) :
    (succStruct I κ).prop ((iterationFunctor I κ).map (homOfLE (Order.le_succ j))) := by
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  exact (succStruct I κ).prop_iterationFunctor_map_succ j (not_isMax j)

set_option backward.isDefEq.respectTransparency false in
/-- For any `f : Arrow C` and `j : κ.ord.ToType`, the morphism
`((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f` identifies
to a morphism given by `SmallObject.ε I.homFamily`. -/
noncomputable def iterationFunctorMapSuccAppArrowIso (f : Arrow C) (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    Arrow.mk (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f) ≅
      (ε I.homFamily).app (((iterationFunctor I κ).obj j).obj f) :=
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  Arrow.isoMk (Iso.refl _)
    (((evaluation _ _).obj f).mapIso
      ((succStruct I κ).iterationFunctorObjSuccIso j (not_isMax j))) (by
    have this := NatTrans.congr_app ((succStruct I κ).iterationFunctor_map_succ j (not_isMax j)) f
    dsimp at this
    dsimp [iterationFunctor]
    rw [id_comp, this, assoc, Iso.inv_hom_id_app, comp_id]
    dsimp [succStruct])

@[simp]
lemma iterationFunctorMapSuccAppArrowIso_hom_left (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorMapSuccAppArrowIso I κ f j).hom.left = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency false in -- Needed below
@[reassoc (attr := simp)]
lemma iterationFunctorMapSuccAppArrowIso_hom_right_right_comp
    (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorMapSuccAppArrowIso I κ f j).hom.right.right ≫
      (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right = 𝟙 _ := by
  have := Arrow.rightFunc.congr_map ((iterationFunctorMapSuccAppArrowIso I κ f j).hom.w)
  dsimp at this ⊢
  rw [← cancel_epi (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right,
    ← reassoc_of% this, comp_id]

section

variable {X Y : C} (f : X ⟶ Y)

/-- The intermediate object in the factorization given by the
small object argument. -/
noncomputable def obj : C := ((iteration I κ).obj (Arrow.mk f)).left

/-- The "inclusion" morphism in the factorization given by
the small object argument. -/
noncomputable def ιObj : X ⟶ obj I κ f := ((ιIteration I κ).app (Arrow.mk f)).left

set_option backward.isDefEq.respectTransparency false in
/-- The "projection" morphism in the factorization given by
the small object argument. -/
noncomputable def πObj : obj I κ f ⟶ Y :=
  ((iteration I κ).obj (Arrow.mk f)).hom ≫ inv ((ιIteration I κ).app f).right

@[reassoc (attr := simp)]
lemma πObj_ιIteration_app_right :
    πObj I κ f ≫ ((ιIteration I κ).app f).right =
      ((iteration I κ).obj (Arrow.mk f)).hom := by simp [πObj]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ιObj_πObj : ιObj I κ f ≫ πObj I κ f = f := by
  simp [ιObj, πObj]

/-- The morphism `ιObj I κ f` is a relative `I`-cell complex. -/
noncomputable def relativeCellComplexιObj :
    RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ I.homFamily)
      (ιObj I κ f) := by
  have := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  exact
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.leftFunc)
    attachCells j hj :=
      attachCellsOfSuccStructProp I κ (h.map_mem j hj) f }

lemma transfiniteCompositionsOfShape_ιObj :
    (coproducts.{w} I).pushouts.transfiniteCompositionsOfShape κ.ord.ToType
      (ιObj I κ f) :=
  ⟨((relativeCellComplexιObj I κ f).transfiniteCompositionOfShape).ofLE
    (by simp)⟩

lemma llp_rlp_ιObj : I.rlp.llp (ιObj I κ f) := by
  apply I.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp κ.ord.ToType
  apply transfiniteCompositionsOfShape_ιObj

/-- When `ιObj I κ f` is considered as a relative `I`-cell complex,
the object at the `j`th step is obtained by applying the construction
`SmallObject.functorObj`. -/
noncomputable def relativeCellComplexιObjFObjSuccIso (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    (relativeCellComplexιObj I κ f).F.obj (Order.succ j) ≅
      functorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom :=
  (Arrow.rightFunc ⋙ Arrow.leftFunc).mapIso
    (iterationFunctorMapSuccAppArrowIso I κ f j)

lemma ιFunctorObj_eq (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    ιFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObj I κ f).F.map (homOfLE (Order.le_succ j)) ≫
        (relativeCellComplexιObjFObjSuccIso I κ f j).hom := by
  simpa using Arrow.leftFunc.congr_map (iterationFunctorMapSuccAppArrowIso I κ f j).hom.w

set_option backward.isDefEq.respectTransparency false in
lemma πFunctorObj_eq (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    πFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObjFObjSuccIso I κ f j).inv ≫
      (relativeCellComplexιObj I κ f).incl.app (Order.succ j) ≫
      πObj I κ f ≫ (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).inv := by
  have h₁ := (iterationFunctorMapSuccAppArrowIso I κ f j).hom.right.w
  have h₂ := (transfiniteCompositionOfShapeSuccStructPropιIteration I κ).incl.naturality
    (homOfLE (Order.le_succ j))
  dsimp at h₁ h₂
  rw [comp_id] at h₂
  rw [← cancel_mono (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).hom,
    ← cancel_mono ((ιIteration I κ).app f).right, assoc, assoc, assoc, assoc, assoc,
    Iso.inv_hom_id_assoc, πObj_ιIteration_app_right,
    iterationFunctorObjObjRightIso_ιIteration_app_right,
    ← cancel_epi (relativeCellComplexιObjFObjSuccIso I κ f j).hom, Iso.hom_inv_id_assoc]
  dsimp [relativeCellComplexιObjFObjSuccIso,
    relativeCellComplexιObj, transfiniteCompositionOfShapeιIterationAppRight]
  simp only [reassoc_of% h₁, comp_id, comp_id, Arrow.w_mk_right, ← h₂,
    NatTrans.comp_app, Arrow.comp_right,
    iterationFunctorMapSuccAppArrowIso_hom_right_right_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
lemma hasRightLiftingProperty_πObj {A B : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y) :
    HasLiftingProperty i (πObj I κ f) := ⟨by
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  haveI := preservesColimit I κ i hi _ (relativeCellComplexιObj I κ f)
  intro g b sq
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (coyoneda.obj (Opposite.op A))
      (relativeCellComplexιObj I κ f).isColimit) g
  dsimp at g b sq t ht
  obtain ⟨l, hl₁, hl₂⟩ := ιFunctorObj_extension' I.homFamily
    ((relativeCellComplexιObj I κ f).incl.app j ≫ πObj I κ f)
    ((relativeCellComplexιObj I κ f).F.map (homOfLE (Order.le_succ j)))
    ((relativeCellComplexιObj I κ f).incl.app (Order.succ j) ≫ πObj I κ f) (by simp) (Iso.refl _)
    (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).symm
    (relativeCellComplexιObjFObjSuccIso I κ f j)
    (by dsimp; rw [ιFunctorObj_eq, id_comp])
    (by dsimp; rw [πFunctorObj_eq, assoc, Iso.hom_inv_id_assoc])
    (i := ⟨i, hi⟩) t b (by rw [reassoc_of% ht, sq.w]; dsimp)
  dsimp at hl₁
  exact ⟨⟨{
    l := l ≫ (relativeCellComplexιObj I κ f).incl.app (Order.succ j)
    fac_left := by simp [reassoc_of% hl₁, ← ht]
    fac_right := by rw [assoc, hl₂]
  }⟩⟩⟩

lemma rlp_πObj : I.rlp (πObj I κ f) :=
  fun _ _ _ hi ↦ hasRightLiftingProperty_πObj _ _ _ hi _

end

/-- The functoriality of the intermediate object in the
factorization of the small object argument. -/
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

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma πObj_naturality {f g : Arrow C} (φ : f ⟶ g) :
    objMap I κ φ ≫ πObj I κ g.hom = πObj I κ f.hom ≫ φ.right := by
  let e₁ := asIso ((ιIteration I κ).app (Arrow.mk f.hom)).right
  let e₂ := asIso ((ιIteration I κ).app (Arrow.mk g.hom)).right
  change _ ≫ _ ≫ e₂.inv = (_ ≫ e₁.inv) ≫ _
  have h₁ := ((iteration I κ).map φ).w =≫ e₂.inv
  have h₂ : φ.right ≫ e₂.hom = e₁.hom ≫ ((iteration I κ).map φ).right :=
    ((Functor.whiskerRight (ιIteration I κ) Arrow.rightFunc).naturality φ)
  dsimp at h₁
  rw [assoc] at h₁
  apply h₁.trans
  simp only [← cancel_mono e₂.hom, assoc, e₂.inv_hom_id, h₂, e₁.inv_hom_id_assoc]
  rw [← assoc]
  apply comp_id

/-- The functorial factorization `ιObj I κ f ≫ πObj I κ f.hom = f`
with `ιObj I κ f` in `I.rlp.llp` and `πObj I κ f.hom` in `I.rlp`. -/
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
of transfinite compositions (of shape `κ.ord.ToType`) of pushouts of coproducts
of maps in `I`. -/
lemma llp_rlp_of_isCardinalForSmallObjectArgument' :
    I.rlp.llp = (transfiniteCompositionsOfShape
      (coproducts.{w} I).pushouts κ.ord.ToType).retracts := by
  refine le_antisymm ?_
    (retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp I κ.ord.ToType)
  intro X Y f hf
  have sq : CommSq (ιObj I κ f) f (πObj I κ f) (𝟙 _) := ⟨by simp⟩
  have := hf _ (rlp_πObj I κ f)
  refine ⟨_, _, _, ?_, transfiniteCompositionsOfShape_ιObj I κ f⟩
  exact
    { i := Arrow.homMk (𝟙 _) sq.lift
      r := Arrow.homMk (𝟙 _) (πObj I κ f) }

omit κ in
attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType in
lemma llp_rlp_of_isCardinalForSmallObjectArgument_aleph0
    [I.IsCardinalForSmallObjectArgument Cardinal.aleph0.{w}] :
    I.rlp.llp = (transfiniteCompositionsOfShape (coproducts.{w} I).pushouts ℕ).retracts := by
  let e : ℕ ≃o Cardinal.aleph0.{w}.ord.ToType :=
    ULift.orderIso.{w}.symm.trans
      (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' _ Cardinal.aleph0,
    MorphismProperty.transfiniteCompositionsOfShape_eq_of_orderIso _ e]

/-- If `κ` is a suitable cardinal for the small object argument for `I : MorphismProperty C`,
then the class `I.rlp.llp` is exactly the class of morphisms that are retracts
of transfinite compositions of pushouts of coproducts of maps in `I`. -/
lemma llp_rlp_of_isCardinalForSmallObjectArgument :
    I.rlp.llp =
      (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts := by
  refine le_antisymm ?_
    (retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp I)
  rw [llp_rlp_of_isCardinalForSmallObjectArgument' I κ]
  apply retracts_monotone
  apply transfiniteCompositionsOfShape_le_transfiniteCompositions

end SmallObject

end CategoryTheory
