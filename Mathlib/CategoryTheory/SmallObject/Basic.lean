/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

/-!
# The small object argument

Let `C` be a category. A class of morphisms `I : MorphismProperty C`
permits the small object argument (typeclass `HasSmallObjectArgument.{w} I`
where `w` is an auxiliary universe) if there exists a regular
cardinal `κ : Cardinal.{w}` such that `IsCardinalForSmallObjectArgument I κ`
holds. This technical condition is defined in the file
`SmallObject.IsCardinalForSmallObjectArgument`. It involves certain
smallness conditions relative to `w`, the existence of certain colimits,
and for each object `A` which is the source of a morphism in `I`,
the `Hom(A, _)` functor (`coyoneda.obj (op A)`) should commute
to transfinite compositions of pushouts of coproducts of morphisms in `I`
(this condition is automatically satisfied when `A` is a `κ`-presentable
object of `C`).

## Main reulsts

Assuming `I` permits the small object argument, the two main results
obtained in this file are:
* the class `I.rlp.llp` of morphisms that have the left lifting property with
respect to the maps that have the right lifting property with respect
to `I` are exactly the retracts of transfinite compositions
of pushouts of coproducts of morphisms in `I`;
* morphisms in `C` have a functorial factorization as a morphism in
`I.rlp.llp` followed by a morphism in `I.rlp`.

## Structure of the proof

The main part in the proof is the construction of the functorial factorization.
This involves a construction by transfinite induction. A general
procedure for constructions by transfinite
induction in categories (including the iteration of a functor)
is done in the file `SmallObject.TransfiniteIteration`.
The factorization of the small object argument is obtained by doing
a transfinite of a specific functor `Arrow C ⥤ Arrow C` which
is defined in the file `SmallObject.Construction` (this definition
involves coproducts and pushout). These ingredients are combined
in the file `SmallObject.IsCardinalForSmallObjectArgument`
where the main results are obtaned under a `IsCardinalForSmallObjectArgument I κ`
assumption.


## References
- https://ncatlab.org/nlab/show/small+object+argument

--In the context of model categories, this result is known as Quillen's small object
--argument (originally for `J := ℕ`). Actually, the more general construction by
--transfinite induction already appeared in the proof of the existence of enough
--injectives in abelian categories with AB5 and a generator by Grothendieck, who then
--wrote that the "proof was essentially known". Indeed, the argument appears
--in *Homological algebra* by Cartan and Eilenberg (p. 9-10) in the case of modules,
--and they mention that the result was initially obtained by Baer.

-/

universe w v u

namespace CategoryTheory

open Category Limits SmallObject

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)

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

instance : HasFunctorialFactorization I.rlp.llp I.rlp :=
  hasFunctorialFactorization I I.smallObjectκ

/-- If `I : MorphismProperty C` permits the small object argument,
then the class of morphism that have the left lifting property with respect to
the maps that have the right lifting property with respect to `I` are
exactly the retracts of transfinite compositions (indexed by `I.smallObjectκ.ord.toType`)
of pushouts of coproducts of morphisms in `C`. -/
lemma rlp_llp_of_hasSmallObjectArgument' :
    I.rlp.llp = (transfiniteCompositionsOfShape (coproducts.{w} I).pushouts
        I.smallObjectκ.ord.toType).retracts :=
  rlp_llp_of_isCardinalForSmallObjectArgument' I I.smallObjectκ

/-- If `I : MorphismProperty C` permits the small object argument,
then the class of morphism that have the left lifting property with respect to
the maps that have the right lifting property with respect to `I` are
exactly the retracts of transfinite compositions
of pushouts of coproducts of morphisms in `C`. -/
lemma rlp_llp_of_hasSmallObjectArgument :
    I.rlp.llp =
      (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts :=
  rlp_llp_of_isCardinalForSmallObjectArgument I I.smallObjectκ

end MorphismProperty


#exit
namespace SmallObject

variable {C : Type u} [Category.{v} C]
  {ι : Type t} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
  {X : C} (Y : C)
  [∀ {Z : C} (πZ : Z ⟶ Y), HasColimitsOfShape (Discrete (FunctorObjIndex f πZ)) C]
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape C J] [HasPushouts C]

variable (Z : C) (πZ : Z ⟶ Y)

instance : HasIterationOfShape (Over Y) J where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

variable {Y} (p : X ⟶ Y)

/-- The intermediate which appears in the factorization of the lemma `ιObj_πObj`. -/
noncomputable def obj : C :=
  (((functor f Y).transfiniteIteration (ε f Y) J).obj (Over.mk p)).left

/-- Given `f i : A i ⟶ B i` a family of morphisms in a category `C`,
`J` a well-ordered type and `p : X ⟶ Y` a morphism in `C`, this is
morphism `ιObj : X ⟶ obj f J p` which appears in the factorization
`ιObj_πObj`, and it is a transfinite composition of pushouts of
coproducts of morphisms in the family of morphism `f`. -/
noncomputable def ιObj : X ⟶ obj f J p :=
  (((functor f Y).ιTransfiniteIteration (ε f Y) J).app (Over.mk p)).left

/-- Given `f i : A i ⟶ B i` a family of morphisms in a category `C`,
`J` a well-ordered type and `p : X ⟶ Y` a morphism in `C`, this
morphism `πObj : obj f J p ⟶ Y` which appears in the factorization
`ιObj_πObj`, and under favorable circumstances (see `hasLiftingProperty_πObj`),
this morphism has the right lifting property with respect to all the
morphisms in the family `f`. -/
noncomputable def πObj : obj f J p ⟶ Y :=
  (((functor f Y).transfiniteIteration (ε f Y) J).obj (Over.mk p)).hom

/-- Given `f i : A i ⟶ B i` a family of morphisms in a category `C`,
`J` a well-ordered type and `p : X ⟶ Y` a morphism in `C`, this is
a factorization of `p` as a morphism `ιObj : X ⟶ obj f J p`
which is a transfinite composition of pushouts of coproducts
of morphisms in the family `f`, followed by `πObj : obj f J p ⟶ Y`,
which under favorable circumstances (see `hasLiftingProperty_πObj`)
has the right lifting property with respect to all the morphisms
in the family `f`. -/
@[reassoc (attr := simp)]
lemma ιObj_πObj : ιObj f J p ≫ πObj f J p = p := by
  simp [ιObj, πObj]

/-- The inductive system `J ⥤ Over Y` in `Over Y` given by
the transfinite iteration of `functor f Y : Over Y ⥤ Over Y`.
Its colimit corresponds to the intermediate object `obj f J p`
in the factorization `ιObj_πObj`.
-/
noncomputable def inductiveSystem : J ⥤ Over Y :=
  ((functor f Y).transfiniteIterationFunctor (ε f Y) J).flip.obj (Over.mk p)

/-- The inductive system `J ⥤ C` induced by `inductiveSystem f J p`.
Its colimit is `obj f J p`, see `isColimitInductiveSystemForgetCocone`. -/
noncomputable def inductiveSystemForget : J ⥤ C :=
    inductiveSystem f J p ⋙ Over.forget _

/-- The projection `(inductiveSystemForget f J p).obj j ⟶ Y`. -/
noncomputable def πInductiveSystemForgetObj (j : J) :
    (inductiveSystemForget f J p).obj j ⟶ Y :=
  ((inductiveSystem f J p).obj j).hom

@[simp]
lemma inductiveSystem_map_left {j j' : J} (φ : j ⟶ j') :
    ((inductiveSystem f J p).map φ).left = (inductiveSystemForget f J p).map φ := rfl

/-- The isomorphism `(inductiveSystem f J p).obj ⊥ ≅ Over.mk p`. -/
noncomputable def inductiveSystemObjBotIso :
    (inductiveSystem f J p).obj ⊥ ≅ Over.mk p :=
  ((functor f Y).transfiniteIterationObjBotIso (ε f Y) J).app _

/-- The isomorphism `(inductiveSystemForget f J p).obj ⊥ ≅ X`. -/
noncomputable def inductiveSystemForgetObjBotIso :
    (inductiveSystemForget f J p).obj ⊥ ≅ X :=
  (Over.forget _).mapIso (inductiveSystemObjBotIso f J p)

/-- The object `(inductiveSystem f J p).obj (Order.succ j)` identifies to the
image of `(inductiveSystem f J p).obj j` by the functor `functor f Y : Over Y ⥤ Over Y`. -/
noncomputable def inductiveSystemObjSuccIso (j : J) (hj : ¬ IsMax j) :
    (inductiveSystem f J p).obj (Order.succ j) ≅
      (functor f Y).obj ((inductiveSystem f J p).obj j) :=
  ((functor f Y).transfiniteIterationObjSuccIso (ε f Y) j hj).app _

lemma inductiveSystem_map_le_succ (j : J) (hj : ¬ IsMax j) :
    (inductiveSystem f J p).map (homOfLE (Order.le_succ j)) =
      (ε f Y).app ((inductiveSystem f J p).obj j) ≫
        (inductiveSystemObjSuccIso f J p j hj).inv := by
  dsimp [inductiveSystem]
  rw [(functor f Y).transfiniteIterationMap_le_succ _ j hj]
  rfl

/-- The object `(inductiveSystemForget f J p).obj (Order.succ j)` identified to the
left object of the image of `(inductiveSystem f J p).obj j` by the
functor `functor f Y : Over Y ⥤ Over Y`. -/
noncomputable def inductiveSystemForgetObjSuccIso (j : J) (hj : ¬ IsMax j) :
    (inductiveSystemForget f J p).obj (Order.succ j) ≅
      ((functor f Y).obj ((inductiveSystem f J p).obj j)).left :=
  (Over.forget _).mapIso (inductiveSystemObjSuccIso f J p j hj)

@[reassoc]
lemma inductiveSystemForget_map_le_succ (j : J) (hj : ¬ IsMax j) :
    (inductiveSystemForget f J p).map (homOfLE (Order.le_succ j)) =
      ((ε f Y).app ((inductiveSystem f J p).obj j)).left ≫
        (inductiveSystemObjSuccIso f J p j hj).inv.left :=
  (Over.forget _).congr_map (inductiveSystem_map_le_succ f J p j hj)

@[reassoc]
lemma ιFunctorObj_inductiveSystemForgetObjSuccIso_inv (j : J) (hj : ¬ IsMax j) :
    ιFunctorObj f ((inductiveSystem f J p).obj j).hom ≫
        (inductiveSystemForgetObjSuccIso f J p j hj).inv =
    (inductiveSystemForget f J p).map (homOfLE (Order.le_succ j)) := by
  dsimp [inductiveSystemForget, -inductiveSystem_map_left]
  rw [inductiveSystem_map_le_succ f J p j hj]
  rfl

@[reassoc (attr := simp)]
lemma inductiveSystemForgetObjSuccIso_inv_πInductiveSystemForgetObj (j : J) (hj : ¬ IsMax j) :
  (inductiveSystemForgetObjSuccIso f J p j hj).inv ≫
    πInductiveSystemForgetObj f J p (Order.succ j) = πFunctorObj _ _ :=
  Over.w (inductiveSystemObjSuccIso f J p j hj).inv

/-- The cocone of `inductiveSystemForget f J p : J ⥤ C` with point `obj f J p`. -/
noncomputable def inductiveSystemForgetCocone :
    Cocone (inductiveSystemForget f J p) :=
  ((evaluation _ _).obj (Over.mk p) ⋙ Over.forget _).mapCocone
    ((functor f Y).transfiniteIterationCocone (ε f Y) J)

@[simp]
lemma inductiveSystemForgetCocone_pt : (inductiveSystemForgetCocone f J p).pt = obj f J p := rfl

@[reassoc (attr := simp)]
lemma inductiveSystemForgetCocone_ι_app_πObj (j : J) :
    (inductiveSystemForgetCocone f J p).ι.app j ≫ πObj f J p =
      πInductiveSystemForgetObj f J p j :=
  Over.w ((((functor f Y).transfiniteIterationCocone (ε f Y) J).ι.app j).app (Over.mk p))

/-- The colimit of `inductiveSystemForget f J p : J ⥤ C` is `obj f J p`. -/
noncomputable def isColimitInductiveSystemForgetCocone :
    IsColimit (inductiveSystemForgetCocone f J p) :=
  isColimitOfPreserves _
    (((functor f Y).isColimitTransfiniteIterationCocone (ε f Y) J))

@[reassoc (attr := simp)]
lemma inductiveSystemForgetObjBotIso_inv_comp_ι_app :
    (inductiveSystemForgetObjBotIso f J p).inv ≫
        (inductiveSystemForgetCocone f J p).ι.app ⊥ = ιObj f J p :=
  (Over.forget _).congr_map
    ((functor f Y).transfiniteIterationObjBotIso_inv_app_ι_app
      (ε f Y) J (Over.mk p))

@[reassoc (attr := simp)]
lemma inductiveSystemForgetObjBotIso_hom_ιObj :
    (inductiveSystemForgetObjBotIso f J p).hom ≫ ιObj f J p =
      (inductiveSystemForgetCocone f J p).ι.app ⊥ := by
  rw [← inductiveSystemForgetObjBotIso_inv_comp_ι_app, Iso.hom_inv_id_assoc]

instance : (inductiveSystem f J p).IsWellOrderContinuous :=
  inferInstanceAs ((functor f Y).transfiniteIterationFunctor (ε f Y) J ⋙
    (evaluation _ _).obj (Over.mk p)).IsWellOrderContinuous

instance : (inductiveSystemForget f J p).IsWellOrderContinuous :=
  inferInstanceAs (inductiveSystem f J p ⋙ Over.forget Y).IsWellOrderContinuous

instance {Z : C} (π : Z ⟶ Y) [Small.{w} ι] [LocallySmall.{w} C] :
    Small.{w} (SmallObject.FunctorObjIndex f π) := by
  let φ : SmallObject.FunctorObjIndex f π →
    Σ (i : Shrink.{w} ι),
      Shrink.{w} ((A ((equivShrink _).symm i) ⟶ Z) ×
        (B ((equivShrink _).symm i) ⟶ Y)) := fun x ↦ ⟨equivShrink _ x.i, equivShrink _
          (⟨eqToHom (by simp) ≫ x.t, eqToHom (by simp) ≫ x.b⟩)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨i₁, t₁, b₁, _⟩ ⟨i₂, t₂, b₂, _⟩ h
    obtain rfl : i₁ = i₂ := by simpa using congr_arg Sigma.fst h
    simpa [cancel_epi, φ] using h
  exact small_of_injective hφ

open MorphismProperty in
lemma coproducts_pushouts_ιFunctorObj {Z : C} (π : Z ⟶ Y)
    [Small.{w} ι] [LocallySmall.{w} C] :
    (coproducts.{w} (ofHoms f)).pushouts (ιFunctorObj f π) := by
  apply pushouts_mk _ (functorObj_isPushout f π)
  refine coproducts_of_small _ _ (colimitsOfShape_colimMap _ _ ?_)
  rintro ⟨j⟩
  constructor

open MorphismProperty in
lemma transfiniteCompositionsOfShape_ιObj [Small.{w} ι] [LocallySmall.{w} C] :
    (coproducts.{w} (ofHoms f)).pushouts.transfiniteCompositionsOfShape J
      (ιObj f J p) := by
  let e : Arrow.mk ((inductiveSystemForgetCocone f J p).ι.app ⊥) ≅
      Arrow.mk (ιObj f J p) :=
    Arrow.isoMk (inductiveSystemForgetObjBotIso f J p) (Iso.refl _)
  refine (arrow_iso_iff _ e).1 ?_
  apply (transfiniteCompositionsOfShape.mk
    (hc := isColimitInductiveSystemForgetCocone f J p))
  intro j hj
  rw [inductiveSystemForget_map_le_succ _ _ _ _ hj]
  apply RespectsIso.postcomp
  apply MorphismProperty.pushouts_mk _
    ((functorObj_isPushout f ((inductiveSystem f J p).obj j).hom))
  exact coproducts_of_small _ _ (colimitsOfShape_colimMap _ _ (fun _ ↦ ⟨_⟩))

variable [∀ i, PreservesColimit (inductiveSystemForget f J p) (coyoneda.obj (op (A i)))]
  [NoMaxOrder J]

instance hasLiftingProperty_πObj (i : ι) :
    HasLiftingProperty (f i) (πObj f J p) where
  sq_hasLift {g h} sq := by
    obtain ⟨j, t, ht⟩ := Types.jointly_surjective _
      (isColimitOfPreserves (coyoneda.obj (op (A i)))
        (isColimitInductiveSystemForgetCocone f J p)) g
    dsimp at t ht
    let x : FunctorObjIndex f ((inductiveSystem f J p).obj j).hom :=
      { i := i
        t := t
        b := h
        w := by
          rw [← sq.w, ← ht, assoc]
          dsimp [inductiveSystemForgetCocone, πObj]
          rw [Over.w]
          rfl }
    exact ⟨⟨{
      l := Sigma.ι (functorObjTgtFamily _ _) x ≫ ρFunctorObj _ _ ≫
        (inductiveSystemForgetObjSuccIso f J p j (not_isMax j)).inv ≫
        (inductiveSystemForgetCocone f J p).ι.app (Order.succ j)
      fac_left := by
        erw [x.comm_assoc]
        simp [← ht, ιFunctorObj_inductiveSystemForgetObjSuccIso_inv_assoc]
      fac_right := by simp }⟩⟩

end SmallObject

end CategoryTheory
