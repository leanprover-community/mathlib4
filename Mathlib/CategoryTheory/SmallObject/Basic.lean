/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.SmallObject.Construction
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Limits.Over

/-!
# The small object argument

Let `f i : A i ⟶ B i` be a family of morphisms indexed by `ι` in a category `C`.
Let `J` be a well-ordered type without a maximal element. Under suitable assumptions
(which include the existence of pushouts, certain coproducts and suitable colimits),
given a morphism `p : X ⟶ Y` we construct a factorization (in the `SmallObject` namespace)
of `p` as `ιObj f J p ≫ πObj f J p = p`. The intermediate object `obj f J p` which
appears in this filtration is obtained by transfinite iteration of the functor
`functor f Y : Over Y ⥤ Over Y` (see file `SmallObject.Construction`).

When `J` is chosen carefully so that for all `i`, the functor `coyoneda.obj (op A i)`
commutes with the colimit of the system which gives `obj f J p`, then
the morphism `πObj f J p : obj f J p ⟶ Y` has the right lifting property
with respect to the morphisms `f i : A i ⟶ B i`, and by construction,
the morphism `ιObj f J p : X ⟶ obj f J p` is a transfinite composition of pushouts
of coproducts of morphisms in the family `f`.

In the context of model categories, this result is known as Quillen's small object
argument (originally for `J := ℕ`). Actually, the more general construction by
transfinite induction already appeared in the proof of the existence of enough
injectives in abelian categories with AB5 and a generator by Grothendieck, who then
wrote that the "proof was essentially known". Indeed, the argument appears
in *Homological algebra* by Cartan and Eilenberg (p. 9-10) in the case of modules,
and they mention that the result was initially obtained by Baer.

-/

universe t w v u

namespace CategoryTheory

open Category Limits Opposite

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

open MorphismProperty in
lemma transfiniteCompositionsOfShape_ιObj :
    (coproducts.{max v t} (ofHoms f)).pushouts.transfiniteCompositionsOfShape J
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
  rw [coproducts_iff]
  exact ⟨FunctorObjIndex f ((inductiveSystem f J p).obj j).hom,
    colimitsOfShape_colimMap _ _ (fun _ ↦ ⟨_⟩)⟩

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

lemma rlp_πObj : (MorphismProperty.ofHoms f).rlp (πObj f J p) := by
  rintro _ _ _ ⟨i⟩
  apply hasLiftingProperty_πObj

end SmallObject

end CategoryTheory
