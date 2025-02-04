/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous

/-!
# The transfinite iteration of a successor structure

Given a successor structure `Φ : SuccStruct C` (see the file `SmallObject.Iteration.Basic`)
and a well-ordered type `J`, we define the iteration `Φ.iteration J : C`. It is
defined as the colimit of a functor `Φ.iterationFunctor J : J ⥤ C`.

-/

universe w v u

namespace CategoryTheory.SmallObject.SuccStruct

open Category Limits

variable {C : Type u} [Category.{v} C] (Φ : SuccStruct C)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

variable {J} in
/-- Given `Φ : SuccStruct C` and an element `j : J` in a well-ordered type,
this is the unique element in `Φ.Iteration j`. -/
noncomputable def iter (j : J) : Φ.Iteration j := Classical.arbitrary _

/-- Given `Φ : SuccStruct C` and a well-ordered type `J`, this
is the functor `J ⥤ C` which gives the iterations of `Φ` indexed by `J`. -/
noncomputable def iterationFunctor : J ⥤ C where
  obj j := (Φ.iter j).F.obj ⟨j, by simp⟩
  map f := Iteration.mapObj _ _ (leOfHom f) _ _ (leOfHom f)

/-- Given `Φ : SuccStruct C` and a well-ordered type `J`,
this is an object of `C` which is the iteration of `Φ` to the power `J`:
it is defined as the colimit of the functor `Φ.iterationFunctor J : J ⥤ C`. -/
noncomputable def iteration : C := colimit (Φ.iterationFunctor J)

/-- The colimit cocone expressing that `Φ.iteration J` is the colimit
of `Φ.iterationFunctor J`. -/
noncomputable def iterationCocone : Cocone (Φ.iterationFunctor J) :=
  colimit.cocone _

@[simp]
lemma iterationCocone_pt : (Φ.iterationCocone J).pt = Φ.iteration J := rfl

/-- `Φ.iteration J` identifies to the colimit of `Φ.iterationFunctor J`. -/
noncomputable def isColimitIterationCocone : IsColimit (Φ.iterationCocone J) :=
  colimit.isColimit _

variable {J}

lemma iterationFunctor_obj (i : J) {j : J} (iter : Φ.Iteration j) (hi : i ≤ j) :
    (Φ.iterationFunctor J).obj i = iter.F.obj ⟨i, hi⟩ :=
  Iteration.congr_obj (Φ.iter i) iter i (by simp) hi

lemma arrow_mk_iterationFunctor_map (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂)
    {j : J} (iter : Φ.Iteration j) (hj : i₂ ≤ j) :
    Arrow.mk ((Φ.iterationFunctor J).map (homOfLE h₁₂)) =
      Arrow.mk (iter.F.map (homOfLE h₁₂ : ⟨i₁, h₁₂.trans hj⟩ ⟶ ⟨i₂, hj⟩)) := by
  dsimp [iterationFunctor]
  rw [Iteration.arrow_mk_mapObj]
  exact Arrow.ext (Iteration.congr_obj _ _ _ _ _)
    (Iteration.congr_obj _ _ _ _ _) (Iteration.congr_map _ _ _ _ _)

lemma prop_iterationFunctor_map_succ (j : J) (hj : ¬ IsMax j) :
    Φ.prop ((Φ.iterationFunctor J).map (homOfLE (Order.le_succ j))) := by
  have := (Φ.iter (Order.succ j)).prop_map_succ j (Order.lt_succ_of_not_isMax hj)
  rw [prop_iff] at this ⊢
  simp only [Φ.iterationFunctor_obj j (Φ.iter (Order.succ j)) (Order.le_succ j),
    Φ.arrow_mk_iterationFunctor_map _ _ (Order.le_succ j) (Φ.iter (Order.succ j)) (by simp),
    this]

/-- For any `i : J`, the restriction to `Set.Iio i` of `Φ.iterationFunctor J`
is isomorphic to the restriction of `(Φ.iter i).F : Set.Iic i ⥤ C`. -/
noncomputable def restrictionLTiterationFunctorIso (i : J) :
    (Φ.iterationFunctor J).restrictionLT i ≅ restrictionLT (Φ.iter i).F (by simp) :=
  NatIso.ofComponents (fun _ ↦ eqToIso (Φ.iterationFunctor_obj _ _ _)) (by
    rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ f
    apply Arrow.mk_injective
    simpa using Φ.arrow_mk_iterationFunctor_map k₁ k₂ (leOfHom f) (Φ.iter i) h₂.le)

variable (J)

/-- The isomorphism `Φ.X₀ ≅ (Φ.iterationFunctor J).obj ⊥`. -/
noncomputable def iterationFunctorObjBotIso : Φ.X₀ ≅ (Φ.iterationFunctor J).obj ⊥ :=
  eqToIso (Φ.iter (⊥ : J)).obj_bot.symm

/-- The natural map `Φ.X₀ ⟶ (Φ.iterationFunctor J).obj j`. -/
noncomputable def ιIterationFunctor :
    (Functor.const _).obj Φ.X₀ ⟶ Φ.iterationFunctor J where
  app j := (Φ.iterationFunctorObjBotIso J).hom ≫
    (Φ.iterationFunctor J).map (homOfLE bot_le : ⊥ ⟶ j)
  naturality _ _ f := by
    dsimp
    rw [id_comp, assoc, ← Functor.map_comp]
    rfl

lemma ιIterationFunctor_app_bot :
    (Φ.ιIterationFunctor J).app ⊥ = (Φ.iterationFunctorObjBotIso J).hom := by
  simp [ιIterationFunctor]

/-- The canonical map `Φ.X₀ ⟶ Φ.iteration J` which is the `J`th-transfinite composition
of maps `Φ.toSucc`. -/
noncomputable def ιIteration : Φ.X₀ ⟶ Φ.iteration J :=
  (Φ.iterationFunctorObjBotIso J).hom ≫ (Φ.iterationCocone J).ι.app ⊥

@[reassoc]
lemma iterationCoconeι_app :
    (Φ.iterationCocone J).ι.app ⊥ =
      (Φ.iterationFunctorObjBotIso J).inv ≫ Φ.ιIteration J := by
  simp [ιIteration]

lemma arrow_mk_ιIteration :
    Arrow.mk (Φ.ιIteration J) = (Φ.iterationCocone J).ι.app ⊥ := by
  simp [ιIteration, iterationFunctorObjBotIso]

instance : (Φ.iterationFunctor J).IsWellOrderContinuous where
  nonempty_isColimit i hi := ⟨by
    refine (IsColimit.precomposeInvEquiv (Φ.restrictionLTiterationFunctorIso i) _).1 ?_
    refine IsColimit.ofIsoColimit ((Φ.iter i).isColimit i hi (by simp)) ?_
    refine Cocones.ext (eqToIso (Φ.iterationFunctor_obj i (Φ.iter i) (by simp)).symm) ?_
    rintro ⟨k, hk⟩
    apply Arrow.mk_injective
    simp [Φ.arrow_mk_iterationFunctor_map k i hk.le (Φ.iter i) (by simp),
      restrictionLTiterationFunctorIso]⟩

lemma transfiniteCompositionOfShape_ιIteration :
    Φ.prop.transfiniteCompositionsOfShape J (Φ.ιIteration J) := by
  simp only [← MorphismProperty.arrow_mk_mem_toSet_iff]
  rw [arrow_mk_ιIteration, MorphismProperty.arrow_mk_mem_toSet_iff]
  exact ⟨_, Φ.prop_iterationFunctor_map_succ, _, Φ.isColimitIterationCocone J⟩

variable {J}

lemma transfiniteCompositionOfShape_iterationFunctor_map_from_bot (j : J) :
    Φ.prop.transfiniteCompositionsOfShape (Set.Iic j)
      ((Φ.iterationFunctor J).map (homOfLE bot_le : ⊥ ⟶ j)) :=
  Φ.prop.transfiniteCompositionsOfShape_map_bot_le (Φ.iterationFunctor J) _
    (fun _ hi ↦ Φ.prop_iterationFunctor_map_succ _ hi.not_isMax)

noncomputable def iterationFunctorObjSuccIso (j : J) (hj : ¬ IsMax j) :
    (Φ.iterationFunctor J).obj (Order.succ j) ≅
      Φ.succ ((Φ.iterationFunctor J).obj j) :=
  eqToIso (by
    rw [iterationFunctor, Iteration.obj_succ _ _ (Order.lt_succ_of_not_isMax hj),
      Iteration.congr_obj])

@[reassoc]
lemma iterationFunctor_map_succ (j : J) (hj : ¬ IsMax j) :
    (Φ.iterationFunctor J).map (homOfLE (Order.le_succ j)) =
      Φ.toSucc _ ≫ (Φ.iterationFunctorObjSuccIso j hj).inv := by
  have := Φ.prop_iterationFunctor_map_succ j hj
  rw [prop_iff, toSuccArrow, Arrow.mk_eq_mk_iff] at this
  obtain ⟨h₁, h₂, h⟩ := this
  simp [h, iterationFunctorObjSuccIso]

end CategoryTheory.SmallObject.SuccStruct
