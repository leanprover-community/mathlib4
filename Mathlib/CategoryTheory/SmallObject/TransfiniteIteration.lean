/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Transfinite iteration of a functor

Let `Φ : C ⥤ C` be a functor and `ε : 𝟭 C ⟶ Φ` be a natural transformation.
For any well-ordered type `J` such that suitable colimits exists
(condition `HasIterationOfShape C J`), we define `Φ.transfiniteIteration ε J : C ⥤ C`.
It is defined as the colimit of the functor `Φ.transfiniteIterationCocone ε J : J ⥤ C ⥤ C`
which sends `j : J` to `Φ.transfiniteIterationObj ε j` which is the
value at `j` of the functor `(Φ.iteration ε j).F` where
`Φ.iteration ε j` is the unique object (up to a unique isomorphism) of
the category `Iteration ε j` (see the files `SmallObject.Iteration.Basic`,
`SmallObject.Iteration.UniqueHom` and `SmallObject.Iteration.Nonempty`).

If `ε` consists of morphisms which belong to a class `W : MorphismProperty C`,
we show in the lemma `transfiniteCompositionsOfShape_ιTransfiniteIteration_app`
that the map `(Φ.ιTransfiniteIteration ε J).app X : X ⟶ (Φ.transfiniteIteration ε J).obj X`
is in the class `W.transfiniteCompositionsOfShape J`, i.e. the class of
transfinite compositions of `W` of shape `J`.

-/

universe u

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C : Type*} [Category C] (Φ : C ⥤ C) (ε : 𝟭 C ⟶ Φ)
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape C J]

/-- Given a natural transformation `ε : 𝟭 C ⟶ Φ` and `j : J`,
this is a choice of object in the category `Iteration ε j`. -/
noncomputable def iteration (j : J) : Iteration ε j := Classical.arbitrary _

/-- Given a natural transformation `ε : 𝟭 C ⟶ Φ` and `j : J`,
this is the functor `C ⥤ C` obtained by evaluating at `j`
the functor `(Φ.iteration ε j).F`. -/
noncomputable def transfiniteIterationObj (j : J) : C ⥤ C :=
  (Φ.iteration ε j).F.obj ⟨j, by simp⟩

/-- The inclusion `𝟭 C ⟶ Φ.transfiniteIterationObj ε j`. -/
noncomputable def ιTransfiniteIterationObj (j : J) :
    𝟭 C ⟶ Φ.transfiniteIterationObj ε j :=
  (Φ.iteration ε j).isoZero.inv ≫ (Φ.iteration ε j).F.map (homOfLE bot_le)

/-- The map `Φ.transfiniteIterationObj ε j₁ ⟶ Φ.transfiniteIterationObj ε j₂`
induced by an inequality `j₁ ≤ j₂`. -/
noncomputable def transfiniteIterationMap {j₁ j₂ : J} (h : j₁ ≤ j₂) :
    Φ.transfiniteIterationObj ε j₁ ⟶ Φ.transfiniteIterationObj ε j₂ :=
  (Iteration.iso (Φ.iteration ε j₁)
    ((Φ.iteration ε j₂).trunc h)).hom.natTrans.app ⟨j₁, by simp⟩ ≫
      (Φ.iteration ε j₂).F.map (homOfLE h)

@[reassoc (attr := simp)]
lemma ι_transfiniteIterationMap {j₁ j₂ : J} (h : j₁ ≤ j₂) :
    Φ.ιTransfiniteIterationObj ε j₁ ≫ Φ.transfiniteIterationMap ε h =
      Φ.ιTransfiniteIterationObj ε j₂ := by
  simp [ιTransfiniteIterationObj, transfiniteIterationMap, ← Functor.map_comp]

@[simp]
lemma transfiniteIterationMap_refl (j : J) :
    Φ.transfiniteIterationMap ε (le_refl j) = 𝟙 _ := by
  simp [transfiniteIterationMap, transfiniteIterationObj]

@[reassoc]
lemma transfiniteIterationMap_trans {j₁ j₂ j₃ : J} (h₁₂ : j₁ ≤ j₂) (h₂₃ : j₂ ≤ j₃) :
    Φ.transfiniteIterationMap ε (h₁₂.trans h₂₃) =
      Φ.transfiniteIterationMap ε h₁₂ ≫ Φ.transfiniteIterationMap ε h₂₃ := by
  dsimp [transfiniteIterationMap, transfiniteIterationObj]
  rw [← Iteration.iso_hom_comp_iso_hom _ ((Φ.iteration ε j₂).trunc h₁₂) _]
  simp [← map_comp, ← Iteration.iso_trunc_hom_natTrans_app _ _ h₁₂]

/-- The canonical isomorphism
`Φ.transfiniteIterationObj ε (Order.succ j) ≅ Φ.transfiniteIterationObj ε j ⋙ Φ`. -/
noncomputable def transfiniteIterationObjSuccIso (j : J) (hj : ¬ IsMax j) :
    Φ.transfiniteIterationObj ε (Order.succ j) ≅
      Φ.transfiniteIterationObj ε j ⋙ Φ :=
  (Φ.iteration ε (Order.succ j)).isoSucc j (Order.lt_succ_of_not_isMax hj) ≪≫
    isoWhiskerRight ((Iteration.eval ε (le_refl j)).mapIso
      (Iteration.iso ((Φ.iteration ε (Order.succ j)).trunc (Order.le_succ j))
        (Φ.iteration ε j))) Φ

lemma transfiniteIterationMap_le_succ (j : J) (hj : ¬ IsMax j) :
    Φ.transfiniteIterationMap ε (Order.le_succ j) =
      whiskerLeft _ ε ≫ (Φ.transfiniteIterationObjSuccIso ε j hj).inv := by
  ext X
  have := congr_app ((Φ.iteration ε (Order.succ j)).mapSucc_eq j
    (Order.lt_succ_of_not_isMax hj)) X
  dsimp at this
  dsimp [transfiniteIterationObjSuccIso]
  rw [← ε.naturality_assoc, ← this]
  rfl

lemma transfiniteIterationMap_le_succ_app (j : J) (hj : ¬ IsMax j) (X : C) :
    (Φ.transfiniteIterationMap ε (Order.le_succ j)).app X =
      ε.app _ ≫ (Φ.transfiniteIterationObjSuccIso ε j hj).inv.app X := by
  simp [transfiniteIterationMap_le_succ _ _ _ hj]

variable (J)

/-- The canonical isomorphism `Φ.transfiniteIterationObj ε (⊥ : J) ≅ 𝟭 C`. -/
noncomputable def transfiniteIterationObjBotIso :
    Φ.transfiniteIterationObj ε (⊥ : J) ≅ 𝟭 C :=
  (Φ.iteration ε (⊥ : J)).isoZero

lemma ιTransfiniteIterationObj_bot :
    Φ.ιTransfiniteIterationObj ε (⊥ : J) =
      (Φ.transfiniteIterationObjBotIso ε J).inv := by
  simp [ιTransfiniteIterationObj, transfiniteIterationObjBotIso]

/-- The functor `J ⥤ C ⥤ C` which sends `j : J` to `Φ.transfiniteIterationObj ε j`. -/
@[simps]
noncomputable def transfiniteIterationFunctor : J ⥤ C ⥤ C where
  obj j := Φ.transfiniteIterationObj ε j
  map φ := Φ.transfiniteIterationMap ε (leOfHom φ)
  map_comp φ₁₂ φ₂₃ := Φ.transfiniteIterationMap_trans ε (leOfHom φ₁₂) (leOfHom φ₂₃)

variable {J}

variable (j : J)

/-- For any `j : J`, the restriction of the functor `Φ.transfiniteIterationFunctor ε J`
to `Set.Iic j` identifies to `(Φ.iteration ε j).F`. -/
@[simps!]
noncomputable def transfiniteIterationFunctorRestrictionLEIso (j : J) :
    (Φ.transfiniteIterationFunctor ε J).restrictionLE j ≅ (Φ.iteration ε j).F :=
  NatIso.ofComponents (fun ⟨i, hi⟩ ↦ (Iteration.eval ε (le_refl i)).mapIso
      (Iteration.iso (Φ.iteration ε i) ((Φ.iteration ε j).trunc hi))) (by
        rintro ⟨k₁, hk₁ : k₁ ≤ j⟩ ⟨k₂, hk₂ : k₂ ≤ j⟩ φ
        have h : k₁ ≤ k₂ := leOfHom φ
        dsimp [transfiniteIterationMap]
        simp only [homOfLE_leOfHom, assoc, NatTrans.naturality, Iteration.restrictionLE_obj,
          Iteration.restrictionLE_map, Monotone.functor_obj]
        conv_rhs => rw [← Iteration.iso_hom_comp_iso_hom _ ((Φ.iteration ε k₂).trunc h) _]
        rw [← Iteration.iso_trunc_hom_natTrans_app _ _ h _ (by rfl)]
        dsimp
        rw [assoc]
        rfl)

/-- For any `j : J`, the restriction of the functor `Φ.transfiniteIterationFunctor ε J`
to `Set.Iio j` identifies the restriction of `(Φ.iteration ε j).F`. -/
@[simps!]
noncomputable def transfiniteIterationFunctorRestrictionLTIso (j : J) :
    (Φ.transfiniteIterationFunctor ε J).restrictionLT j ≅
      Iteration.restrictionLT (Φ.iteration ε j).F (le_refl j) :=
  isoWhiskerLeft (monotone_inclusion_lt_le_of_le (le_refl j)).functor
    (Φ.transfiniteIterationFunctorRestrictionLEIso ε j)

variable (J)

instance transfiniteIterationFunctor_isWellOrderContinuous :
    (Φ.transfiniteIterationFunctor ε J).IsWellOrderContinuous where
  nonempty_isColimit j hj :=
    ⟨(IsColimit.precomposeHomEquiv
      (Φ.transfiniteIterationFunctorRestrictionLTIso ε j).symm _).1
        (IsColimit.ofIsoColimit ((Φ.iteration ε j).isColimit j hj (le_refl j))
          (Cocones.ext (Iso.refl _) (fun ⟨k, hk⟩ ↦ by
            dsimp [transfiniteIterationMap]
            simp only [homOfLE_leOfHom, comp_id, ← NatTrans.comp_app_assoc,
              Iteration.restrictionLE_obj, ← Iteration.natTrans_comp, Iso.inv_hom_id,
              Iteration.natTrans_id, Iteration.trunc_F, NatTrans.id_app, id_comp])))⟩

/-- A colimit cocone of `Φ.transfiniteIterationFunctor ε J`,
with point `Φ.transfiniteIteration ε J`. -/
noncomputable def transfiniteIterationCocone : Cocone (Φ.transfiniteIterationFunctor ε J) :=
  colimit.cocone _

/-- `Φ.transfiniteIterationCocone ε J` is a colimit cocone,
with point `Φ.transfiniteIteration ε J`. -/
noncomputable def isColimitTransfiniteIterationCocone :
    IsColimit (Φ.transfiniteIterationCocone ε J) :=
  colimit.isColimit _

/-- Let `Φ : C ⥤ C` a functor and `ε : 𝟭 C ⟶ Φ` be a natural transformation.
For any well-ordered type `J` such that suitable colimits exists
(condition `HasIterationOfShape C J`), this is the `J`-th iteration of the functor `Φ`. -/
noncomputable def transfiniteIteration : C ⥤ C := (Φ.transfiniteIterationCocone ε J).pt

@[simp]
lemma transfiniteIterationCocone_pt :
    (Φ.transfiniteIterationCocone ε J).pt = Φ.transfiniteIteration ε J := rfl

/-- The inclusion `𝟭 C ⟶ Φ.transfiniteIteration ε J`. -/
noncomputable def ιTransfiniteIteration : 𝟭 C ⟶ Φ.transfiniteIteration ε J :=
  Φ.ιTransfiniteIterationObj ε ⊥ ≫ (Φ.transfiniteIterationCocone ε J).ι.app ⊥

variable {J} in
@[reassoc (attr := simp)]
lemma ι_transfiniteIterationCocone_ι_app (j : J) :
  Φ.ιTransfiniteIterationObj ε j ≫ (Φ.transfiniteIterationCocone ε J).ι.app j =
    Φ.ιTransfiniteIteration ε J := by
  simp [ιTransfiniteIteration, ← (Φ.transfiniteIterationCocone ε J).w (homOfLE bot_le : ⊥ ⟶ j),
    ι_transfiniteIterationMap_assoc]

@[reassoc (attr := simp)]
lemma transfiniteIterationObjBotIso_inv_ι :
    (Φ.transfiniteIterationObjBotIso ε J).inv ≫ ((Φ.transfiniteIterationCocone ε J).ι.app ⊥) =
      Φ.ιTransfiniteIteration ε J := by
  rw [← Φ.ι_transfiniteIterationCocone_ι_app ε (⊥ : J), ← ιTransfiniteIterationObj_bot]

@[reassoc (attr := simp)]
lemma transfiniteIterationObjBotIso_inv_app_ι_app (X : C):
    (Φ.transfiniteIterationObjBotIso ε J).inv.app X ≫
      ((Φ.transfiniteIterationCocone ε J).ι.app ⊥).app X =
        (Φ.ιTransfiniteIteration ε J).app X := by
  simp [← transfiniteIterationObjBotIso_inv_ι]

section

variable (W : MorphismProperty C) [W.RespectsIso] (hε : ∀ (T : C), W (ε.app T))

include hε

lemma transfiniteCompositionsOfShape_transfiniteIterationCocone_ι_app_bot :
    (W.functorCategory C).transfiniteCompositionsOfShape J
      ((Φ.transfiniteIterationCocone ε J).ι.app ⊥) :=
  ⟨_, fun j hj X ↦ by
        dsimp
        rw [transfiniteIterationMap_le_succ _ _ _ hj]
        exact MorphismProperty.RespectsIso.postcomp _ _ _ (hε _), _,
    Φ.isColimitTransfiniteIterationCocone ε J⟩

lemma transfiniteCompositionsOfShape_transfiniteIterationCocone_ι_app_bot_app (X : C) :
    W.transfiniteCompositionsOfShape J
      (((Φ.transfiniteIterationCocone ε J).ι.app ⊥).app X) :=
  ⟨_, fun j hj ↦ by
        dsimp
        rw [transfiniteIterationMap_le_succ_app _ _ _ hj]
        exact MorphismProperty.RespectsIso.postcomp _ _ _ (hε _), _,
    isColimitOfPreserves ((evaluation C C).obj X) (Φ.isColimitTransfiniteIterationCocone ε J)⟩

lemma transfiniteCompositionsOfShape_ιTransfiniteIteration_app (X : C) :
    W.transfiniteCompositionsOfShape J ((Φ.ιTransfiniteIteration ε J).app X) := by
  refine (MorphismProperty.arrow_mk_iso_iff _ ?_).2
    (Φ.transfiniteCompositionsOfShape_transfiniteIterationCocone_ι_app_bot_app ε J W hε X)
  exact Arrow.isoMk ((Φ.transfiniteIterationObjBotIso ε J).app X).symm (Iso.refl _)

end

end Functor

end CategoryTheory
