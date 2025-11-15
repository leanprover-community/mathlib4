import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

open CategoryTheory Limits Category

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C]

inductive WeakSaturation (S : MorphismProperty C) : MorphismProperty C where
  | of {X Y : C} (f : X ⟶ Y) (h : S f) : WeakSaturation S f
  | cobaseChange {A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
      (sq : IsPushout g f f' g') (hf : WeakSaturation S f) : WeakSaturation S f'
  | retracts {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)
      (hg : WeakSaturation S g) : WeakSaturation S f
  | id_mem (X : C) : WeakSaturation S (𝟙 X)
  | comp_mem {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : WeakSaturation S f)
      (hg : WeakSaturation S g) : WeakSaturation S (f ≫ g)
  -- Here, we could take a universe parameter `w` and take `J : Type w`.
  -- For the right lifting property, the universe does change anything
  -- (see `WeakSaturation.rlp_eq` below)
  | transfiniteComposition (J : Type) [LinearOrder J] [SuccOrder J] [OrderBot J]
      [WellFoundedLT J] (F : J ⥤ C) [F.IsWellOrderContinuous]
      (hF : ∀ (j : J) (_ : ¬IsMax j), WeakSaturation S (F.map (homOfLE (Order.le_succ j))))
      (c : Cocone F) (hc : IsColimit c) : WeakSaturation S (c.ι.app ⊥)

variable (S : MorphismProperty C)

instance : IsStableUnderCobaseChange (WeakSaturation S) where
  of_isPushout hP h:= WeakSaturation.cobaseChange hP h

instance : IsStableUnderRetracts (WeakSaturation S) where
  of_retract h hg := WeakSaturation.retracts h hg

instance : IsMultiplicative (WeakSaturation S) where
  id_mem := WeakSaturation.id_mem
  comp_mem _ _ := WeakSaturation.comp_mem

instance : IsStableUnderTransfiniteComposition.{0} (WeakSaturation S) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    constructor
    intro _ _ f hf
    induction hf with
    | mk F hF c hc =>
      exact WeakSaturation.transfiniteComposition J F hF c hc

lemma weakSaturation_le (T : MorphismProperty C) [IsStableUnderCobaseChange T]
    [IsStableUnderRetracts T] [IsStableUnderTransfiniteComposition.{0} T] (le : S ≤ T) :
    WeakSaturation S ≤ T := by
  intro _ _ f hf
  induction hf with
  | of f h => exact le f h
  | cobaseChange sq hf ih => exact T.of_isPushout sq ih
  | retracts h hg ih => exact T.of_retract h ih
  | id_mem X => exact T.id_mem X
  | comp_mem hf hg hf_ih hg_ih => exact T.comp_mem _ _ hf_ih hg_ih
  | transfiniteComposition J F hF c hc ih =>
      apply T.transfiniteCompositionsOfShape_le J
      exact transfiniteCompositionsOfShape.mk F (fun j x ↦ ih j x) c hc

lemma WeakSaturation.rlp_eq : S.rlp = (WeakSaturation S).rlp := by
  ext X Y f
  refine ⟨fun h _ _ g hg ↦ ?_, fun h _ _ _ hg ↦ h _ (of _ hg)⟩
  induction hg with
  | of _ h' => exact h _ h'
  | cobaseChange P hf ih => exact { sq_hasLift := fun {u _} sq ↦
      ⟨P.desc u (P.toCommSq.horiz_comp sq).lift (by simp),
        by simp, P.hom_ext (by simpa using sq.w) (by simp)⟩ }
  | retracts h _ ih => exact {
      sq_hasLift := fun sq ↦ by
        obtain ⟨l, hl₁, hl₂⟩ := ih.1 ((CommSq.mk h.r_w).horiz_comp sq)
        refine ⟨⟨h.i.right ≫ l, ?_, ?_⟩⟩
        · rw [← assoc, ← h.i_w, assoc, hl₁]; simp
        · simp [hl₂] }
  | id_mem _ => exact HasLiftingProperty.of_left_iso _ _
  | comp_mem _ _ _ _ => exact HasLiftingProperty.of_comp_left _ _ f
  | transfiniteComposition J F hF c hc ih =>
      exact HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot hc ih

end CategoryTheory.MorphismProperty
