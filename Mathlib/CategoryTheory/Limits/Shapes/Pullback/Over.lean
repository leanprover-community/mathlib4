/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!

# Products in over categories are pullbacks

## TODO
- Dualize to under categories
- Generalize to wide pullbacks

-/

namespace CategoryTheory

variable {C} [Category C] {X : C} {Y Z : Over X}

open Limits

lemma Over.isPullback_of_binaryFan_isLimit (c : BinaryFan Y Z) (hc : IsLimit c) :
    IsPullback c.fst.left c.snd.left Y.hom Z.hom := by
  have l (s : PullbackCone Y.hom Z.hom) := BinaryFan.IsLimit.lift' hc
      (Over.homMk (U := Over.mk (s.fst ≫ Y.hom)) s.fst rfl)
      (Over.homMk (U := Over.mk (s.fst ≫ Y.hom)) s.snd s.condition.symm)
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk (by simp) (fun s ↦ (l s).1.left)
    (fun s ↦ congr($((l s).2.1).left)) (fun s ↦ congr($((l s).2.2).left)) ?_⟩⟩
  intros s m h₁ h₂
  have : Over.homMk (U := (Over.mk (s.fst ≫ Y.hom))) m
      (show _ = s.fst ≫ Y.hom by rw [← h₁, Category.assoc, Over.w (B := Y) c.fst]) = (l s).1 := by
    apply BinaryFan.IsLimit.hom_ext hc
    · exact (OverMorphism.ext h₁).trans (l s).2.1.symm
    · exact (OverMorphism.ext h₂).trans (l s).2.2.symm
  exact congr(($this).left)

variable (Y Z) [HasPullback Y.hom Z.hom] [HasBinaryProduct Y Z]

/-- The product of `Y` and `Z` in `Over X` is isomorpic to `Y ×ₓ Z`. -/
noncomputable
def Over.prod_left_iso_pullback :
    (Y ⨯ Z).left ≅ pullback Y.hom Z.hom :=
  (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd Y Z)).isoPullback

@[reassoc (attr := simp)]
lemma Over.prod_left_iso_pullback_hom_fst :
    (prod_left_iso_pullback Y Z).hom ≫ pullback.fst _ _ = (prod.fst (X := Y)).left :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
lemma Over.prod_left_iso_pullback_hom_snd :
    (prod_left_iso_pullback Y Z).hom ≫ pullback.snd _ _ = (prod.snd (X := Y)).left :=
  IsPullback.isoPullback_hom_snd _

@[reassoc (attr := simp)]
lemma Over.prod_left_iso_pullback_inv_fst :
    (prod_left_iso_pullback Y Z).inv ≫ (prod.fst (X := Y)).left = pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst _

@[reassoc (attr := simp)]
lemma Over.prod_left_iso_pullback_inv_snd :
    (prod_left_iso_pullback Y Z).inv ≫ (prod.snd (X := Y)).left = pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

end CategoryTheory
