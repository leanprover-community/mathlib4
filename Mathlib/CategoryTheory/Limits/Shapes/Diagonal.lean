/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.Limits.Shapes.CommSq

#align_import category_theory.limits.shapes.diagonal from "leanprover-community/mathlib"@"f6bab67886fb92c3e2f539cc90a83815f69a189d"

/-!
# The diagonal object of a morphism.

We provide various API and isomorphisms considering the diagonal object `Δ_{Y/X} := pullback f f`
of a morphism `f : X ⟶ Y`.

-/


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {X Y Z : C}

namespace pullback

section Diagonal

variable (f : X ⟶ Y) [HasPullback f f]

/-- The diagonal object of a morphism `f : X ⟶ Y` is `Δ_{X/Y} := pullback f f`. -/
abbrev diagonalObj : C :=
  pullback f f
#align category_theory.limits.pullback.diagonal_obj CategoryTheory.Limits.pullback.diagonalObj

/-- The diagonal morphism `X ⟶ Δ_{X/Y}` for a morphism `f : X ⟶ Y`. -/
def diagonal : X ⟶ diagonalObj f :=
  pullback.lift (𝟙 _) (𝟙 _) rfl
#align category_theory.limits.pullback.diagonal CategoryTheory.Limits.pullback.diagonal

@[reassoc (attr := simp)]
theorem diagonal_fst : diagonal f ≫ pullback.fst = 𝟙 _ :=
  pullback.lift_fst _ _ _
#align category_theory.limits.pullback.diagonal_fst CategoryTheory.Limits.pullback.diagonal_fst

@[reassoc (attr := simp)]
theorem diagonal_snd : diagonal f ≫ pullback.snd = 𝟙 _ :=
  pullback.lift_snd _ _ _
#align category_theory.limits.pullback.diagonal_snd CategoryTheory.Limits.pullback.diagonal_snd

instance : IsSplitMono (diagonal f) :=
  ⟨⟨⟨pullback.fst, diagonal_fst f⟩⟩⟩

instance : IsSplitEpi (pullback.fst : pullback f f ⟶ X) :=
  ⟨⟨⟨diagonal f, diagonal_fst f⟩⟩⟩

instance : IsSplitEpi (pullback.snd : pullback f f ⟶ X) :=
  ⟨⟨⟨diagonal f, diagonal_snd f⟩⟩⟩

instance [Mono f] : IsIso (diagonal f) := by
  rw [(IsIso.inv_eq_of_inv_hom_id (diagonal_fst f)).symm]
  -- ⊢ IsIso (inv fst)
  infer_instance
  -- 🎉 no goals

/-- The two projections `Δ_{X/Y} ⟶ X` form a kernel pair for `f : X ⟶ Y`. -/
theorem diagonal_isKernelPair : IsKernelPair f (pullback.fst : diagonalObj f ⟶ _) pullback.snd :=
  IsPullback.of_hasPullback f f
#align category_theory.limits.pullback.diagonal_is_kernel_pair CategoryTheory.Limits.pullback.diagonal_isKernelPair

end Diagonal

end pullback

variable [HasPullbacks C]

open pullback

section

variable {U V₁ V₂ : C} (f : X ⟶ Y) (i : U ⟶ Y)

variable (i₁ : V₁ ⟶ pullback f i) (i₂ : V₂ ⟶ pullback f i)

@[reassoc (attr := simp)]
theorem pullback_diagonal_map_snd_fst_fst :
    (pullback.snd :
          pullback (diagonal f)
              (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i (by simp [condition])
                                                                         -- 🎉 no goals
                (by simp [condition])) ⟶
                    -- 🎉 no goals
            _) ≫
        fst ≫ i₁ ≫ fst =
      pullback.fst := by
  conv_rhs => rw [← Category.comp_id pullback.fst]
  -- ⊢ snd ≫ fst ≫ i₁ ≫ fst = fst ≫ 𝟙 X
  rw [← diagonal_fst f, pullback.condition_assoc, pullback.lift_fst]
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_snd_fst_fst CategoryTheory.Limits.pullback_diagonal_map_snd_fst_fst

@[reassoc (attr := simp)]
theorem pullback_diagonal_map_snd_snd_fst :
    (pullback.snd :
          pullback (diagonal f)
              (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i (by simp [condition])
                                                                         -- 🎉 no goals
                (by simp [condition])) ⟶
                    -- 🎉 no goals
            _) ≫
        snd ≫ i₂ ≫ fst =
      pullback.fst := by
  conv_rhs => rw [← Category.comp_id pullback.fst]
  -- ⊢ snd ≫ snd ≫ i₂ ≫ fst = fst ≫ 𝟙 X
  rw [← diagonal_snd f, pullback.condition_assoc, pullback.lift_snd]
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_snd_snd_fst CategoryTheory.Limits.pullback_diagonal_map_snd_snd_fst

variable [HasPullback i₁ i₂]

set_option maxHeartbeats 400000 in
/-- This iso witnesses the fact that
given `f : X ⟶ Y`, `i : U ⟶ Y`, and `i₁ : V₁ ⟶ X ×[Y] U`, `i₂ : V₂ ⟶ X ×[Y] U`, the diagram

V₁ ×[X ×[Y] U] V₂ ⟶ V₁ ×[U] V₂
        |                 |
        |                 |
        ↓                 ↓
        X        ⟶ X ×[Y] X

is a pullback square.
Also see `pullback_fst_map_snd_isPullback`.
-/
def pullbackDiagonalMapIso :
    pullback (diagonal f)
        (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i
          (by simp only [Category.assoc, condition])
              -- 🎉 no goals
          (by simp only [Category.assoc, condition])) ≅
              -- 🎉 no goals
      pullback i₁ i₂ where
  hom :=
    pullback.lift (pullback.snd ≫ pullback.fst) (pullback.snd ≫ pullback.snd) (by
      ext
      -- ⊢ ((snd ≫ fst) ≫ i₁) ≫ fst = ((snd ≫ snd) ≫ i₂) ≫ fst
      · simp [Category.assoc, pullback_diagonal_map_snd_fst_fst, pullback_diagonal_map_snd_snd_fst]
        -- 🎉 no goals
      · simp [Category.assoc, pullback.condition, pullback.condition_assoc])
        -- 🎉 no goals
  inv :=
    pullback.lift (pullback.fst ≫ i₁ ≫ pullback.fst)
      (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) pullback.snd (Category.id_comp _).symm
        (Category.id_comp _).symm) (by
        ext
        -- ⊢ ((fst ≫ i₁ ≫ fst) ≫ diagonal f) ≫ fst = (map i₁ i₂ (i₁ ≫ snd) (i₂ ≫ snd) (𝟙  …
        · simp only [Category.assoc, diagonal_fst, Category.comp_id, limit.lift_π,
            PullbackCone.mk_pt, PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left]
        · simp only [condition_assoc, Category.assoc, diagonal_snd, Category.comp_id,
            limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
            limit.lift_π_assoc, cospan_right])
#align category_theory.limits.pullback_diagonal_map_iso CategoryTheory.Limits.pullbackDiagonalMapIso

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso_hom_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).hom ≫ pullback.fst = pullback.snd ≫ pullback.fst := by
  delta pullbackDiagonalMapIso
  -- ⊢ (Iso.mk (lift (snd ≫ fst) (snd ≫ snd) (_ : (snd ≫ fst) ≫ i₁ = (snd ≫ snd) ≫  …
  simp
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_iso_hom_fst CategoryTheory.Limits.pullbackDiagonalMapIso_hom_fst

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso_hom_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).hom ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  delta pullbackDiagonalMapIso
  -- ⊢ (Iso.mk (lift (snd ≫ fst) (snd ≫ snd) (_ : (snd ≫ fst) ≫ i₁ = (snd ≫ snd) ≫  …
  simp
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_iso_hom_snd CategoryTheory.Limits.pullbackDiagonalMapIso_hom_snd

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso_inv_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.fst = pullback.fst ≫ i₁ ≫ pullback.fst := by
  delta pullbackDiagonalMapIso
  -- ⊢ (Iso.mk (lift (snd ≫ fst) (snd ≫ snd) (_ : (snd ≫ fst) ≫ i₁ = (snd ≫ snd) ≫  …
  simp
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_iso_inv_fst CategoryTheory.Limits.pullbackDiagonalMapIso_inv_fst

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso_inv_snd_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd ≫ pullback.fst = pullback.fst := by
  delta pullbackDiagonalMapIso
  -- ⊢ (Iso.mk (lift (snd ≫ fst) (snd ≫ snd) (_ : (snd ≫ fst) ≫ i₁ = (snd ≫ snd) ≫  …
  simp
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_iso_inv_snd_fst CategoryTheory.Limits.pullbackDiagonalMapIso_inv_snd_fst

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso_inv_snd_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd ≫ pullback.snd = pullback.snd := by
  delta pullbackDiagonalMapIso
  -- ⊢ (Iso.mk (lift (snd ≫ fst) (snd ≫ snd) (_ : (snd ≫ fst) ≫ i₁ = (snd ≫ snd) ≫  …
  simp
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_iso_inv_snd_snd CategoryTheory.Limits.pullbackDiagonalMapIso_inv_snd_snd

theorem pullback_fst_map_snd_isPullback :
    IsPullback (fst ≫ i₁ ≫ fst)
      (map i₁ i₂ (i₁ ≫ snd) (i₂ ≫ snd) _ _ _ (Category.id_comp _).symm (Category.id_comp _).symm)
      (diagonal f)
      (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i (by simp [condition])
                                                                 -- 🎉 no goals
        (by simp [condition])) :=
            -- 🎉 no goals
  IsPullback.of_iso_pullback ⟨by ext <;> simp [condition_assoc]⟩
                                 -- ⊢ ((fst ≫ i₁ ≫ fst) ≫ diagonal f) ≫ fst = (map i₁ i₂ (i₁ ≫ snd) (i₂ ≫ snd) (𝟙  …
                                         -- 🎉 no goals
                                         -- 🎉 no goals
    (pullbackDiagonalMapIso f i i₁ i₂).symm (pullbackDiagonalMapIso_inv_fst f i i₁ i₂)
    (by aesop_cat)
        -- 🎉 no goals
#align category_theory.limits.pullback_fst_map_snd_is_pullback CategoryTheory.Limits.pullback_fst_map_snd_isPullback

end

section

variable {S T : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S)

variable [HasPullback i i] [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)]

variable
  [HasPullback (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _))]

/-- This iso witnesses the fact that
given `f : X ⟶ T`, `g : Y ⟶ T`, and `i : T ⟶ S`, the diagram

X ×ₜ Y ⟶ X ×ₛ Y
  |         |
  |         |
  ↓         ↓
  T  ⟶  T ×ₛ T

is a pullback square.
Also see `pullback_map_diagonal_isPullback`.
-/
def pullbackDiagonalMapIdIso :
    pullback (diagonal i)
        (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ≅
      pullback f g := by
  refine' _ ≪≫
    pullbackDiagonalMapIso i (𝟙 _) (f ≫ inv pullback.fst) (g ≫ inv pullback.fst) ≪≫ _
  · refine' @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 T) ((pullback.congrHom _ _).hom) (𝟙 _) _ _) ?_
    · rw [← Category.comp_id pullback.snd, ← condition, Category.assoc, IsIso.inv_hom_id_assoc]
      -- 🎉 no goals
    · rw [← Category.comp_id pullback.snd, ← condition, Category.assoc, IsIso.inv_hom_id_assoc]
      -- 🎉 no goals
    · rw [Category.comp_id, Category.id_comp]
      -- 🎉 no goals
    · ext <;> simp
      -- ⊢ (map (f ≫ i) (g ≫ i) i i f g (𝟙 S) (_ : (f ≫ i) ≫ 𝟙 S = f ≫ i) (_ : (g ≫ i)  …
              -- 🎉 no goals
              -- 🎉 no goals
    · infer_instance
      -- 🎉 no goals
  · refine' @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) pullback.fst _ _) ?_
    · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
      -- 🎉 no goals
    · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
      -- 🎉 no goals
    · infer_instance
      -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_id_iso CategoryTheory.Limits.pullbackDiagonalMapIdIso

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_hom_fst :
    (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.fst = pullback.snd ≫ pullback.fst := by
  delta pullbackDiagonalMapIdIso
  -- ⊢ (asIso (map (diagonal i) (map (f ≫ i) (g ≫ i) i i f g (𝟙 S) (_ : (f ≫ i) ≫ 𝟙 …
  simp
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_id_iso_hom_fst CategoryTheory.Limits.pullbackDiagonalMapIdIso_hom_fst

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_hom_snd :
    (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  delta pullbackDiagonalMapIdIso
  -- ⊢ (asIso (map (diagonal i) (map (f ≫ i) (g ≫ i) i i f g (𝟙 S) (_ : (f ≫ i) ≫ 𝟙 …
  simp
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_id_iso_hom_snd CategoryTheory.Limits.pullbackDiagonalMapIdIso_hom_snd

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_inv_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.fst = pullback.fst ≫ f := by
  rw [Iso.inv_comp_eq, ← Category.comp_id pullback.fst, ← diagonal_fst i, pullback.condition_assoc]
  -- ⊢ snd ≫ map (f ≫ i) (g ≫ i) i i f g (𝟙 S) (_ : (f ≫ i) ≫ 𝟙 S = f ≫ i) (_ : (g  …
  simp
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_id_iso_inv_fst CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_fst

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_inv_snd_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd ≫ pullback.fst = pullback.fst := by
  rw [Iso.inv_comp_eq]
  -- ⊢ snd ≫ fst = (pullbackDiagonalMapIdIso f g i).hom ≫ fst
  simp
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_id_iso_inv_snd_fst CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_snd_fst

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_inv_snd_snd :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd ≫ pullback.snd = pullback.snd := by
  rw [Iso.inv_comp_eq]
  -- ⊢ snd ≫ snd = (pullbackDiagonalMapIdIso f g i).hom ≫ snd
  simp
  -- 🎉 no goals
#align category_theory.limits.pullback_diagonal_map_id_iso_inv_snd_snd CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_snd_snd

theorem pullback.diagonal_comp (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullback f f] [HasPullback g g]
    [HasPullback (f ≫ g) (f ≫ g)] :
    diagonal (f ≫ g) = diagonal f ≫ (pullbackDiagonalMapIdIso f f g).inv ≫ pullback.snd := by
  ext <;> simp
  -- ⊢ diagonal (f ≫ g) ≫ fst = (diagonal f ≫ (pullbackDiagonalMapIdIso f f g).inv  …
          -- 🎉 no goals
          -- 🎉 no goals
#align category_theory.limits.pullback.diagonal_comp CategoryTheory.Limits.pullback.diagonal_comp

theorem pullback_map_diagonal_isPullback :
    IsPullback (pullback.fst ≫ f)
      (pullback.map f g (f ≫ i) (g ≫ i) _ _ i (Category.id_comp _).symm (Category.id_comp _).symm)
      (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) := by
  apply IsPullback.of_iso_pullback _ (pullbackDiagonalMapIdIso f g i).symm
  · simp
    -- 🎉 no goals
  · ext <;> simp
    -- ⊢ ((pullbackDiagonalMapIdIso f g i).symm.hom ≫ snd) ≫ fst = map f g (f ≫ i) (g …
            -- 🎉 no goals
            -- 🎉 no goals
  · constructor
    -- ⊢ (fst ≫ f) ≫ diagonal i = map f g (f ≫ i) (g ≫ i) (𝟙 X) (𝟙 Y) i (_ : f ≫ i =  …
    ext <;> simp [condition]
    -- ⊢ ((fst ≫ f) ≫ diagonal i) ≫ fst = (map f g (f ≫ i) (g ≫ i) (𝟙 X) (𝟙 Y) i (_ : …
            -- 🎉 no goals
            -- 🎉 no goals
#align category_theory.limits.pullback_map_diagonal_is_pullback CategoryTheory.Limits.pullback_map_diagonal_isPullback

/-- The diagonal object of `X ×[Z] Y ⟶ X` is isomorphic to `Δ_{Y/Z} ×[Z] X`. -/
def diagonalObjPullbackFstIso {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonalObj (pullback.fst : pullback f g ⟶ X) ≅
      pullback (pullback.snd ≫ g : diagonalObj g ⟶ Z) f :=
  pullbackRightPullbackFstIso _ _ _ ≪≫
    pullback.congrHom pullback.condition rfl ≪≫
      pullbackAssoc _ _ _ _ ≪≫ pullbackSymmetry _ _ ≪≫ pullback.congrHom pullback.condition rfl
#align category_theory.limits.diagonal_obj_pullback_fst_iso CategoryTheory.Limits.diagonalObjPullbackFstIso

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_hom_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst ≫ pullback.fst =
      pullback.fst ≫ pullback.snd := by
  delta diagonalObjPullbackFstIso
  -- ⊢ (pullbackRightPullbackFstIso f g fst ≪≫ congrHom (_ : fst ≫ f = snd ≫ g) (_  …
  simp
  -- 🎉 no goals
#align category_theory.limits.diagonal_obj_pullback_fst_iso_hom_fst_fst CategoryTheory.Limits.diagonalObjPullbackFstIso_hom_fst_fst

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_hom_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst ≫ pullback.snd =
      pullback.snd ≫ pullback.snd := by
  delta diagonalObjPullbackFstIso
  -- ⊢ (pullbackRightPullbackFstIso f g fst ≪≫ congrHom (_ : fst ≫ f = snd ≫ g) (_  …
  simp
  -- 🎉 no goals
#align category_theory.limits.diagonal_obj_pullback_fst_iso_hom_fst_snd CategoryTheory.Limits.diagonalObjPullbackFstIso_hom_fst_snd

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_hom_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.snd = pullback.fst ≫ pullback.fst := by
  delta diagonalObjPullbackFstIso
  -- ⊢ (pullbackRightPullbackFstIso f g fst ≪≫ congrHom (_ : fst ≫ f = snd ≫ g) (_  …
  simp
  -- 🎉 no goals
#align category_theory.limits.diagonal_obj_pullback_fst_iso_hom_snd CategoryTheory.Limits.diagonalObjPullbackFstIso_hom_snd

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst ≫ pullback.fst = pullback.snd := by
  delta diagonalObjPullbackFstIso
  -- ⊢ (pullbackRightPullbackFstIso f g fst ≪≫ congrHom (_ : fst ≫ f = snd ≫ g) (_  …
  simp
  -- 🎉 no goals
#align category_theory.limits.diagonal_obj_pullback_fst_iso_inv_fst_fst CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_fst_fst

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst ≫ pullback.snd =
      pullback.fst ≫ pullback.fst := by
  delta diagonalObjPullbackFstIso
  -- ⊢ (pullbackRightPullbackFstIso f g fst ≪≫ congrHom (_ : fst ≫ f = snd ≫ g) (_  …
  simp
  -- 🎉 no goals
#align category_theory.limits.diagonal_obj_pullback_fst_iso_inv_fst_snd CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_fst_snd

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_snd_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd ≫ pullback.fst = pullback.snd := by
  delta diagonalObjPullbackFstIso
  -- ⊢ (pullbackRightPullbackFstIso f g fst ≪≫ congrHom (_ : fst ≫ f = snd ≫ g) (_  …
  simp
  -- 🎉 no goals
#align category_theory.limits.diagonal_obj_pullback_fst_iso_inv_snd_fst CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_snd_fst

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_snd_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd ≫ pullback.snd =
      pullback.fst ≫ pullback.snd := by
  delta diagonalObjPullbackFstIso
  -- ⊢ (pullbackRightPullbackFstIso f g fst ≪≫ congrHom (_ : fst ≫ f = snd ≫ g) (_  …
  simp
  -- 🎉 no goals
#align category_theory.limits.diagonal_obj_pullback_fst_iso_inv_snd_snd CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_snd_snd

theorem diagonal_pullback_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonal (pullback.fst : pullback f g ⟶ _) =
      (pullbackSymmetry _ _).hom ≫
        ((baseChange f).map
              (Over.homMk (diagonal g) : Over.mk g ⟶ Over.mk (pullback.snd ≫ g))).left ≫
          (diagonalObjPullbackFstIso f g).inv := by
  ext <;> dsimp <;> simp
          -- ⊢ (diagonal fst ≫ fst) ≫ fst = (((pullbackSymmetry f g).hom ≫ map g f (snd ≫ g …
          -- ⊢ (diagonal fst ≫ fst) ≫ snd = (((pullbackSymmetry f g).hom ≫ map g f (snd ≫ g …
          -- ⊢ (diagonal fst ≫ snd) ≫ fst = (((pullbackSymmetry f g).hom ≫ map g f (snd ≫ g …
          -- ⊢ (diagonal fst ≫ snd) ≫ snd = (((pullbackSymmetry f g).hom ≫ map g f (snd ≫ g …
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
#align category_theory.limits.diagonal_pullback_fst CategoryTheory.Limits.diagonal_pullback_fst

end

/-- Given the following diagram with `S ⟶ S'` a monomorphism,

    X ⟶ X'
      ↘      ↘
        S ⟶ S'
      ↗      ↗
    Y ⟶ Y'

This iso witnesses the fact that

      X ×[S] Y ⟶ (X' ×[S'] Y') ×[Y'] Y
          |                  |
          |                  |
          ↓                  ↓
(X' ×[S'] Y') ×[X'] X ⟶ X' ×[S'] Y'

is a pullback square. The diagonal map of this square is `pullback.map`.
Also see `pullback_lift_map_is_pullback`.
-/
@[simps]
def pullbackFstFstIso {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [Mono i₃] :
    pullback (pullback.fst : pullback (pullback.fst : pullback f' g' ⟶ _) i₁ ⟶ _)
        (pullback.fst : pullback (pullback.snd : pullback f' g' ⟶ _) i₂ ⟶ _) ≅
      pullback f g
    where
  hom :=
    pullback.lift (pullback.fst ≫ pullback.snd) (pullback.snd ≫ pullback.snd)
      (by
        rw [← cancel_mono i₃, Category.assoc, Category.assoc, Category.assoc, Category.assoc, e₁,
          e₂, ← pullback.condition_assoc, pullback.condition_assoc, pullback.condition,
          pullback.condition_assoc])
  inv :=
    pullback.lift
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) pullback.fst (pullback.lift_fst _ _ _))
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) pullback.snd (pullback.lift_snd _ _ _))
      (by rw [pullback.lift_fst, pullback.lift_fst])
          -- 🎉 no goals
  hom_inv_id := by
    -- We could use `ext` here to immediately descend to the leaf goals,
    -- but it only obscures the structure.
    apply pullback.hom_ext
    -- ⊢ (lift (fst ≫ snd) (snd ≫ snd) (_ : (fst ≫ snd) ≫ f = (snd ≫ snd) ≫ g) ≫ lift …
    · apply pullback.hom_ext
      -- ⊢ ((lift (fst ≫ snd) (snd ≫ snd) (_ : (fst ≫ snd) ≫ f = (snd ≫ snd) ≫ g) ≫ lif …
      · apply pullback.hom_ext
        -- ⊢ (((lift (fst ≫ snd) (snd ≫ snd) (_ : (fst ≫ snd) ≫ f = (snd ≫ snd) ≫ g) ≫ li …
        · simp only [Category.assoc, lift_fst, lift_fst_assoc, Category.id_comp]
          -- ⊢ fst ≫ snd ≫ i₁ = fst ≫ fst ≫ fst
          rw [condition]
          -- 🎉 no goals
        · simp [Category.assoc, lift_snd]
          -- ⊢ snd ≫ snd ≫ i₂ = fst ≫ fst ≫ snd
          rw [condition_assoc, condition]
          -- 🎉 no goals
      · simp only [Category.assoc, lift_fst_assoc, lift_snd, lift_fst, Category.id_comp]
        -- 🎉 no goals
    · apply pullback.hom_ext
      -- ⊢ ((lift (fst ≫ snd) (snd ≫ snd) (_ : (fst ≫ snd) ≫ f = (snd ≫ snd) ≫ g) ≫ lif …
      · apply pullback.hom_ext
        -- ⊢ (((lift (fst ≫ snd) (snd ≫ snd) (_ : (fst ≫ snd) ≫ f = (snd ≫ snd) ≫ g) ≫ li …
        · simp only [Category.assoc, lift_snd_assoc, lift_fst_assoc, lift_fst, Category.id_comp]
          -- ⊢ fst ≫ snd ≫ i₁ = snd ≫ fst ≫ fst
          rw [← condition_assoc, condition]
          -- 🎉 no goals
        · simp only [Category.assoc, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.id_comp]
          -- ⊢ snd ≫ snd ≫ i₂ = snd ≫ fst ≫ snd
          rw [condition]
          -- 🎉 no goals
      · simp only [Category.assoc, lift_snd_assoc, lift_snd, Category.id_comp]
        -- 🎉 no goals
  inv_hom_id := by
    apply pullback.hom_ext
    -- ⊢ (lift (lift (map f g f' g' i₁ i₂ i₃ e₁ e₂) fst (_ : lift (fst ≫ i₁) (snd ≫ i …
    · simp only [Category.assoc, lift_fst, lift_fst_assoc, lift_snd, Category.id_comp]
      -- 🎉 no goals
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, Category.id_comp]
      -- 🎉 no goals
#align category_theory.limits.pullback_fst_fst_iso CategoryTheory.Limits.pullbackFstFstIso

theorem pullback_map_eq_pullbackFstFstIso_inv {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
    (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ =
      (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).inv ≫ pullback.snd ≫ pullback.fst := by
  simp only [pullbackFstFstIso_inv, lift_snd_assoc, lift_fst]
  -- 🎉 no goals
#align category_theory.limits.pullback_map_eq_pullback_fst_fst_iso_inv CategoryTheory.Limits.pullback_map_eq_pullbackFstFstIso_inv

theorem pullback_lift_map_isPullback {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
    (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
    (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    IsPullback (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) fst (lift_fst _ _ _))
      (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) snd (lift_snd _ _ _)) pullback.fst
      pullback.fst :=
  IsPullback.of_iso_pullback ⟨by rw [lift_fst, lift_fst]⟩
                                 -- 🎉 no goals
    (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).symm (by simp) (by simp)
                                                          -- 🎉 no goals
                                                                    -- 🎉 no goals
#align category_theory.limits.pullback_lift_map_is_pullback CategoryTheory.Limits.pullback_lift_map_isPullback

end CategoryTheory.Limits
