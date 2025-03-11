/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Adjunction.AdjunctionTwo

/-!
# Lifting properties and adjunctions of bifunctors

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Arrow

universe v u

variable {C : Type u} [Category.{v} C]

abbrev LiftStruct {f g : Arrow C} (φ : f ⟶ g) := (CommSq.mk φ.w).LiftStruct

lemma hasLiftingProperty_iff {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ ∀ (φ : Arrow.mk i ⟶ Arrow.mk p), Nonempty (LiftStruct φ) := by
  constructor
  · intro _ φ
    have sq : CommSq φ.left i p φ.right := (CommSq.mk φ.w)
    exact ⟨{ l := sq.lift }⟩
  · intro h
    exact ⟨fun {f g} sq ↦ ⟨h (Arrow.homMk f g sq.w)⟩⟩

end Arrow

open Opposite Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

namespace Functor

section

variable {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂)

structure PushoutObjObj where
  pt : C₃
  inl : (F.obj Y₁).obj X₂ ⟶ pt
  inr : (F.obj X₁).obj Y₂ ⟶ pt
  isPushout : IsPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂) inl inr

namespace PushoutObjObj

@[simps]
noncomputable def ofHasPushout
    [HasPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂)] :
    F.PushoutObjObj f₁ f₂ where
  isPushout := IsPushout.of_hasPushout _ _

variable {F f₁ f₂} (sq : F.PushoutObjObj f₁ f₂)

@[reassoc]
lemma w : (F.map f₁).app X₂ ≫ sq.inl = (F.obj X₁).map f₂ ≫ sq.inr :=
  sq.isPushout.w

noncomputable def ι : sq.pt ⟶ (F.obj Y₁).obj Y₂ :=
  sq.isPushout.desc ((F.obj Y₁).map f₂) ((F.map f₁).app Y₂) (by simp)

@[reassoc (attr := simp)]
lemma inl_ι : sq.inl ≫ sq.ι = (F.obj Y₁).map f₂ := by simp [ι]

@[reassoc (attr := simp)]
lemma inr_ι : sq.inr ≫ sq.ι = (F.map f₁).app Y₂ := by simp [ι]

end PushoutObjObj

end

section

variable {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₃ Y₃ : C₃} (f₃ : X₃ ⟶ Y₃)

structure PullbackObjObj where
  pt : C₂
  fst : pt ⟶ (G.obj (op X₁)).obj X₃
  snd : pt ⟶ (G.obj (op Y₁)).obj Y₃
  isPullback : IsPullback fst snd ((G.obj (op X₁)).map f₃)
    ((G.map f₁.op).app Y₃)

namespace PullbackObjObj

@[simps]
noncomputable def ofHasPullback
    [HasPullback ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)] :
    G.PullbackObjObj f₁ f₃ where
  isPullback := IsPullback.of_hasPullback _ _

variable {G f₁ f₃} (sq : G.PullbackObjObj f₁ f₃)

@[reassoc]
lemma w : sq.fst ≫ (G.obj (op X₁)).map f₃ =
    sq.snd ≫ (G.map f₁.op).app Y₃ :=
  sq.isPullback.w

noncomputable def π : (G.obj (op Y₁)).obj X₃ ⟶ sq.pt :=
  sq.isPullback.lift ((G.map f₁.op).app X₃) ((G.obj (op Y₁)).map f₃) (by simp)

@[reassoc (attr := simp)]
lemma π_fst : sq.π ≫ sq.fst = (G.map f₁.op).app X₃ := by simp [π]

@[reassoc (attr := simp)]
lemma π_snd : sq.π ≫ sq.snd = (G.obj (op Y₁)).map f₃ := by simp [π]

end PullbackObjObj

end

end Functor

namespace Adjunction₂

variable {F G} (adj₂ : F ⊣₂ G)
  {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁} {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂}
  {X₃ Y₃ : C₃} {f₃ : X₃ ⟶ Y₃}
  (sq₁₂ : F.PushoutObjObj f₁ f₂) (sq₁₃ : G.PullbackObjObj f₁ f₃)

@[simps! -isSimp apply_left apply_right symm_apply_left symm_apply_right]
noncomputable def arrowHomEquiv :
    (Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) ≃
      (Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) where
  toFun α := Arrow.homMk (adj₂.homEquiv (sq₁₂.inl ≫ α.left))
    (sq₁₃.isPullback.lift
      (adj₂.homEquiv (sq₁₂.inr ≫ α.left)) (adj₂.homEquiv α.right)
        (by simp [← adj₂.homEquiv_naturality_one,
            ← adj₂.homEquiv_naturality_three])) (by
          apply sq₁₃.isPullback.hom_ext
          · simp [← adj₂.homEquiv_naturality_two,
              ← adj₂.homEquiv_naturality_one,
              sq₁₂.w_assoc]
          · simp [← adj₂.homEquiv_naturality_two,
              ← adj₂.homEquiv_naturality_three])
  invFun β := Arrow.homMk
      (sq₁₂.isPushout.desc
        (adj₂.homEquiv.symm (β.left))
        (adj₂.homEquiv.symm (β.right ≫ sq₁₃.fst)) (by
          have := Arrow.w β =≫ sq₁₃.fst
          dsimp at this
          simp only [Category.assoc, sq₁₃.π_fst] at this
          simp only [← adj₂.homEquiv_symm_naturality_one,
            ← adj₂.homEquiv_symm_naturality_two,
            Arrow.mk_left, Arrow.mk_right, this]))
      (adj₂.homEquiv.symm (β.right ≫ sq₁₃.snd)) (by
        apply sq₁₂.isPushout.hom_ext
        · have := Arrow.w β =≫ sq₁₃.snd
          dsimp at this
          simp only [Category.assoc, sq₁₃.π_snd] at this
          simp [← adj₂.homEquiv_symm_naturality_two,
            ← adj₂.homEquiv_symm_naturality_three, this]
        · simp [← adj₂.homEquiv_symm_naturality_one,
            ← adj₂.homEquiv_symm_naturality_three, sq₁₃.w])
  left_inv α := by
    ext
    · apply sq₁₂.isPushout.hom_ext <;> simp
    · simp
  right_inv β := by
    ext
    · simp
    · apply sq₁₃.isPullback.hom_ext <;> simp

attribute [local simp] arrowHomEquiv_apply_left arrowHomEquiv_apply_right
  arrowHomEquiv_symm_apply_left arrowHomEquiv_symm_apply_right

def liftStructEquiv (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) :
    Arrow.LiftStruct α ≃ Arrow.LiftStruct (adj₂.arrowHomEquiv sq₁₂ sq₁₃ α) where
  toFun l :=
    { l := adj₂.homEquiv l.l
      fac_left := by
        have := l.fac_left
        dsimp at this ⊢
        simp only [← adj₂.homEquiv_naturality_two, ← this,
          sq₁₂.inl_ι_assoc]
      fac_right := by
        apply sq₁₃.isPullback.hom_ext
        · have := l.fac_left
          dsimp at this ⊢
          simp only [Category.assoc, sq₁₃.π_fst, IsPullback.lift_fst,
            ← adj₂.homEquiv_naturality_one, ← this, sq₁₂.inr_ι_assoc]
        · have := l.fac_right
          dsimp at this ⊢
          simp only [Category.assoc, sq₁₃.π_snd, IsPullback.lift_snd, ← this,
            adj₂.homEquiv_naturality_three] }
  invFun l :=
    { l := adj₂.homEquiv.symm l.l
      fac_left := by
        apply sq₁₂.isPushout.hom_ext
        · have := l.fac_left
          dsimp at this ⊢
          simp only [sq₁₂.inl_ι_assoc, ← adj₂.homEquiv_symm_naturality_two,
            this, Equiv.symm_apply_apply]
        · have := l.fac_right =≫ sq₁₃.fst
          dsimp at this ⊢
          simp only [Category.assoc, sq₁₃.π_fst, IsPullback.lift_fst] at this
          simp only [sq₁₂.inr_ι_assoc, ← adj₂.homEquiv_symm_naturality_one,
            this, Equiv.symm_apply_apply]
      fac_right := by
        have := l.fac_right =≫ sq₁₃.snd
        dsimp at this ⊢
        simp only [Category.assoc, sq₁₃.π_snd, IsPullback.lift_snd] at this
        rw [← adj₂.homEquiv_symm_naturality_three, this,
          Equiv.symm_apply_apply] }
  left_inv _ := by aesop
  right_inv _ := by aesop

include adj₂ in
lemma hasLiftingProperty_iff :
    HasLiftingProperty sq₁₂.ι f₃ ↔ HasLiftingProperty f₂ sq₁₃.π := by
  simp only [Arrow.hasLiftingProperty_iff]
  constructor
  · intro h β
    obtain ⟨α, rfl⟩ := (adj₂.arrowHomEquiv sq₁₂ sq₁₃).surjective β
    exact ⟨adj₂.liftStructEquiv sq₁₂ sq₁₃ α (h α).some⟩
  · intro h α
    exact ⟨(adj₂.liftStructEquiv sq₁₂ sq₁₃ α).symm (h _).some⟩

end Adjunction₂

end CategoryTheory
