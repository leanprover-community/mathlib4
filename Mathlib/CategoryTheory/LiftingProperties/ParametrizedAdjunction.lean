/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Lifting properties and parametrized adjunctions

If we have a parametrized adjunction `adj₂ : F ⊣₂ G`,
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`,
we show that `sq₁₂.ι` has the left lifting property with respect to
`f₃` if and only if `f₂` has the left lifting property with respect
to `sq₁₃.π`: this is the lemma `ParametrizedAdjunction.hasLiftingProperty_iff`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

namespace ParametrizedAdjunction

variable {F G} (adj₂ : F ⊣₂ G)
  {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁} {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂}
  {X₃ Y₃ : C₃} {f₃ : X₃ ⟶ Y₃}
  (sq₁₂ : F.PushoutObjObj f₁ f₂) (sq₁₃ : G.PullbackObjObj f₁ f₃)

/-- Given a parametrized adjunction `F ⊣₂ G` between bifunctors, and structures
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`, there are
as many commutative squares with left map `sq₁₂.ι` and right map `f₃`
as commutative squares with left map `f₂` and right map `sq₁₃.π`. -/
@[simps! apply_left symm_apply_right]
noncomputable def arrowHomEquiv :
    (Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) ≃
      (Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) where
  toFun α :=
    Arrow.homMk (adj₂.homEquiv (sq₁₂.inl ≫ α.left))
      (sq₁₃.isPullback.lift
        (adj₂.homEquiv (sq₁₂.inr ≫ α.left)) (adj₂.homEquiv α.right)
          (by simp [← adj₂.homEquiv_naturality_one,
              ← adj₂.homEquiv_naturality_three])) (by
            apply sq₁₃.isPullback.hom_ext
            · simp [← adj₂.homEquiv_naturality_two,
                ← adj₂.homEquiv_naturality_one,
                sq₁₂.isPushout.w_assoc]
            · simp [← adj₂.homEquiv_naturality_two,
                ← adj₂.homEquiv_naturality_three])
  invFun β :=
    Arrow.homMk
      (sq₁₂.isPushout.desc
        (adj₂.homEquiv.symm β.left)
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
            ← adj₂.homEquiv_symm_naturality_three, sq₁₃.isPullback.w])
  left_inv α := by
    ext
    · apply sq₁₂.isPushout.hom_ext <;> simp
    · simp
  right_inv β := by
    ext
    · simp
    · apply sq₁₃.isPullback.hom_ext <;> simp

@[reassoc (attr := simp)]
lemma arrowHomEquiv_apply_right_fst (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) :
    ((adj₂.arrowHomEquiv sq₁₂ sq₁₃) α).right ≫ sq₁₃.fst = adj₂.homEquiv (sq₁₂.inr ≫ α.left) :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma arrowHomEquiv_apply_right_snd (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) :
    ((adj₂.arrowHomEquiv sq₁₂ sq₁₃) α).right ≫ sq₁₃.snd = adj₂.homEquiv α.right :=
  IsPullback.lift_snd _ _ _ _

@[reassoc (attr := simp)]
lemma inl_arrowHomEquiv_symm_apply_left (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) :
    sq₁₂.inl ≫ ((adj₂.arrowHomEquiv sq₁₂ sq₁₃).symm β).left = adj₂.homEquiv.symm β.left :=
  IsPushout.inl_desc _ _ _ _

@[reassoc (attr := simp)]
lemma inr_arrowHomEquiv_symm_apply_left (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) :
    sq₁₂.inr ≫ ((adj₂.arrowHomEquiv sq₁₂ sq₁₃).symm β).left =
    adj₂.homEquiv.symm (β.right ≫ sq₁₃.fst) :=
  IsPushout.inr_desc _ _ _ _

/-- Given a parametrized adjunction `F ⊣₂ G` between bifunctors, structures
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`,
there are as many liftings for the commutative square given by a
map `α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃` as there are liftings
for the square given by the corresponding map `Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π`. -/
noncomputable def liftStructEquiv (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) :
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
          simp only [Category.assoc, sq₁₃.π_fst, ← adj₂.homEquiv_naturality_one,
            arrowHomEquiv_apply_right_fst, Arrow.mk_left, ← this, sq₁₂.inr_ι_assoc]
        · have := l.fac_right
          dsimp at this ⊢
          simp only [Category.assoc, sq₁₃.π_snd, ← this, adj₂.homEquiv_naturality_three,
            arrowHomEquiv_apply_right_snd, Arrow.mk_right] }
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
          simp only [Category.assoc, sq₁₃.π_fst] at this
          simp only [sq₁₂.inr_ι_assoc, ← adj₂.homEquiv_symm_naturality_one,
            this, Equiv.symm_apply_apply, arrowHomEquiv_apply_right_fst, Arrow.mk_left]
      fac_right := by
        have := l.fac_right =≫ sq₁₃.snd
        dsimp at this ⊢
        simp only [Category.assoc, sq₁₃.π_snd, arrowHomEquiv_apply_right_snd,
          Arrow.mk_right] at this
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

end ParametrizedAdjunction

end CategoryTheory
