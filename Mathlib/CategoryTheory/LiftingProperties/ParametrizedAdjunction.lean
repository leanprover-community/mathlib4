/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Lifting properties and parametrized adjunctions

Let `F : C₁ ⥤ C₂ ⥤ C₃`. Given morphisms `f₁ : X₁ ⟶ Y₁` in `C₁`
and `f₂ : X₂ ⟶ Y₂` in `C₂`, we introduce a structure
`F.PushoutObjObj f₁ f₂` which contains the data of a
pushout of `(F.obj Y₁).obj X₂` and `(F.obj X₁).obj Y₂`
along `(F.obj X₁).obj X₂`. If `sq₁₂ : F.PushoutObjObj f₁ f₂`,
we have a canonical "inclusion" `sq₁₂.ι : sq₁₂.pt ⟶ (F.obj Y₁).obj Y₂`.

Similarly, if we have a bifunctor `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`, and
morphisms `f₁ : X₁ ⟶ Y₁` in `C₁` and `f₃ : X₃ ⟶ Y₃` in `C₃`,
we introduce a structure `F.PullbackObjObj f₁ f₃` which
contains the data of a pullback of `(G.obj (op X₁)).obj X₃`
and `(G.obj (op Y₁)).obj Y₃` over `(G.obj (op X₁)).obj Y₃`.
If `sq₁₃ : F.PullbackObjObj f₁ f₃`, we have a canonical
projection `sq₁₃.π : (G.obj Y₁).obj X₃ ⟶ sq₁₃.pt`.

Now, if we have a parametrized adjunction `adj₂ : F ⊣₂ G`,
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`,
we show that `sq₁₂.ι` has the left lifting property with respect to
`f₃` if and only if `f₂` has the left lifting property with respect
to `sq₁₃.π`: this is the lemma `ParametrizedAdjunction.hasLiftingProperty_iff`.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

namespace Functor

section

variable {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂)

/-- Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C₃`, and morphisms `f₁ : X₁ ⟶ Y₁` in `C₁`
and `f₂ : X₂ ⟶ Y₂` in `C₂`, this structure contains the data of
a pushout of `(F.obj Y₁).obj X₂` and `(F.obj X₁).obj Y₂`
along `(F.obj X₁).obj X₂`. -/
structure PushoutObjObj where
  /-- the pushout -/
  pt : C₃
  /-- the first inclusion -/
  inl : (F.obj Y₁).obj X₂ ⟶ pt
  /-- the second inclusion -/
  inr : (F.obj X₁).obj Y₂ ⟶ pt
  isPushout : IsPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂) inl inr

namespace PushoutObjObj

/-- The `PushoutObjObj` structure given by the pushout of the colimits API. -/
@[simps]
noncomputable def ofHasPushout
    [HasPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂)] :
    F.PushoutObjObj f₁ f₂ :=
  { isPushout := IsPushout.of_hasPushout _ _, .. }

variable {F f₁ f₂} (sq : F.PushoutObjObj f₁ f₂)

/-- The "inclusion" `sq.pt ⟶ (F.obj Y₁).obj Y₂` when
`sq : F.PushoutObjObj f₁ f₂`. -/
noncomputable def ι : sq.pt ⟶ (F.obj Y₁).obj Y₂ :=
  sq.isPushout.desc ((F.obj Y₁).map f₂) ((F.map f₁).app Y₂) (by simp)

@[reassoc (attr := simp)]
lemma inl_ι : sq.inl ≫ sq.ι = (F.obj Y₁).map f₂ := by simp [ι]

@[reassoc (attr := simp)]
lemma inr_ι : sq.inr ≫ sq.ι = (F.map f₁).app Y₂ := by simp [ι]

/-- Given `sq : F.PushoutObjObj f₁ f₂`, flipping the pushout square gives
`sq.flip : F.flip.PushoutObjObj f₂ f₁`. -/
@[simps]
def flip : F.flip.PushoutObjObj f₂ f₁ where
  pt := sq.pt
  inl := sq.inr
  inr := sq.inl
  isPushout := sq.isPushout.flip

@[simp]
lemma ι_flip : sq.flip.ι = sq.ι := by
  apply sq.flip.isPushout.hom_ext
  · rw [inl_ι, flip_inl, inr_ι, flip_obj_map]
  · rw [inr_ι, flip_inr, inl_ι, flip_map_app]

end PushoutObjObj

end

section

variable {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₃ Y₃ : C₃} (f₃ : X₃ ⟶ Y₃)

/-- Given a bifunctor `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`, and morphisms `f₁ : X₁ ⟶ Y₁` in `C₁`
and `f₃ : X₃ ⟶ Y₃` in `C₃`, this structure contains the data of
a pullback of `(G.obj (op X₁)).obj X₃`
and `(G.obj (op Y₁)).obj Y₃` over `(G.obj (op X₁)).obj Y₃`. -/
structure PullbackObjObj where
  /-- the pullback -/
  pt : C₂
  /-- the first projection -/
  fst : pt ⟶ (G.obj (op X₁)).obj X₃
  /-- the second projection -/
  snd : pt ⟶ (G.obj (op Y₁)).obj Y₃
  isPullback : IsPullback fst snd ((G.obj (op X₁)).map f₃)
    ((G.map f₁.op).app Y₃)

namespace PullbackObjObj

/-- The `PullbackObjObj` structure given by the pullback of the limits API. -/
@[simps]
noncomputable def ofHasPullback
    [HasPullback ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)] :
    G.PullbackObjObj f₁ f₃ :=
  { isPullback := IsPullback.of_hasPullback _ _, ..}

variable {G f₁ f₃} (sq : G.PullbackObjObj f₁ f₃)

/-- The projection `(G.obj (op Y₁)).obj X₃ ⟶ sq.pt` when
`sq : G.PullbackObjObj f₁ f₃`. -/
noncomputable def π : (G.obj (op Y₁)).obj X₃ ⟶ sq.pt :=
  sq.isPullback.lift ((G.map f₁.op).app X₃) ((G.obj (op Y₁)).map f₃) (by simp)

@[reassoc (attr := simp)]
lemma π_fst : sq.π ≫ sq.fst = (G.map f₁.op).app X₃ := by simp [π]

@[reassoc (attr := simp)]
lemma π_snd : sq.π ≫ sq.snd = (G.obj (op Y₁)).map f₃ := by simp [π]

end PullbackObjObj

end

end Functor

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
          simp only [Category.assoc, sq₁₃.π_fst, IsPullback.lift_fst] at this
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
