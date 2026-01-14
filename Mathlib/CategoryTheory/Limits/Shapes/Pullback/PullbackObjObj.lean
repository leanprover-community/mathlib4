/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Pushout-products and pullback-powers

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

-/

@[expose] public section

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

@[simp]
lemma ofHasPushout_ι
    [HasPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂)] :
    (ofHasPushout F f₁ f₂).ι =
    (IsPushout.of_hasPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂)).desc
      ((F.obj Y₁).map f₂) ((F.map f₁).app Y₂) (((F.map f₁).naturality f₂).symm) := rfl

end PushoutObjObj

end

/-- The pushout-product of `f₁` and `f₂`. -/
@[simp]
noncomputable
abbrev pushoutProduct [HasPushouts C₃]
    {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂) :=
  (Functor.PushoutObjObj.ofHasPushout F f₁ f₂).ι

notation3 f₁ " [" F "] " f₂:10 => Functor.pushoutProduct F f₁ f₂

namespace PushoutProduct

section Functor

variable (f₁ : Arrow C₁) {f₂ f₂' : Arrow C₂} (sq : f₂ ⟶ f₂')
  (sq₁₂ : F.PushoutObjObj f₁.hom f₂.hom)
  (sq₁₂' : F.PushoutObjObj f₁.hom f₂'.hom)

@[simp]
noncomputable
def leftFunctor_map_left :
    sq₁₂.pt ⟶ sq₁₂'.pt :=
  sq₁₂.isPushout.desc
    (((F.obj f₁.right).map sq.left) ≫ sq₁₂'.inl)
    (((F.obj f₁.left).map sq.right) ≫ sq₁₂'.inr)
    (by grind [sq.w, sq₁₂'.isPushout.w])

@[simp]
noncomputable
def leftFunctor_map :
    Arrow.mk sq₁₂.ι ⟶ Arrow.mk sq₁₂'.ι where
  left := leftFunctor_map_left F f₁ sq sq₁₂ sq₁₂'
  right := (F.obj f₁.right).map sq.right
  w := by
    apply sq₁₂.isPushout.hom_ext
    · simp [← map_comp]
    · cat_disch

noncomputable
def iso_of_arrow_iso (iso : f₂ ≅ f₂') :
    Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂'.ι where
  hom := PushoutProduct.leftFunctor_map F f₁ iso.hom sq₁₂ sq₁₂'
  inv := PushoutProduct.leftFunctor_map F f₁ iso.inv sq₁₂' sq₁₂
  hom_inv_id := by
    apply Arrow.hom_ext
    · apply sq₁₂.isPushout.hom_ext
      all_goals simp [← map_comp_assoc]
    · simp [← map_comp]
  inv_hom_id := by
    apply Arrow.hom_ext
    · apply sq₁₂'.isPushout.hom_ext
      all_goals simp [← map_comp_assoc]
    · simp [← map_comp]

@[simp]
noncomputable
def leftFunctor [HasPushouts C₃] (f₁ : Arrow C₁) : Arrow C₂ ⥤ Arrow C₃ where
  obj f₂ := f₁.hom [F] f₂.hom
  map sq := leftFunctor_map F f₁ sq (PushoutObjObj.ofHasPushout F f₁.hom _)
    (PushoutObjObj.ofHasPushout F f₁.hom _)

variable {f₁ f₁' : Arrow C₁} (f₂ : Arrow C₂) (sq : f₁ ⟶ f₁')
  (sq₁₂ : F.PushoutObjObj f₁.hom f₂.hom)
  (sq₁₂' : F.PushoutObjObj f₁'.hom f₂.hom)

@[simp]
noncomputable
def leftBifunctor_map_left :
    sq₁₂.pt ⟶ sq₁₂'.pt :=
  sq₁₂.isPushout.desc
    ((F.map sq.right).app f₂.left ≫ sq₁₂'.inl)
    ((F.map sq.left).app f₂.right ≫ sq₁₂'.inr)
    (by grind [sq.w, sq₁₂'.isPushout.w])

@[simp]
noncomputable
def leftBifunctor_map [HasPushouts C₃] {f₁ f₁' : Arrow C₁} (sq : f₁ ⟶ f₁') :
    leftFunctor F f₁ ⟶ leftFunctor F f₁' where
  app f₂ := {
    left := leftBifunctor_map_left F f₂ sq (PushoutObjObj.ofHasPushout _ _ _)
      (PushoutObjObj.ofHasPushout _ _ _)
    right := (F.map sq.right).app f₂.right
    w := by
      apply pushout.hom_ext
      all_goals simp [← NatTrans.comp_app, ← Functor.map_comp] }

@[simps!]
noncomputable
def leftBifunctor [HasPushouts C₃] : Arrow C₁ ⥤ Arrow C₂ ⥤ Arrow C₃ where
  obj := leftFunctor F
  map := leftBifunctor_map F

end Functor

end PushoutProduct

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

@[simp]
lemma ofHasPullback_π
    [HasPullback ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)] :
    (ofHasPullback G f₁ f₃).π =
    (IsPullback.of_hasPullback ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)).lift
      ((G.map f₁.op).app X₃) ((G.obj (op Y₁)).map f₃) ((G.map f₁.op).naturality f₃).symm := rfl

end PullbackObjObj

end

/-- The pullback-power of `f₁` and `f₃`. -/
@[simp]
noncomputable
abbrev pullbackPower [HasPullbacks C₂]
    {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₃ Y₃ : C₃} (f₃ : X₃ ⟶ Y₃) :=
  (Functor.PullbackObjObj.ofHasPullback G f₁ f₃).π

notation3 f₁ " {" G "} " f₃:10 => Functor.pullbackPower G f₁ f₃

namespace PullbackPower

section Functor

variable (f₁ : (Arrow C₁)ᵒᵖ) {f₃ f₃' : Arrow C₃} (sq : f₃ ⟶ f₃')
  (sq₁₃ : G.PullbackObjObj f₁.unop.hom f₃.hom)
  (sq₁₃' : G.PullbackObjObj f₁.unop.hom f₃'.hom)

@[simp]
noncomputable
def rightFunctor_map_right :
    sq₁₃.pt ⟶ sq₁₃'.pt := by
  refine sq₁₃'.isPullback.lift
    (sq₁₃.fst ≫ (G.obj (.op f₁.unop.left)).map sq.left)
    (sq₁₃.snd ≫ (G.obj (.op f₁.unop.right)).map sq.right)
    (by grind [sq.w, sq₁₃.isPullback.w])

@[simp]
noncomputable
def rightFunctor_map :
    Arrow.mk sq₁₃.π ⟶ Arrow.mk sq₁₃'.π where
  left := (G.obj (.op f₁.unop.right)).map sq.left
  right := rightFunctor_map_right G f₁ sq sq₁₃ sq₁₃'
  w := by
    apply sq₁₃'.isPullback.hom_ext
    all_goals simp [← Functor.map_comp]

@[simp]
noncomputable
def rightFunctor [HasPullbacks C₂] (f₁ : (Arrow C₁)ᵒᵖ) : Arrow C₃ ⥤ Arrow C₂ where
  obj f₃ := f₁.unop.hom {G} f₃.hom
  map sq := rightFunctor_map G f₁ sq (PullbackObjObj.ofHasPullback _ _ _)
    (PullbackObjObj.ofHasPullback _ _ _)

variable {f₁ f₁' : (Arrow C₁)ᵒᵖ} (f₃ : Arrow C₃) (sq : f₁ ⟶ f₁')
  (sq₁₃ : G.PullbackObjObj f₁.unop.hom f₃.hom)
  (sq₁₃' : G.PullbackObjObj f₁'.unop.hom f₃.hom)

@[simp]
noncomputable
def rightBifunctor_map_right :
    sq₁₃.pt ⟶ sq₁₃'.pt :=
  sq₁₃'.isPullback.lift
    (sq₁₃.fst ≫ (G.map sq.unop.left.op).app f₃.left)
    (sq₁₃.snd ≫ (G.map sq.unop.right.op).app f₃.right)
    (by simp only [id_obj, Category.assoc]; grind [sq.unop.w, sq₁₃.isPullback.w])

@[simp]
noncomputable
def rightBifunctor_map_app :
    Arrow.mk sq₁₃.π ⟶ Arrow.mk sq₁₃'.π where
  left := (G.map sq.unop.right.op).app f₃.left
  right := rightBifunctor_map_right G f₃ sq sq₁₃ sq₁₃'
  w := by
    apply sq₁₃'.isPullback.hom_ext
    · simp [← NatTrans.comp_app, ← map_comp, ← op_comp]
    · cat_disch

noncomputable
def iso_of_arrow_iso (iso : f₁.unop ≅ f₁'.unop) :
    Arrow.mk sq₁₃.π ≅ Arrow.mk sq₁₃'.π where
  hom := rightBifunctor_map_app G f₃ iso.inv.op sq₁₃ sq₁₃'
  inv := rightBifunctor_map_app G f₃ iso.hom.op sq₁₃' sq₁₃
  hom_inv_id := by
    apply Arrow.hom_ext
    · simp [← NatTrans.comp_app, ← map_comp, ← op_comp]
    · apply sq₁₃.isPullback.hom_ext
      all_goals simp [← NatTrans.comp_app, ← map_comp, ← op_comp]
  inv_hom_id := by
    apply Arrow.hom_ext
    · simp [← NatTrans.comp_app, ← map_comp, ← op_comp]
    · apply sq₁₃'.isPullback.hom_ext
      all_goals simp [← NatTrans.comp_app, ← map_comp, ← op_comp]

@[simp]
noncomputable
def rightBifunctor_map [HasPullbacks C₂] {f₁ f₁' : (Arrow C₁)ᵒᵖ} (sq : f₁ ⟶ f₁') :
    rightFunctor G f₁ ⟶ rightFunctor G f₁' where
  app f₃ := rightBifunctor_map_app G f₃ sq (PullbackObjObj.ofHasPullback _ _ _)
    (PullbackObjObj.ofHasPullback _ _ _)

@[simp]
noncomputable
def rightBifunctor [HasPullbacks C₂] : (Arrow C₁)ᵒᵖ ⥤ Arrow C₃ ⥤ Arrow C₂ where
  obj := rightFunctor G
  map := rightBifunctor_map G

end Functor

end PullbackPower

end Functor

end CategoryTheory
