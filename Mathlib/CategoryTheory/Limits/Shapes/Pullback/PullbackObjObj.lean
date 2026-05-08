/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Leibniz Constructions

Let `F : C₁ ⥤ C₂ ⥤ C₃`. Given morphisms `f₁ : X₁ ⟶ Y₁` in `C₁`
and `f₂ : X₂ ⟶ Y₂` in `C₂`, we introduce a structure
`F.PushoutObjObj f₁ f₂` which contains the data of a
pushout of `(F.obj Y₁).obj X₂` and `(F.obj X₁).obj Y₂`
along `(F.obj X₁).obj X₂`. If `sq₁₂ : F.PushoutObjObj f₁ f₂`,
we have a canonical "inclusion" `sq₁₂.ι : sq₁₂.pt ⟶ (F.obj Y₁).obj Y₂`.

If `C₃` has pushouts, then we define the Leibniz pushout (often called pushout-product) as the
canonical inclusion `(PushoutObjObj.ofHasPushout F f₁ f₂).ι`. This defines a bifunctor
`F.leibnizPushout : Arrow C₁ ⥤ Arrow C₂ ⥤ Arrow C₃`.

Similarly, if we have a bifunctor `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`, and
morphisms `f₁ : X₁ ⟶ Y₁` in `C₁` and `f₃ : X₃ ⟶ Y₃` in `C₃`,
we introduce a structure `F.PullbackObjObj f₁ f₃` which
contains the data of a pullback of `(G.obj (op X₁)).obj X₃`
and `(G.obj (op Y₁)).obj Y₃` over `(G.obj (op X₁)).obj Y₃`.
If `sq₁₃ : F.PullbackObjObj f₁ f₃`, we have a canonical
projection `sq₁₃.π : (G.obj Y₁).obj X₃ ⟶ sq₁₃.pt`.

If `C₂` has pullbacks, then we define the Leibniz pullback (often called pullback-hom) as the
canonical projection `(PullbackObjObj.ofHasPullback G f₁ f₃).π`. This defines a bifunctor
`G.leibnizPullback : (Arrow C₁)ᵒᵖ ⥤ Arrow C₃ ⥤ Arrow C₂`.

If `C₂` has pullbacks and `C₃` has pushouts, then a parameterized adjunction `adj₂ : F ⊣₂ G` induces
a parameterized adjunction `F.leibnizAdjunction G adj₂ : F.leibnizPushout ⊣₂ G.leibnizPullback`.

## References

* [Emily Riehl, Dominic Verity, *Elements of ∞-Category Theory*, Definition C.2.8][RV22]
* https://ncatlab.org/nlab/show/pushout-product
* https://ncatlab.org/nlab/show/pullback-power

## Tags

pushout-product, pullback-hom, pullback-power, Leibniz
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
@[simps -isSimp]
noncomputable def ofHasPushout
    [HasPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂)] :
    F.PushoutObjObj f₁ f₂ where
  pt := pushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂)
  inl := pushout.inl _ _
  inr := pushout.inr _ _
  isPushout := IsPushout.of_hasPushout _ _

variable {F f₁ f₂} (sq : F.PushoutObjObj f₁ f₂)

/-- The "inclusion" `sq.pt ⟶ (F.obj Y₁).obj Y₂` when
`sq : F.PushoutObjObj f₁ f₂`. -/
noncomputable def ι : sq.pt ⟶ (F.obj Y₁).obj Y₂ :=
  sq.isPushout.desc ((F.obj Y₁).map f₂) ((F.map f₁).app Y₂) (by simp)

@[reassoc (attr := simp)]
lemma inl_ι : sq.inl ≫ sq.ι = (F.obj Y₁).map f₂ := by simp [ι]

@[reassoc (attr := simp)]
lemma inr_ι : sq.inr ≫ sq.ι = (F.map f₁).app Y₂ := by simp [ι]

@[ext]
lemma hom_ext {X₃ : C₃} {f g : sq.pt ⟶ X₃} (hₗ : sq.inl ≫ f = sq.inl ≫ g)
    (hᵣ : sq.inr ≫ f = sq.inr ≫ g) : f = g :=
  sq.isPushout.hom_ext hₗ hᵣ

/-- Given `sq : F.PushoutObjObj f₁ f₂`, flipping the pushout square gives
`sq.flip : F.flip.PushoutObjObj f₂ f₁`. -/
@[simps]
def flip : F.flip.PushoutObjObj f₂ f₁ where
  pt := sq.pt
  inl := sq.inr
  inr := sq.inl
  isPushout := sq.isPushout.flip

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma ι_flip : sq.flip.ι = sq.ι := by
  apply sq.flip.isPushout.hom_ext
  · rw [inl_ι, flip_inl, inr_ι, flip_obj_map]
  · rw [inr_ι, flip_inr, inl_ι, flip_map_app]

set_option backward.isDefEq.respectTransparency false in
lemma ofHasPushout_ι [HasPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂)] :
    (ofHasPushout F f₁ f₂).ι =
      pushout.desc ((F.obj Y₁).map f₂) ((F.map f₁).app Y₂) (by simp) := by
  ext <;> simp [PushoutObjObj.ι, ofHasPushout_inl, ofHasPushout_inr]

noncomputable section Arrow

variable {f₁ f₁' : Arrow C₁} {f₂ : Arrow C₂}
  (sq₁₂ : F.PushoutObjObj f₁.hom f₂.hom)
  (sq₁₂' : F.PushoutObjObj f₁'.hom f₂.hom)

set_option backward.defeqAttrib.useBackward true in
/-- Given a `PushoutObjObj` of `f₁ : Arrow C₁` and `f₂ : Arrow C₂`, a `PushoutObjObj` of `f₁'` and
  `f₂ : Arrow C₂`, and a morphism `f₁ ⟶ f₁'`, this defines a morphism between the induced
  pushout maps. -/
@[simps]
def mapArrowLeft (sq : f₁ ⟶ f₁') :
    Arrow.mk sq₁₂.ι ⟶ Arrow.mk sq₁₂'.ι where
  left := sq₁₂.isPushout.desc
    ((F.map sq.right).app f₂.left ≫ sq₁₂'.inl)
    ((F.map sq.left).app f₂.right ≫ sq₁₂'.inr)
    (by
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal without the `simp only`. It is not yet clear whether this is due to defeq abuse in
      Mathlib or a problem in the new canonicalizer; a minimization would help. The original
      proof was: `by grind [sq.w, sq₁₂'.isPushout.w]` -/
      simp only [Arrow.mk_left]; grind [sq.w, sq₁₂'.isPushout.w])
  right := (F.map sq.right).app f₂.right
  w := by
    apply PushoutObjObj.hom_ext
    all_goals simp [← NatTrans.comp_app, ← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma mapArrowLeft_id :
    mapArrowLeft sq₁₂ sq₁₂ (𝟙 _) = 𝟙 _ := by cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma mapArrowLeft_comp {f₁'' : Arrow C₁} (sq₁₂'' : F.PushoutObjObj f₁''.hom f₂.hom)
    (sq : f₁ ⟶ f₁') (sq' : f₁' ⟶ f₁'') :
    mapArrowLeft sq₁₂ sq₁₂' sq ≫ mapArrowLeft sq₁₂' sq₁₂'' sq' =
      mapArrowLeft sq₁₂ sq₁₂'' (sq ≫ sq') := by cat_disch

/-- Given a `PushoutObjObj` of `f₁ : Arrow C₁` and `f₂ : Arrow C₂`, a `PushoutObjObj` of `f₁'` and
  `f₂ : Arrow C₂`, and an isomorphism `f₁ ≅ f₁'`, this defines an isomorphism of the induced
  pushout maps. -/
@[simps]
def ι_iso_of_iso_left (iso : f₁ ≅ f₁') :
    Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂'.ι where
  hom := mapArrowLeft sq₁₂ sq₁₂' iso.hom
  inv := mapArrowLeft sq₁₂' sq₁₂ iso.inv

variable {f₁ : Arrow C₁} {f₂ f₂' : Arrow C₂}
    (sq₁₂ : F.PushoutObjObj f₁.hom f₂.hom)
    (sq₁₂' : F.PushoutObjObj f₁.hom f₂'.hom)

set_option backward.defeqAttrib.useBackward true in
/-- Given a `PushoutObjObj` of `f₁ : Arrow C₁` and `f₂ : Arrow C₂`, a `PushoutObjObj` of `f₁` and
  `f₂' : Arrow C₂`, and a morphism `f₂ ⟶ f₂'`, this defines a morphism between the induced
  pushout maps. -/
@[simps]
def mapArrowRight (sq : f₂ ⟶ f₂') :
    Arrow.mk sq₁₂.ι ⟶ Arrow.mk sq₁₂'.ι where
  left := sq₁₂.isPushout.desc
    (((F.obj f₁.right).map sq.left) ≫ sq₁₂'.inl)
    (((F.obj f₁.left).map sq.right) ≫ sq₁₂'.inr)
    (by
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal without the `simp only`. It is not yet clear whether this is due to defeq abuse in
      Mathlib or a problem in the new canonicalizer; a minimization would help. The original
      proof was: `by grind [sq.w, sq₁₂'.isPushout.w]` -/
      simp only [Arrow.mk_left]; grind [sq.w, sq₁₂'.isPushout.w])
  right := (F.obj f₁.right).map sq.right
  w := by
    apply PushoutObjObj.hom_ext
    · simp [← map_comp]
    · cat_disch

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma mapArrowRight_id :
    mapArrowRight sq₁₂ sq₁₂ (𝟙 _) = 𝟙 _ := by cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma mapArrowRight_comp {f₂'' : Arrow C₂} (sq₁₂'' : F.PushoutObjObj f₁.hom f₂''.hom)
    (sq : f₂ ⟶ f₂') (sq' : f₂' ⟶ f₂'') :
    mapArrowRight sq₁₂ sq₁₂' sq ≫ mapArrowRight sq₁₂' sq₁₂'' sq' =
      mapArrowRight sq₁₂ sq₁₂'' (sq ≫ sq') := by cat_disch

/-- Given a `PushoutObjObj` of `f₁ : Arrow C₁` and `f₂ : Arrow C₂`, a `PushoutObjObj` of `f₁` and
  `f₂' : Arrow C₂`, and an isomorphism `f₂ ≅ f₂'`, this defines an isomorphism of the induced
  pushout maps. -/
@[simps]
def ι_iso_of_iso_right (iso : f₂ ≅ f₂') :
    Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂'.ι where
  hom := mapArrowRight sq₁₂ sq₁₂' iso.hom
  inv := mapArrowRight sq₁₂' sq₁₂ iso.inv

end Arrow

end PushoutObjObj

end

set_option backward.defeqAttrib.useBackward true in
/-- Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C₃` to a category `C₃` which has pushouts, the Leibniz pushout
  (pushout-product) of `f₁ : X₁ ⟶ Y₁` in `C₁` and `f₂ : X₂ ⟶ Y₂` in `C₂` is the map
  `pushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂) ⟶ (F.obj Y₁).obj Y₂` induced by the diagram
```
  `(F.obj X₁).obj X₂` ----> `(F.obj Y₁).obj X₂`
          |                            |
          |                            |
          v                            v
  `(F.obj X₁).obj Y₂` ----> `(F.obj Y₁).obj Y₂`
```
-/
@[simps]
noncomputable
def leibnizPushout [HasPushouts C₃] : Arrow C₁ ⥤ Arrow C₂ ⥤ Arrow C₃ where
  obj f₁ :=
    { obj f₂ := Arrow.mk (PushoutObjObj.ofHasPushout F f₁.hom f₂.hom).ι
      map sq :=
        PushoutObjObj.mapArrowRight
          (PushoutObjObj.ofHasPushout F ..)
          (PushoutObjObj.ofHasPushout F ..) sq }
  map sq :=
    { app f₂ :=
        PushoutObjObj.mapArrowLeft
          (PushoutObjObj.ofHasPushout F ..)
          (PushoutObjObj.ofHasPushout F ..) sq }

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
@[simps -isSimp]
noncomputable def ofHasPullback
    [HasPullback ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)] :
    G.PullbackObjObj f₁ f₃ where
  pt := pullback ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)
  fst := pullback.fst _ _
  snd := pullback.snd _ _
  isPullback := IsPullback.of_hasPullback _ _

variable {G f₁ f₃} (sq : G.PullbackObjObj f₁ f₃)

/-- The projection `(G.obj (op Y₁)).obj X₃ ⟶ sq.pt` when
`sq : G.PullbackObjObj f₁ f₃`. -/
noncomputable def π : (G.obj (op Y₁)).obj X₃ ⟶ sq.pt :=
  sq.isPullback.lift ((G.map f₁.op).app X₃) ((G.obj (op Y₁)).map f₃) (by simp)

@[reassoc (attr := simp)]
lemma π_fst : sq.π ≫ sq.fst = (G.map f₁.op).app X₃ := by simp [π]

@[reassoc (attr := simp)]
lemma π_snd : sq.π ≫ sq.snd = (G.obj (op Y₁)).map f₃ := by simp [π]

@[ext]
lemma hom_ext {X₂ : C₂} {f g : X₂ ⟶ sq.pt} (h₁ : f ≫ sq.fst = g ≫ sq.fst)
    (h₂ : f ≫ sq.snd = g ≫ sq.snd) : f = g :=
  sq.isPullback.hom_ext h₁ h₂

set_option backward.isDefEq.respectTransparency false in
lemma ofHasPullback_π
    [HasPullback ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)] :
    (ofHasPullback G f₁ f₃).π =
      pullback.lift ((G.map f₁.op).app X₃) ((G.obj (op Y₁)).map f₃) (by simp) := by
  ext <;> simp [PullbackObjObj.π, ofHasPullback_fst, ofHasPullback_snd]

noncomputable section Arrow

variable {f₁ f₁' : Arrow C₁} {f₃ : Arrow C₃}
  (sq₁₃ : G.PullbackObjObj f₁.hom f₃.hom)
  (sq₁₃' : G.PullbackObjObj f₁'.hom f₃.hom)

set_option backward.defeqAttrib.useBackward true in
/-- Given a `PullbackObjObj` of `f₁ : Arrow C₁` and `f₃ : Arrow C₃`, a `PullbackObjObj` of `f₁'` and
  `f₃ : Arrow C₃`, and a morphism `f₁' ⟶ f₁`, this defines a morphism between the induced
  pullback maps. -/
@[simps]
def mapArrowLeft (sq : f₁' ⟶ f₁) :
    Arrow.mk sq₁₃.π ⟶ Arrow.mk sq₁₃'.π where
  left := (G.map sq.right.op).app f₃.left
  right := sq₁₃'.isPullback.lift
    (sq₁₃.fst ≫ (G.map sq.left.op).app f₃.left)
    (sq₁₃.snd ≫ (G.map sq.right.op).app f₃.right)
    (by
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal without the `simp`. It is not yet clear whether this is due to defeq abuse in
      Mathlib or a problem in the new canonicalizer; a minimization would help. The original
      proof was: `by simp only [id_obj, Category.assoc]; grind [sq.w, sq₁₃.isPullback.w]` -/
      simp [Arrow.mk_right]; grind [sq.w, sq₁₃.isPullback.w])
  w := by
    apply PullbackObjObj.hom_ext
    · simp [← NatTrans.comp_app, ← map_comp, ← op_comp]
    · cat_disch

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma mapArrowLeft_id :
    mapArrowLeft sq₁₃ sq₁₃ (𝟙 _) = 𝟙 _ := by cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma mapArrowLeft_comp {f₁'' : Arrow C₁} (sq₁₃'' : G.PullbackObjObj f₁''.hom f₃.hom)
    (sq' : f₁'' ⟶ f₁') (sq : f₁' ⟶ f₁) :
    mapArrowLeft sq₁₃ sq₁₃' sq ≫ mapArrowLeft sq₁₃' sq₁₃'' sq' =
      mapArrowLeft sq₁₃ sq₁₃'' (sq' ≫ sq) := by cat_disch

/-- Given a `PullbackObjObj` of `f₁ : Arrow C₁` and `f₃ : Arrow C₃`, a `PullbackObjObj` of `f₁'` and
  `f₃ : Arrow C₃`, and an isomorphism `f₁ ≅ f₁'`, this defines an isomorphism of the induced
  pullback maps. -/
@[simps]
def π_iso_of_iso_left (iso : f₁ ≅ f₁') :
    Arrow.mk sq₁₃.π ≅ Arrow.mk sq₁₃'.π where
  hom := mapArrowLeft sq₁₃ sq₁₃' iso.inv
  inv := mapArrowLeft sq₁₃' sq₁₃ iso.hom

variable {f₁ : Arrow C₁} {f₃ f₃' : Arrow C₃}
  (sq₁₃ : G.PullbackObjObj f₁.hom f₃.hom)
  (sq₁₃' : G.PullbackObjObj f₁.hom f₃'.hom)

set_option backward.defeqAttrib.useBackward true in
/-- Given a `PullbackObjObj` of `f₁ : Arrow C₁` and `f₃ : Arrow C₃`, a `PullbackObjObj` of `f₁` and
  `f₃' : Arrow C₃`, and a morphism `f₃ ⟶ f₃'`, this defines a morphism between the induced
  pullback maps. -/
@[simps]
def mapArrowRight (sq : f₃ ⟶ f₃') :
    Arrow.mk sq₁₃.π ⟶ Arrow.mk sq₁₃'.π where
  left := (G.obj (.op f₁.right)).map sq.left
  right := sq₁₃'.isPullback.lift
    (sq₁₃.fst ≫ (G.obj (.op f₁.left)).map sq.left)
    (sq₁₃.snd ≫ (G.obj (.op f₁.right)).map sq.right)
    (by
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal without the `simp`. It is not yet clear whether this is due to defeq abuse in
      Mathlib or a problem in the new canonicalizer; a minimization would help. The original
      proof was: `by grind [sq.w, sq₁₃.isPullback.w]` -/
      simp [Arrow.mk_right]; grind [sq.w, sq₁₃.isPullback.w])
  w := by
    apply PullbackObjObj.hom_ext
    all_goals simp [← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma mapArrowRight_id :
    mapArrowRight sq₁₃ sq₁₃ (𝟙 _) = 𝟙 _ := by cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma mapArrowRight_comp {f₃'' : Arrow C₃} (sq₁₃'' : G.PullbackObjObj f₁.hom f₃''.hom)
    (sq : f₃ ⟶ f₃') (sq' : f₃' ⟶ f₃'') :
    mapArrowRight sq₁₃ sq₁₃' sq ≫ mapArrowRight sq₁₃' sq₁₃'' sq' =
      mapArrowRight sq₁₃ sq₁₃'' (sq ≫ sq') := by cat_disch

/-- Given a `PullbackObjObj` of `f₁ : Arrow C₁` and `f₃ : Arrow C₃`, a `PullbackObjObj` of `f₁` and
  `f₃' : Arrow C₃`, and an isomorphism `f₃ ≅ f₃'`, this defines an isomorphism of the induced
  pullback maps. -/
@[simps]
def π_iso_of_iso_right (iso : f₃ ≅ f₃') :
    Arrow.mk sq₁₃.π ≅ Arrow.mk sq₁₃'.π where
  hom := mapArrowRight sq₁₃ sq₁₃' iso.hom
  inv := mapArrowRight sq₁₃' sq₁₃ iso.inv

end Arrow

end PullbackObjObj

end

set_option backward.defeqAttrib.useBackward true in
/-- Given a bifunctor `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂` to a category `C₂` which has pullbacks, the Leibniz
  pullback (pullback-power) of `f₁ : X₁ ⟶ Y₁` in `C₁` and `f₃ : X₃ ⟶ Y₃` in `C₃` is the map
  `(G.obj (op Y₁)).obj X₃ ⟶ pullback ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)` induced by
  the diagram
```
  `(G.obj (op Y₁)).obj X₃` ----> `(G.obj (op X₁)).obj X₃`
              |                              |
              |                              |
              v                              v
  `(G.obj (op Y₁)).obj Y₃` ----> `(G.obj (op X₁)).obj Y₃`
```
-/
@[simps]
noncomputable
def leibnizPullback [HasPullbacks C₂] : (Arrow C₁)ᵒᵖ ⥤ Arrow C₃ ⥤ Arrow C₂ where
  obj f₁ :=
    { obj f₃ := Arrow.mk (PullbackObjObj.ofHasPullback G f₁.unop.hom f₃.hom).π
      map sq :=
        PullbackObjObj.mapArrowRight
          (PullbackObjObj.ofHasPullback G ..)
          (PullbackObjObj.ofHasPullback G ..) sq }
  map sq :=
    { app f₃ :=
        PullbackObjObj.mapArrowLeft
          (PullbackObjObj.ofHasPullback G ..)
          (PullbackObjObj.ofHasPullback G ..) sq.unop }

noncomputable section

open PushoutObjObj PullbackObjObj ParametrizedAdjunction

attribute [local simp] ofHasPushout_inl ofHasPushout_inr ι
  ofHasPullback_fst ofHasPullback_snd π

namespace LeibnizAdjunction

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a parametrized adjunction `F ⊣₂ G` and an arrow `X₁ : Arrow C₁`, this is the induced
  adjunction `F.leibnizPushout.obj X₁ ⊣ G.leibnizPullback.obj (op X₁)`. -/
@[simps!]
def adj (adj₂ : F ⊣₂ G) (X₁ : Arrow C₁) [HasPullbacks C₂] [HasPushouts C₃] :
    F.leibnizPushout.obj X₁ ⊣ G.leibnizPullback.obj (op X₁) where
  unit.app X₂ := Arrow.homMk (adj₂.homEquiv (pushout.inl ..))
    (pullback.lift (adj₂.homEquiv (pushout.inr ..)) (adj₂.homEquiv (𝟙 _))
      (by simp [← homEquiv_naturality_one, ← homEquiv_naturality_three])) (by
      apply pullback.hom_ext
      · simp [← homEquiv_naturality_one, ← homEquiv_naturality_two, pushout.condition]
      · simp [← homEquiv_naturality_two, ← homEquiv_naturality_three])
  unit.naturality _ _ _ := by
    ext
    · simp [← homEquiv_naturality_two, ← homEquiv_naturality_three]
    · apply pullback.hom_ext <;> simp [← homEquiv_naturality_two, ← homEquiv_naturality_three]
  counit.app X₃ := Arrow.homMk
    (pushout.desc (adj₂.homEquiv.symm (𝟙 _)) (adj₂.homEquiv.symm (pullback.fst ..))
        (by simp [← homEquiv_symm_naturality_one, ← homEquiv_symm_naturality_two]))
    (adj₂.homEquiv.symm (pullback.snd ..)) (by
    apply pushout.hom_ext
    · simp [← homEquiv_symm_naturality_two, ← homEquiv_symm_naturality_three]
    · simp [← homEquiv_symm_naturality_one, ← homEquiv_symm_naturality_three,
      pullback.condition])
  counit.naturality _ _ _ := by
    ext
    · apply pushout.hom_ext <;> simp [← homEquiv_symm_naturality_two,
        ← homEquiv_symm_naturality_three]
    · simp [← homEquiv_symm_naturality_two, ← homEquiv_symm_naturality_three]
  left_triangle_components _ := by
    ext
    · apply pushout.hom_ext <;> simp [← homEquiv_symm_naturality_two, ofHasPushout_pt]
    · simp [← homEquiv_symm_naturality_two]
  right_triangle_components _ := by
    ext
    · simp [← homEquiv_naturality_three]
    · apply pullback.hom_ext <;> simp [← homEquiv_naturality_three]

end LeibnizAdjunction

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Leibniz (parametrized) adjunction `F.leibnizPushout ⊣₂ G.leibnizPullback` induced by a
  parameterized adjunction `F ⊣₂ G`. -/
@[simps]
def leibnizAdjunction (adj₂ : F ⊣₂ G) [HasPullbacks C₂] [HasPushouts C₃] :
    F.leibnizPushout ⊣₂ G.leibnizPullback where
  adj X₁ := LeibnizAdjunction.adj F G adj₂ X₁
  unit_whiskerRight_map _ := by
    ext
    · simp [← homEquiv_naturality_one, ← homEquiv_naturality_three]
    · apply pullback.hom_ext <;> simp [← homEquiv_naturality_one, ← homEquiv_naturality_three]

end

end Functor

end CategoryTheory
