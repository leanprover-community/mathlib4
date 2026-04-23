/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Adjunction of pushforward and pullback in `P.Over Q X`

Under suitable assumptions on `P`, `Q` and `f`,
a morphism `f : X ⟶ Y` defines two functors:

- `Over.map`: post-composition with `f`
- `Over.pullback`: base-change along `f`

such that `Over.map` is the left adjoint to `Over.pullback`.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {T : Type*} [Category* T] (P Q : MorphismProperty T) [Q.IsMultiplicative]
variable {X Y Z : T}

section Over

section Map

variable {P} [P.IsStableUnderComposition]

/-- If `P` is stable under composition and `f : X ⟶ Y` satisfies `P`,
this is the functor `P.Over Q X ⥤ P.Over Q Y` given by composing with `f`. -/
@[simps! obj_left obj_hom map_left]
def Over.map {f : X ⟶ Y} (hPf : P f) : P.Over Q X ⥤ P.Over Q Y :=
  Comma.mapRight _ (Discrete.natTrans fun _ ↦ f) <| fun X ↦ P.comp_mem _ _ X.prop hPf

lemma Over.map_comp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) :
    map Q (P.comp_mem f g hf hg) = map Q hf ⋙ map Q hg := by
  fapply Functor.ext
  · simp [map, Comma.mapRight, CategoryTheory.Comma.mapRight, Comma.lift]
  · intro U V k
    ext
    simp

/-- Promote an equality to an isomorphism of `Over.map` functors. -/
@[simps!]
def Over.mapCongr [Q.RespectsIso] {X Y : T} {f g : X ⟶ Y} (hfg : f = g) (hf : P f) :
    Over.map Q hf ≅ Over.map (f := g) Q (by cat_disch) :=
  NatIso.ofComponents (fun Y ↦ Over.isoMk (Iso.refl _))

/-- `Over.map` preserves identities. -/
@[simps!]
def Over.mapId [P.IsMultiplicative] [Q.RespectsIso] (X : T) (f : X ⟶ X := 𝟙 X)
    (hf : f = 𝟙 X := by cat_disch) :
    Over.map (f := f) (P := P) Q (by subst hf; exact P.id_mem X) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun Y ↦ Over.isoMk (Iso.refl _))

/-- `Over.map` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
def Over.mapComp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) [Q.RespectsIso]
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    map (f := fg) Q (by subst hfg; exact P.comp_mem f g hf hg) ≅ map Q hf ⋙ map Q hg :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (Iso.refl _))

end Map

section Pullback

set_option backward.isDefEq.respectTransparency false in
instance (f : X ⟶ Y) [P.HasPullbacksAlong f] (A : P.Over Q Y) : HasPullback A.hom f :=
  HasPullbacksAlong.hasPullback A.hom A.prop

set_option backward.isDefEq.respectTransparency false in
instance {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g]
    (A : P.Over Q Z) : HasPullback (pullback.snd A.hom g) f :=
  HasPullbacksAlong.hasPullback (pullback.snd A.hom g)
  (IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback A.hom g) A.prop)

set_option backward.isDefEq.respectTransparency false in
/-- If `P` and `Q` are stable under base change and pullbacks along `f` exist for morphisms in `P`,
this is the functor `P.Over Q Y ⥤ P.Over Q X` given by base change along `f`. -/
@[simps! obj_left obj_hom map_left]
noncomputable def Over.pullback (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [Q.IsStableUnderBaseChange] :
    P.Over Q Y ⥤ P.Over Q X where
  obj A := Over.mk Q (Limits.pullback.snd A.hom f)
    (pullback_snd A.hom f A.prop)
  map {A B} g := Over.homMk (pullback.lift (pullback.fst A.hom f ≫ g.left)
    (pullback.snd A.hom f) (by simp [pullback.condition])) (by simp)
    (pullbackLift_fst_snd _ _ g.prop_hom_left)

variable {P} {Q}

set_option backward.isDefEq.respectTransparency false in
/-- `Over.pullback` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
noncomputable def Over.pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] [Q.RespectsIso] [Q.IsStableUnderBaseChange]
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong fg := by subst hfg; infer_instance
    Over.pullback P Q fg ≅ Over.pullback P Q g ⋙ Over.pullback P Q f :=
  haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
  NatIso.ofComponents fun X ↦
    haveI : HasPullback X.hom fg := HasPullbacksAlong.hasPullback _ X.prop
    Over.isoMk (pullback.congrHom rfl hfg ≪≫ (pullbackLeftPullbackSndIso X.hom g f).symm) (by simp)

lemma Over.pullbackComp_left_fst_fst (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g] [P.HasPullbacksAlong f] [P.HasPullbacksAlong g]
    [Q.RespectsIso] [Q.IsStableUnderBaseChange] (A : P.Over Q Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫ pullback.fst (pullback.snd A.hom g) f ≫
    pullback.fst A.hom g = pullback.fst A.hom (f ≫ g) := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- If `f = g`, then base change along `f` is naturally isomorphic to base change along `g`. -/
noncomputable def Over.pullbackCongr {f : X ⟶ Y} [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [Q.IsStableUnderBaseChange] {g : X ⟶ Y} (h : f = g) :
    haveI : P.HasPullbacksAlong g := by subst h; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong g := by subst h; infer_instance
    Over.pullback P Q f ≅ Over.pullback P Q g :=
  haveI : P.HasPullbacksAlong g := by subst h; infer_instance
  NatIso.ofComponents fun X ↦
    haveI : HasPullback X.hom g := HasPullbacksAlong.hasPullback _ X.prop
    Over.isoMk (pullback.congrHom rfl h)

@[reassoc (attr := simp)]
lemma Over.pullbackCongr_hom_app_left_fst {f : X ⟶ Y} [P.HasPullbacksAlong f] {g : X ⟶ Y}
    [P.IsStableUnderBaseChangeAlong f] [Q.IsStableUnderBaseChange] (h : f = g) (A : P.Over Q Y) :
    haveI : P.HasPullbacksAlong g := by subst h; infer_instance
    ((Over.pullbackCongr h).hom.app A).left ≫ pullback.fst A.hom g = pullback.fst A.hom f := by
  subst h
  simp [pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
/-- The natural map between pullback functors induced by `pullback.map`. -/
@[simps]
noncomputable def Over.pullbackMapHomPullback [P.IsStableUnderComposition]
    {X Y Z : T} (f : X ⟶ Y) (hPf : P f) (hQf : Q f) (g : Y ⟶ Z)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [Q.IsStableUnderBaseChange] [HasPullbacks T]
    (fg : X ⟶ Z := f ≫ g) (hfg : f ≫ g = fg := by cat_disch) :
    haveI : P.IsStableUnderBaseChangeAlong fg := by subst hfg; infer_instance
    Over.pullback P Q fg ⋙ Over.map (f := f) _ hPf ⟶
      Over.pullback P Q g where
  app A :=
    Over.homMk (pullback.map _ _ _ _ (𝟙 A.left) f (𝟙 Z) (by simp) (by cat_disch))
    (by simp) (Q.pullbackMap (Q.id_mem _) hQf (by simp) (by cat_disch))

end Pullback

section Adjunction

variable [P.IsStableUnderComposition] [Q.IsStableUnderBaseChange]

set_option backward.isDefEq.respectTransparency false in
/-- `P.Over.map` is left adjoint to `P.Over.pullback` if pullbacks of morphisms satisfying `P`
exist along `f` and are also in `P`, and `f` is in both `P` and `Q`. -/
@[simps! unit_app counit_app]
noncomputable def Over.mapPullbackAdj (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [Q.HasOfPostcompProperty Q] (hPf : P f) (hQf : Q f) :
    Over.map Q hPf ⊣ Over.pullback P Q f where
  unit.app A := Over.homMk (pullback.lift (𝟙 _) A.hom (by simp)) (by simp) <| by
    apply Q.of_postcomp (W' := Q)
    · exact Q.pullback_fst _ _ hQf
    · simpa using Q.of_isIso _
  unit.naturality A B g := by ext; apply pullback.hom_ext <;> simp
  counit.app A := Over.homMk (pullback.fst _ _) pullback.condition (Q.pullback_fst _ _ hQf)

instance (f : X ⟶ Y) [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (hPf : P f) :
    (MorphismProperty.Over.map ⊤ hPf).IsLeftAdjoint :=
  (Over.mapPullbackAdj P ⊤ f hPf trivial).isLeftAdjoint

lemma isRightAdjoint_pullback (f : X ⟶ Y) [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    (hPf : P f) :
    (MorphismProperty.Over.pullback P ⊤ f).IsRightAdjoint :=
  (Over.mapPullbackAdj P ⊤ f hPf trivial).isRightAdjoint

end Adjunction

end Over

section Under

section Map

variable {P} [P.IsStableUnderComposition]

/-- If `P` is stable under composition and `f : X ⟶ Y` satisfies `P`,
this is the functor `P.Under Q Y ⥤ P.Under Q X` given by composing with `f`. -/
@[simps! obj_right obj_hom map_right]
def Under.map {f : X ⟶ Y} (hPf : P f) : P.Under Q Y ⥤ P.Under Q X :=
  Comma.mapLeft _ (Discrete.natTrans fun _ ↦ f) <| fun X ↦ P.comp_mem _ _ hPf X.prop

lemma Under.map_comp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) :
    map Q (P.comp_mem f g hf hg) = map Q hg ⋙ map Q hf := by
  fapply Functor.ext
  · simp [map, Comma.mapLeft, CategoryTheory.Comma.mapLeft, Comma.lift]
  · intro U V k
    ext
    simp

/-- Promote an equality to an isomorphism of `Under.map` functors. -/
@[simps!]
def Under.mapCongr [Q.RespectsIso] {X Y : T} {f g : X ⟶ Y} (hfg : f = g) (hf : P f) :
    Under.map Q hf ≅ Under.map (f := g) Q (by cat_disch) :=
  NatIso.ofComponents (fun Y ↦ Under.isoMk (Iso.refl _))

/-- `Under.map` preserves identities. -/
@[simps!]
def Under.mapId [P.IsMultiplicative] [Q.RespectsIso] (X : T) (f : X ⟶ X := 𝟙 X)
    (hf : f = 𝟙 X := by cat_disch) :
    Under.map (f := f) (P := P) Q (by subst hf; exact P.id_mem X) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun Y ↦ Under.isoMk (Iso.refl _))

/-- `Under.map` commutes with composition. -/
@[simps! hom_app_left]
def Under.mapComp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) [Q.RespectsIso]
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    map (f := fg) Q (by subst hfg; exact P.comp_mem f g hf hg) ≅ map Q hg ⋙ map Q hf :=
  NatIso.ofComponents (fun X ↦ Under.isoMk (Iso.refl _))

end Map

section Pushout

set_option backward.isDefEq.respectTransparency false in
instance (f : X ⟶ Y) [P.HasPushoutsAlong f] (A : P.Under Q X) : HasPushout A.hom f :=
  HasPushoutsAlong.hasPushout A.hom A.prop

set_option backward.isDefEq.respectTransparency false in
instance {X Y Z} (f : Y ⟶ X) (g : Z ⟶ Y)
    [P.HasPushoutsAlong f] [P.HasPushoutsAlong g] [P.IsStableUnderCobaseChangeAlong g]
    (A : P.Under Q Z) : HasPushout (pushout.inr A.hom g) f :=
  HasPushoutsAlong.hasPushout (pushout.inr A.hom g)
  (IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout A.hom g).flip A.prop)

set_option backward.isDefEq.respectTransparency false in
/-- If `P` and `Q` are stable under cobase change and pushouts along `f` exist for morphisms in `P`,
this is the functor `P.Under Q X ⥤ P.Under Q Y` given by cobase change along `f`. -/
@[simps! obj_right obj_hom map_right]
noncomputable def Under.pushout (f : X ⟶ Y) [P.HasPushoutsAlong f]
    [P.IsStableUnderCobaseChangeAlong f] [Q.IsStableUnderCobaseChange] :
    P.Under Q X ⥤ P.Under Q Y where
  obj A := Under.mk Q (Limits.pushout.inr A.hom f)
    (pushout_inr A.hom f A.prop)
  map {A B} g := Under.homMk (pushout.desc (g.right ≫ pushout.inl _ _)
    (pushout.inr _ _) (by simp [pushout.condition])) (by simp)
    (pushoutDesc_inl_inr _ (by simp) g.prop_hom_right)
  map_comp _ _ := by ext; apply pushout.hom_ext <;> simp

variable {P} {Q}

set_option backward.isDefEq.respectTransparency false in
/-- `Under.pushout` commutes with composition. -/
@[simps! hom_app_right inv_app_right]
noncomputable def Under.pushoutComp (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.IsStableUnderCobaseChangeAlong f] [P.IsStableUnderCobaseChangeAlong g]
    [P.HasPushoutsAlong f] [P.HasPushoutsAlong g] [Q.RespectsIso] [Q.IsStableUnderCobaseChange]
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    haveI : P.HasPushoutsAlong fg := by subst hfg; infer_instance
    haveI : P.IsStableUnderCobaseChangeAlong fg := by subst hfg; infer_instance
    Under.pushout P Q fg ≅ Under.pushout P Q f ⋙ Under.pushout P Q g :=
  haveI : P.HasPushoutsAlong fg := by subst hfg; infer_instance
  NatIso.ofComponents fun X ↦
    haveI : HasPushout X.hom fg := HasPushoutsAlong.hasPushout _ X.prop
    Under.isoMk (pushout.congrHom rfl hfg ≪≫ (pushoutLeftPushoutInrIso X.hom f g).symm) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- If `f = g`, then cobase change along `f` is naturally isomorphic to cobase change along `g`. -/
noncomputable def Under.pushoutCongr {f : X ⟶ Y} [P.HasPushoutsAlong f]
    [P.IsStableUnderCobaseChangeAlong f] [Q.IsStableUnderCobaseChange] {g : X ⟶ Y} (h : f = g) :
    haveI : P.HasPushoutsAlong g := by subst h; infer_instance
    haveI : P.IsStableUnderCobaseChangeAlong g := by subst h; infer_instance
    Under.pushout P Q f ≅ Under.pushout P Q g :=
  haveI : P.HasPushoutsAlong g := by subst h; infer_instance
  NatIso.ofComponents fun X ↦
    haveI : HasPushout X.hom g := HasPushoutsAlong.hasPushout _ X.prop
    Under.isoMk (pushout.congrHom rfl h)

@[reassoc (attr := simp)]
lemma Under.pushoutCongr_hom_app_left_fst {f : X ⟶ Y} [P.HasPushoutsAlong f] {g : X ⟶ Y}
    [P.IsStableUnderCobaseChangeAlong f] [Q.IsStableUnderCobaseChange] (h : f = g)
    (A : P.Under Q X) :
    haveI : P.HasPushoutsAlong g := by subst h; infer_instance
    pushout.inl _ _ ≫ ((Under.pushoutCongr h).hom.app A).right = pushout.inl _ _ := by
  subst h
  simp [pushoutCongr]

end Pushout

section Adjunction

variable [P.IsStableUnderComposition] [Q.IsStableUnderCobaseChange]

attribute [local instance] hasPushouts_symmetry_of_hasPushoutsAlong in
set_option backward.isDefEq.respectTransparency false in
/-- `P.Under.pushout` is left adjoint to `P.Under.map` if pushouts of morphisms satisfying `P`
exist along `f` and are also in `P`, and `f` is in both `P` and `Q`. -/
@[simps! unit_app counit_app]
noncomputable def Under.mapPushoutAdj (f : X ⟶ Y) [P.HasPushoutsAlong f]
    [P.IsStableUnderCobaseChangeAlong f] [Q.HasOfPrecompProperty Q] (hPf : P f) (hQf : Q f) :
    Under.pushout P Q f ⊣ Under.map Q hPf where
  unit.app A := Under.homMk (pushout.inl _ _) pushout.condition (Q.pushout_inl _ _ hQf)
  counit.app A := Under.homMk (pushout.desc (𝟙 _) A.hom (by simp)) (by simp) <| by
    apply Q.of_precomp (W' := Q)
    · exact Q.pushout_inl _ _ hQf
    · simpa using Q.of_isIso _
  counit.naturality A B g := by ext; apply pushout.hom_ext <;> simp

instance (f : X ⟶ Y) [P.HasPushoutsAlong f] [P.IsStableUnderCobaseChangeAlong f] (hPf : P f) :
    (MorphismProperty.Under.map ⊤ hPf).IsRightAdjoint :=
  (Under.mapPushoutAdj P ⊤ f hPf trivial).isRightAdjoint

lemma isLeftAdjoint_pushout (f : X ⟶ Y) [P.HasPushoutsAlong f] [P.IsStableUnderCobaseChangeAlong f]
    (hPf : P f) :
    (MorphismProperty.Under.pushout P ⊤ f).IsLeftAdjoint :=
  (Under.mapPushoutAdj P ⊤ f hPf trivial).isLeftAdjoint

end Adjunction

end Under

end CategoryTheory.MorphismProperty
