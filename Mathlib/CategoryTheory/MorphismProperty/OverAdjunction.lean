/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits

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

instance (f : X ⟶ Y) [P.HasPullbacksAlong f] (A : P.Over Q Y) : HasPullback A.hom f :=
  HasPullbacksAlong.hasPullback A.hom A.prop

instance {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g]
    (A : P.Over Q Z) : HasPullback (pullback.snd A.hom g) f :=
  HasPullbacksAlong.hasPullback (pullback.snd A.hom g)
  (IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback A.hom g) A.prop)

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
    (baseChange_map' _ _ g.prop_hom_left)

variable {P} {Q}

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
    (by simp) (Q.pullback_map (Q.id_mem _) hQf (by simp) (by cat_disch))

end Pullback

section Adjunction

variable [P.IsStableUnderComposition] [Q.IsStableUnderBaseChange]

/-- `P.Over.map` is left adjoint to `P.Over.pullback` if pullbacks of morphisms satisfying `P`
exist along `f` and are also in `P`, and `f` is in both `P` and `Q`. -/
@[simps! unit_app counit_app]
noncomputable def Over.mapPullbackAdj (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [Q.HasOfPostcompProperty Q] (hPf : P f) (hQf : Q f) :
    Over.map Q hPf ⊣ Over.pullback P Q f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A B ↦
        { toFun := fun g ↦
            Over.homMk (pullback.lift g.left A.hom <| by simp) (by simp) <| by
              apply Q.of_postcomp (W' := Q)
              · exact Q.pullback_fst B.hom f hQf
              · simpa using g.prop_hom_left
          invFun := fun h ↦ Over.homMk (h.left ≫ pullback.fst B.hom f)
            (by
              simp only [map_obj_left, Functor.const_obj_obj, pullback_obj_left, Functor.id_obj,
                Category.assoc, pullback.condition, map_obj_hom, ← pullback_obj_hom, Over.w_assoc])
            (Q.comp_mem _ _ h.prop_hom_left (Q.pullback_fst _ _ hQf))
          left_inv := by cat_disch
          right_inv := fun h ↦ by
            ext
            dsimp
            ext
            · simp
            · simpa using h.w.symm } }

instance (f : X ⟶ Y) [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (hPf : P f) :
    (MorphismProperty.Over.map ⊤ hPf).IsLeftAdjoint :=
  (Over.mapPullbackAdj P ⊤ f hPf trivial).isLeftAdjoint

end Adjunction

end CategoryTheory.MorphismProperty
