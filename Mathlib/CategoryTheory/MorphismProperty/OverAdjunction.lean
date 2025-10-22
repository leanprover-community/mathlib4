/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Adjunction of pushforward and pullback in `P.Over Q X`

Under suitable assumptions on `P`, `Q` and `f`,
a morphism `f : X ⟶ Y` defines two functors:

- `Over.map`: post-composition with `f`
- `Over.pullback`: base-change along `f`

such that `Over.map` is the left adjoint to `Over.pullback`.
-/

namespace CategoryTheory.MorphismProperty

open Limits

variable {T : Type*} [Category T] (P Q : MorphismProperty T) [Q.IsMultiplicative]
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

/-- `Over.map` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
def Over.mapComp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) [Q.RespectsIso] :
    map Q (P.comp_mem f g hf hg) ≅ map Q hf ⋙ map Q hg :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (Iso.refl _))

end Map

section Pullback

variable [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]

/-- If `P` and `Q` are stable under base change and pullbacks exist in `T`,
this is the functor `P.Over Q Y ⥤ P.Over Q X` given by base change along `f`. -/
@[simps! obj_left obj_hom map_left]
noncomputable def Over.pullback (f : X ⟶ Y) [HasPullbacksAlong f] :
    P.Over Q Y ⥤ P.Over Q X where
  obj A :=
    { __ := (CategoryTheory.Over.pullback f).obj A.toComma
      prop := P.pullback_snd _ _ A.prop }
  map {A B} g :=
    { __ := (CategoryTheory.Over.pullback f).map g.toCommaMorphism
      prop_hom_left := Q.baseChange_map f g.toCommaMorphism g.prop_hom_left
      prop_hom_right := trivial }

variable {P} {Q}

/-- `Over.pullback` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
noncomputable def Over.pullbackComp (f : X ⟶ Y) [HasPullbacksAlong f] (g : Y ⟶ Z)
    [HasPullbacksAlong g] [Q.RespectsIso] : Over.pullback P Q (f ≫ g) ≅
    Over.pullback P Q g ⋙ Over.pullback P Q f :=
  NatIso.ofComponents
    (fun X ↦ Over.isoMk ((pullbackLeftPullbackSndIso X.hom g f).symm) (by simp))

lemma Over.pullbackComp_left_fst_fst (f : X ⟶ Y) [HasPullbacksAlong f] (g : Y ⟶ Z)
    [HasPullbacksAlong g] [Q.RespectsIso] (A : P.Over Q Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫ pullback.fst (pullback.snd A.hom g) f ≫
    pullback.fst A.hom g = pullback.fst A.hom (f ≫ g) := by
  simp

/-- If `f = g`, then base change along `f` is naturally isomorphic to base change along `g`. -/
noncomputable def Over.pullbackCongr {f : X ⟶ Y} [HasPullbacksAlong f] {g : X ⟶ Y} (h : f = g) :
    have : HasPullbacksAlong g := by subst h; infer_instance
    Over.pullback P Q f ≅ Over.pullback P Q g :=
  NatIso.ofComponents (fun X ↦ eqToIso (by simp [h]))

@[reassoc (attr := simp)]
lemma Over.pullbackCongr_hom_app_left_fst {f : X ⟶ Y} [HasPullbacksAlong f] {g : X ⟶ Y}
    (h : f = g) (A : P.Over Q Y) :
    have : HasPullbacksAlong g := by subst h; infer_instance
    ((Over.pullbackCongr h).hom.app A).left ≫ pullback.fst A.hom g = pullback.fst A.hom f := by
  subst h
  simp [pullbackCongr]

end Pullback

section Adjunction

variable [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
  [Q.IsStableUnderBaseChange]

/-- `P.Over.map` is left adjoint to `P.Over.pullback` if `f` satisfies `P`. -/
noncomputable def Over.mapPullbackAdj (f : X ⟶ Y) [HasPullbacksAlong f]
    [Q.HasOfPostcompProperty Q] (hPf : P f) (hQf : Q f) :
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

end Adjunction

end CategoryTheory.MorphismProperty
