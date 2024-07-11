/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/

import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Representable morphisms of presheaves

In this file we define and develop basic results on the representability of morphisms of presheaves.

## Main definitions

* `Presheaf.representable` is a `MorphismProperty` expressing the fact that a morphism of presheaves
  is representable.
* `MorphismProperty.presheaf`: given a `P : MorphismProperty C`, we say that a morphism of
  presheaves `f : F ⟶ G` satisfies `P.presheaf` if it is representable, and the property `P`
  holds for the preimage under yoneda of pullbacks of `f` by morphisms `g : yoneda.obj X ⟶ G`.

## API


## Main results
* `representable_isStableUnderComposition`: Being representable is stable under composition.
* `representable_stableUnderBaseChange`: Being representable is stable under base change.
* `representable_ofIso`: Isomorphisms are representable

* `presheaf_yoneda_map`: If `f : X ⟶ Y` satisfies `P`, and `P` is stable under compostions,
  then `yoneda.map f` satisfies `P.presheaf`.

For the following results, we assume that `P : MorphismProperty C` is stable under base change:
* `presheaf_stableUnderBaseChange`: `P.presheaf` is stable under base change
* `presheaf_respectsIso`: `P.presheaf` respects isomorphisms
* `presheaf_isStableUnderComp`: If `P` is stable under composition, then so is `P.presheaf`

## TODO
Can improve definitions & basic API
converse of `presheaf_yoneda_map`

-/


namespace CategoryTheory

open Category Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- A morphism of presheaves `f : F ⟶ G` is representable if for any `X : C`, and any morphism
`g : yoneda.obj X ⟶ G`, there exists a pullback square
```
yoneda.obj Y --yoneda.map snd--> yoneda.obj X
    |                                |
   fst                               g
    |                                |
    v                                v
    F ------------ f --------------> G
``` -/
def Presheaf.representable : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  fun F G f ↦ ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), ∃ (Y : C) (snd : Y ⟶ X)
    (fst : yoneda.obj Y ⟶ F), IsPullback fst (yoneda.map snd) f g

namespace Presheaf.representable

section

variable {F G : Cᵒᵖ ⥤ Type v} {f : F ⟶ G} (hf : Presheaf.representable f)
  {Y : C} {f' : yoneda.obj Y ⟶ G} (hf' : Presheaf.representable f')
  {X : C} (g : yoneda.obj X ⟶ G) (hg : Presheaf.representable g)

/-- Let `f : F ⟶ G` be a representable morphism in the category of presheaves of types on
a category `C`. Then, for any `g : yoneda.obj X ⟶ G`, `hf.pullback g` denotes the (choice of) a
corresponding object in `C` such that `yoneda.obj (hf.pullback g)` forms a categorical pullback
of `f` and `g` in the category of presheaves. -/
noncomputable def pullback : C :=
  (hf g).choose

/-- Given a representable morphism `f : F ⟶ G`, then for any `g : yoneda.obj X ⟶ G`, `hf.snd g`
denotes the morphism in `C` whose image under `yoneda` is the second projection in the choice of a
pullback square given by the defining property of `f` being representable. -/
noncomputable abbrev snd : hf.pullback g ⟶ X :=
  (hf g).choose_spec.choose

/-- Given a representable morphism `f : F ⟶ G`, then for any `g : yoneda.obj X ⟶ G`, `hf.fst g`
denotes the first projection in the choice of a pullback square given by the defining property of
`f` being representable. -/
noncomputable abbrev fst : yoneda.obj (hf.pullback g) ⟶ F :=
  (hf g).choose_spec.choose_spec.choose

/-- The preimage under yoneda of `hf.fst g`, whenever this makes sense. -/
noncomputable abbrev preFst : hf'.pullback g ⟶ Y :=
  Yoneda.fullyFaithful.preimage (hf'.fst g)

lemma yoneda_map_preFst : yoneda.map (hf'.preFst g) = hf'.fst g :=
  Functor.FullyFaithful.map_preimage _ _

lemma isPullback : IsPullback (hf.fst g) (yoneda.map (hf.snd g)) f g :=
  (hf g).choose_spec.choose_spec.choose_spec

-- (Calle) maybe this should have a better name?
@[reassoc]
lemma condition : yoneda.map (hf'.preFst g) ≫ f' = yoneda.map (hf'.snd g) ≫ g := by
  simpa only [yoneda_map_preFst] using (hf'.isPullback g).w

/-- Variant of `condition` when all vertices of the pullback square lie in the image of yoneda. -/
@[reassoc]
lemma condition' {X Y Z : C} {f : X ⟶ Z} (g : yoneda.obj Y ⟶ yoneda.obj Z)
    (hf : Presheaf.representable (yoneda.map f)) :
      hf.preFst g ≫ f = hf.snd g ≫ (Yoneda.fullyFaithful.preimage g) :=
  yoneda.map_injective <| by simp [(hf.isPullback g).w]

variable {g}

/-- Two morphisms `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf.snd g : hf.pullback  ⟶ X` are equal.
* The compositions of `yoneda.map a` and `yoneda.map b` with `(hf.pullbackCone g).fst` are equal. -/
@[ext 100]
lemma hom_ext {Z : C} {a b : Z ⟶ hf.pullback g}
    (h₁ : yoneda.map a ≫ hf.fst g = yoneda.map b ≫ hf.fst g)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b :=
  yoneda.map_injective <|
    PullbackCone.IsLimit.hom_ext (hf.isPullback g).isLimit h₁ (by simpa using yoneda.congr_map h₂)

/-- In the case of a representable morphism `f' : yoneda.obj Y ⟶ G`, whose codomain lies
in the image of yoneda, we get that two morphism `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf'.snd g : hf.pullback  ⟶ X` are equal.
* Their compositions (in `C`) with `hf'.fst g : hf.pullback  ⟶ X` are equal. -/
@[ext]
lemma hom_ext' {Z : C} {a b : Z ⟶ hf'.pullback g} (h₁ : a ≫ hf'.preFst g = b ≫ hf'.preFst g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  hf'.hom_ext (by simpa [yoneda_map_preFst] using yoneda.congr_map h₁) h₂

section

variable {Z : C} (i : yoneda.obj Z ⟶ F) (h : Z ⟶ X) (hi : i ≫ f = yoneda.map h ≫ g)

/-- The lift (in `C`) obtained from the universal property of `yoneda.obj (hf.pullback g)`, in the
case when one of the morphisms lies in the image of `yoneda.map`. -/
noncomputable def lift : Z ⟶ hf.pullback g :=
  Yoneda.fullyFaithful.preimage <| PullbackCone.IsLimit.lift (hf.isPullback g).isLimit _ _ hi

@[reassoc (attr := simp)]
lemma lift_fst : yoneda.map (hf.lift i h hi) ≫ hf.fst g = i := by
  simpa [lift] using PullbackCone.IsLimit.lift_fst _ _ _ _


@[reassoc (attr := simp)]
lemma lift_snd : hf.lift i h hi ≫ hf.snd g = h :=
  yoneda.map_injective <| by simpa [lift] using PullbackCone.IsLimit.lift_snd _ _ _ _

end

section

variable {Z : C} (i : Z ⟶ Y) (h : Z ⟶ X) (hi : (yoneda.map i) ≫ f' = yoneda.map h ≫ g)

/-- TODO -/
noncomputable def lift' : Z ⟶ hf'.pullback g := hf'.lift _ _ hi

@[reassoc (attr := simp)]
lemma lift'_fst : hf'.lift' i h hi ≫ hf'.preFst g = i :=
  yoneda.map_injective (by simp [yoneda_map_preFst, lift'])

@[reassoc (attr := simp)]
lemma lift'_snd : hf'.lift' i h hi ≫ hf'.snd g = h := by
  simp [lift']

end

/-- TODO -/
noncomputable def symmetry : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift' (hf'.snd g) (hf'.preFst g) (condition _ _).symm

@[reassoc (attr := simp)]
lemma symmetry_fst : hf'.symmetry hg ≫ hg.preFst f' = hf'.snd g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_snd : hf'.symmetry hg ≫ hg.snd f' = hf'.preFst g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_symmetry : hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _ := by aesop_cat

/-- TODO -/
@[simps]
noncomputable def symmetryIso : hf'.pullback g ≅ hg.pullback f' where
  hom := hf'.symmetry hg
  inv := hg.symmetry hf'

instance : IsIso (hf'.symmetry hg) :=
  (hf'.symmetryIso hg).isIso_hom

end

/-- When `C` has pullbacks, then `yoneda.map f` is representable for any `f : X ⟶ Y`. -/
lemma yoneda_map [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    Presheaf.representable (yoneda.map f) := fun Z g ↦ by
  obtain ⟨g, rfl⟩ := yoneda.map_surjective g
  refine ⟨Limits.pullback f g, Limits.pullback.snd f g, yoneda.map (Limits.pullback.fst f g), ?_⟩
  apply yoneda.map_isPullback <| IsPullback.of_hasPullback f g

end Presheaf.representable

namespace MorphismProperty

variable {F G : Cᵒᵖ ⥤ Type v} (P : MorphismProperty C)

/-- Given a morphism property `P` in a category `C`, a morphism `f : F ⟶ G` of presheaves in the
category `Cᵒᵖ ⥤ Type v` satisfies the morphism property `P.presheaf` iff:
* The morphism is representable.
* The property `P` holds for the pullback of `f` by any morphism `g : yoneda.obj X ⟶ G`. -/
def presheaf : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  fun _ G f ↦ ∃ (hf : Presheaf.representable f), ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), P (hf.snd g)

variable {P}

/-- A morphism satisfying `P.presheaf` is representable. -/
lemma presheaf.rep {f : F ⟶ G} (hf : P.presheaf f) : Presheaf.representable f :=
  hf.choose

lemma presheaf.property {f : F ⟶ G} (hf : P.presheaf f) {X : C} (g : yoneda.obj X ⟶ G) :
    P (hf.choose.snd g) :=
  hf.choose_spec g

-- possibly this should be the definition, and the weaker condition should be derived from this?
lemma presheaf.property' (hP : P.RespectsIso) {f : F ⟶ G} (hf : P.presheaf f) :
    ∀ ⦃X Y : C⦄ (g : yoneda.obj X ⟶ G) (fst : yoneda.obj Y ⟶ F) (snd : Y ⟶ X)
    (_ : IsPullback fst (yoneda.map snd) f g), P snd := by
  intro X Y g fst snd h

  have comp := h.isoIsPullback_hom_snd <| hf.rep.isPullback g
  apply congr_arg Yoneda.fullyFaithful.preimage at comp
  rw [Yoneda.fullyFaithful.preimage_map] at comp
  rw [← comp, Yoneda.fullyFaithful.preimage_comp]

  simpa using hP.1 (Yoneda.fullyFaithful.preimageIso <|
    h.isoIsPullback (hf.rep.isPullback g)) _ (hf.property g)

lemma presheaf_mk' (hP : P.RespectsIso) {f : F ⟶ G} (hf : Presheaf.representable f)
    (h : (∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), ∃ (Y : C)
    (fst : yoneda.obj Y ⟶ F) (snd : Y ⟶ X) (_ : IsPullback fst (yoneda.map snd) f g),
    P snd)) : P.presheaf f := by
  use hf
  intro X g
  obtain ⟨Y, fst, snd, ⟨h, P_snd⟩⟩ := h g

  have comp := (hf.isPullback g).isoIsPullback_hom_snd h
  apply congr_arg (Yoneda.fullyFaithful.preimage ·) at comp
  rw [Functor.FullyFaithful.preimage_map] at comp
  rw [← comp, Yoneda.fullyFaithful.preimage_comp]

  simpa using hP.1 (Yoneda.fullyFaithful.preimageIso <| (hf.isPullback g).isoIsPullback h) _ P_snd

/-- If `P : MorphismProperty C` is stable under base change, then for any `f : X ⟶ Y` in `C`,
`yoneda.map f` satisfies `P.presheaf` if `f` does. -/
-- TODO: converse!
lemma presheaf_yoneda_map [HasPullbacks C] (hP : StableUnderBaseChange P) {X Y : C} {f : X ⟶ Y}
    (hf : P f) : P.presheaf (yoneda.map f) := by
  use Presheaf.representable.yoneda_map f
  intro Z g
  apply hP (f := (Yoneda.fullyFaithful.preimage g))
    (f' := (Presheaf.representable.yoneda_map f).preFst g) _ hf
  apply IsPullback.of_map yoneda ((Presheaf.representable.yoneda_map f).condition' g)
  simpa using (Presheaf.representable.yoneda_map f).isPullback g

lemma presheaf_of_yoneda (hP : RespectsIso P) {X Y : C} {f : X ⟶ Y}
    (hf : P.presheaf (yoneda.map f)) : P f :=
  hf.property' hP (𝟙 _) (𝟙 _) f (IsPullback.id_horiz (yoneda.map f))

/-- Morphisms satisfying `(monomorphism C).presheaf` are in particular monomorphisms.-/
lemma presheaf_monomorphisms_le_monomorphisms :
    (monomorphisms C).presheaf ≤ monomorphisms _ := fun F G f hf ↦ by
  suffices ∀ {X : C} {a b : yoneda.obj X ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_yoneda (fun _ _ ↦ this (by simp only [assoc, h]))⟩
  intro X a b h
  /- It suffices to show that the lifts of `a` and `b` to morphisms
  `X ⟶ hf.rep.pullback g` are equal, where `g = a ≫ f = a ≫ f`. -/
  suffices hf.rep.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.rep.lift b (𝟙 X) (by simp [← h]) by
    simpa using yoneda.congr_map this =≫ (hf.rep.fst (a ≫ f))
  -- This follows from the fact that the induced maps `hf.rep.pullback g ⟶ X` are Mono.
  have : Mono (hf.rep.snd (a ≫ f)) := hf.property (a ≫ f)
  simp only [← cancel_mono (hf.rep.snd (a ≫ f)),
    Presheaf.representable.lift_snd]

/-- If `P' : MorphismProperty C` is satisfied whenever `P` is, then also `P'.presheaf` is
satisfied whenever `P.presheaf` is. -/
lemma presheaf_monotone {P' : MorphismProperty C} (h : P ≤ P') :
    P.presheaf ≤ P'.presheaf := fun _ _ _ hf ↦
  ⟨hf.rep, fun _ g ↦ h _ (hf.property g)⟩

instance representable_isStableUnderComposition :
    IsStableUnderComposition (Presheaf.representable (C:=C)) where
  comp_mem {F G H} f g hf hg := fun X h ↦
    ⟨hf.pullback (hg.fst h), hf.snd (hg.fst h) ≫ hg.snd h, hf.fst (hg.fst h),
      by simpa using IsPullback.paste_vert (hf.isPullback (hg.fst h)) (hg.isPullback h)⟩

lemma representable_stableUnderBaseChange :
    StableUnderBaseChange (Presheaf.representable (C:=C)) := by
  intro F G G' H f g f' g' P₁ hg X h
  refine ⟨hg.pullback (h ≫ f), hg.snd (h ≫ f), ?_, ?_⟩
  apply P₁.lift (hg.fst (h ≫ f)) (yoneda.map (hg.snd (h ≫ f)) ≫ h) (hg.isPullback (h ≫ f)).w
  apply IsPullback.of_right' (hg.isPullback (h ≫ f)) P₁

lemma representable_ofIsIso {F G : Cᵒᵖ ⥤ Type v} (f : F ⟶ G) [IsIso f] :
    Presheaf.representable f :=
  fun X g ↦ ⟨X, 𝟙 X, g ≫ inv f, IsPullback.of_vert_isIso ⟨by simp⟩⟩

lemma representable_isomorphisms_le :
    MorphismProperty.isomorphisms (Cᵒᵖ ⥤ Type v) ≤ Presheaf.representable :=
  fun _ _ f hf ↦ letI : IsIso f := hf; representable_ofIsIso f

lemma representable_respectsIso : RespectsIso (Presheaf.representable (C:=C)) :=
  representable_stableUnderBaseChange.respectsIso

section

variable [HasPullbacks C] (hP₀ : P.RespectsIso)

lemma presheaf_stableUnderBaseChange : StableUnderBaseChange (MorphismProperty.presheaf P) := by
  intro F G G' H f g f' g' hfBC hg
  have hg' := representable_stableUnderBaseChange hfBC hg.rep
  refine ⟨hg', fun X h ↦ hg.property' hP₀ _ _ _ (IsPullback.paste_horiz (hg'.isPullback h) hfBC)⟩

-- if P.presheaf assumes `StableUnderBaseChange`, this could be maybe an instance
lemma presheaf_isStableUnderComp [P.IsStableUnderComposition] :
    IsStableUnderComposition (P.presheaf) where
  comp_mem {F G H} f g hf hg := by
    apply P.presheaf_mk' hP₀ (Presheaf.representable.comp_mem f g hf.rep hg.rep)
    intro X h

    have hBC := IsPullback.paste_vert (hf.rep.isPullback (hg.rep.fst h)) (hg.rep.isPullback h)
    use hf.rep.pullback (hg.rep.fst h), hBC.cone.fst, hf.rep.snd (hg.rep.fst h) ≫ (hg.rep.snd h)

    -- (Calle) maybe this can be combined into the statement of hBC to make proof cleaner
    simp only [IsPullback.cone_fst, Functor.map_comp, Functor.FullyFaithful.map_preimage,
      exists_prop]
    use hBC
    apply P.comp_mem _ _ (hf.property _) (hg.property _)

lemma presheaf_respectsIso : RespectsIso P.presheaf :=
  (presheaf_stableUnderBaseChange hP₀).respectsIso

end

end MorphismProperty

end CategoryTheory
