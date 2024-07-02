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

section

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (t : PullbackCone f g) (ht : IsLimit t)

--lemma pullbackCone_eq_mk_self (t : PullbackCone f g) : t = PullbackCone.mk t.fst t.snd t.condition
-- := by
--  sorry

def pullbackCone_iso_mk_self : t ≅ PullbackCone.mk t.fst t.snd t.condition := by
  apply PullbackCone.ext (by apply Iso.refl) <;> simp

def pullbackCone_iso_mk_self_pt : t.pt ≅ (PullbackCone.mk t.fst t.snd t.condition).pt := by
  exact Iso.refl t.pt

-- TODO: look at pullbackIsPullback...!
def pullbackConeMkSelf_isLimit : IsLimit (PullbackCone.mk t.fst t.snd t.condition) := by
  apply IsLimit.ofIsoLimit ht
  apply PullbackCone.ext (by apply Iso.refl) <;> simp

end

/-- A morphism of presheaves `F ⟶ G` is representable if for any `X : C`, and any morphism
`g : yoneda.obj X ⟶ G`, the pullback `F ×_G yoneda.obj X` is also representable. -/
def Presheaf.representable : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  fun _ G f ↦ ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), (pullback f g).Representable


namespace Presheaf.representable

section

variable {F G : Cᵒᵖ ⥤ Type v} {f : F ⟶ G} (hf : Presheaf.representable f)
  {Y : C} {f' : yoneda.obj Y ⟶ G} (hf' : Presheaf.representable f')
  {X : C} (g : yoneda.obj X ⟶ G) (hg : Presheaf.representable g)

/-- Let `f : F ⟶ G` be a representable morphism in the category of presheaves of types on
a category `C`. Then, for any `g : yoneda.obj X ⟶ G`, `hf.pullback g` denotes the (choice of) a
corresponding object in `C` equipped with an isomorphism between `yoneda.obj (hf.pullback g)`
and the categorical pullback of `f` and `g` in the category of presheaves. -/
noncomputable def pullback : C :=
  Functor.reprX (hF := hf g)

/-- The given isomorphism between `yoneda.obj (hf.pullback g)` and the choice of categorical
pullback of `f` and `g`-/
noncomputable def pullbackIso : yoneda.obj (hf.pullback g) ≅ Limits.pullback f g :=
  Functor.reprW (hF := hf g)

-- (Calle): I think the following API could probably be improved somewhat, as I am still not
-- so familiar with the pullback API.

/-- The pullback cone obtained by the isomorphism `hf.pullbackIso`. -/
noncomputable def pullbackCone : PullbackCone f g :=
  PullbackCone.mk ((hf.pullbackIso g).hom ≫ pullback.fst)
    ((hf.pullbackIso g).hom ≫ pullback.snd) (by simpa using pullback.condition)

/-- The pullback cone obtained via `hf.pullbackIso` is a limit cone. -/
noncomputable def pullbackConeIsLimit : IsLimit (hf.pullbackCone g) :=
  IsLimit.ofIsoLimit (pullbackIsPullback _ _)
    (PullbackCone.ext (hf.pullbackIso g).symm (by simp [pullbackCone]) (by simp [pullbackCone]))

/-- The preimage under yoneda of the second projection of `hf.pullbackCone g` -/
noncomputable abbrev snd : hf.pullback g ⟶ X :=
  Yoneda.fullyFaithful.preimage ((hf.pullbackCone g).snd)

/-- The preimage under yoneda of the first projection of `hf.pullbackCone g`, whenever this
makes sense. -/
noncomputable abbrev fst : hf'.pullback g ⟶ Y :=
  Yoneda.fullyFaithful.preimage ((hf'.pullbackCone g).fst)

-- Note(JR): while these are useful to setup the API, better not make these simp lemmas
lemma yoneda_map_snd : yoneda.map (hf.snd g) = (hf.pullbackCone g).snd := by
  apply Functor.FullyFaithful.map_preimage

lemma yoneda_map_fst : yoneda.map (hf'.fst g) = (hf'.pullbackCone g).fst := by
  apply Functor.FullyFaithful.map_preimage

/- (Calle): A possibly better approach to the API would be to construct pullbackCone
so that `yoneda.map (hf.snd g)` is definitionally `pullbackCone.snd`. Then `condition_yoneda`
would just bee pullbackCone.condition -/
@[reassoc]
lemma condition_yoneda : (hf.pullbackCone g).fst ≫ f = yoneda.map (hf.snd g) ≫ g := by
  simpa only [yoneda_map_snd] using (hf.pullbackCone g).condition

@[reassoc]
lemma condition : yoneda.map (hf'.fst g) ≫ f' = yoneda.map (hf'.snd g) ≫ g := by
  simpa only [yoneda_map_fst] using hf'.condition_yoneda g

/-- Variant of `condition` when all vertices of the pullback square lie in the image of yoneda. -/
@[reassoc]
lemma condition' {X Y Z : C} {f : X ⟶ Z} (g : yoneda.obj Y ⟶ yoneda.obj Z)
    (hf : Presheaf.representable (yoneda.map f)) :
      hf.fst g ≫ f = hf.snd g ≫ (Yoneda.fullyFaithful.preimage g) :=
  yoneda.map_injective <| by simp [condition_yoneda]

variable {g}

/-- Two morphisms `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf.snd g : hf.pullback  ⟶ X` are equal.
* The compositions of `yoneda.map a` and `yoneda.map b` with `(hf.pullbackCone g).fst` are equal. -/
@[ext 100]
lemma hom_ext {Z : C} {a b : Z ⟶ hf.pullback g}
    (h₁ : yoneda.map a ≫ (hf.pullbackCone g).fst = yoneda.map b ≫ (hf.pullbackCone g).fst)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b :=
  yoneda.map_injective <|
    PullbackCone.IsLimit.hom_ext (hf.pullbackConeIsLimit g) h₁ (by simpa using yoneda.congr_map h₂)

/-- In the case of a representable morphism `f' : yoneda.obj Y ⟶ G`, whose codomain lies
in the image of yoneda, we get that two morphism `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf'.snd g : hf.pullback  ⟶ X` are equal.
* Their compositions (in `C`) with `hf'.fst g : hf.pullback  ⟶ X` are equal. -/
@[ext]
lemma hom_ext' {Z : C} {a b : Z ⟶ hf'.pullback g} (h₁ : a ≫ hf'.fst g = b ≫ hf'.fst g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  hf'.hom_ext (by simpa [yoneda_map_fst] using yoneda.congr_map h₁) h₂

section

variable {Z : C} (i : yoneda.obj Z ⟶ F) (h : Z ⟶ X) (hi : i ≫ f = yoneda.map h ≫ g)

/-- The lift (in `C`) obtained from the universal property of `yoneda.obj (hf.pullback g)`, in the
case when one of the morphisms lies in the image of `yoneda.map`. -/
noncomputable def lift : Z ⟶ hf.pullback g :=
  Yoneda.fullyFaithful.preimage <| PullbackCone.IsLimit.lift (hf.pullbackConeIsLimit g) _ _ hi

@[reassoc (attr := simp)]
lemma lift_fst : yoneda.map (hf.lift i h hi) ≫ (hf.pullbackCone g).fst = i := by
  simp [lift]

@[reassoc (attr := simp)]
lemma lift_snd : hf.lift i h hi ≫ hf.snd g = h :=
  yoneda.map_injective (by simp [lift, yoneda_map_snd])

end

section

variable {Z : C} (i : Z ⟶ Y) (h : Z ⟶ X) (hi : (yoneda.map i) ≫ f' = yoneda.map h ≫ g)

/-- TODO -/
noncomputable def lift' : Z ⟶ hf'.pullback g := hf'.lift _ _ hi

@[reassoc (attr := simp)]
lemma lift'_fst : hf'.lift' i h hi ≫ hf'.fst g = i :=
  yoneda.map_injective (by simp [yoneda_map_fst, lift'])

@[reassoc (attr := simp)]
lemma lift'_snd : hf'.lift' i h hi ≫ hf'.snd g = h := by
  simp [lift']

end

/-- TODO -/
noncomputable def symmetry : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift' (hf'.snd g) (hf'.fst g) (condition _ _).symm

@[reassoc (attr := simp)]
lemma symmetry_fst : hf'.symmetry hg ≫ hg.fst f' = hf'.snd g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_snd : hf'.symmetry hg ≫ hg.snd f' = hf'.fst g := by simp [symmetry]

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
  exact ⟨Limits.pullback f g, ⟨PreservesPullback.iso _ _ _⟩⟩

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
lemma presheaf.representable {f : F ⟶ G} (hf : P.presheaf f) : Presheaf.representable f :=
  hf.choose

lemma presheaf.property {f : F ⟶ G} (hf : P.presheaf f) {X : C} (g : yoneda.obj X ⟶ G) :
    P (hf.choose.snd g) :=
  hf.choose_spec g

-- (Calle): this can definitely be golfed later. Also maybe provide other versions
-- of this lemma with other pullback API's (e.g. `pullback f g` could be useful)
-- possibly this should be the definition, and the weaker condition should be derived from this?
lemma presheaf.property' (hP : P.RespectsIso) {f : F ⟶ G} (hf : P.presheaf f) :
    ∀ ⦃X Y : C⦄ {g : yoneda.obj X ⟶ G} {fst : yoneda.obj Y ⟶ F} {snd : Y ⟶ X}
    (_ : IsPullback fst (yoneda.map snd) f g), P snd := by
  intro X Y g fst snd h
  have h' := IsPullback.of_isLimit (hf.representable.pullbackConeIsLimit g)
  rw [← hf.representable.yoneda_map_snd] at h' -- TODO: this should be unecessary w better API above
  have comp := h.isoIsPullback_hom_snd h'

  apply congr_arg (Yoneda.fullyFaithful.preimage ·) at comp
  rw [Functor.FullyFaithful.preimage_map] at comp
  rw [← comp, Yoneda.fullyFaithful.preimage_comp]

  simpa using hP.1 (Yoneda.fullyFaithful.preimageIso <| h.isoIsPullback h') _ (hf.property g)

lemma presheaf_mk' (hP : P.RespectsIso) {f : F ⟶ G} (hf : Presheaf.representable f)
    (h : (∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), ∃ (Y : C)
    (fst : yoneda.obj Y ⟶ F) (snd : Y ⟶ X) (_ : IsPullback fst (yoneda.map snd) f g),
    P snd)) : P.presheaf f := by
  use hf
  intro X g
  obtain ⟨Y, fst, snd, ⟨h, P_snd⟩⟩ := h g

  have h' := IsPullback.of_isLimit (hf.pullbackConeIsLimit g)
  rw [← hf.yoneda_map_snd] at h' -- TODO: this should be unecessary w better API above
  have comp := h'.isoIsPullback_hom_snd h

  apply congr_arg (Yoneda.fullyFaithful.preimage ·) at comp
  rw [Functor.FullyFaithful.preimage_map] at comp
  rw [← comp, Yoneda.fullyFaithful.preimage_comp]

  simpa using hP.1 (Yoneda.fullyFaithful.preimageIso <| h'.isoIsPullback h) _ P_snd

-- this lemma is also introduced in PR #10425, this should be moved to CategoryTheory.Yoneda
/-- Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `yoneda.obj X ⟶ P` agree. -/
lemma _root_.CategoryTheory.hom_ext_yoneda {P Q : Cᵒᵖ ⥤ Type v} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (yonedaEquiv) (h _ (yonedaEquiv.symm x))

/-- If `P : MorphismProperty C` is stable under base change, then for any `f : X ⟶ Y` in `C`,
`yoneda.map f` satisfies `P.presheaf` if `f` does. -/
-- TODO: converse!
lemma presheaf_yoneda_map [HasPullbacks C] (hP : StableUnderBaseChange P) {X Y : C} {f : X ⟶ Y}
    (hf : P f) : P.presheaf (yoneda.map f) := by
  use Presheaf.representable.yoneda_map f
  intro Z g
  have BC : IsPullback ((Presheaf.representable.yoneda_map f).fst g)
      ((Presheaf.representable.yoneda_map f).snd g) f (Yoneda.fullyFaithful.preimage g) := by
    apply IsPullback.of_map yoneda ((Presheaf.representable.yoneda_map f).condition' g)
    simpa using IsPullback.of_isLimit <| (Presheaf.representable.yoneda_map f).pullbackConeIsLimit g
  exact hP BC hf

/-- Morphisms satisfying `(monomorphism C).presheaf` are in particular monomorphisms.-/
lemma presheaf_monomorphisms_le_monomorphisms :
    (monomorphisms C).presheaf ≤ monomorphisms _ := fun F G f hf ↦ by
  suffices ∀ {X : C} {a b : yoneda.obj X ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_yoneda (fun _ _ ↦ this (by simp only [assoc, h]))⟩
  intro X a b h
  /- It suffices to show that the lifts of `a` and `b` to morphisms
  `X ⟶ hf.representable.pullback g` are equal. -/
  suffices hf.representable.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.representable.lift b (𝟙 X) (by simp [← h]) by
    simpa using yoneda.congr_map this =≫ (hf.representable.pullbackCone (a ≫ f)).fst
  -- This follows from the fact that the induced maps `hf.representable.pullback g ⟶ X` are Mono.
  have : Mono (hf.representable.snd (a ≫ f)) := hf.property (a ≫ f)
  simp only [← cancel_mono (hf.representable.snd (a ≫ f)),
    Presheaf.representable.lift_snd]

/-- If `P' : MorphismProperty C` is satisfied whenever `P` is, then also `P'.presheaf` is
satisfied whenever `P.presheaf` is. -/
lemma presheaf_monotone {P' : MorphismProperty C} (h : P ≤ P') :
    P.presheaf ≤ P'.presheaf := fun _ _ _ hf ↦
  ⟨hf.representable, fun _ g ↦ h _ (hf.property g)⟩

instance representable_isStableUnderComposition :
    IsStableUnderComposition (Presheaf.representable (C:=C)) where
  comp_mem {F G H} f g hf hg := fun X h ↦ by
    use hf.pullback (hg.pullbackCone h).fst

    /- The morphism `f₁` puts the pullback of `f ≫ g` and `h` into a `bigSquare` with
    `yoneda.obj (hg.pullback h)`. -/
    let f₁ : pullback (f ≫ g) h ⟶ yoneda.obj (hg.pullback h) :=
      PullbackCone.IsLimit.lift (hg.pullbackConeIsLimit h) (pullback.fst ≫ f) pullback.snd
        (by rw [← pullback.condition, assoc])

    /- It follows that `pullback (f ≫ g) h` is the "limit point" of a pullback over `f` and
    `(hg.pullbackCone h).snd`. -/
    -- TODO: this should be done using the IsPullback API!
    let P' := leftSquareIsPullback f₁ (hg.pullbackCone h).snd f g pullback.fst
      (hg.pullbackCone h).fst h (by simp [f₁]) (hg.pullbackCone h).condition
      (pullbackConeMkSelf_isLimit _ (hg.pullbackConeIsLimit h))
      (by simpa only [PullbackCone.IsLimit.lift_snd, f₁] using pullbackIsPullback (f ≫ g) h)

    refine ⟨Limits.IsLimit.conePointUniqueUpToIso (hf.pullbackConeIsLimit _) P'⟩

lemma representable_stableUnderBaseChange :
    StableUnderBaseChange (Presheaf.representable (C:=C)) := by
  intro F G G' H f g f' g' P₁ hg X h
  use hg.pullback (h ≫ f)
  let P₂ := IsPullback.of_isLimit (limit.isLimit (cospan g' h))
  let P := IsPullback.paste_horiz P₂ P₁
  refine ⟨hg.pullbackIso (h ≫ f) ≪≫ P.isoPullback.symm⟩

lemma representable_ofIsIso {F G : Cᵒᵖ ⥤ Type v} (f : F ⟶ G) [IsIso f] :
    Presheaf.representable f :=
  fun X g ↦ ⟨X, ⟨(asIso <| Limits.pullback.snd (f:=f) (g:=g)).symm⟩⟩

lemma representable_isomorphisms_le :
    MorphismProperty.isomorphisms (Cᵒᵖ ⥤ Type v) ≤ Presheaf.representable :=
  fun _ _ f hf ↦ letI : IsIso f := hf; representable_ofIsIso f

lemma representable_respectsIso : RespectsIso (Presheaf.representable (C:=C)) :=
  representable_stableUnderBaseChange.respectsIso

section

variable [HasPullbacks C] (hP₀ : P.RespectsIso)

lemma presheaf_stableUnderBaseChange : StableUnderBaseChange (MorphismProperty.presheaf P) := by
  intro F G G' H f g f' g' hfBC hg
  have hg' := representable_stableUnderBaseChange hfBC hg.representable
  use hg'
  intro X h

  have P₁ : IsPullback ((hg'.pullbackCone h).fst ≫ f') (yoneda.map (hg'.snd h)) g (h ≫ f) := by
    rw [hg'.yoneda_map_snd h]
    exact IsPullback.paste_horiz (IsPullback.of_isLimit (hg'.pullbackConeIsLimit h)) hfBC

  apply hg.property' hP₀ P₁


-- if P.presheaf assumes `StableUnderBaseChange`, this could be maybe an instance
-- (Calle): This is definitely golfable
lemma presheaf_isStableUnderComp [P.IsStableUnderComposition] :
    IsStableUnderComposition (P.presheaf) where
  comp_mem {F G H} f g hf hg := by
    have hfg : Presheaf.representable (f ≫ g) := Presheaf.representable.comp_mem f g
      hf.representable hg.representable
    apply P.presheaf_mk' hP₀ hfg
    intro X h
    -- (Calle): Maybe its worth givin P.presheaf.representable a shorter name, e.g. P.presheaf.repr
    have hgBC := IsPullback.of_isLimit (hg.representable.pullbackConeIsLimit h)
    have hfBC := IsPullback.of_isLimit (hf.representable.pullbackConeIsLimit
      (hg.representable.pullbackCone h).fst)
    have hBC := IsPullback.paste_vert hfBC hgBC
    have := hBC.cone.pt
    use hf.representable.pullback (hg.representable.pullbackCone h).fst
    use hBC.cone.fst
    use hf.representable.snd (hg.representable.pullbackCone h).fst ≫ (hg.representable.snd h)
    simp only [IsPullback.cone_fst, Functor.map_comp, Functor.FullyFaithful.map_preimage,
      exists_prop]
    use hBC
    apply P.comp_mem _ _ (hf.property _) (hg.property _)

lemma presheaf_respectsIso : RespectsIso P.presheaf :=
  (presheaf_stableUnderBaseChange hP₀).respectsIso

end

/-
Calle's notes on current pullback API (I might try PR some of this if I don't end up finding good
  ways to do it):
- pullback f g: is there no super easy way to access its cone? (i.e. pullback.cone?)
  - should start by constructing the cone, then deriving pullback etc

- Is there too few variants of the BigSquare lemmas? i.e. is there a way to do it w/ specified
  PullbackCones? (Pullback.mk is slightly annoying there)
  - Want: BigSquare & pullback interaction

- PullbackCone:
 - Want PullbackCone.IsLimit.uniqueUpToIso? (not sure if I need this in the end)
 - More PullbackCone.IsLimit constructors?
 - PullbackCone eq mk self (as above?)
-/

end MorphismProperty

end CategoryTheory
