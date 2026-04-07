/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Relation of morphism properties with limits

The following predicates are introduces for morphism properties `P`:
* `IsStableUnderBaseChange`: `P` is stable under base change if in all pullback
  squares, the left map satisfies `P` if the right map satisfies it.
* `IsStableUnderCobaseChange`: `P` is stable under cobase change if in all pushout
  squares, the right map satisfies `P` if the left map satisfies it.

We define `P.universally` for the class of morphisms which satisfy `P` after any base change.

We also introduce properties `IsStableUnderProductsOfShape`, `IsStableUnderLimitsOfShape`,
`IsStableUnderFiniteProducts`, and similar properties for colimits and coproducts.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Category Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

section

variable (P : MorphismProperty C)

/-- Given a class of morphisms `P`, this is the class of pullbacks
of morphisms in `P`. -/
def pullbacks : MorphismProperty C := fun A B q ↦
  ∃ (X Y : C) (p : X ⟶ Y) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPullback f q p g

lemma pullbacks_mk {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPullback f q p g) (hp : P p) :
    P.pullbacks q :=
  ⟨_, _, _, _, _, hp, sq⟩

lemma le_pullbacks : P ≤ P.pullbacks := by
  intro A B q hq
  exact P.pullbacks_mk IsPullback.of_id_fst hq

lemma pullbacks_monotone : Monotone (pullbacks (C := C)) := by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩

/-- Given a class of morphisms `P`, this is the class of pushouts
of morphisms in `P`. -/
def pushouts : MorphismProperty C := fun X Y q ↦
  ∃ (A B : C) (p : A ⟶ B) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPushout f p q g

lemma pushouts_mk {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPushout f q p g) (hq : P q) :
    P.pushouts p :=
  ⟨_, _, _, _, _, hq, sq⟩

lemma le_pushouts : P ≤ P.pushouts := by
  intro X Y p hp
  exact P.pushouts_mk IsPushout.of_id_fst hp

lemma pushouts_monotone : Monotone (pushouts (C := C)) := by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩

set_option backward.isDefEq.respectTransparency false in
instance : P.pushouts.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨A, B, p, f, g, hp, h⟩
    exact ⟨A, B, p, f ≫ e.hom.left, g ≫ e.hom.right, hp,
      IsPushout.paste_horiz h (IsPushout.of_horiz_isIso ⟨e.hom.w⟩)⟩)

set_option backward.isDefEq.respectTransparency false in
instance : P.pullbacks.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨X, Y, p, f, g, hp, h⟩
    exact ⟨X, Y, p, e.inv.left ≫ f, e.inv.right ≫ g, hp,
      IsPullback.paste_horiz (IsPullback.of_horiz_isIso ⟨e.inv.w⟩) h⟩)

/-- If `P : MorphismProperty C` is such that any object in `C` maps to the
target of some morphism in `P`, then `P.pushouts` contains the isomorphisms. -/
lemma isomorphisms_le_pushouts
    (h : ∀ (X : C), ∃ (A B : C) (p : A ⟶ B) (_ : P p) (_ : B ⟶ X), IsIso p) :
    isomorphisms C ≤ P.pushouts := by
  intro X Y f (_ : IsIso f)
  obtain ⟨A, B, p, hp, g, _⟩ := h X
  exact ⟨A, B, p, p ≫ g, g ≫ f, hp, (IsPushout.of_id_snd (f := p ≫ g)).of_iso
    (Iso.refl _) (Iso.refl _) (asIso p) (asIso f) (by simp) (by simp) (by simp) (by simp)⟩

/-- A morphism property is `IsStableUnderBaseChange` if the base change of such a morphism
still falls in the class. -/
class IsStableUnderBaseChange : Prop where
  of_isPullback {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : P g) : P g'

instance : P.pullbacks.IsStableUnderBaseChange where
  of_isPullback := by
    rintro _ _ _ _ _ _ _ _ h ⟨_, _, _, _, _, hp, hq⟩
    exact P.pullbacks_mk (h.paste_horiz hq) hp

/-- A morphism property is `IsStableUnderCobaseChange` if the cobase change of such a morphism
still falls in the class. -/
class IsStableUnderCobaseChange : Prop where
  of_isPushout {A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
    (sq : IsPushout g f f' g') (hf : P f) : P f'

instance : P.pushouts.IsStableUnderCobaseChange where
  of_isPushout := by
    rintro _ _ _ _ _ _ _ _ h ⟨_, _, _, _, _, hp, hq⟩
    exact P.pushouts_mk (hq.paste_horiz h) hp

/-- `P.HasPullbacksAlong f` states that for any morphism satisfying `P` with the same codomain
as `f`, the pullback of that morphism along `f` exists. -/
protected class HasPullbacksAlong {X Y : C} (f : X ⟶ Y) : Prop where
  hasPullback {W} (g : W ⟶ Y) : P g → HasPullback g f

/-- `P.HasPushoutsAlong f` states that for any morphism satisfying `P` with the same domain
as `f`, the pushout of that morphism along `f` exists. -/
protected class HasPushoutsAlong {X Y : C} (f : X ⟶ Y) : Prop where
  hasPushout {W} (g : X ⟶ W) : P g → HasPushout g f

/-- `P.IsStableUnderBaseChangeAlong f` states that for any morphism satisfying `P` with the same
codomain as `f`, any pullback of that morphism along `f` also satisfies `P`. -/
class IsStableUnderBaseChangeAlong {X Y : C} (f : X ⟶ Y) : Prop where
  of_isPullback {Z W : C} {f' : W ⟶ Z} {g' : W ⟶ X} {g : Z ⟶ Y}
    (pb : IsPullback f' g' g f) : P g → P g'

instance [P.IsStableUnderBaseChange] {X Y : C} (f : X ⟶ Y) : P.IsStableUnderBaseChangeAlong f where
  of_isPullback := IsStableUnderBaseChange.of_isPullback

/-- `P.IsStableUnderCobaseChangeAlong f` states that for any morphism satisfying `P` with the same
codomain as `f`, any pullback of that morphism along `f` also satisfies `P`. -/
class IsStableUnderCobaseChangeAlong {X Y : C} (f : X ⟶ Y) : Prop where
  of_isPushout {Z W : C} {f' : Z ⟶ W} {g' : Y ⟶ W} {g : X ⟶ Z}
    (pb : IsPushout f g g' f') : P g → P g'

instance [P.IsStableUnderCobaseChange] {X Y : C} (f : X ⟶ Y) :
    P.IsStableUnderCobaseChangeAlong f where
  of_isPushout := IsStableUnderCobaseChange.of_isPushout

alias of_isPullback := IsStableUnderBaseChange.of_isPullback

lemma isStableUnderBaseChange_iff_pullbacks_le :
    P.IsStableUnderBaseChange ↔ P.pullbacks ≤ P := by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPullback h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

lemma pullbacks_le [P.IsStableUnderBaseChange] : P.pullbacks ≤ P := by
  rwa [← isStableUnderBaseChange_iff_pullbacks_le]

variable {P} in
/-- Alternative constructor for `IsStableUnderBaseChange`. -/
theorem IsStableUnderBaseChange.mk' [RespectsIso P]
    (hP₂ : ∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (_ : P g),
      P (pullback.fst f g)) :
    IsStableUnderBaseChange P where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    haveI : HasPullback f g := sq.flip.hasPullback
    let e := sq.flip.isoPullback
    rw [← P.cancel_left_of_respectsIso e.inv, sq.flip.isoPullback_inv_fst]
    exact hP₂ _ _ _ f g hg

lemma IsStableUnderBaseChange.of_forall_exists_isPullback {P : MorphismProperty C} [P.RespectsIso]
    (H : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (_ : P g),
      ∃ (T : C) (fst : T ⟶ X) (snd : T ⟶ Y), IsPullback fst snd f g ∧ P fst) :
    P.IsStableUnderBaseChange := by
  refine .mk' fun X Y S f g _ hg ↦ ?_
  obtain ⟨T, fst, snd, h, hfst⟩ := H f g hg
  rwa [← h.isoPullback_inv_fst, P.cancel_left_of_respectsIso]

variable (C)

instance IsStableUnderBaseChange.isomorphisms :
    (isomorphisms C).IsStableUnderBaseChange where
  of_isPullback h _ := h.isIso_snd_of_isIso

instance IsStableUnderBaseChange.monomorphisms :
    (monomorphisms C).IsStableUnderBaseChange where
  of_isPullback h _ := h.mono_snd_of_mono

variable {C P}

instance (priority := 900) IsStableUnderBaseChange.respectsIso
    [IsStableUnderBaseChange P] : RespectsIso P := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e
  exact of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))

theorem pullback_fst {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    [P.IsStableUnderBaseChangeAlong f] (H : P g) : P (pullback.fst f g) :=
  IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g).flip H

theorem pullback_snd {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    [P.IsStableUnderBaseChangeAlong g] (H : P f) : P (pullback.snd f g) :=
  IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g) H

set_option backward.isDefEq.respectTransparency false in
theorem baseChange_obj {S S' : C} (f : S' ⟶ S)
    [HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (X : Over S) (H : P X.hom) :
    P ((Over.pullback f).obj X).hom :=
  pullback_snd X.hom f H

set_option backward.isDefEq.respectTransparency false in
theorem pullbackLift_fst_snd [IsStableUnderBaseChange P] {S S' X Y : C} (f : S' ⟶ S)
    {v₁₂ : X ⟶ S} {v₂₂ : Y ⟶ S} {g : X ⟶ Y} (hv₁₂ : v₁₂ = g ≫ v₂₂) [HasPullback v₁₂ f]
    [HasPullback v₂₂ f] (H : P g) : P (pullback.lift (f := v₂₂) (g := f) (pullback.fst v₁₂ f ≫ g)
    (pullback.snd v₁₂ f) (by simp [pullback.condition, ← hv₁₂])) := by
  subst hv₁₂
  refine of_isPullback (f' := pullback.fst (g ≫ v₂₂) f)
    (f := pullback.fst v₂₂ f) ?_ H
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback v₂₂ f)
  simpa using IsPullback.of_hasPullback (g ≫ v₂₂) f

@[deprecated (since := "2026-03-20")]
alias baseChange_map' := pullbackLift_fst_snd

theorem overPullbackMap [IsStableUnderBaseChange P] {S S' : C} (f : S' ⟶ S)
    [HasPullbacksAlong f] {X Y : Over S} (g : X ⟶ Y) (H : P g.left) :
    P ((Over.pullback f).map g).left := by
  dsimp only [Over.pullback_obj_left, Over.pullback_map_left]
  convert pullbackLift_fst_snd f (g.w.symm) H <;> simp

@[deprecated (since := "2026-03-20")]
alias baseChange_map := overPullbackMap

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] hasPullback_symmetry_of_hasPullbacksAlong in
theorem pullbackMap
    [IsStableUnderBaseChange P] [P.IsStableUnderComposition] {S X X' Y Y' : C} {f : X ⟶ S}
    [HasPullbacksAlong f] {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'}
    [HasPullbacksAlong g'] {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
    (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂)) := by
  have : HasPullbacksAlong (Over.mk f).hom := by cat_disch
  have : pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂) =
      ((pullbackSymmetry _ _).hom ≫
          ((Over.pullback _).map (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g')).left) ≫
        (pullbackSymmetry _ _).hom ≫
          ((Over.pullback g').map (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f')).left := by
    ext <;> simp
  rw [this]
  apply P.comp_mem <;> rw [P.cancel_left_of_respectsIso]
  exacts [overPullbackMap _ (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g') h₂,
    overPullbackMap _ (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f') h₁]

@[deprecated (since := "2026-03-20")]
alias pullback_map := pullbackMap

instance IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
    [P.IsStableUnderBaseChange] : P.HasOfPostcompProperty (MorphismProperty.monomorphisms C) where
  of_postcomp {X Y Z} f g (hg : Mono g) hcomp := by
    have : f = (asIso (pullback.fst (f ≫ g) g)).inv ≫ pullback.snd (f ≫ g) g := by
      simp [← cancel_mono g, pullback.condition]
    rw [this, cancel_left_of_respectsIso (P := P)]
    exact P.pullback_snd _ _ hcomp

alias of_isPushout := IsStableUnderCobaseChange.of_isPushout

lemma isStableUnderCobaseChange_iff_pushouts_le :
    P.IsStableUnderCobaseChange ↔ P.pushouts ≤ P := by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPushout h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

lemma pushouts_le [P.IsStableUnderCobaseChange] : P.pushouts ≤ P := by
  rwa [← isStableUnderCobaseChange_iff_pushouts_le]

@[simp]
lemma pushouts_le_iff {P Q : MorphismProperty C} [Q.IsStableUnderCobaseChange] :
    P.pushouts ≤ Q ↔ P ≤ Q := by
  constructor
  · exact le_trans P.le_pushouts
  · intro h
    exact le_trans (pushouts_monotone h) pushouts_le

/-- An alternative constructor for `IsStableUnderCobaseChange`. -/
theorem IsStableUnderCobaseChange.mk' [RespectsIso P]
    (hP₂ : ∀ (A B A' : C) (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (_ : P f),
      P (pushout.inr f g)) :
    IsStableUnderCobaseChange P where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    haveI : HasPushout f g := sq.flip.hasPushout
    let e := sq.flip.isoPushout
    rw [← P.cancel_right_of_respectsIso _ e.hom, sq.flip.inr_isoPushout_hom]
    exact hP₂ _ _ _ f g hf

lemma IsStableUnderCobaseChange.of_forall_exists_isPullback {P : MorphismProperty C} [P.RespectsIso]
    (H : ∀ {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g] (_ : P f),
      ∃ (T : C) (inl : X ⟶ T) (inr : Y ⟶ T), IsPushout f g inl inr ∧ P inr) :
    P.IsStableUnderCobaseChange := by
  refine .mk' fun X Y S f g _ hg ↦ ?_
  obtain ⟨T, inl, inr, h, hinl⟩ := H f g hg
  rwa [← h.inr_isoPushout_hom, P.cancel_right_of_respectsIso]

instance IsStableUnderCobaseChange.isomorphisms :
    (isomorphisms C).IsStableUnderCobaseChange where
  of_isPushout h _ := h.isIso_inl_of_isIso

variable (C) in
instance IsStableUnderCobaseChange.epimorphisms :
    (epimorphisms C).IsStableUnderCobaseChange where
  of_isPushout h _ := h.epi_inl_of_epi

instance IsStableUnderCobaseChange.respectsIso
    [IsStableUnderCobaseChange P] : RespectsIso P :=
  RespectsIso.of_respects_arrow_iso _ fun _ _ e ↦
    of_isPushout (IsPushout.of_horiz_isIso (CommSq.mk e.hom.w))

theorem pushout_inl {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g]
    [P.IsStableUnderCobaseChangeAlong f] (H : P g) :
    P (pushout.inl f g) :=
  IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout f g) H

theorem pushout_inr {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g]
    [P.IsStableUnderCobaseChangeAlong g] (H : P f) : P (pushout.inr f g) :=
  IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout f g).flip H

set_option backward.isDefEq.respectTransparency false in
theorem pushoutDesc_inl_inr [IsStableUnderCobaseChange P] {S S' X Y : C} (f : S ⟶ S')
    {v₁₂ : S ⟶ X} {v₂₂ : S ⟶ Y} {g : Y ⟶ X} (hv₁₂ : v₁₂ = v₂₂ ≫ g) [HasPushout v₁₂ f]
    [HasPushout v₂₂ f] (H : P g) :
    P (pushout.desc (f := v₂₂) (g := f) (g ≫ pushout.inl v₁₂ f)
      (pushout.inr v₁₂ f) (by simp [pushout.condition, ← reassoc_of% hv₁₂])) := by
  subst hv₁₂
  refine IsStableUnderCobaseChangeAlong.of_isPushout (f' := pushout.inl (v₂₂ ≫ g) f)
    (f := pushout.inl v₂₂ f) ?_ H
  refine IsPushout.of_top ?_ (by simp) (IsPushout.of_hasPushout v₂₂ f).flip
  simpa using (IsPushout.of_hasPushout (v₂₂ ≫ g) f).flip

theorem underPushoutMap [IsStableUnderCobaseChange P] {S S' : C} (f : S' ⟶ S)
    [HasPushoutsAlong f] {X Y : Under S'} (g : X ⟶ Y) (H : P g.right) :
    P ((Under.pushout f).map g).right := by
  dsimp only [Under.pushout_obj, Functor.const_obj_obj, Functor.id_obj, Under.mk_right,
    Under.pushout_map, Under.homMk_right]
  convert pushoutDesc_inl_inr f (g.w) H <;> simp

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] hasPushouts_symmetry_of_hasPushoutsAlong in
theorem pushoutMap
    [IsStableUnderCobaseChange P] [P.IsStableUnderComposition] {S X X' Y Y' : C} {f : S ⟶ X}
    {g : S ⟶ Y} {f' : S ⟶ X'} {g' : S ⟶ Y'} {i₁ : X ⟶ X'} [HasPushoutsAlong f]
    [HasPushoutsAlong g'] {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
    (e₁ : f' = f ≫ i₁) (e₂ : g' = g ≫ i₂) :
    P (pushout.map f g f' g' i₁ i₂ (𝟙 _) (by simp [e₁]) (by simp [e₂])) := by
  have : HasPushoutsAlong (Under.mk g').hom := by cat_disch
  have : pushout.map f g f' g' i₁ i₂ (𝟙 _) (by simp [e₁]) (by simp [e₂]) =
      ((pushoutSymmetry _ _).hom ≫
        ((Under.pushout f).map (Under.homMk _ e₂.symm : Under.mk g ⟶ Under.mk g')).right) ≫
        (pushoutSymmetry _ _).hom ≫
        ((Under.pushout g').map (Under.homMk _ e₁.symm : Under.mk f ⟶ Under.mk f')).right := by
    ext <;> simp
  rw [this]
  apply P.comp_mem <;> rw [P.cancel_left_of_respectsIso]
  exacts [underPushoutMap _ _ h₂, underPushoutMap _ _ h₁]

instance IsStableUnderCobaseChange.hasOfPrecompProperty_epimorphisms
    [P.IsStableUnderCobaseChange] : P.HasOfPrecompProperty (MorphismProperty.epimorphisms C) where
  of_precomp {X Y Z} f g (hf : Epi f) hcomp := by
    have : g = pushout.inr (f ≫ g) f ≫ (asIso (pushout.inl (f ≫ g) f)).inv := by
      rw [asIso_inv, IsIso.eq_comp_inv, ← cancel_epi f, ← pushout.condition, assoc]
    rw [this, cancel_right_of_respectsIso (P := P)]
    exact P.pushout_inr _ _ hcomp

instance IsStableUnderCobaseChange.op [IsStableUnderCobaseChange P] :
    IsStableUnderBaseChange P.op where
  of_isPullback sq hg := P.of_isPushout sq.unop hg

instance IsStableUnderCobaseChange.unop {P : MorphismProperty Cᵒᵖ} [IsStableUnderCobaseChange P] :
    IsStableUnderBaseChange P.unop where
  of_isPullback sq hg := P.of_isPushout sq.op hg

instance IsStableUnderBaseChange.op [IsStableUnderBaseChange P] :
    IsStableUnderCobaseChange P.op where
  of_isPushout sq hf := P.of_isPullback sq.unop hf

instance IsStableUnderBaseChange.unop {P : MorphismProperty Cᵒᵖ} [IsStableUnderBaseChange P] :
    IsStableUnderCobaseChange P.unop where
  of_isPushout sq hf := P.of_isPullback sq.op hf

instance IsStableUnderBaseChange.inf {P Q : MorphismProperty C} [IsStableUnderBaseChange P]
    [IsStableUnderBaseChange Q] :
    IsStableUnderBaseChange (P ⊓ Q) where
  of_isPullback hp hg := ⟨of_isPullback hp hg.left, of_isPullback hp hg.right⟩

instance IsStableUnderCobaseChange.inf {P Q : MorphismProperty C} [IsStableUnderCobaseChange P]
    [IsStableUnderCobaseChange Q] :
    IsStableUnderCobaseChange (P ⊓ Q) where
  of_isPushout hp hg := ⟨of_isPushout hp hg.left, of_isPushout hp hg.right⟩

instance : (⊤ : MorphismProperty C).IsStableUnderBaseChange where
  of_isPullback _ _ := trivial

instance : (⊤ : MorphismProperty C).IsStableUnderCobaseChange where
  of_isPushout _ _ := trivial

end

section LimitsOfShape

variable (W : MorphismProperty C) (J : Type*) [Category* J]

/-- The class of morphisms in `C` that are limits of shape `J` of
natural transformations involving morphisms in `W`. -/
inductive limitsOfShape : MorphismProperty C
  | mk (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) :
      limitsOfShape (h₂.lift (Cone.mk _ (c₁.π ≫ f)))

variable {W J} in
lemma limitsOfShape.mk' (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (h₁ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (hf : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) :
    W.limitsOfShape J φ := by
  obtain rfl : φ = h₂.lift (Cone.mk _ (c₁.π ≫ f)) := h₂.hom_ext (fun j ↦ by simp [hφ])
  exact ⟨_, _, _, _, h₁, _, _, hf⟩

lemma limitsOfShape_monotone {W₁ W₂ : MorphismProperty C} (h : W₁ ≤ W₂)
    (J : Type*) [Category* J] :
    W₁.limitsOfShape J ≤ W₂.limitsOfShape J := by
  rintro _ _ _ ⟨_, _, _, _, h₁, _, f, hf⟩
  exact ⟨_, _, _, _, h₁, _, f, fun j ↦ h _ (hf j)⟩

set_option backward.isDefEq.respectTransparency false in
instance : (W.limitsOfShape J).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : g ≫ e₂.inv = e₁.inv ≫ h₂.lift (Cone.mk _ (c₁.π ≫ f)) :=
      e.inv.w.symm
    let c₁' : Cone X₁ := { pt := Y₁, π := (Functor.const _).map e₁.inv ≫ c₁.π }
    let c₂' : Cone X₂ := { pt := Y₂, π := (Functor.const _).map e₂.inv ≫ c₂.π }
    have h₁' : IsLimit c₁' := IsLimit.ofIsoLimit h₁ (Cone.ext e₁)
    have h₂' : IsLimit c₂' := IsLimit.ofIsoLimit h₂ (Cone.ext e₂)
    obtain hg : h₂'.lift (Cone.mk _ (c₁'.π ≫ f)) = g :=
      h₂'.hom_ext (fun j ↦ by
        rw [h₂'.fac]
        simp [reassoc_of% fac, c₁', c₂'])
    rw [← hg]
    exact ⟨_, _, _, _, h₁', _, _, hf⟩)

variable {W J} in
lemma limitsOfShape_limMap {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasLimit X] [HasLimit Y] (hf : W.functorCategory _ f) :
    W.limitsOfShape J (limMap f) :=
  ⟨_, _, _, _, limit.isLimit X, _, _, hf⟩

/-- The property that a morphism property `W` is stable under limits
indexed by a category `J`. -/
class IsStableUnderLimitsOfShape : Prop where
  condition (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) : W φ

lemma isStableUnderLimitsOfShape_iff_limitsOfShape_le :
    W.IsStableUnderLimitsOfShape J ↔ W.limitsOfShape J ≤ W := by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h.condition _ _ _ _ h₁ h₂ f hf _ (by simp)
  · rintro h
    constructor
    intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
    exact h _ (limitsOfShape.mk' X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ)

variable {W J}

lemma limitsOfShape_le [W.IsStableUnderLimitsOfShape J] :
    W.limitsOfShape J ≤ W := by
  rwa [← isStableUnderLimitsOfShape_iff_limitsOfShape_le]

protected lemma limMap [W.IsStableUnderLimitsOfShape J] {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasLimit X] [HasLimit Y] (hf : W.functorCategory _ f) :
    W (limMap f) :=
  limitsOfShape_le _ (limitsOfShape_limMap _ hf)

end LimitsOfShape

section ColimitsOfShape

variable (W : MorphismProperty C) (J : Type*) [Category* J]

/-- The class of morphisms in `C` that are colimits of shape `J` of
natural transformations involving morphisms in `W`. -/
inductive colimitsOfShape : MorphismProperty C
  | mk (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) :
      colimitsOfShape (h₁.desc (Cocone.mk _ (f ≫ c₂.ι)))

set_option backward.isDefEq.respectTransparency false in
variable {W J} in
lemma colimitsOfShape.mk' (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂) (hf : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    W.colimitsOfShape J φ := by
  obtain rfl : φ = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) := h₁.hom_ext (fun j ↦ by simp [hφ])
  exact ⟨_, _, _, _, _, h₂, _, hf⟩

lemma colimitsOfShape_monotone {W₁ W₂ : MorphismProperty C} (h : W₁ ≤ W₂)
    (J : Type*) [Category* J] :
    W₁.colimitsOfShape J ≤ W₂.colimitsOfShape J := by
  rintro _ _ _ ⟨_, _, _, _, _, h₂, f, hf⟩
  exact ⟨_, _, _, _, _, h₂, f, fun j ↦ h _ (hf j)⟩

set_option backward.isDefEq.respectTransparency false in
variable {J} in
lemma colimitsOfShape_le_of_final {J' : Type*} [Category* J'] (F : J ⥤ J') [F.Final] :
    W.colimitsOfShape J' ≤ W.colimitsOfShape J := by
  intro _ _ _ ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
  have h₁' : IsColimit (c₁.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c₁).symm h₁
  have h₂' : IsColimit (c₂.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c₂).symm h₂
  have : h₁.desc (Cocone.mk c₂.pt (f ≫ c₂.ι)) =
      h₁'.desc (Cocone.mk c₂.pt (Functor.whiskerLeft _ f ≫ (c₂.whisker F).ι)) :=
    h₁'.hom_ext (fun j ↦ by
      have := h₁'.fac (Cocone.mk c₂.pt (Functor.whiskerLeft F f ≫ Functor.whiskerLeft F c₂.ι)) j
      dsimp at this ⊢
      simp [this])
  rw [this]
  exact ⟨_, _, _, _, h₁', h₂', _, fun _ ↦ hf _⟩

variable {J} in
lemma colimitsOfShape_eq_of_equivalence {J' : Type*} [Category* J'] (e : J ≌ J') :
    W.colimitsOfShape J = W.colimitsOfShape J' :=
  le_antisymm (W.colimitsOfShape_le_of_final e.inverse)
    (W.colimitsOfShape_le_of_final e.functor)

set_option backward.isDefEq.respectTransparency false in
instance : (W.colimitsOfShape J).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : e₁.hom ≫ g = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) ≫ e₂.hom := e.hom.w
    let c₁' : Cocone X₁ := { pt := Y₁, ι := c₁.ι ≫ (Functor.const _).map e₁.hom }
    let c₂' : Cocone X₂ := { pt := Y₂, ι := c₂.ι ≫ (Functor.const _).map e₂.hom }
    have h₁' : IsColimit c₁' := IsColimit.ofIsoColimit h₁ (Cocone.ext e₁)
    have h₂' : IsColimit c₂' := IsColimit.ofIsoColimit h₂ (Cocone.ext e₂)
    obtain hg : h₁'.desc (Cocone.mk _ (f ≫ c₂'.ι)) = g :=
      h₁'.hom_ext (fun j ↦ by
        rw [h₁'.fac]
        simp [fac, c₁', c₂'])
    rw [← hg]
    exact ⟨_, _, _, _, _, h₂', _, hf⟩)

variable {W J} in
lemma colimitsOfShape_colimMap {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasColimit X] [HasColimit Y] (hf : W.functorCategory _ f) :
    W.colimitsOfShape J (colimMap f) :=
  ⟨_, _, _, _, _, colimit.isColimit Y, _, hf⟩

attribute [local instance] IsCofiltered.isConnected in
variable {W} in
lemma colimitsOfShape.of_isColimit
    {J : Type*} [Preorder J] [OrderBot J] {F : J ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (h : ∀ (j : J), W (F.map (homOfLE bot_le : ⊥ ⟶ j))) :
    W.colimitsOfShape J (c.ι.app ⊥) :=
  .mk' _ _ _ _ (isColimitConstCocone J (F.obj ⊥)) hc
    { app k := F.map (homOfLE bot_le)
      naturality _ _ _ := by
        dsimp
        rw [Category.id_comp, ← Functor.map_comp]
        rfl } h _ (by simp)

/-- The property that a morphism property `W` is stable under colimits
indexed by a category `J`. -/
class IsStableUnderColimitsOfShape : Prop where
  condition (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₁ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) : W φ

set_option backward.isDefEq.respectTransparency false in
lemma isStableUnderColimitsOfShape_iff_colimitsOfShape_le :
    W.IsStableUnderColimitsOfShape J ↔ W.colimitsOfShape J ≤ W := by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h.condition _ _ _ _ h₁ h₂ f hf _ (by simp)
  · rintro h
    constructor
    intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
    exact h _ (colimitsOfShape.mk' X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ)

variable {W J}

lemma colimitsOfShape_le [W.IsStableUnderColimitsOfShape J] :
    W.colimitsOfShape J ≤ W := by
  rwa [← isStableUnderColimitsOfShape_iff_colimitsOfShape_le]

protected lemma colimMap [W.IsStableUnderColimitsOfShape J] {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasColimit X] [HasColimit Y] (hf : W.functorCategory _ f) :
    W (colimMap f) :=
  colimitsOfShape_le _ (colimitsOfShape_colimMap _ hf)

set_option backward.isDefEq.respectTransparency false in
variable (C J) in
instance IsStableUnderColimitsOfShape.isomorphisms :
    (isomorphisms C).IsStableUnderColimitsOfShape J where
  condition F₁ F₂ c₁ c₂ h₁ h₂ f (_ : ∀ j, IsIso (f.app j)) φ hφ := by
    have := NatIso.isIso_of_isIso_app f
    exact ⟨h₂.desc (Cocone.mk _ (inv f ≫ c₁.ι)),
      h₁.hom_ext (fun j ↦ by simp [reassoc_of% (hφ j)]),
      h₂.hom_ext (by simp [hφ])⟩

end ColimitsOfShape

/-- The condition that a property of morphisms is stable by filtered colimits. -/
@[pp_with_univ]
class IsStableUnderFilteredColimits (W : MorphismProperty C) : Prop where
  isStableUnderColimitsOfShape (J : Type w') [Category.{w} J] [IsFiltered J] :
    W.IsStableUnderColimitsOfShape J := by infer_instance

attribute [instance] IsStableUnderFilteredColimits.isStableUnderColimitsOfShape

instance : IsStableUnderFilteredColimits.{w, w'} (isomorphisms C) where

section Coproducts

variable (W : MorphismProperty C)

/-- Given `W : MorphismProperty C`, this is class of morphisms that are
isomorphic to a coproduct of a family (indexed by some `J : Type w`) of maps in `W`. -/
@[pp_with_univ]
def coproducts : MorphismProperty C := ⨆ (J : Type w), W.colimitsOfShape (Discrete J)

lemma colimitsOfShape_le_coproducts (J : Type w) :
    W.colimitsOfShape (Discrete J) ≤ coproducts.{w} W :=
  le_iSup (f := fun (J : Type w) ↦ W.colimitsOfShape (Discrete J)) J

lemma coproducts_iff {X Y : C} (f : X ⟶ Y) :
    coproducts.{w} W f ↔ ∃ (J : Type w), W.colimitsOfShape (Discrete J) f := by
  simp only [coproducts, iSup_iff]

lemma coproducts_of_small {X Y : C} (f : X ⟶ Y) {J : Type w'}
    (hf : W.colimitsOfShape (Discrete J) f) [Small.{w} J] :
    coproducts.{w} W f := by
  rw [coproducts_iff]
  refine ⟨Shrink J, ?_⟩
  rwa [← W.colimitsOfShape_eq_of_equivalence (Discrete.equivalence (equivShrink.{w} J))]

lemma le_colimitsOfShape_punit : W ≤ W.colimitsOfShape (Discrete PUnit.{w + 1}) := by
  intro X₁ X₂ f hf
  have h := initialIsInitial (C := Discrete (PUnit.{w + 1}))
  let c₁ := coconeOfDiagramInitial (F := Discrete.functor (fun _ ↦ X₁)) h
  let c₂ := coconeOfDiagramInitial (F := Discrete.functor (fun _ ↦ X₂)) h
  have hc₁ : IsColimit c₁ := colimitOfDiagramInitial h _
  have hc₂ : IsColimit c₂ := colimitOfDiagramInitial h _
  have : hc₁.desc (Cocone.mk _ (Discrete.natTrans (fun _ ↦ by exact f) ≫ c₂.ι)) = f :=
    hc₁.hom_ext (fun x ↦ by
      obtain rfl : x = ⊥_ _ := by ext
      rw [IsColimit.fac]
      simp [c₁, c₂])
  rw [← this]
  exact ⟨_, _, _, _, _, hc₂, _, fun _ ↦ hf⟩

lemma le_coproducts : W ≤ coproducts.{w} W :=
  (le_colimitsOfShape_punit.{w} W).trans
    (colimitsOfShape_le_coproducts W PUnit.{w + 1})

lemma coproducts_monotone : Monotone (coproducts.{w} (C := C)) := by
  rintro W₁ W₂ h X Y f hf
  rw [coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact W₂.colimitsOfShape_le_coproducts J _
    (colimitsOfShape_monotone h _ _ hf)

end Coproducts

section Products

variable (W : MorphismProperty C)

/-- The property that a morphism property `W` is stable under products indexed by a type `J`. -/
abbrev IsStableUnderProductsOfShape (J : Type*) := W.IsStableUnderLimitsOfShape (Discrete J)

/-- The property that a morphism property `W` is stable under coproducts indexed by a type `J`. -/
abbrev IsStableUnderCoproductsOfShape (J : Type*) := W.IsStableUnderColimitsOfShape (Discrete J)

set_option backward.isDefEq.respectTransparency false in
lemma IsStableUnderProductsOfShape.mk (J : Type*) [W.RespectsIso]
    (hW : ∀ (X₁ X₂ : J → C) [HasProduct X₁] [HasProduct X₂]
      (f : ∀ j, X₁ j ⟶ X₂ j) (_ : ∀ (j : J), W (f j)),
      W (Limits.Pi.map f)) : W.IsStableUnderProductsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf α hα := by
    let φ := fun j => f.app (Discrete.mk j)
    have : HasLimit X₁ := ⟨c₁, hc₁⟩
    have : HasLimit X₂ := ⟨c₂, hc₂⟩
    have : HasProduct fun j ↦ X₁.obj (Discrete.mk j) :=
      hasLimit_of_iso (Discrete.natIso (fun j ↦ Iso.refl (X₁.obj j)))
    have : HasProduct fun j ↦ X₂.obj (Discrete.mk j) :=
      hasLimit_of_iso (Discrete.natIso (fun j ↦ Iso.refl (X₂.obj j)))
    have hf' := hW _ _ φ (fun j => hf (Discrete.mk j))
    refine (W.arrow_mk_iso_iff ?_).2 hf'
    refine Arrow.isoMk
      (IsLimit.conePointUniqueUpToIso hc₁ (limit.isLimit X₁) ≪≫ (Pi.isoLimit X₁).symm)
      (IsLimit.conePointUniqueUpToIso hc₂ (limit.isLimit X₂) ≪≫ (Pi.isoLimit _).symm) ?_
    apply limit.hom_ext
    rintro ⟨j⟩
    simp [φ, hα]

set_option backward.isDefEq.respectTransparency false in
lemma IsStableUnderCoproductsOfShape.mk (J : Type*) [W.RespectsIso]
    (hW : ∀ (X₁ X₂ : J → C) [HasCoproduct X₁] [HasCoproduct X₂]
      (f : ∀ j, X₁ j ⟶ X₂ j) (_ : ∀ (j : J), W (f j)),
      W (Limits.Sigma.map f)) : W.IsStableUnderCoproductsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf α hα := by
    let φ := fun j => f.app (Discrete.mk j)
    have : HasColimit X₁ := ⟨c₁, hc₁⟩
    have : HasColimit X₂ := ⟨c₂, hc₂⟩
    have : HasCoproduct fun j ↦ X₁.obj (Discrete.mk j) :=
      hasColimit_of_iso (Discrete.natIso (fun j ↦ Iso.refl (X₁.obj j)))
    have : HasCoproduct fun j ↦ X₂.obj (Discrete.mk j) :=
      hasColimit_of_iso (Discrete.natIso (fun j ↦ Iso.refl (X₂.obj j)))
    have hf' := hW _ _ φ (fun j => hf (Discrete.mk j))
    refine (W.arrow_mk_iso_iff ?_).1 hf'
    refine Arrow.isoMk
      ((Sigma.isoColimit _) ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit X₁) hc₁)
      ((Sigma.isoColimit _) ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit X₂) hc₂) ?_
    apply colimit.hom_ext
    rintro ⟨j⟩
    simp [φ, hα]

/-- The condition that a property of morphisms is stable by finite products. -/
class IsStableUnderFiniteProducts : Prop where
  isStableUnderProductsOfShape (J : Type) [Finite J] : W.IsStableUnderProductsOfShape J

attribute [instance] IsStableUnderFiniteProducts.isStableUnderProductsOfShape

/-- The condition that a property of morphisms is stable by finite coproducts. -/
class IsStableUnderFiniteCoproducts : Prop where
  isStableUnderCoproductsOfShape (J : Type) [Finite J] : W.IsStableUnderCoproductsOfShape J

attribute [instance] IsStableUnderFiniteCoproducts.isStableUnderCoproductsOfShape

/-- The condition that a property of morphisms is stable by coproducts. -/
@[pp_with_univ]
class IsStableUnderCoproducts : Prop where
  isStableUnderCoproductsOfShape (J : Type w) : W.IsStableUnderCoproductsOfShape J := by
    infer_instance

attribute [instance] IsStableUnderCoproducts.isStableUnderCoproductsOfShape

lemma coproducts_le [IsStableUnderCoproducts.{w} W] :
    coproducts.{w} W ≤ W := by
  intro X Y f hf
  rw [coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact colimitsOfShape_le _ hf

@[simp]
lemma coproducts_eq_self [IsStableUnderCoproducts.{w} W] :
    coproducts.{w} W = W :=
  le_antisymm W.coproducts_le W.le_coproducts

@[simp]
lemma coproducts_le_iff {P Q : MorphismProperty C} [IsStableUnderCoproducts.{w} Q] :
    coproducts.{w} P ≤ Q ↔ P ≤ Q := by
  constructor
  · exact le_trans P.le_coproducts
  · intro h
    exact le_trans (coproducts_monotone h) Q.coproducts_le

end Products

section Diagonal

variable [HasPullbacks C] {P : MorphismProperty C}

/-- For `P : MorphismProperty C`, `P.diagonal` is a morphism property that holds for `f : X ⟶ Y`
whenever `P` holds for `X ⟶ Y xₓ Y`. -/
def diagonal (P : MorphismProperty C) : MorphismProperty C := fun _ _ f => P (pullback.diagonal f)

theorem diagonal_iff {X Y : C} {f : X ⟶ Y} : P.diagonal f ↔ P (pullback.diagonal f) :=
  Iff.rfl

instance RespectsIso.diagonal [P.RespectsIso] : P.diagonal.RespectsIso := by
  apply RespectsIso.mk
  · introv H
    rwa [diagonal_iff, pullback.diagonal_comp, P.cancel_left_of_respectsIso,
      P.cancel_left_of_respectsIso, ← P.cancel_right_of_respectsIso _
        (pullback.map (e.hom ≫ f) (e.hom ≫ f) f f e.hom e.hom (𝟙 Z) (by simp) (by simp)),
      ← pullback.condition, P.cancel_left_of_respectsIso]
  · introv H
    delta diagonal
    rwa [pullback.diagonal_comp, P.cancel_right_of_respectsIso]

instance diagonal_isStableUnderComposition [P.IsStableUnderComposition] [RespectsIso P]
    [IsStableUnderBaseChange P] : P.diagonal.IsStableUnderComposition where
  comp_mem _ _ h₁ h₂ := by
    rw [diagonal_iff, pullback.diagonal_comp]
    exact P.comp_mem _ _ h₁
      (by simpa only [cancel_left_of_respectsIso] using P.pullback_snd _ _ h₂)

instance [P.ContainsIdentities] [P.RespectsIso] : P.diagonal.ContainsIdentities where
  id_mem _ := P.of_isIso _

instance [P.IsMultiplicative] [P.IsStableUnderBaseChange] : P.diagonal.IsMultiplicative where

set_option backward.isDefEq.respectTransparency false in
instance IsStableUnderBaseChange.diagonal [IsStableUnderBaseChange P] [P.RespectsIso] :
    P.diagonal.IsStableUnderBaseChange :=
  IsStableUnderBaseChange.mk'
    (by
      introv h
      rw [diagonal_iff, diagonal_pullback_fst, P.cancel_left_of_respectsIso,
        P.cancel_right_of_respectsIso]
      exact P.overPullbackMap f _ (by simpa))

lemma diagonal_isomorphisms : (isomorphisms C).diagonal = monomorphisms C :=
  ext _ _ fun _ _ _ ↦ pullback.isIso_diagonal_iff _

set_option backward.isDefEq.respectTransparency false in
/-- If `P` is multiplicative and stable under base change, having the of-postcomp property
w.r.t. `Q` is equivalent to `Q` implying `P` on the diagonal. -/
lemma hasOfPostcompProperty_iff_le_diagonal [P.IsStableUnderBaseChange]
    [P.IsMultiplicative] {Q : MorphismProperty C} [Q.IsStableUnderBaseChange] :
    P.HasOfPostcompProperty Q ↔ Q ≤ P.diagonal := by
  refine ⟨fun hP X Y f hf ↦ ?_, fun hP ↦ ⟨fun {Y X S} g f hf hcomp ↦ ?_⟩⟩
  · exact hP.of_postcomp _ _ (Q.pullback_fst _ _ hf) (by simpa using P.id_mem X)
  · set gr : Y ⟶ pullback (g ≫ f) f := pullback.lift (𝟙 Y) g (by simp)
    have : g = gr ≫ pullback.snd _ _ := by simp [gr]
    rw [this]
    apply P.comp_mem
    · exact P.of_isPullback (pullback_lift_diagonal_isPullback g f) (hP _ hf)
    · exact P.pullback_snd _ _ hcomp

end Diagonal

section Universally

/-- `P.universally` holds for a morphism `f : X ⟶ Y` iff `P` holds for all `X ×[Y] Y' ⟶ Y'`. -/
def universally (P : MorphismProperty C) : MorphismProperty C := fun X Y f =>
  ∀ ⦃X' Y' : C⦄ (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y) (f' : X' ⟶ Y') (_ : IsPullback f' i₁ i₂ f), P f'

instance universally_respectsIso (P : MorphismProperty C) : P.universally.RespectsIso := by
  apply RespectsIso.mk
  · intro X Y Z e f hf X' Z' i₁ i₂ f' H
    have : IsPullback (𝟙 _) (i₁ ≫ e.hom) i₁ e.inv :=
      IsPullback.of_horiz_isIso
        ⟨by rw [Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
    exact hf _ _ _
      (by simpa only [Iso.inv_hom_id_assoc, Category.id_comp] using this.paste_horiz H)
  · intro X Y Z e f hf X' Z' i₁ i₂ f' H
    have : IsPullback (𝟙 _) i₂ (i₂ ≫ e.inv) e.inv :=
      IsPullback.of_horiz_isIso ⟨Category.id_comp _⟩
    exact hf _ _ _ (by simpa only [Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.comp_id] using H.paste_horiz this)

instance universally_isStableUnderBaseChange (P : MorphismProperty C) :
    P.universally.IsStableUnderBaseChange where
  of_isPullback H h₁ _ _ _ _ _ H' := h₁ _ _ _ (H'.paste_vert H.flip)

instance IsStableUnderComposition.universally [HasPullbacks C] (P : MorphismProperty C)
    [hP : P.IsStableUnderComposition] : P.universally.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg X' Z' i₁ i₂ f' H := by
    have := pullback.lift_fst _ _ (H.w.trans (Category.assoc _ _ _).symm)
    rw [← this] at H ⊢
    apply P.comp_mem _ _ _ (hg _ _ _ <| IsPullback.of_hasPullback _ _)
    exact hf _ _ _ (H.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback i₂ g))

theorem universally_le (P : MorphismProperty C) : P.universally ≤ P := by
  intro X Y f hf
  exact hf (𝟙 _) (𝟙 _) _ (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩)

theorem universally_inf (P Q : MorphismProperty C) :
    (P ⊓ Q).universally = P.universally ⊓ Q.universally := by
  ext X Y f
  change _ ↔ _ ∧ _
  simp_rw [universally, ← forall_and]
  rfl

theorem universally_eq_iff {P : MorphismProperty C} :
    P.universally = P ↔ P.IsStableUnderBaseChange :=
  ⟨(· ▸ P.universally_isStableUnderBaseChange),
    fun hP ↦ P.universally_le.antisymm fun _ _ _ hf _ _ _ _ _ H => hP.of_isPullback H.flip hf⟩

theorem IsStableUnderBaseChange.universally_eq {P : MorphismProperty C}
    [hP : P.IsStableUnderBaseChange] : P.universally = P := universally_eq_iff.mpr hP

theorem universally_mono : Monotone (universally : MorphismProperty C → MorphismProperty C) :=
  fun _ _ h _ _ _ h₁ _ _ _ _ _ H => h _ (h₁ _ _ _ H)

lemma universally_mk' (P : MorphismProperty C) [P.RespectsIso] {X Y : C} (g : X ⟶ Y)
    (H : ∀ {T : C} (f : T ⟶ Y) [HasPullback f g], P (pullback.fst f g)) :
    universally P g := by
  introv X' h
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst, P.cancel_left_of_respectsIso]
  exact H ..

end Universally

variable (P : MorphismProperty C)

/-- `P` has pullbacks if for every `f` satisfying `P`, pullbacks of arbitrary morphisms along `f`
exist. -/
protected class HasPullbacks : Prop where
  hasPullback {X Y S : C} {f : X ⟶ S} (g : Y ⟶ S) : P f → HasPullback f g := by infer_instance

instance [HasPullbacks C] : P.HasPullbacks where

alias hasPullback := HasPullbacks.hasPullback

instance [P.HasPullbacks] {X Y : C} {f : X ⟶ Y} : P.HasPullbacksAlong f where
  hasPullback _ := hasPullback _

/-- `P` has pushouts if for every `f` satisfying `P`, pushouts of arbitrary morphisms along `f`
exist. -/
protected class HasPushouts : Prop where
  hasPushout {X Y S : C} {f : S ⟶ X} (g : S ⟶ Y) : P f → HasPushout f g := by infer_instance

instance [HasPushouts C] : P.HasPushouts where

alias hasPushout := HasPushouts.hasPushout

instance [P.HasPushouts] {X Y : C} {f : X ⟶ Y} : P.HasPushoutsAlong f where
  hasPushout _ := hasPushout _

instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] : P.HasPullbacksAlong (f ≫ g) where
  hasPullback h p :=
    have : HasPullback h g := HasPullbacksAlong.hasPullback h p
    have : HasPullback (pullback.snd h g) f := HasPullbacksAlong.hasPullback (pullback.snd h g)
      (P.pullback_snd h g p)
    IsPullback.hasPullback (IsPullback.paste_horiz (IsPullback.of_hasPullback
      (pullback.snd h g) f) (IsPullback.of_hasPullback h g))

instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g] [P.HasPullbacksAlong g] :
    P.IsStableUnderBaseChangeAlong (f ≫ g) where
  of_isPullback {_ _ _ _ p} pb hp :=
    have : HasPullback p g := HasPullbacksAlong.hasPullback p hp
    have right := IsPullback.of_hasPullback p g
    IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_right' pb right)
      (IsStableUnderBaseChangeAlong.of_isPullback right hp)

instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderCobaseChangeAlong f]
    [P.HasPushoutsAlong f] [P.HasPushoutsAlong g] : P.HasPushoutsAlong (f ≫ g) where
  hasPushout h p :=
    have : HasPushout h f := HasPushoutsAlong.hasPushout h p
    have : HasPushout (pushout.inr h f) g := HasPushoutsAlong.hasPushout _
      (P.pushout_inr _ _ p)
    IsPushout.hasPushout (IsPushout.paste_vert (.of_hasPushout _ _) (.of_hasPushout _ _))

instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderCobaseChangeAlong f]
    [P.IsStableUnderCobaseChangeAlong g] [P.HasPushoutsAlong f] :
    P.IsStableUnderCobaseChangeAlong (f ≫ g) where
  of_isPushout {_ _ _ _ p} pb hp :=
    have : HasPushout p f := HasPushoutsAlong.hasPushout p hp
    have right := IsPushout.of_hasPushout p f
    IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_left' pb right.flip)
      (IsStableUnderCobaseChangeAlong.of_isPushout right.flip hp)

end MorphismProperty

end CategoryTheory
