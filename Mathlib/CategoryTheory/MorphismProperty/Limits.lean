/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.MorphismProperty.Composition

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

universe w v u

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

instance : P.pushouts.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨A, B, p, f, g, hp, h⟩
    exact ⟨A, B, p, f ≫ e.hom.left, g ≫ e.hom.right, hp,
      IsPushout.paste_horiz h (IsPushout.of_horiz_isIso ⟨e.hom.w⟩)⟩)

instance : P.pullbacks.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨X, Y, p, f, g, hp, h⟩
    exact ⟨X, Y, p, e.inv.left ≫ f, e.inv.right ≫ g, hp,
      IsPullback.paste_horiz (IsPullback.of_horiz_isIso ⟨e.inv.w⟩) h⟩)

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

variable {P} in
lemma of_isPullback [P.IsStableUnderBaseChange]
    {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : P g) : P g' :=
  IsStableUnderBaseChange.of_isPullback sq hg

lemma isStableUnderBaseChange_iff_pullbacks_le :
    P.IsStableUnderBaseChange ↔ P.pullbacks ≤ P := by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPullback h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

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

variable (C)

instance IsStableUnderBaseChange.isomorphisms :
    (isomorphisms C).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ f g _ _} h hg :=
    have : IsIso g := hg
    have := hasPullback_of_left_iso g f
    h.isoPullback_hom_snd ▸ inferInstanceAs (IsIso _)

instance IsStableUnderBaseChange.monomorphisms :
    (monomorphisms C).IsStableUnderBaseChange where
  of_isPullback {X Y Y' S f g f' g'} h hg := by
    have : Mono g := hg
    constructor
    intro Z f₁ f₂ h₁₂
    apply PullbackCone.IsLimit.hom_ext h.isLimit
    · rw [← cancel_mono g]
      dsimp
      simp only [Category.assoc, h.w, reassoc_of% h₁₂]
    · exact h₁₂

variable {C P}

instance (priority := 900) IsStableUnderBaseChange.respectsIso
    [IsStableUnderBaseChange P] : RespectsIso P := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e
  exact of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))

theorem pullback_fst [IsStableUnderBaseChange P]
    {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (H : P g) :
    P (pullback.fst f g) :=
  of_isPullback (IsPullback.of_hasPullback f g).flip H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.fst := pullback_fst

theorem pullback_snd [IsStableUnderBaseChange P]
    {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (H : P f) :
    P (pullback.snd f g) :=
  of_isPullback (IsPullback.of_hasPullback f g) H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.snd := pullback_snd

theorem baseChange_obj [HasPullbacks C]
    [IsStableUnderBaseChange P] {S S' : C} (f : S' ⟶ S) (X : Over S) (H : P X.hom) :
    P ((Over.pullback f).obj X).hom :=
  pullback_snd X.hom f H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.baseChange_obj := baseChange_obj

theorem baseChange_map [HasPullbacks C]
    [IsStableUnderBaseChange P] {S S' : C} (f : S' ⟶ S) {X Y : Over S} (g : X ⟶ Y)
    (H : P g.left) : P ((Over.pullback f).map g).left := by
  let e :=
    pullbackRightPullbackFstIso Y.hom f g.left ≪≫
      pullback.congrHom (g.w.trans (Category.comp_id _)) rfl
  have : e.inv ≫ (pullback.snd _ _) = ((Over.pullback f).map g).left := by
    ext <;> dsimp [e] <;> simp
  rw [← this, P.cancel_left_of_respectsIso]
  exact pullback_snd _ _ H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.baseChange_map := baseChange_map

theorem pullback_map [HasPullbacks C]
    [IsStableUnderBaseChange P] [P.IsStableUnderComposition] {S X X' Y Y' : C} {f : X ⟶ S}
    {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
    (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂)) := by
  have :
    pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂) =
      ((pullbackSymmetry _ _).hom ≫
          ((Over.pullback _).map (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g')).left) ≫
        (pullbackSymmetry _ _).hom ≫
          ((Over.pullback g').map (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f')).left := by
    ext <;> dsimp <;> simp
  rw [this]
  apply P.comp_mem <;> rw [P.cancel_left_of_respectsIso]
  exacts [baseChange_map _ (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g') h₂,
    baseChange_map _ (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f') h₁]

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.pullback_map := pullback_map

lemma of_isPushout [P.IsStableUnderCobaseChange]
    {A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
    (sq : IsPushout g f f' g') (hf : P f) : P f' :=
  IsStableUnderCobaseChange.of_isPushout sq hf

lemma isStableUnderCobaseChange_iff_pushouts_le :
    P.IsStableUnderCobaseChange ↔ P.pushouts ≤ P := by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPushout h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

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

instance IsStableUnderCobaseChange.isomorphisms :
    (isomorphisms C).IsStableUnderCobaseChange where
  of_isPushout {_ _ _ _ f g _ _} h (_ : IsIso f) :=
    have := hasPushout_of_right_iso g f
    h.inl_isoPushout_inv ▸ inferInstanceAs (IsIso _)

variable (C) in
instance IsStableUnderCobaseChange.epimorphisms :
    (epimorphisms C).IsStableUnderCobaseChange where
  of_isPushout {X Y Y' S f g f' g'} h hf := by
    have : Epi f := hf
    constructor
    intro Z f₁ f₂ h₁₂
    apply PushoutCocone.IsColimit.hom_ext h.isColimit
    · exact h₁₂
    · rw [← cancel_epi f]
      dsimp
      simp only [← reassoc_of% h.w, h₁₂]

instance IsStableUnderCobaseChange.respectsIso
    [IsStableUnderCobaseChange P] : RespectsIso P :=
  RespectsIso.of_respects_arrow_iso _ fun _ _ e ↦
    of_isPushout (IsPushout.of_horiz_isIso (CommSq.mk e.hom.w))

theorem pushout_inl [IsStableUnderCobaseChange P]
    {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (H : P g) :
    P (pushout.inl f g) :=
  of_isPushout (IsPushout.of_hasPushout f g) H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.inl := pushout_inl

theorem pushout_inr [IsStableUnderCobaseChange P]
    {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (H : P f) : P (pushout.inr f g) :=
  of_isPushout (IsPushout.of_hasPushout f g).flip H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.inr := pushout_inr

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

end

section LimitsOfShape

variable (W : MorphismProperty C) (J : Type*) [Category J]

/-- The class of morphisms in `C` that are limits of shape `J` of
natural transformations involving morphisms in `W`. -/
inductive limitsOfShape : MorphismProperty C
  | mk (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) :
      limitsOfShape (h₂.lift (Cone.mk _ (c₁.π ≫ f)))

instance : (W.limitsOfShape J).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : g ≫ e₂.inv = e₁.inv ≫ h₂.lift (Cone.mk _ (c₁.π ≫ f)) :=
      e.inv.w.symm
    let c₁' : Cone X₁ := { pt := Y₁, π := (Functor.const _).map e₁.inv ≫ c₁.π }
    let c₂' : Cone X₂ := { pt := Y₂, π := (Functor.const _).map e₂.inv ≫ c₂.π }
    have h₁' : IsLimit c₁' := IsLimit.ofIsoLimit h₁ (Cones.ext e₁)
    have h₂' : IsLimit c₂' := IsLimit.ofIsoLimit h₂ (Cones.ext e₂)
    obtain hg : h₂'.lift (Cone.mk _ (c₁'.π ≫ f)) = g :=
      h₂'.hom_ext (fun j ↦ by
        rw [h₂'.fac]
        simp [reassoc_of% fac, c₁', c₂'])
    rw [← hg]
    exact ⟨_, _, _, _, h₁', _, _, hf⟩)

variable {J} in
lemma limitsOfShape_limMap {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasLimit X] [HasLimit Y] (hf : W.functorCategory _ f) :
    W.limitsOfShape J (limMap f) :=
  ⟨_, _, _, _, limit.isLimit X, _, _, hf⟩

/-- The property that a morphism property `W` is stable under limits
indexed by a category `J`. -/
def IsStableUnderLimitsOfShape : Prop :=
  ∀ (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f),
      W (h₂.lift (Cone.mk _ (c₁.π ≫ f)))

lemma isStableUnderLimitsOfShape_iff_limitsOfShape_le :
    W.IsStableUnderLimitsOfShape J ↔ W.limitsOfShape J ≤ W := by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h _ _ _ _ h₁ h₂ f hf
  · intro h _ _ _ _ h₁ h₂ f hf
    exact h _ ⟨_, _, _, _, h₁, _, _, hf⟩

variable {W J}

lemma IsStableUnderLimitsOfShape.limitsOfShape_le
    (hW : W.IsStableUnderLimitsOfShape J) : W.limitsOfShape J ≤ W :=
  (W.isStableUnderLimitsOfShape_iff_limitsOfShape_le J).1 hW

lemma IsStableUnderLimitsOfShape.limMap
    (hW : W.IsStableUnderLimitsOfShape J) {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasLimit X] [HasLimit Y] (hf : W.functorCategory _ f) :
    W (limMap f) :=
  hW.limitsOfShape_le _ (limitsOfShape_limMap _ _ hf)

end LimitsOfShape

section ColimitsOfShape

variable (W : MorphismProperty C) (J : Type*) [Category J]

/-- The class of morphisms in `C` that are colimits of shape `J` of
natural transformations involving morphisms in `W`. -/
inductive colimitsOfShape : MorphismProperty C
  | mk (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) :
      colimitsOfShape (h₁.desc (Cocone.mk _ (f ≫ c₂.ι)))

instance : (W.colimitsOfShape J).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : e₁.hom ≫ g = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) ≫ e₂.hom := e.hom.w
    let c₁' : Cocone X₁ := { pt := Y₁, ι := c₁.ι ≫ (Functor.const _).map e₁.hom}
    let c₂' : Cocone X₂ := { pt := Y₂, ι := c₂.ι ≫ (Functor.const _).map e₂.hom}
    have h₁' : IsColimit c₁' := IsColimit.ofIsoColimit h₁ (Cocones.ext e₁)
    have h₂' : IsColimit c₂' := IsColimit.ofIsoColimit h₂ (Cocones.ext e₂)
    obtain hg : h₁'.desc (Cocone.mk _ (f ≫ c₂'.ι)) = g :=
      h₁'.hom_ext (fun j ↦ by
        rw [h₁'.fac]
        simp [fac, c₁', c₂'])
    rw [← hg]
    exact ⟨_, _, _, _, _, h₂', _, hf⟩)

variable {J} in
lemma colimitsOfShape_colimMap {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasColimit X] [HasColimit Y] (hf : W.functorCategory _ f) :
    W.colimitsOfShape J (colimMap f) :=
  ⟨_, _, _, _, _, colimit.isColimit Y, _, hf⟩

/-- The property that a morphism property `W` is stable under colimits
indexed by a category `J`. -/
def IsStableUnderColimitsOfShape : Prop :=
  ∀ (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f),
      W (h₁.desc (Cocone.mk _ (f ≫ c₂.ι)))

lemma isStableUnderColimitsOfShape_iff_colimitsOfShape_le :
    W.IsStableUnderColimitsOfShape J ↔ W.colimitsOfShape J ≤ W := by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h _ _ _ _ h₁ h₂ f hf
  · intro h _ _ _ _ h₁ h₂ f hf
    exact h _ ⟨_, _, _, _, _, h₂, _, hf⟩

variable {W J}

lemma IsStableUnderColimitsOfShape.colimitsOfShape_le
    (hW : W.IsStableUnderColimitsOfShape J) : W.colimitsOfShape J ≤ W :=
  (W.isStableUnderColimitsOfShape_iff_colimitsOfShape_le J).1 hW

lemma IsStableUnderColimitsOfShape.colimMap
    (hW : W.IsStableUnderColimitsOfShape J) {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasColimit X] [HasColimit Y] (hf : W.functorCategory _ f) :
    W (colimMap f) :=
  hW.colimitsOfShape_le _ (colimitsOfShape_colimMap _ _ hf)

end ColimitsOfShape

section Coproducts

variable (W : MorphismProperty C)

/-- Given `W : MorphismProperty C`, this is class of morphisms that are
isomorphic to a coproduct of a family (indexed by some `J : Type w`) of maps in `W`. -/
def coproducts : MorphismProperty C := ⨆ (J : Type w), W.colimitsOfShape (Discrete J)

lemma colimitsOfShape_le_coproducts (J : Type w) :
    W.colimitsOfShape (Discrete J) ≤ coproducts.{w} W :=
  le_iSup (f := fun (J : Type w) ↦ W.colimitsOfShape (Discrete J)) J

lemma coproducts_iff {X Y : C} (f : X ⟶ Y) :
    coproducts.{w} W f ↔ ∃ (J : Type w), W.colimitsOfShape (Discrete J) f := by
  simp only [coproducts, iSup_iff]

end Coproducts

section Products

variable (W : MorphismProperty C)

/-- The property that a morphism property `W` is stable under products indexed by a type `J`. -/
abbrev IsStableUnderProductsOfShape (J : Type*) := W.IsStableUnderLimitsOfShape (Discrete J)

/-- The property that a morphism property `W` is stable under coproducts indexed by a type `J`. -/
abbrev IsStableUnderCoproductsOfShape (J : Type*) := W.IsStableUnderColimitsOfShape (Discrete J)

lemma IsStableUnderProductsOfShape.mk (J : Type*) [W.RespectsIso]
    (hW : ∀ (X₁ X₂ : J → C) [HasProduct X₁] [HasProduct X₂]
      (f : ∀ j, X₁ j ⟶ X₂ j) (_ : ∀ (j : J), W (f j)),
      W (Limits.Pi.map f)) : W.IsStableUnderProductsOfShape J := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf
  let φ := fun j => f.app (Discrete.mk j)
  have : HasLimit X₁ := ⟨c₁, hc₁⟩
  have : HasLimit X₂ := ⟨c₂, hc₂⟩
  have : HasProduct fun j ↦ X₁.obj (Discrete.mk j) :=
    hasLimitOfIso (Discrete.natIso (fun j ↦ Iso.refl (X₁.obj j)))
  have : HasProduct fun j ↦ X₂.obj (Discrete.mk j) :=
    hasLimitOfIso (Discrete.natIso (fun j ↦ Iso.refl (X₂.obj j)))
  have hf' := hW _ _ φ (fun j => hf (Discrete.mk j))
  refine (W.arrow_mk_iso_iff ?_).2 hf'
  refine Arrow.isoMk
    (IsLimit.conePointUniqueUpToIso hc₁ (limit.isLimit X₁) ≪≫ (Pi.isoLimit X₁).symm)
    (IsLimit.conePointUniqueUpToIso hc₂ (limit.isLimit X₂) ≪≫ (Pi.isoLimit _).symm) ?_
  apply limit.hom_ext
  rintro ⟨j⟩
  simp [φ]

lemma IsStableUnderCoproductsOfShape.mk (J : Type*) [W.RespectsIso]
    (hW : ∀ (X₁ X₂ : J → C) [HasCoproduct X₁] [HasCoproduct X₂]
      (f : ∀ j, X₁ j ⟶ X₂ j) (_ : ∀ (j : J), W (f j)),
      W (Limits.Sigma.map f)) : W.IsStableUnderCoproductsOfShape J := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf
  let φ := fun j => f.app (Discrete.mk j)
  have : HasColimit X₁ := ⟨c₁, hc₁⟩
  have : HasColimit X₂ := ⟨c₂, hc₂⟩
  have : HasCoproduct fun j ↦ X₁.obj (Discrete.mk j) :=
    hasColimitOfIso (Discrete.natIso (fun j ↦ Iso.refl (X₁.obj j)))
  have : HasCoproduct fun j ↦ X₂.obj (Discrete.mk j) :=
    hasColimitOfIso (Discrete.natIso (fun j ↦ Iso.refl (X₂.obj j)))
  have hf' := hW _ _ φ (fun j => hf (Discrete.mk j))
  refine (W.arrow_mk_iso_iff ?_).1 hf'
  refine Arrow.isoMk
    ((Sigma.isoColimit _) ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit X₁) hc₁)
    ((Sigma.isoColimit _) ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit X₂) hc₂) ?_
  apply colimit.hom_ext
  rintro ⟨j⟩
  simp [φ]

/-- The condition that a property of morphisms is stable by finite products. -/
class IsStableUnderFiniteProducts : Prop where
  isStableUnderProductsOfShape (J : Type) [Finite J] : W.IsStableUnderProductsOfShape J

/-- The condition that a property of morphisms is stable by finite coproducts. -/
class IsStableUnderFiniteCoproducts : Prop where
  isStableUnderCoproductsOfShape (J : Type) [Finite J] : W.IsStableUnderCoproductsOfShape J

lemma isStableUnderProductsOfShape_of_isStableUnderFiniteProducts
    (J : Type) [Finite J] [W.IsStableUnderFiniteProducts] :
    W.IsStableUnderProductsOfShape J :=
  IsStableUnderFiniteProducts.isStableUnderProductsOfShape J

lemma isStableUnderCoproductsOfShape_of_isStableUnderFiniteCoproducts
    (J : Type) [Finite J] [W.IsStableUnderFiniteCoproducts] :
    W.IsStableUnderCoproductsOfShape J :=
  IsStableUnderFiniteCoproducts.isStableUnderCoproductsOfShape J

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

instance IsStableUnderBaseChange.diagonal [IsStableUnderBaseChange P] [P.RespectsIso] :
    P.diagonal.IsStableUnderBaseChange :=
  IsStableUnderBaseChange.mk'
    (by
      introv h
      rw [diagonal_iff, diagonal_pullback_fst, P.cancel_left_of_respectsIso,
        P.cancel_right_of_respectsIso]
      exact P.baseChange_map f _ (by simpa))

lemma diagonal_isomorphisms : (isomorphisms C).diagonal = monomorphisms C :=
  ext _ _ fun _ _ _ ↦ pullback.isIso_diagonal_iff _

/-- If `P` is multiplicative and stable under base change, having the of-postcomp property
wrt. `Q` is equivalent to `Q` implying `P` on the diagonal. -/
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
  show _ ↔ _ ∧ _
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

end Universally

end MorphismProperty

end CategoryTheory
