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
`IsStableUnderFiniteProducts`.

-/

universe v u

namespace CategoryTheory

open Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- A morphism property is `IsStableUnderBaseChange` if the base change of such a morphism
still falls in the class. -/
class IsStableUnderBaseChange (P : MorphismProperty C) : Prop where
  of_isPullback {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : P g) : P g'

/-- A morphism property is `IsStableUnderCobaseChange` if the cobase change of such a morphism
still falls in the class. -/
class IsStableUnderCobaseChange (P : MorphismProperty C) : Prop where
  of_isPushout {A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
    (sq : IsPushout g f f' g') (hf : P f) : P f'

lemma of_isPullback {P : MorphismProperty C} [P.IsStableUnderBaseChange]
    {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : P g) : P g' :=
  IsStableUnderBaseChange.of_isPullback sq hg

/-- Alternative constructor for `IsStableUnderBaseChange`. -/
theorem IsStableUnderBaseChange.mk' {P : MorphismProperty C} [RespectsIso P]
    (hP₂ : ∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (_ : P g),
      P (pullback.fst f g)) :
    IsStableUnderBaseChange P where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    haveI : HasPullback f g := sq.flip.hasPullback
    let e := sq.flip.isoPullback
    rw [← P.cancel_left_of_respectsIso e.inv, sq.flip.isoPullback_inv_fst]
    exact hP₂ _ _ _ f g hg

instance IsStableUnderBaseChange.isomorphisms :
    (isomorphisms C).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ f g _ _} h hg :=
    have : IsIso g := hg
    have := hasPullback_of_left_iso g f
    h.isoPullback_hom_snd ▸ inferInstanceAs (IsIso _)

variable (C) in
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

instance (priority := 900) IsStableUnderBaseChange.respectsIso {P : MorphismProperty C}
    [IsStableUnderBaseChange P] : RespectsIso P := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e
  exact of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))

theorem pullback_fst {P : MorphismProperty C} [IsStableUnderBaseChange P]
    {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (H : P g) :
    P (pullback.fst f g) :=
  of_isPullback (IsPullback.of_hasPullback f g).flip H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.fst := pullback_fst

theorem pullback_snd {P : MorphismProperty C} [IsStableUnderBaseChange P]
    {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (H : P f) :
    P (pullback.snd f g) :=
  of_isPullback (IsPullback.of_hasPullback f g) H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.snd := pullback_snd

theorem baseChange_obj [HasPullbacks C] {P : MorphismProperty C}
    [IsStableUnderBaseChange P] {S S' : C} (f : S' ⟶ S) (X : Over S) (H : P X.hom) :
    P ((Over.pullback f).obj X).hom :=
  pullback_snd X.hom f H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.baseChange_obj := baseChange_obj

theorem baseChange_map [HasPullbacks C] {P : MorphismProperty C}
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

theorem pullback_map [HasPullbacks C] {P : MorphismProperty C}
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

lemma of_isPushout {P : MorphismProperty C} [P.IsStableUnderCobaseChange]
    {A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
    (sq : IsPushout g f f' g') (hf : P f) : P f' :=
  IsStableUnderCobaseChange.of_isPushout sq hf

/-- An alternative constructor for `IsStableUnderCobaseChange`. -/
theorem IsStableUnderCobaseChange.mk' {P : MorphismProperty C} [RespectsIso P]
    (hP₂ : ∀ (A B A' : C) (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (_ : P f),
      P (pushout.inr f g)) :
    IsStableUnderCobaseChange P where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    haveI : HasPushout f g := sq.flip.hasPushout
    let e := sq.flip.isoPushout
    rw [← P.cancel_right_of_respectsIso _ e.hom, sq.flip.inr_isoPushout_hom]
    exact hP₂ _ _ _ f g hf

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

instance IsStableUnderCobaseChange.respectsIso {P : MorphismProperty C}
    [IsStableUnderCobaseChange P] : RespectsIso P :=
  RespectsIso.of_respects_arrow_iso _ fun _ _ e ↦
    of_isPushout (IsPushout.of_horiz_isIso (CommSq.mk e.hom.w))

theorem pushout_inl {P : MorphismProperty C} [IsStableUnderCobaseChange P]
    {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (H : P g) :
    P (pushout.inl f g) :=
  of_isPushout (IsPushout.of_hasPushout f g) H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.inl := pushout_inl

theorem pushout_inr {P : MorphismProperty C} [IsStableUnderCobaseChange P]
    {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (H : P f) : P (pushout.inr f g) :=
  of_isPushout (IsPushout.of_hasPushout f g).flip H

@[deprecated (since := "2024-11-06")] alias IsStableUnderBaseChange.inr := pushout_inr

instance IsStableUnderCobaseChange.op {P : MorphismProperty C} [IsStableUnderCobaseChange P] :
    IsStableUnderBaseChange P.op where
  of_isPullback sq hg := P.of_isPushout sq.unop hg

instance IsStableUnderCobaseChange.unop {P : MorphismProperty Cᵒᵖ} [IsStableUnderCobaseChange P] :
    IsStableUnderBaseChange P.unop where
  of_isPullback sq hg := P.of_isPushout sq.op hg

instance IsStableUnderBaseChange.op {P : MorphismProperty C} [IsStableUnderBaseChange P] :
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

section

variable (W : MorphismProperty C)

/-- The property that a morphism property `W` is stable under limits
indexed by a category `J`. -/
def IsStableUnderLimitsOfShape (J : Type*) [Category J] : Prop :=
  ∀ (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f),
      W (h₂.lift (Cone.mk _ (c₁.π ≫ f)))

variable {W}

lemma IsStableUnderLimitsOfShape.lim_map {J : Type*} [Category J]
    (hW : W.IsStableUnderLimitsOfShape J) {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasLimitsOfShape J C] (hf : W.functorCategory _ f) :
    W (lim.map f) :=
  hW X Y _ _ (limit.isLimit X) (limit.isLimit Y) f hf

variable (W)

/-- The property that a morphism property `W` is stable under products indexed by a type `J`. -/
abbrev IsStableUnderProductsOfShape (J : Type*) := W.IsStableUnderLimitsOfShape (Discrete J)

lemma IsStableUnderProductsOfShape.mk (J : Type*)
    [W.RespectsIso] [HasProductsOfShape J C]
    (hW : ∀ (X₁ X₂ : J → C) (f : ∀ j, X₁ j ⟶ X₂ j) (_ : ∀ (j : J), W (f j)),
      W (Limits.Pi.map f)) : W.IsStableUnderProductsOfShape J := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf
  let φ := fun j => f.app (Discrete.mk j)
  have hf' := hW _ _ φ (fun j => hf (Discrete.mk j))
  refine (W.arrow_mk_iso_iff ?_).2 hf'
  refine Arrow.isoMk
    (IsLimit.conePointUniqueUpToIso hc₁ (limit.isLimit X₁) ≪≫ (Pi.isoLimit _).symm)
    (IsLimit.conePointUniqueUpToIso hc₂ (limit.isLimit X₂) ≪≫ (Pi.isoLimit _).symm) ?_
  apply limit.hom_ext
  rintro ⟨j⟩
  simp

/-- The condition that a property of morphisms is stable by finite products. -/
class IsStableUnderFiniteProducts : Prop where
  isStableUnderProductsOfShape (J : Type) [Finite J] : W.IsStableUnderProductsOfShape J

lemma isStableUnderProductsOfShape_of_isStableUnderFiniteProducts
    (J : Type) [Finite J] [W.IsStableUnderFiniteProducts] :
    W.IsStableUnderProductsOfShape J :=
  IsStableUnderFiniteProducts.isStableUnderProductsOfShape J

end

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
