/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Relation of morphism properties with limits

The following predicates are introduces for morphism properties `P`:
* `StableUnderBaseChange`: `P` is stable under base change if in all pullback
  squares, the left map satisfies `P` if the right map satisfies it.
* `StableUnderCobaseChange`: `P` is stable under cobase change if in all pushout
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

/-- A morphism property is `StableUnderBaseChange` if the base change of such a morphism
still falls in the class. -/
def StableUnderBaseChange (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Y' S : C⦄ ⦃f : X ⟶ S⦄ ⦃g : Y ⟶ S⦄ ⦃f' : Y' ⟶ Y⦄ ⦃g' : Y' ⟶ X⦄ (_ : IsPullback f' g' g f)
    (_ : P g), P g'
#align category_theory.morphism_property.stable_under_base_change CategoryTheory.MorphismProperty.StableUnderBaseChange

/-- A morphism property is `StableUnderCobaseChange` if the cobase change of such a morphism
still falls in the class. -/
def StableUnderCobaseChange (P : MorphismProperty C) : Prop :=
  ∀ ⦃A A' B B' : C⦄ ⦃f : A ⟶ A'⦄ ⦃g : A ⟶ B⦄ ⦃f' : B ⟶ B'⦄ ⦃g' : A' ⟶ B'⦄ (_ : IsPushout g f f' g')
    (_ : P f), P f'
#align category_theory.morphism_property.stable_under_cobase_change CategoryTheory.MorphismProperty.StableUnderCobaseChange

theorem StableUnderBaseChange.mk {P : MorphismProperty C} [HasPullbacks C] (hP₁ : RespectsIso P)
    (hP₂ : ∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) (_ : P g), P (pullback.fst : pullback f g ⟶ X)) :
    StableUnderBaseChange P := fun X Y Y' S f g f' g' sq hg => by
  let e := sq.flip.isoPullback
  rw [← hP₁.cancel_left_isIso e.inv, sq.flip.isoPullback_inv_fst]
  exact hP₂ _ _ _ f g hg
#align category_theory.morphism_property.stable_under_base_change.mk CategoryTheory.MorphismProperty.StableUnderBaseChange.mk

theorem StableUnderBaseChange.respectsIso {P : MorphismProperty C} (hP : StableUnderBaseChange P) :
    RespectsIso P := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e
  exact hP (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
#align category_theory.morphism_property.stable_under_base_change.respects_iso CategoryTheory.MorphismProperty.StableUnderBaseChange.respectsIso

theorem StableUnderBaseChange.fst {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (H : P g) :
    P (pullback.fst : pullback f g ⟶ X) :=
  hP (IsPullback.of_hasPullback f g).flip H
#align category_theory.morphism_property.stable_under_base_change.fst CategoryTheory.MorphismProperty.StableUnderBaseChange.fst

theorem StableUnderBaseChange.snd {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (H : P f) :
    P (pullback.snd : pullback f g ⟶ Y) :=
  hP (IsPullback.of_hasPullback f g) H
#align category_theory.morphism_property.stable_under_base_change.snd CategoryTheory.MorphismProperty.StableUnderBaseChange.snd

theorem StableUnderBaseChange.baseChange_obj [HasPullbacks C] {P : MorphismProperty C}
    (hP : StableUnderBaseChange P) {S S' : C} (f : S' ⟶ S) (X : Over S) (H : P X.hom) :
    P ((Over.baseChange f).obj X).hom :=
  hP.snd X.hom f H
#align category_theory.morphism_property.stable_under_base_change.base_change_obj CategoryTheory.MorphismProperty.StableUnderBaseChange.baseChange_obj

theorem StableUnderBaseChange.baseChange_map [HasPullbacks C] {P : MorphismProperty C}
    (hP : StableUnderBaseChange P) {S S' : C} (f : S' ⟶ S) {X Y : Over S} (g : X ⟶ Y)
    (H : P g.left) : P ((Over.baseChange f).map g).left := by
  let e :=
    pullbackRightPullbackFstIso Y.hom f g.left ≪≫
      pullback.congrHom (g.w.trans (Category.comp_id _)) rfl
  have : e.inv ≫ pullback.snd = ((Over.baseChange f).map g).left := by
    ext <;> dsimp [e] <;> simp
  rw [← this, hP.respectsIso.cancel_left_isIso]
  exact hP.snd _ _ H
#align category_theory.morphism_property.stable_under_base_change.base_change_map CategoryTheory.MorphismProperty.StableUnderBaseChange.baseChange_map

theorem StableUnderBaseChange.pullback_map [HasPullbacks C] {P : MorphismProperty C}
    (hP : StableUnderBaseChange P) [P.IsStableUnderComposition] {S X X' Y Y' : C} {f : X ⟶ S}
    {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
    (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂)) := by
  have :
    pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂) =
      ((pullbackSymmetry _ _).hom ≫
          ((Over.baseChange _).map (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g')).left) ≫
        (pullbackSymmetry _ _).hom ≫
          ((Over.baseChange g').map (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f')).left := by
    ext <;> dsimp <;> simp
  rw [this]
  apply P.comp_mem <;> rw [hP.respectsIso.cancel_left_isIso]
  exacts [hP.baseChange_map _ (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g') h₂,
    hP.baseChange_map _ (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f') h₁]
#align category_theory.morphism_property.stable_under_base_change.pullback_map CategoryTheory.MorphismProperty.StableUnderBaseChange.pullback_map

theorem StableUnderCobaseChange.mk {P : MorphismProperty C} [HasPushouts C] (hP₁ : RespectsIso P)
    (hP₂ : ∀ (A B A' : C) (f : A ⟶ A') (g : A ⟶ B) (_ : P f), P (pushout.inr : B ⟶ pushout f g)) :
    StableUnderCobaseChange P := fun A A' B B' f g f' g' sq hf => by
  let e := sq.flip.isoPushout
  rw [← hP₁.cancel_right_isIso _ e.hom, sq.flip.inr_isoPushout_hom]
  exact hP₂ _ _ _ f g hf
#align category_theory.morphism_property.stable_under_cobase_change.mk CategoryTheory.MorphismProperty.StableUnderCobaseChange.mk

theorem StableUnderCobaseChange.respectsIso {P : MorphismProperty C}
    (hP : StableUnderCobaseChange P) : RespectsIso P :=
  RespectsIso.of_respects_arrow_iso _ fun _ _ e => hP (IsPushout.of_horiz_isIso (CommSq.mk e.hom.w))
#align category_theory.morphism_property.stable_under_cobase_change.respects_iso CategoryTheory.MorphismProperty.StableUnderCobaseChange.respectsIso

theorem StableUnderCobaseChange.inl {P : MorphismProperty C} (hP : StableUnderCobaseChange P)
    {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (H : P g) :
    P (pushout.inl : A' ⟶ pushout f g) :=
  hP (IsPushout.of_hasPushout f g) H
#align category_theory.morphism_property.stable_under_cobase_change.inl CategoryTheory.MorphismProperty.StableUnderCobaseChange.inl

theorem StableUnderCobaseChange.inr {P : MorphismProperty C} (hP : StableUnderCobaseChange P)
    {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (H : P f) :
    P (pushout.inr : B ⟶ pushout f g) :=
  hP (IsPushout.of_hasPushout f g).flip H
#align category_theory.morphism_property.stable_under_cobase_change.inr CategoryTheory.MorphismProperty.StableUnderCobaseChange.inr

theorem StableUnderCobaseChange.op {P : MorphismProperty C} (hP : StableUnderCobaseChange P) :
    StableUnderBaseChange P.op := fun _ _ _ _ _ _ _ _ sq hg => hP sq.unop hg
#align category_theory.morphism_property.stable_under_cobase_change.op CategoryTheory.MorphismProperty.StableUnderCobaseChange.op

theorem StableUnderCobaseChange.unop {P : MorphismProperty Cᵒᵖ} (hP : StableUnderCobaseChange P) :
    StableUnderBaseChange P.unop := fun _ _ _ _ _ _ _ _ sq hg => hP sq.op hg
#align category_theory.morphism_property.stable_under_cobase_change.unop CategoryTheory.MorphismProperty.StableUnderCobaseChange.unop

theorem StableUnderBaseChange.op {P : MorphismProperty C} (hP : StableUnderBaseChange P) :
    StableUnderCobaseChange P.op := fun _ _ _ _ _ _ _ _ sq hf => hP sq.unop hf
#align category_theory.morphism_property.stable_under_base_change.op CategoryTheory.MorphismProperty.StableUnderBaseChange.op

theorem StableUnderBaseChange.unop {P : MorphismProperty Cᵒᵖ} (hP : StableUnderBaseChange P) :
    StableUnderCobaseChange P.unop := fun _ _ _ _ _ _ _ _ sq hf => hP sq.op hf
#align category_theory.morphism_property.stable_under_base_change.unop CategoryTheory.MorphismProperty.StableUnderBaseChange.unop

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
    (hW₀ : W.RespectsIso) [HasProductsOfShape J C]
    (hW : ∀ (X₁ X₂ : J → C) (f : ∀ j, X₁ j ⟶ X₂ j) (_ : ∀ (j : J), W (f j)),
      W (Pi.map f)) : W.IsStableUnderProductsOfShape J := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf
  let φ := fun j => f.app (Discrete.mk j)
  have hf' := hW _ _ φ (fun j => hf (Discrete.mk j))
  refine (hW₀.arrow_mk_iso_iff ?_).2 hf'
  refine Arrow.isoMk
    (IsLimit.conePointUniqueUpToIso hc₁ (limit.isLimit X₁) ≪≫ (Pi.isoLimit _).symm)
    (IsLimit.conePointUniqueUpToIso hc₂ (limit.isLimit X₂) ≪≫ (Pi.isoLimit _).symm) ?_
  apply limit.hom_ext
  rintro ⟨j⟩
  simp

/-- The condition that a property of morphisms is stable by finite products. -/
class IsStableUnderFiniteProducts : Prop :=
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
#align category_theory.morphism_property.diagonal CategoryTheory.MorphismProperty.diagonal

theorem diagonal_iff {X Y : C} {f : X ⟶ Y} : P.diagonal f ↔ P (pullback.diagonal f) :=
  Iff.rfl
#align category_theory.morphism_property.diagonal_iff CategoryTheory.MorphismProperty.diagonal_iff

theorem RespectsIso.diagonal (hP : P.RespectsIso) : P.diagonal.RespectsIso := by
  constructor
  · introv H
    rwa [diagonal_iff, pullback.diagonal_comp, hP.cancel_left_isIso, hP.cancel_left_isIso,
      ← hP.cancel_right_isIso _
        (pullback.map (e.hom ≫ f) (e.hom ≫ f) f f e.hom e.hom (𝟙 Z) (by simp) (by simp)),
      ← pullback.condition, hP.cancel_left_isIso]
  · introv H
    delta diagonal
    rwa [pullback.diagonal_comp, hP.cancel_right_isIso]
#align category_theory.morphism_property.respects_iso.diagonal CategoryTheory.MorphismProperty.RespectsIso.diagonal

theorem diagonal_isStableUnderComposition [P.IsStableUnderComposition] (hP' : RespectsIso P)
    (hP'' : StableUnderBaseChange P) : P.diagonal.IsStableUnderComposition where
  comp_mem _ _ h₁ h₂ := by
    rw [diagonal_iff, pullback.diagonal_comp]
    exact P.comp_mem _ _ h₁ (by simpa [hP'.cancel_left_isIso] using hP''.snd _ _ h₂)
#align category_theory.morphism_property.stable_under_composition.diagonal CategoryTheory.MorphismProperty.diagonal_isStableUnderComposition

theorem StableUnderBaseChange.diagonal (hP : StableUnderBaseChange P) (hP' : RespectsIso P) :
    P.diagonal.StableUnderBaseChange :=
  StableUnderBaseChange.mk hP'.diagonal
    (by
      introv h
      rw [diagonal_iff, diagonal_pullback_fst, hP'.cancel_left_isIso, hP'.cancel_right_isIso]
      exact hP.baseChange_map f _ (by simpa))
#align category_theory.morphism_property.stable_under_base_change.diagonal CategoryTheory.MorphismProperty.StableUnderBaseChange.diagonal

end Diagonal

section Universally

/-- `P.universally` holds for a morphism `f : X ⟶ Y` iff `P` holds for all `X ×[Y] Y' ⟶ Y'`. -/
def universally (P : MorphismProperty C) : MorphismProperty C := fun X Y f =>
  ∀ ⦃X' Y' : C⦄ (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y) (f' : X' ⟶ Y') (_ : IsPullback f' i₁ i₂ f), P f'
#align category_theory.morphism_property.universally CategoryTheory.MorphismProperty.universally

theorem universally_respectsIso (P : MorphismProperty C) : P.universally.RespectsIso := by
  constructor
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
#align category_theory.morphism_property.universally_respects_iso CategoryTheory.MorphismProperty.universally_respectsIso

theorem universally_stableUnderBaseChange (P : MorphismProperty C) :
    P.universally.StableUnderBaseChange := fun _ _ _ _ _ _ _ _ H h₁ _ _ _ _ _ H' =>
  h₁ _ _ _ (H'.paste_vert H.flip)
#align category_theory.morphism_property.universally_stable_under_base_change CategoryTheory.MorphismProperty.universally_stableUnderBaseChange

instance IsStableUnderComposition.universally [HasPullbacks C] (P : MorphismProperty C)
    [hP : P.IsStableUnderComposition] : P.universally.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg X' Z' i₁ i₂ f' H := by
    have := pullback.lift_fst _ _ (H.w.trans (Category.assoc _ _ _).symm)
    rw [← this] at H ⊢
    apply P.comp_mem _ _ _ (hg _ _ _ <| IsPullback.of_hasPullback _ _)
    exact hf _ _ _ (H.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback i₂ g))
#align category_theory.morphism_property.stable_under_composition.universally CategoryTheory.MorphismProperty.IsStableUnderComposition.universally

theorem universally_le (P : MorphismProperty C) : P.universally ≤ P := by
  intro X Y f hf
  exact hf (𝟙 _) (𝟙 _) _ (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩)
#align category_theory.morphism_property.universally_le CategoryTheory.MorphismProperty.universally_le

theorem universally_eq_iff {P : MorphismProperty C} :
    P.universally = P ↔ P.StableUnderBaseChange :=
  ⟨(· ▸ P.universally_stableUnderBaseChange),
    fun hP ↦ P.universally_le.antisymm fun _ _ _ hf _ _ _ _ _ H => hP H.flip hf⟩

theorem StableUnderBaseChange.universally_eq {P : MorphismProperty C}
    (hP : P.StableUnderBaseChange) : P.universally = P := universally_eq_iff.mpr hP
#align category_theory.morphism_property.stable_under_base_change.universally_eq CategoryTheory.MorphismProperty.StableUnderBaseChange.universally_eq

theorem universally_mono : Monotone (universally : MorphismProperty C → MorphismProperty C) :=
  fun _ _ h _ _ _ h₁ _ _ _ _ _ H => h _ (h₁ _ _ _ H)
#align category_theory.morphism_property.universally_mono CategoryTheory.MorphismProperty.universally_mono

end Universally

end MorphismProperty

end CategoryTheory
