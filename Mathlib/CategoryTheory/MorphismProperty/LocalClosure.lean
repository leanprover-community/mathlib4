/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.Sites.MorphismProperty

/-!
# Local closure of morphism properties

We define the source local closure of a morphism property `P` w.r.t. a precoverage `K` as the
weakest property containing `P` that is `K`-local on the source.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MorphismProperty

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.MorphismProperty

variable {K : Precoverage C}

/-- The source-local closure of `P` along a precoverage `K` is the weakest property
containing `P` that is local on the source. -/
inductive sourceLocalClosure (K : Precoverage C) (P : MorphismProperty C) : MorphismProperty C
  /-- Force `P ≤ sourceLocalClosure K P`. -/
  | of {X Y : C} (f : X ⟶ Y) : P f → sourceLocalClosure K P f
  /-- Force `RespectsIso`. -/
  | of_iso {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (e : Arrow.mk f ≅ Arrow.mk g) :
      sourceLocalClosure K P f → sourceLocalClosure K P g
  | comp {X Y : C} (f : X ⟶ Y) (hf : sourceLocalClosure K P f) (R : Presieve X) (hR : R ∈ K X)
      {U : C} (g : U ⟶ X) : R g → sourceLocalClosure K P (g ≫ f)
  | of_presieve {X Y : C} (f : X ⟶ Y) (R : Presieve X) (hR : R ∈ K X)
      (h : ∀ (U : C) (g : U ⟶ X), R g → sourceLocalClosure K P (g ≫ f)) :
      sourceLocalClosure K P f

namespace sourceLocalClosure

attribute [grind .] of

variable {P Q : MorphismProperty C} {X Y : C}

instance : (sourceLocalClosure K P).IsLocalAtSource K where
  precomp i hi f hf := .of_iso _ _ (Arrow.isoMk' _ _ (asIso i).symm (.refl _)) hf
  postcomp i hi f hf := .of_iso _ _ (Arrow.isoMk' _ _ (.refl _) (asIso i)) hf
  comp hR _ g hg hf := .comp _ hf _ hR _ hg
  of_forall_comp hR h := .of_presieve _ _ hR h

lemma le : P ≤ sourceLocalClosure K P :=
  fun _ _ _ ↦ .of _

lemma le_of_isLocalAtSource (h : P ≤ Q) [Q.IsLocalAtSource K] : sourceLocalClosure K P ≤ Q := by
  intro X Y f hf
  induction hf with
  | of f hf => exact h _ hf
  | of_iso f g e _ hf => rwa [Q.arrow_mk_iso_iff e.symm]
  | comp f hf R hR g hg ih => apply IsLocalAtSource.comp hR _ hg ih
  | of_presieve f R hR h ih => apply IsLocalAtSource.of_forall_comp hR fun U g hg ↦ ih _ _ hg

instance [P.ContainsIdentities] : ContainsIdentities (sourceLocalClosure K P) where
  id_mem _ := le _ (P.id_mem _)

set_option backward.isDefEq.respectTransparency false in
instance [P.IsStableUnderBaseChange] [K.IsStableUnderBaseChange] [HasPullbacks C] :
    IsStableUnderBaseChange (sourceLocalClosure K P) where
  of_isPullback {Y} X W Z g f fst snd h hf := by
    induction hf generalizing W snd with
    | of f' hf' => exact .of _ (P.of_isPullback h hf')
    | of_iso f' g' e hf' ih =>
      exact ih _ (g ≫ e.inv.right) (fst ≫ e.inv.left) _ (h.paste_horiz (.of_horiz_isIso ⟨e.inv.w⟩))
    | comp f' hf' R hR g' hg' ih =>
      let u : W ⟶ pullback g f' := pullback.lift snd (fst ≫ g') (by simp [h.w.symm])
      have : snd = u ≫ pullback.fst g f' := by simp [u]
      rw [this] at h ⊢
      let e : W ≅ pullback g' (pullback.snd g f') :=
        IsPullback.isoPullback (.of_bot h (by simp [u]) (.flip <| .of_hasPullback _ _))
      rw [← (sourceLocalClosure K P).cancel_left_of_respectsIso e.inv, ← Category.assoc]
      refine .comp _ (ih _ _ _ _ (.flip (.of_hasPullback _ _))) _
        (K.pullbackArrows_mem (pullback.snd _ _) hR) _ ?_
      simpa [e, u] using .mk _ _ hg'
    | of_presieve f R hR h ih =>
      refine .of_presieve _ _ (K.pullbackArrows_mem fst hR) ?_
      intro U v ⟨Z, u, hu⟩
      exact ih _ _ hu _ g (pullback.fst _ _) _ (.paste_vert (.of_hasPullback _ _) h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma sourceLocalClosure_iff_of_respectsLeft [P.RespectsIso] [P.RespectsLeft K.morphismProperty]
    [K.HasIsos] [K.IsStableUnderBaseChange] [K.IsStableUnderComposition] [K.HasPullbacks] {X Y : C}
    {f : X ⟶ Y} :
    sourceLocalClosure K P f ↔ ∃ R ∈ K X, ∀ (U : C) (g : U ⟶ X), R g → P (g ≫ f) := by
  refine ⟨?_, ?_⟩
  · intro h
    induction h with
    | of f hf => exact ⟨.singleton (𝟙 _), K.mem_coverings_of_isIso _, fun U g ⟨⟩ ↦ by simpa⟩
    | of_iso f g e hf h =>
      obtain ⟨R, hR, h⟩ := h
      rw [K.mem_iff_exists_zeroHypercover] at hR
      obtain ⟨E, rfl⟩ := hR
      refine ⟨_, (E.pushforward e.hom.left (K.mem_coverings_of_isIso _)).mem₀, ?_⟩
      intro U v ⟨i⟩
      dsimp
      simp only [Category.assoc, Arrow.w_mk_right, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
      rw [← Category.assoc, P.cancel_right_of_respectsIso]
      exact h _ _ ⟨i⟩
    | comp f hf R hR g hg ih =>
      obtain ⟨S, hS, h⟩ := ih
      rw [K.mem_iff_exists_zeroHypercover] at hS hR
      obtain ⟨E, rfl⟩ := hS
      obtain ⟨F, rfl⟩ := hR
      refine ⟨(E.pullback₁ g).presieve₀, (E.pullback₁ g).mem₀, ?_⟩
      intro U v ⟨i⟩
      dsimp
      rw [pullback.condition_assoc]
      refine RespectsLeft.precomp (Q := K.morphismProperty) _ ?_ _ ?_
      · obtain ⟨j⟩ := hg
        exact (F.pullback₂ (E.f i)).morphismProperty j
      · exact h _ _ ⟨i⟩
    | of_presieve f R hR h ih =>
      rw [K.mem_iff_exists_zeroHypercover] at hR
      obtain ⟨E, rfl⟩ := hR
      choose S hS h' using fun i : E.I₀ ↦ ih _ _ ⟨i⟩
      simp_rw [K.mem_iff_exists_zeroHypercover] at hS
      choose F hF using hS
      refine ⟨_, (E.bind F).mem₀, fun U g ⟨j⟩ ↦ ?_⟩
      dsimp
      rw [Category.assoc]
      exact h' _ _ _ (by simp [hF])
  · intro ⟨R, hR, h⟩
    exact .of_presieve _ _ hR (by grind)

end sourceLocalClosure

end CategoryTheory.MorphismProperty
