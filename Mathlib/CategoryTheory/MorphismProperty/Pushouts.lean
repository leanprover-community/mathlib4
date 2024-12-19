/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# The class of pushouts of a class of morphisms

-/

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category C] (P : MorphismProperty C)

/-- Given `P : MorphismProperty C`, this is the class of morphisms which are
pushouts of some morphism in `P`. -/
def pushouts : MorphismProperty C := fun X Y q ↦
  ∃ (A B : C) (p : A ⟶ B) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPushout f p q g

lemma le_pushouts : P ≤ P.pushouts := by
  intro A B p hp
  exact ⟨A, B, p, 𝟙 A, 𝟙 B, hp, IsPushout.id_horiz p⟩

instance : RespectsIso P.pushouts :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨A, B, p, f, g, hp, h⟩
    exact ⟨A, B, p, f ≫ e.hom.left, g ≫ e.hom.right, hp,
      IsPushout.paste_horiz h (IsPushout.of_horiz_isIso ⟨e.hom.w⟩)⟩)

instance : IsStableUnderCobaseChange P.pushouts where
  of_isPushout := by
    rintro X' X Y' Y k q l q' h ⟨A, B, p, f, g, hp, hq⟩
    exact ⟨A, B, p, f ≫ q, g ≫ q', hp, hq.paste_horiz h⟩

lemma isomorphisms_le_pushouts
    (h : ∀ (X : C), ∃ (A B : C) (p : A ⟶ B) (_ : P p) (_ : B ⟶ X), IsIso p) :
    isomorphisms C ≤ P.pushouts := by
  intro X Y f (_ : IsIso f)
  obtain ⟨A, B, p, hp, g, _⟩ := h X
  exact ⟨A, B, p, p ≫ g, g ≫ f, hp, (IsPushout.of_id_snd (f := p ≫ g)).of_iso
    (Iso.refl _) (Iso.refl _) (asIso p) (asIso f) (by simp) (by simp) (by simp) (by simp)⟩

end MorphismProperty

end CategoryTheory
