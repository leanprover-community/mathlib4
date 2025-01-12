/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.AlgebraicTopology.ModelCategory.Instances
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Fibrant objects in a model category

-/

open CategoryTheory Limits

-- to be moved
namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasInitial C]
    {X Y : C} (c : BinaryCofan X Y)

lemma isPushout_of_isColimit_binaryCofan (hc : IsColimit c) :
    IsPushout (initial.to _) (initial.to _) c.inr c.inl where
  w := Subsingleton.elim _ _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ hc.desc (BinaryCofan.mk s.inr s.inl))
    (fun s ↦ hc.fac (BinaryCofan.mk s.inr s.inl) ⟨.right⟩)
    (fun s ↦ hc.fac (BinaryCofan.mk s.inr s.inl) ⟨.left⟩)
    (fun s m h₁ h₂ ↦ by
      apply BinaryCofan.IsColimit.hom_ext hc
      · rw [h₂, hc.fac (BinaryCofan.mk s.inr s.inl) ⟨.left⟩]
        rfl
      · rw [h₁, hc.fac (BinaryCofan.mk s.inr s.inl) ⟨.right⟩]
        rfl)⟩

end CategoryTheory.Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category C]

section

variable [CategoryWithCofibrations C] [HasInitial C]

abbrev IsCofibrant (X : C) : Prop := Cofibration (initial.to X)

lemma isCofibrant_iff (X : C) :
    IsCofibrant X ↔ Cofibration (initial.to X) := Iff.rfl

lemma isCofibrant_iff_of_isInitial [(cofibrations C).RespectsIso]
    {A X : C} (i : A ⟶ X) (hA : IsInitial A) :
    IsCofibrant X ↔ Cofibration i := by
  simp only [isCofibrant_iff, cofibration_iff]
  apply (cofibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (IsInitial.uniqueUpToIso initialIsInitial hA) (Iso.refl _)

lemma isCofibrant_of_cofibration [(cofibrations C).IsStableUnderComposition]
    {X Y : C} (i : X ⟶ Y) [Cofibration i] [hX : IsCofibrant X] :
    IsCofibrant Y := by
  rw [isCofibrant_iff] at hX ⊢
  rw [Subsingleton.elim (initial.to Y) (initial.to X ≫ i)]
  infer_instance

end

section

variable [CategoryWithFibrations C] [HasTerminal C]

abbrev IsFibrant (X : C) : Prop := Fibration (terminal.from X)

lemma isFibrant_iff (X : C) :
    IsFibrant X ↔ Fibration (terminal.from X) := Iff.rfl

lemma isFibrant_iff_of_isTerminal [(fibrations C).RespectsIso]
    {X Y : C} (p : X ⟶ Y) (hY : IsTerminal Y) :
    IsFibrant X ↔ Fibration p := by
  simp only [isFibrant_iff, fibration_iff]
  symm
  apply (fibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (IsTerminal.uniqueUpToIso hY terminalIsTerminal)

lemma isFibrant_of_fibration [(fibrations C).IsStableUnderComposition]
    {X Y : C} (p : X ⟶ Y) [Fibration p] [hY : IsFibrant Y] :
    IsFibrant X := by
  rw [isFibrant_iff] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y)]
  infer_instance

end

section

variable [CategoryWithCofibrations C] (X Y : C)
  [(cofibrations C).IsStableUnderCobaseChange]

instance [HasInitial C] [HasBinaryCoproduct X Y] [hY : IsCofibrant Y] :
    Cofibration (coprod.inl : X ⟶ X ⨿ Y) := by
  rw [isCofibrant_iff] at hY
  rw [cofibration_iff] at hY ⊢
  exact (cofibrations C).of_isPushout
    (isPushout_of_isColimit_binaryCofan _ (colimit.isColimit (pair X Y))).flip hY

instance [HasInitial C] [HasBinaryCoproduct X Y] [hX : IsCofibrant X] :
    Cofibration (coprod.inr : Y ⟶ X ⨿ Y) := by
  rw [isCofibrant_iff] at hX
  rw [cofibration_iff] at hX ⊢
  exact (cofibrations C).of_isPushout
    (isPushout_of_isColimit_binaryCofan _ (colimit.isColimit (pair X Y))) hX

end

end HomotopicalAlgebra
