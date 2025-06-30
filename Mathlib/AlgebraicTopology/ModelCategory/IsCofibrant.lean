/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Instances
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Fibrant and cofibrant objects in a model category

Once a category `C` has been endowed with a `CategoryWithCofibrations C`
instance, it is possible to define the property `IsCofibrant X` for
any `X : C` as an abbreviation for `Cofibration (initial.to X : ⊥_ C ⟶ X)`.
(Fibrant objects are defined similarly.)

-/

open CategoryTheory Limits

-- to be moved
namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {X Y : C}

lemma isPushout_of_isColimit_binaryCofan_of_isInitial {c : BinaryCofan X Y} (hc : IsColimit c)
    {I : C} (hI : IsInitial I) :
    IsPushout (hI.to _) (hI.to _) c.inl c.inr where
  w := hI.hom_ext _ _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ hc.desc (BinaryCofan.mk s.inl s.inr))
    (fun s ↦ hc.fac (BinaryCofan.mk s.inl s.inr) ⟨.left⟩)
    (fun s ↦ hc.fac (BinaryCofan.mk s.inl s.inr) ⟨.right⟩)
    (fun s m h₁ h₂ ↦ by
      apply BinaryCofan.IsColimit.hom_ext hc
      · rw [h₁, hc.fac (BinaryCofan.mk s.inl s.inr) ⟨.left⟩]
        rfl
      · rw [h₂, hc.fac (BinaryCofan.mk s.inl s.inr) ⟨.right⟩]
        rfl)⟩

lemma isPullback_of_isLimit_binaryFan_of_isTerminal {c : BinaryFan X Y} (hc : IsLimit c)
    {P : C} (hP : IsTerminal P) :
    IsPullback c.fst c.snd (hP.from _) (hP.from _) where
  w := hP.hom_ext _ _
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ hc.lift (BinaryFan.mk s.fst s.snd))
    (fun s ↦ hc.fac (BinaryFan.mk s.fst s.snd) ⟨.left⟩)
    (fun s ↦ hc.fac (BinaryFan.mk s.fst s.snd) ⟨.right⟩)
    (fun s m h₁ h₂ ↦ by
      apply BinaryFan.IsLimit.hom_ext hc
      · rw [h₁, hc.fac (BinaryFan.mk s.fst s.snd) ⟨.left⟩]
        rfl
      · rw [h₂, hc.fac (BinaryFan.mk s.fst s.snd) ⟨.right⟩]
        rfl)⟩

end CategoryTheory.Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category C]

section

variable [CategoryWithCofibrations C] [HasInitial C]

/-- An object `X` is cofibrant if `⊥_ C ⟶ X` is a cofibration. -/
abbrev IsCofibrant (X : C) : Prop := Cofibration (initial.to X)

lemma isCofibrant_iff (X : C) :
    IsCofibrant X ↔ Cofibration (initial.to X) := Iff.rfl

lemma isCofibrant_iff_of_isInitial [(cofibrations C).RespectsIso]
    {A X : C} (i : A ⟶ X) (hA : IsInitial A) :
    IsCofibrant X ↔ Cofibration i := by
  simp only [cofibration_iff]
  apply (cofibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (IsInitial.uniqueUpToIso initialIsInitial hA) (Iso.refl _)

lemma isCofibrant_of_cofibration [(cofibrations C).IsStableUnderComposition]
    {X Y : C} (i : X ⟶ Y) [Cofibration i] [hX : IsCofibrant X] :
    IsCofibrant Y := by
  rw [isCofibrant_iff] at hX ⊢
  rw [Subsingleton.elim (initial.to Y) (initial.to X ≫ i)]
  infer_instance

section

variable (X Y : C) [(cofibrations C).IsStableUnderCobaseChange] [HasInitial C]
  [HasBinaryCoproduct X Y]

instance [hY : IsCofibrant Y] :
    Cofibration (coprod.inl : X ⟶ X ⨿ Y) := by
  rw [isCofibrant_iff] at hY
  rw [cofibration_iff] at hY ⊢
  exact MorphismProperty.of_isPushout
    ((isPushout_of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial)) hY

instance [HasInitial C] [HasBinaryCoproduct X Y] [hX : IsCofibrant X] :
    Cofibration (coprod.inr : Y ⟶ X ⨿ Y) := by
  rw [isCofibrant_iff] at hX
  rw [cofibration_iff] at hX ⊢
  exact MorphismProperty.of_isPushout
    (isPushout_of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial).flip hX

end

end

section

variable [CategoryWithFibrations C] [HasTerminal C]

/-- An object `X` is fibrant if `X ⟶ ⊤_ C` is a fibration. -/
abbrev IsFibrant (X : C) : Prop := Fibration (terminal.from X)

lemma isFibrant_iff (X : C) :
    IsFibrant X ↔ Fibration (terminal.from X) := Iff.rfl

lemma isFibrant_iff_of_isTerminal [(fibrations C).RespectsIso]
    {X Y : C} (p : X ⟶ Y) (hY : IsTerminal Y) :
    IsFibrant X ↔ Fibration p := by
  simp only [fibration_iff]
  symm
  apply (fibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (IsTerminal.uniqueUpToIso hY terminalIsTerminal)

lemma isFibrant_of_fibration [(fibrations C).IsStableUnderComposition]
    {X Y : C} (p : X ⟶ Y) [Fibration p] [hY : IsFibrant Y] :
    IsFibrant X := by
  rw [isFibrant_iff] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y)]
  infer_instance

section

variable (X Y : C) [(fibrations C).IsStableUnderBaseChange] [HasTerminal C]
  [HasBinaryProduct X Y]

instance [hY : IsFibrant Y] :
    Fibration (prod.fst : X ⨯ Y ⟶ X) := by
  rw [isFibrant_iff] at hY
  rw [fibration_iff] at hY ⊢
  exact MorphismProperty.of_isPullback
    ((isPullback_of_isLimit_binaryFan_of_isTerminal
    (limit.isLimit (pair X Y)) terminalIsTerminal)).flip hY

instance [hX : IsFibrant X] :
    Fibration (prod.snd : X ⨯ Y ⟶ Y) := by
  rw [isFibrant_iff] at hX
  rw [fibration_iff] at hX ⊢
  exact MorphismProperty.of_isPullback
    ((isPullback_of_isLimit_binaryFan_of_isTerminal
    (limit.isLimit (pair X Y)) terminalIsTerminal)) hX

end

end

end HomotopicalAlgebra
