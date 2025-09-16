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
    ((IsPushout.of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial).flip) hY

instance [HasInitial C] [HasBinaryCoproduct X Y] [hX : IsCofibrant X] :
    Cofibration (coprod.inr : Y ⟶ X ⨿ Y) := by
  rw [isCofibrant_iff] at hX
  rw [cofibration_iff] at hX ⊢
  exact MorphismProperty.of_isPushout
    (IsPushout.of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial) hX

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
    (IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) terminalIsTerminal).flip hY

instance [HasTerminal C] [HasBinaryProduct X Y] [hX : IsFibrant X] :
    Fibration (prod.snd : X ⨯ Y ⟶ Y) := by
  rw [isFibrant_iff] at hX
  rw [fibration_iff] at hX ⊢
  exact MorphismProperty.of_isPullback
    (IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) terminalIsTerminal) hX

end

end

end HomotopicalAlgebra
