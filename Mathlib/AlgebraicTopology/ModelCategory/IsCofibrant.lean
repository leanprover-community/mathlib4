/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
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
  simp only [isCofibrant_iff, cofibration_iff]
  apply (cofibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (IsInitial.uniqueUpToIso initialIsInitial hA) (Iso.refl _)

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
  simp only [isFibrant_iff, fibration_iff]
  symm
  apply (fibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (IsTerminal.uniqueUpToIso hY terminalIsTerminal)

end

end HomotopicalAlgebra
