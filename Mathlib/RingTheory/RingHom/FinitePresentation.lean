/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!

# The meta properties of finitely-presented ring homomorphisms.

The main result is `RingHom.finitePresentation_isLocal`.

-/

@[expose] public section

open scoped Pointwise TensorProduct

namespace RingHom

/-- Being finitely-presented is stable under composition. -/
theorem finitePresentation_stableUnderComposition : StableUnderComposition @FinitePresentation := by
  introv R hf hg
  exact hg.comp hf

/-- Being finitely-presented respects isomorphisms. -/
theorem finitePresentation_respectsIso : RingHom.RespectsIso @RingHom.FinitePresentation :=
  finitePresentation_stableUnderComposition.respectsIso
    fun e ↦ .of_surjective _ e.surjective <| by simpa using Submodule.fg_bot

/-- Being finitely-presented is stable under base change. -/
theorem finitePresentation_isStableUnderBaseChange :
    IsStableUnderBaseChange @FinitePresentation := by
  apply IsStableUnderBaseChange.mk
  · exact finitePresentation_respectsIso
  · simp only [finitePresentation_algebraMap]
    intros
    infer_instance

/-- Being finitely-presented is preserved by localizations. -/
theorem finitePresentation_localizationPreserves : LocalizationPreserves @FinitePresentation :=
  finitePresentation_isStableUnderBaseChange.localizationPreserves

/-- If `R` is a ring, then `Rᵣ` is `R`-finitely-presented for any `r : R`. -/
theorem finitePresentation_holdsForLocalizationAway :
    HoldsForLocalizationAway @FinitePresentation := by
  introv R _
  rw [finitePresentation_algebraMap]
  exact IsLocalization.Away.finitePresentation r

/-- Finite-presentation can be checked on a standard covering of the target. -/
theorem finitePresentation_ofLocalizationSpanTarget :
    OfLocalizationSpanTarget @FinitePresentation := by
  introv R hs H
  algebraize [f]
  replace H : ∀ r ∈ s, Algebra.FinitePresentation R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FinitePresentation] at H; convert H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FinitePresentation.of_span_eq_top_target s hs H

/-- Being finitely-presented is a local property of rings. -/
theorem finitePresentation_isLocal : PropertyIsLocal @FinitePresentation :=
  ⟨finitePresentation_localizationPreserves.away,
    finitePresentation_ofLocalizationSpanTarget,
    finitePresentation_ofLocalizationSpanTarget.ofLocalizationSpan
      (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finitePresentation_holdsForLocalizationAway).left,
    (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finitePresentation_holdsForLocalizationAway).right⟩

end RingHom
