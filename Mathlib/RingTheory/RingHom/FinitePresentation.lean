/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal

/-!

# The meta properties of finitely-presented ring homomorphisms.

The main result is `RingHom.finitePresentation_isLocal`.

-/
set_option backward.defeqAttrib.useBackward true

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
