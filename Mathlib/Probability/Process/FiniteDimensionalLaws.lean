/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Jonas Bayer
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.IdentDistrib

/-!
# Finite-dimensional distributions of a stochastic process

For a stochastic process `X : T → Ω → 𝓧` and a finite measure `P` on `Ω`, the law of the process is
`P.map (fun ω ↦ (X · ω))`, and its finite-dimensional distributions are
`P.map (fun ω ↦ I.restrict (X · ω))` for `I : Finset T`.

We show that two stochastic processes have the same laws if and only if they have the same
finite-dimensional distributions.

## Main statements

* `map_eq_iff_forall_finset_map_restrict_eq`: two processes have the same law if and only if
  their finite-dimensional distributions are equal.
* `identDistrib_iff_forall_finset_identDistrib`: same statement, but stated in terms of
  `IdentDistrib`.
* `map_restrict_eq_of_forall_ae_eq`: if two processes are modifications of each other, then
  their finite-dimensional distributions are equal.
* `map_eq_of_forall_ae_eq`: if two processes are modifications of each other, then they have the
  same law.

-/
set_option backward.defeqAttrib.useBackward true

public section

open MeasureTheory

namespace ProbabilityTheory

variable {T Ω : Type*} {𝓧 : T → Type*} {mΩ : MeasurableSpace Ω} {mα : ∀ t, MeasurableSpace (𝓧 t)}
  {X Y : (t : T) → Ω → 𝓧 t} {P : Measure Ω}

/-- The finite-dimensional distributions of a stochastic process are a projective measure family. -/
lemma isProjectiveMeasureFamily_map_restrict (hX : ∀ t, AEMeasurable (X t) P) :
    IsProjectiveMeasureFamily (fun I ↦ P.map (fun ω ↦ I.restrict (X · ω))) := by
  intro I J hJI
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict₂ _).aemeasurable]
  · simp [Finset.restrict_def, Finset.restrict₂_def, Function.comp_def]
  · exact aemeasurable_pi_lambda _ fun _ ↦ hX _

/-- The projective limit of the finite-dimensional distributions of a stochastic process is the law
of the process. -/
lemma isProjectiveLimit_map (hX : AEMeasurable (fun ω ↦ (X · ω)) P) :
    IsProjectiveLimit (P.map (fun ω ↦ (X · ω))) (fun I ↦ P.map (fun ω ↦ I.restrict (X · ω))) := by
  intro I
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable hX,
    Function.comp_def]

/-- Two stochastic processes have same law iff they have the same
finite-dimensional distributions. -/
lemma map_eq_iff_forall_finset_map_restrict_eq [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω ↦ (X · ω)) P) (hY : AEMeasurable (fun ω ↦ (Y · ω)) P) :
    P.map (fun ω ↦ (X · ω)) = P.map (fun ω ↦ (Y · ω))
    ↔ ∀ I : Finset T, P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)) := by
  refine ⟨fun h I ↦ ?_, fun h ↦ ?_⟩
  · have hX' : P.map (fun ω ↦ I.restrict (X · ω)) = (P.map (fun ω ↦ (X · ω))).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX, Function.comp_def]
    have hY' : P.map (fun ω ↦ I.restrict (Y · ω)) = (P.map (fun ω ↦ (Y · ω))).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hY, Function.comp_def]
    rw [hX', hY', h]
  · have hX' := isProjectiveLimit_map hX
    simp_rw [h] at hX'
    exact hX'.unique (isProjectiveLimit_map hY)

/-- Two stochastic processes are identically distributed iff they have the same
finite-dimensional distributions. -/
lemma identDistrib_iff_forall_finset_identDistrib [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω ↦ (X · ω)) P) (hY : AEMeasurable (fun ω ↦ (Y · ω)) P) :
    IdentDistrib (fun ω ↦ (X · ω)) (fun ω ↦ (Y · ω)) P P
      ↔ ∀ I : Finset T,
        IdentDistrib (fun ω ↦ I.restrict (X · ω)) (fun ω ↦ I.restrict (Y · ω)) P P := by
  refine ⟨fun h I ↦ ⟨?_, ?_, ?_⟩, fun h ↦ ⟨hX, hY, ?_⟩⟩
  · exact (Finset.measurable_restrict _).comp_aemeasurable hX
  · exact (Finset.measurable_restrict _).comp_aemeasurable hY
  · exact (map_eq_iff_forall_finset_map_restrict_eq hX hY).mp h.map_eq I
  · exact (map_eq_iff_forall_finset_map_restrict_eq hX hY).mpr (fun I ↦ (h I).map_eq)

/-- If two processes are modifications of each other, then they have the same finite-dimensional
distributions. -/
lemma map_restrict_eq_of_forall_ae_eq (h : ∀ t, X t =ᵐ[P] Y t) (I : Finset T) :
    P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)) := by
  have h' : ∀ᵐ ω ∂P, ∀ (i : I), X i ω = Y i ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun i ↦ h i
  refine Measure.map_congr ?_
  filter_upwards [h'] with ω h using funext h

/-- If two processes are modifications of each other, then they have the same distribution. -/
lemma map_eq_of_forall_ae_eq [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω ↦ (X · ω)) P) (hY : AEMeasurable (fun ω ↦ (Y · ω)) P)
    (h : ∀ t, X t =ᵐ[P] Y t) :
    P.map (fun ω ↦ (X · ω)) = P.map (fun ω ↦ (Y · ω)) := by
  rw [map_eq_iff_forall_finset_map_restrict_eq hX hY]
  exact fun I ↦ map_restrict_eq_of_forall_ae_eq h I

end ProbabilityTheory
