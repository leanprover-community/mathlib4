/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Independence.Basic

/-!
# Links between independence and characteristic function

Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. More specifically, prove this in Hilbert spaces for
two variables and a finite family of variables. We prove the analoguous statemens in Banach spaces,
with an arbitrary Lp norm, for the dual characteristic function.
-/

namespace ProbabilityTheory

open MeasureTheory WithLp
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

section IndepFun

variable [IsFiniteMeasure P] {E F : Type*}
  {mE : MeasurableSpace E} [NormedAddCommGroup E] [CompleteSpace E]
  [BorelSpace E] [SecondCountableTopology E]
  {mF : MeasurableSpace F} [NormedAddCommGroup F] [CompleteSpace F]
  [BorelSpace F] [SecondCountableTopology F]
  {X : Ω → E} {Y : Ω → F}

section InnerProductSpace

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-- Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. This is the version for Hilbert spaces, see
`indepFun_iff_charFunDual_prod` for the Banach space version. -/
lemma indepFun_iff_charFun_prod (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    IndepFun X Y P ↔ ∀ t, charFun (P.map (fun ω ↦ toLp 2 (X ω, Y ω))) t =
      charFun (P.map X) t.ofLp.1 * charFun (P.map Y) t.ofLp.2 := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← charFun_eq_prod_iff,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), Function.comp_def]

end InnerProductSpace

section NormedSpace

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. This is the version for Banach spaces, see
`indepFun_iff_charFun_prod` for the Hilbert space version. -/
lemma indepFun_iff_charFunDual_prod (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    IndepFun X Y P ↔ ∀ L, charFunDual (P.map (fun ω ↦ (X ω, Y ω))) L =
      charFunDual (P.map X) (L.comp (.inl ℝ E F)) *
      charFunDual (P.map Y) (L.comp (.inr ℝ E F)) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← charFunDual_eq_prod_iff]

/-- Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. This is `indepFun_iff_charFunDual_prod` for
`WithLp`. See `indepFun_iff_charFun_prod` for the Hilbert space version. -/
lemma indepFun_iff_charFunDual_prod' (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    IndepFun X Y P ↔ ∀ L, charFunDual (P.map (fun ω ↦ toLp p (X ω, Y ω))) L =
      charFunDual (P.map X) (L.comp
        ((prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inl ℝ E F))) *
      charFunDual (P.map Y) (L.comp
        ((prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inr ℝ E F))) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← charFunDual_eq_prod_iff' p,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), Function.comp_def]

end NormedSpace

end IndepFun

section iIndepFun

variable [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {E : ι → Type*}
  {mE : ∀ i, MeasurableSpace (E i)} [∀ i, NormedAddCommGroup (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}

section InnerProductSpace

variable [∀ i, InnerProductSpace ℝ (E i)]

/-- A finite number of random variables are independent if and only if their joint characteristic
function is equal to the product of the characteristic functions. This is the version for Hilbert
spaces, see `iIndepFun_iff_charFunDual_pi` for the Hilbert space version. -/
lemma iIndepFun_iff_charFun_pi (hX : ∀ i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ ∀ t, charFun (P.map (fun ω ↦ toLp 2 (X · ω))) t =
      ∏ i, charFun (P.map (X i)) (t i) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX, ← charFun_eq_pi_iff,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), Function.comp_def]

end InnerProductSpace

section NormedSpace

variable [∀ i, NormedSpace ℝ (E i)] [DecidableEq ι]

/-- A finite number of random variables are independent if and only if their joint characteristic
function is equal to the product of the characteristic functions. This is the version for Banach
spaces, see `iIndepFun_iff_charFun_pi` for the Hilbert space version. -/
lemma iIndepFun_iff_charFunDual_pi (hX : ∀ i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ ∀ L, charFunDual (P.map (fun ω ↦ (X · ω))) L =
      ∏ i, charFunDual (P.map (X i)) (L.comp (.single ℝ E i)) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX, ← charFunDual_eq_pi_iff]

/-- A finite number of random variables are independent if and only if their joint characteristic
function is equal to the product of the characteristic functions.
This is `iIndepFun_iff_charFunDual_pi` for `WithLp`. See `iIndepFun_iff_charFun_pi` for the
Hilbert space version. -/
lemma iIndepFun_iff_charFunDual_pi' (hX : ∀ i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ ∀ L, charFunDual (P.map (fun ω ↦ toLp p (X · ω))) L =
      ∏ i, charFunDual (P.map (X i)) (L.comp
        ((PiLp.continuousLinearEquiv p ℝ E).symm.toContinuousLinearMap.comp (.single ℝ E i))) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX, ← charFunDual_eq_pi_iff' p,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), Function.comp_def]

end NormedSpace

end iIndepFun

end ProbabilityTheory
