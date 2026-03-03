/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction
public import Mathlib.Probability.Independence.Basic

/-!
# Links between independence and characteristic function

Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. More specifically, prove this in Hilbert spaces for
two variables and a finite family of variables. We prove the analogous statements in Banach spaces,
with an arbitrary Lp norm, for the dual characteristic function.
-/

public section

namespace ProbabilityTheory

open MeasureTheory WithLp
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

section IndepFun

variable [IsFiniteMeasure P] {E F : Type*}
  {mE : MeasurableSpace E} [NormedAddCommGroup E]
  [BorelSpace E] [SecondCountableTopology E]
  {mF : MeasurableSpace F} [NormedAddCommGroup F] [CompleteSpace F]
  [BorelSpace F] [SecondCountableTopology F]
  {X : Ω → E} {Y : Ω → F}

section InnerProductSpace

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

lemma IndepFun.charFun_map_add_eq_mul {Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFun (P.map (X + Y)) = charFun (P.map X) * charFun (P.map Y) := by
  ext t
  rw [hXY.map_add_eq_map_conv_map₀ mX mY, charFun_conv, Pi.mul_apply]

/-- Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. This is the version for Hilbert spaces, see
`indepFun_iff_charFunDual_prod` for the Banach space version. -/
lemma indepFun_iff_charFun_prod [CompleteSpace E] (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ ∀ t, charFun (P.map (fun ω ↦ toLp 2 (X ω, Y ω))) t =
      charFun (P.map X) t.ofLp.1 * charFun (P.map Y) t.ofLp.2 := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← charFun_eq_prod_iff,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), Function.comp_def]

end InnerProductSpace

section NormedSpace

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

lemma IndepFun.charFunDual_map_add_eq_mul {Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFunDual (P.map (X + Y)) = charFunDual (P.map X) * charFunDual (P.map Y) := by
  ext L
  rw [hXY.map_add_eq_map_conv_map₀ mX mY, charFunDual_conv, Pi.mul_apply]

variable [CompleteSpace E]

/-- Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. This is the version for Banach spaces, see
`indepFun_iff_charFun_prod` for the Hilbert space version. -/
lemma indepFun_iff_charFunDual_prod (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ ∀ L, charFunDual (P.map (fun ω ↦ (X ω, Y ω))) L =
      charFunDual (P.map X) (L.comp (.inl ℝ E F)) *
      charFunDual (P.map Y) (L.comp (.inr ℝ E F)) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← charFunDual_eq_prod_iff]

/-- Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. This is `indepFun_iff_charFunDual_prod` for
`WithLp`. See `indepFun_iff_charFun_prod` for the Hilbert space version. -/
lemma indepFun_iff_charFunDual_prod' (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ ∀ L, charFunDual (P.map (fun ω ↦ toLp p (X ω, Y ω))) L =
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

variable {ι : Type*} [Fintype ι]

section Sum

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → E}

lemma iIndepFun.charFunDual_map_sum_eq_prod [NormedSpace ℝ E]
    (mX : ∀ i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFunDual (P.map (∑ i, X i)) = ∏ i, charFunDual (P.map (X i)) := by
  have := hX.isProbabilityMeasure
  refine Fintype.induction_empty_option (P := fun α _ ↦ ∀ (X : α → Ω → E),
    (∀ a, AEMeasurable (X a) P) → iIndepFun X P →
    charFunDual (P.map (∑ a, X a)) = ∏ a, charFunDual (P.map (X a))) ?_ ?_ ?_ ι X mX hX
  · intro α β _ e hα X mX hX
    let := Fintype.ofEquiv β e.symm
    rw [← Equiv.prod_comp e, ← Equiv.sum_comp e]
    exact hα (X ∘ e) (fun _ ↦ mX _) (hX.precomp (g := e) e.injective)
  · simp only [IsEmpty.forall_iff, of_subsingleton, Finset.univ_eq_empty, Finset.sum_empty,
    show (0 : Ω → E) = fun _ ↦ 0 from rfl, Measure.map_const, measure_univ, one_smul,
    Finset.prod_empty, forall_const]
    ext
    simp
  intro α _ hα X mX hX
  simp only [Fintype.sum_option, Fintype.prod_option]
  rw [IndepFun.charFunDual_map_add_eq_mul]
  any_goals fun_prop
  · congr
    refine hα (X ∘ some) (fun _ ↦ mX _) (hX.precomp (g := some) (Option.some_injective α))
  symm
  classical
  rw [← Finset.sum_image (Option.some_injective α).injOn]
  exact indepFun_finset_sum_of_notMem₀ hX (by fun_prop) (by simp)

lemma iIndepFun.charFun_map_sum_eq_prod [InnerProductSpace ℝ E]
    (mX : ∀ i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFun (P.map (∑ i, X i)) = ∏ i, charFun (P.map (X i)) := by
  ext
  simp [charFun_eq_charFunDual_toDualMap, hX.charFunDual_map_sum_eq_prod mX]

end Sum

variable [IsProbabilityMeasure P] {E : ι → Type*}
  {mE : ∀ i, MeasurableSpace (E i)} [∀ i, NormedAddCommGroup (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}

section InnerProductSpace

variable [∀ i, InnerProductSpace ℝ (E i)]

/-- A finite number of random variables are independent if and only if their joint characteristic
function is equal to the product of the characteristic functions. This is the version for Hilbert
spaces, see `iIndepFun_iff_charFunDual_pi` for the Banach space version. -/
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
