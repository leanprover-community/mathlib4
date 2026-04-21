/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Links between independence and characteristic function

Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. More specifically, prove this in Hilbert spaces for
two variables and a finite family of variables. We prove the analogous statements in Banach spaces,
with an arbitrary Lp norm, for the dual characteristic function.
-/
set_option backward.defeqAttrib.useBackward true

public section

namespace ProbabilityTheory

open MeasureTheory WithLp Finset
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

lemma IndepFun.charFun_map_fun_add_eq_mul {Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFun (P.map (fun ω ↦ X ω + Y ω)) = charFun (P.map X) * charFun (P.map Y) :=
  hXY.charFun_map_add_eq_mul mX mY

lemma charFun_map_add_prod_eq_mul {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    charFun ((μ.prod ν).map (fun p ↦ p.1 + p.2)) = charFun μ * charFun ν := by
  rw [IndepFun.charFun_map_fun_add_eq_mul, measurePreserving_fst.map_eq,
    measurePreserving_snd.map_eq]
  any_goals fun_prop
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

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

lemma IndepFun.charFunDual_map_fun_add_eq_mul {Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFunDual (P.map (fun ω ↦ X ω + Y ω)) = charFunDual (P.map X) * charFunDual (P.map Y) :=
  hXY.charFunDual_map_add_eq_mul mX mY

lemma charFunDual_map_add_prod_eq_mul {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    charFunDual ((μ.prod ν).map (fun p ↦ p.1 + p.2)) = charFunDual μ * charFunDual ν := by
  rw [IndepFun.charFunDual_map_fun_add_eq_mul, measurePreserving_fst.map_eq,
    measurePreserving_snd.map_eq]
  any_goals fun_prop
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

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

variable {ι : Type*} {s : Finset ι}

section Sum

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → E}

lemma iIndepFun.charFunDual_map_finset_sum_eq_prod [NormedSpace ℝ E]
    (mX : ∀ i ∈ s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFunDual (P.map (∑ i ∈ s, X i)) = ∏ i ∈ s, charFunDual (P.map (X i)) := by
  classical
  have := hX.isProbabilityMeasure
  induction s using Finset.induction with
  | empty => ext; simp [show (0 : Ω → E) = fun _ ↦ 0 from rfl]
  | insert i s hi hs =>
    rw [Finset.sum_insert hi, IndepFun.charFunDual_map_add_eq_mul, Finset.prod_insert hi, hs]
    · exact fun i hi ↦ (mX i (mem_insert_of_mem hi))
    · exact hX.precomp (g := fun x : s ↦ ⟨x.1, mem_insert_of_mem x.2⟩) (fun _ ↦ by simp)
    · exact mX i (mem_insert_self i s)
    · exact Finset.aemeasurable_sum s (fun i hi ↦ (mX i (mem_insert_of_mem hi)))
    symm
    convert iIndepFun.indepFun_finset_sum_of_notMem₀ (i := ⟨i, mem_insert_self i s⟩)
      (f := fun (x : (insert i s : Finset ι)) ↦ X x.1) (s := {x | x.1 ∈ s}) hX
      (fun i ↦ (mX i.1 i.2)) (by simpa)
    let e : ((insert i s) : Finset ι) → ι := Subtype.val
    convert (Finset.sum_of_injOn Subtype.val ?_ ?_ ?_ ?_).symm
    · simp
    · intro _ _; grind
    · simp; grind
    · grind

lemma iIndepFun.charFunDual_map_sum_eq_prod [Fintype ι] [NormedSpace ℝ E]
    (mX : ∀ i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFunDual (P.map (∑ i, X i)) = ∏ i, charFunDual (P.map (X i)) :=
  (hX.restrict _).charFunDual_map_finset_sum_eq_prod (by simpa)

lemma iIndepFun.charFunDual_map_fun_finset_sum_eq_prod [NormedSpace ℝ E]
    (mX : ∀ i ∈ s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFunDual (P.map (fun ω ↦ ∑ i ∈ s, X i ω)) = ∏ i ∈ s, charFunDual (P.map (X i)) := by
  convert hX.charFunDual_map_finset_sum_eq_prod mX
  simp

lemma iIndepFun.charFunDual_map_fun_sum_eq_prod [Fintype ι] [NormedSpace ℝ E]
    (mX : ∀ i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFunDual (P.map (fun ω ↦ ∑ i, X i ω)) = ∏ i, charFunDual (P.map (X i)) :=
  (hX.restrict _).charFunDual_map_fun_finset_sum_eq_prod (by simpa)

lemma charFunDual_map_sum_pi_eq_prod [Fintype ι] [NormedSpace ℝ E] {μ : ι → Measure E}
    [∀ i, IsProbabilityMeasure (μ i)] :
    charFunDual ((Measure.pi μ).map (fun p ↦ ∑ i, p i)) = ∏ i, charFunDual (μ i) := by
  rw [iIndepFun.charFunDual_map_fun_sum_eq_prod]
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [(measurePreserving_eval μ i).map_eq]
  · exact aemeasurable_id.eval
  · exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)

lemma iIndepFun.charFun_map_finset_sum_eq_prod [InnerProductSpace ℝ E]
    (mX : ∀ i ∈ s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFun (P.map (∑ i ∈ s, X i)) = ∏ i ∈ s, charFun (P.map (X i)) := by
  ext
  simp [charFun_eq_charFunDual_toDualMap, hX.charFunDual_map_finset_sum_eq_prod mX]

lemma iIndepFun.charFun_map_sum_eq_prod [Fintype ι] [InnerProductSpace ℝ E]
    (mX : ∀ i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFun (P.map (∑ i, X i)) = ∏ i, charFun (P.map (X i)) :=
  (hX.restrict _).charFun_map_finset_sum_eq_prod (by simpa)

lemma iIndepFun.charFun_map_fun_finset_sum_eq_prod [InnerProductSpace ℝ E]
    (mX : ∀ i ∈ s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFun (P.map (fun ω ↦ ∑ i ∈ s, X i ω)) = ∏ i ∈ s, charFun (P.map (X i)) := by
  convert hX.charFun_map_finset_sum_eq_prod mX
  simp

lemma iIndepFun.charFun_map_fun_sum_eq_prod [Fintype ι] [InnerProductSpace ℝ E]
    (mX : ∀ i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFun (P.map (fun ω ↦ ∑ i, X i ω)) = ∏ i, charFun (P.map (X i)) :=
  (hX.restrict _).charFun_map_fun_finset_sum_eq_prod (by simpa)

lemma charFun_map_sum_pi_eq_prod [Fintype ι] [InnerProductSpace ℝ E]
    (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)] :
    charFun ((Measure.pi μ).map (fun p ↦ ∑ i, p i)) = ∏ i, charFun (μ i) := by
  ext
  simp [charFun_eq_charFunDual_toDualMap, charFunDual_map_sum_pi_eq_prod]

end Sum

variable [Fintype ι] [IsProbabilityMeasure P] {E : ι → Type*}
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
