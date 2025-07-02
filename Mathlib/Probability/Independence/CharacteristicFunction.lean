/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Independence.Basic

/-!
# Links between independence and characteristic function

We prove several results of the form: random variables are independent if and only if their
joint characteristic function is equal to the product of the characteristic functions.
More specifically, we prove this in Hilbert spaces for two variables
and a finite family of variables. Then we do the same in Banach spaces, with an arbitrary
Lp norm.
-/

open Complex MeasureTheory Measure WithLp

open scoped ENNReal RealInnerProductSpace

namespace ProbabilityTheory

section InnerProductSpace

section Prod

variable {E F Ω : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace ℝ E]
  [InnerProductSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E} {Y : Ω → F}
  (t : WithLp 2 (E × F))

/-- If two random variables are independent then their joint characteristic function
is the product of the charactersitic functions. This is the version for Hilbert spaces,
see `IndepFun.charFunDual_eq_mul` for the Banach space version. -/
lemma IndepFun.charFun_eq_mul (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) (h : IndepFun X Y μ) :
    charFun (μ.map fun ω ↦ toLp 2 (X ω, Y ω)) t =
      charFun (μ.map X) t.fst * charFun (μ.map Y) t.snd := by
  change charFun (μ.map ((toLp 2) ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable,
    (indepFun_iff_map_prod_eq_prod_map_map mX mY).1 h, charFun_prod]
  all_goals fun_prop

/-- Two random variables are independent if and only if their joint characteristic function
is the product of the charactersitic functions. This is the version for Hilbert spaces,
see `indepFun_iff_charFunDual_eq_mul` for the Banach space version. -/
lemma indepFun_iff_charFun_eq_mul [CompleteSpace E] [CompleteSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ ∀ t,
      charFun (μ.map fun ω ↦ toLp 2 (X ω, Y ω)) t =
      charFun (μ.map X) t.fst * charFun (μ.map Y) t.snd := by
  change _ ↔ ∀ _, charFun (μ.map ((toLp 2) ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, charFun_eq_prod_iff,
    indepFun_iff_map_prod_eq_prod_map_map mX mY]
  all_goals fun_prop

end Prod

section Pi

variable {ι Ω : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Π i, Ω → (E i)}
  (t : PiLp 2 E)

/-- If a finite number of random variables are independent then their joint characteristic function
is the product of the charactersitic functions. This is the version for Hilbert spaces,
see `iIndepFun.charFunDual_eq_pi` for the Banach space version. -/
lemma iIndepFun.charFun_eq_pi (mX : ∀ i, AEMeasurable (X i) μ) (h : iIndepFun X μ) :
    charFun (μ.map fun ω ↦ toLp 2 (X · ω)) t = ∏ i, charFun (μ.map (X i)) (t i) := by
  change charFun (μ.map ((toLp 2) ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, (iIndepFun_iff_map_fun_eq_pi_map mX).1 h, charFun_pi]
  all_goals fun_prop

/-- A finite number of random variables are independent if and only if their joint characteristic
function is the product of the charactersitic functions. This is the version for Hilbert spaces,
see `iIndepFun_iff_charFunDual_eq_pi` for the Banach space version. -/
lemma iIndepFun_iff_charFun_eq_pi [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ t,
      charFun (μ.map fun ω ↦ toLp 2 (X · ω)) t = ∏ i, charFun (μ.map (X i)) (t i) := by
  change _ ↔ ∀ _, charFun (μ.map ((toLp 2) ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, charFun_eq_pi_iff,
    iIndepFun_iff_map_fun_eq_pi_map mX]
  all_goals fun_prop

end Pi

end InnerProductSpace

section NormedSpace

section Prod

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] {E F Ω : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E} {Y : Ω → F}

/-- If two random variables are independent then their joint characteristic function
is the product of the charactersitic functions. This is the version for Banach spaces,
see `IndepFun.charFun_eq_mul` for the Hilbert space version. -/
lemma IndepFun.charFunDual_eq_mul (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ)
    (h : IndepFun X Y μ) (L : NormedSpace.Dual ℝ (E × F)) :
    charFunDual (μ.map fun ω ↦ (X ω, Y ω)) L =
      charFunDual (μ.map X) (L.comp (.inl ℝ E F)) *
      charFunDual (μ.map Y) (L.comp (.inr ℝ E F)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map mX mY).1 h, charFunDual_prod]

/-- If two random variables are independent then their joint characteristic function
is the product of the charactersitic functions. This is `IndepFun.charFunDual_eq_mul` for `WithLp`.
See `IndepFun.charFun_eq_mul` for the Hilbert space version. -/
lemma IndepFun.charFunDual_eq_mul' (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ)
    (h : IndepFun X Y μ) (L : NormedSpace.Dual ℝ (WithLp p (E × F))) :
    charFunDual (μ.map fun ω ↦ toLp p (X ω, Y ω)) L =
      charFunDual (μ.map X) (L.comp (WithLp.inl p ℝ E F).toContinuousLinearMap) *
      charFunDual (μ.map Y) (L.comp (WithLp.inr p ℝ E F).toContinuousLinearMap) := by
  change charFunDual (μ.map ((toLp p) ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable,
    (indepFun_iff_map_prod_eq_prod_map_map mX mY).1 h, charFunDual_prod']
  all_goals fun_prop

/-- Two random variables are independent if and only if their joint characteristic function
is the product of the charactersitic functions. This is the version for Banach spaces,
see `indepFun_iff_charFun_eq_mul` for the Hilbert space version. -/
lemma indepFun_iff_charFunDual_eq_mul [CompleteSpace E] [CompleteSpace F] [BorelSpace E]
    [BorelSpace F] [SecondCountableTopology E] [SecondCountableTopology F]
    (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ ∀ L,
      charFunDual (μ.map fun ω ↦ (X ω, Y ω)) L =
      charFunDual (μ.map X) (L.comp (.inl ℝ E F)) *
      charFunDual (μ.map Y) (L.comp (.inr ℝ E F)) := by
  rw [charFunDual_eq_prod_iff, indepFun_iff_map_prod_eq_prod_map_map mX mY]

/-- Two random variables are independent if and only if their joint characteristic function
is the product of the charactersitic functions. This is `indepFun_iffcharFunDual_eq_mul`
for `WithLp`.
See `indepFun_iff_charFun_eq_mul` for the Hilbert space version. -/
lemma indepFun_iff_charFunDual_eq_mul' [CompleteSpace E] [CompleteSpace F] [BorelSpace E]
    [BorelSpace F] [SecondCountableTopology E] [SecondCountableTopology F]
    (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ ∀ L,
      charFunDual (μ.map fun ω ↦ toLp p (X ω, Y ω)) L =
      charFunDual (μ.map X) (L.comp (WithLp.inl p ℝ E F).toContinuousLinearMap) *
      charFunDual (μ.map Y) (L.comp (WithLp.inr p ℝ E F).toContinuousLinearMap) := by
  change _ ↔ ∀ _, charFunDual (μ.map ((toLp p) ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, charFunDual_eq_prod_iff',
    indepFun_iff_map_prod_eq_prod_map_map mX mY]
  all_goals fun_prop

end Prod

section Pi

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Π i, Ω → (E i)}

/-- If a finite number of random variables are independent then their joint characteristic function
is the product of the charactersitic functions. This is the version for Banach spaces,
see `iIndepFun.charFun_eq_pi` for the Hilbert space version. -/
lemma iIndepFun.charFunDual_eq_pi (mX : ∀ i, AEMeasurable (X i) μ) (h : iIndepFun X μ)
    (L : NormedSpace.Dual ℝ (Π i, E i)) :
    charFunDual (μ.map fun ω i ↦ X i ω) L =
      ∏ i, charFunDual (μ.map (X i)) (L.comp (.single ℝ E i)) := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map mX).1 h, charFunDual_pi]

/-- If a finite number of random variables are independent then their joint characteristic function
is the product of the charactersitic functions. This is `iIndepFun.charFunDual_eq_pi` for `WithLp`.
See `iIndepFun.charFun_eq_pi` for the Hilbert space version. -/
lemma iIndepFun.charFunDual_eq_pi' (mX : ∀ i, AEMeasurable (X i) μ) (h : iIndepFun X μ)
    (L : NormedSpace.Dual ℝ (PiLp p E)) :
    charFunDual (μ.map fun ω ↦ toLp p (X · ω)) L =
      ∏ i, charFunDual (μ.map (X i)) (L.comp (PiLp.single p ℝ).toContinuousLinearMap) := by
  change charFunDual (μ.map ((toLp p) ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, (iIndepFun_iff_map_fun_eq_pi_map mX).1 h,
    charFunDual_pi']
  all_goals fun_prop

/-- A finite number of random variables are independent if and only if their joint characteristic
function is the product of the charactersitic functions. This is the version for Banach spaces,
see `iIndepFun_iff_charFun_eq_pi` for the Hilbert space version. -/
lemma iIndepFun_iff_charFunDual_eq_pi [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ L,
      charFunDual (μ.map fun ω i ↦ X i ω) L =
        ∏ i, charFunDual (μ.map (X i)) (L.comp (.single ℝ E i)) := by
  rw [charFunDual_eq_pi_iff, iIndepFun_iff_map_fun_eq_pi_map mX]

/-- A finite number of random variables are independent if and only if their joint characteristic
function is the product of the charactersitic functions. This is `iIndepFun_iffcharFunDual_eq_pi`
for `WithLp`.
See `iIndepFun_iff_charFun_eq_pi` for the Hilbert space version. -/
lemma iIndepFun_iff_charFunDual_eq_pi' [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ L,
      charFunDual (μ.map fun ω ↦ toLp p (X · ω)) L =
      ∏ i, charFunDual (μ.map (X i)) (L.comp (PiLp.single p ℝ).toContinuousLinearMap) := by
  change _ ↔ ∀ _, charFunDual (μ.map ((toLp p) ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, charFunDual_eq_pi_iff',
    iIndepFun_iff_map_fun_eq_pi_map mX]
  all_goals fun_prop

end Pi

end NormedSpace

end ProbabilityTheory
