/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Integration with respect to a finite product of measures

On a finite product of measure spaces, we show that a product of integrable functions each
depending on a single coordinate is integrable, in `MeasureTheory.integrable_fintype_prod`, and
that its integral is the product of the individual integrals,
in `MeasureTheory.integral_fintype_prod_eq_prod`.
-/

public section

open Fintype MeasureTheory MeasureTheory.Measure

namespace MeasureTheory

variable {𝕜 ι : Type*} [Fintype ι]

namespace Integrable

variable [NormedCommRing 𝕜]

/-- On a finite product space in `n` variables, for a natural number `n`, a product of integrable
functions depending on each coordinate is integrable. -/
theorem fin_nat_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → E i → 𝕜} (hf : ∀ i, Integrable (f i) (μ i)) :
    Integrable (fun (x : (i : Fin n) → E i) ↦ ∏ i, f i (x i)) (Measure.pi μ) := by
  induction n with
  | zero => simp only [Finset.univ_eq_empty, Finset.prod_empty, isFiniteMeasure_iff,
      integrable_const_iff, pi_empty_univ, ENNReal.one_lt_top, or_true]
  | succ n n_ih =>
      have := ((measurePreserving_piFinSuccAbove μ 0).symm)
      rw [← this.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero]
      simp only [Fin.zero_succAbove, cast_eq, Function.comp_def]
      have : Integrable (fun (x : (j : Fin n) → E (Fin.succ j)) ↦ ∏ j, f (Fin.succ j) (x j))
          (Measure.pi (fun i ↦ μ i.succ)) :=
        n_ih (fun i ↦ hf _)
      exact Integrable.mul_prod (hf 0) this

/-- On a finite product space, a product of integrable functions depending on each coordinate is
integrable. Version with dependent target. -/
theorem fintype_prod_dep {E : ι → Type*}
    {f : (i : ι) → E i → 𝕜} {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Integrable (f i) (μ i)) :
    Integrable (fun (x : (i : ι) → E i) ↦ ∏ i, f i (x i)) (Measure.pi μ) := by
  let e := (equivFin ι).symm
  simp_rw [← (measurePreserving_piCongrLeft _ e).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _),
    ← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Function.comp_def,
    Equiv.piCongrLeft_apply_apply]
  exact .fin_nat_prod (fun i ↦ hf _)

/-- On a finite product space, a product of integrable functions depending on each coordinate is
integrable. -/
theorem fintype_prod {E : Type*}
    {f : ι → E → 𝕜} {mE : MeasurableSpace E} {μ : ι → Measure E} [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Integrable (f i) (μ i)) :
    Integrable (fun (x : ι → E) ↦ ∏ i, f i (x i)) (Measure.pi μ) :=
  Integrable.fintype_prod_dep hf

end Integrable

variable [RCLike 𝕜]

set_option backward.isDefEq.respectTransparency false in
/-- A version of **Fubini's theorem** in `n` variables, for a natural number `n`. -/
theorem integral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → 𝕜) :
    ∫ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp [measureReal_def]
  | succ n n_ih =>
      calc
        _ = ∫ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih, ← integral_prod_mul]
        _ = ∏ i, ∫ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- A version of **Fubini's theorem** in `n` variables, for a natural number `n`. -/
theorem integral_fin_nat_prod_volume_eq_prod {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))]
    (f : (i : Fin n) → E i → 𝕜) :
    ∫ x : (i : Fin n) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := integral_fin_nat_prod_eq_prod _

/-- A version of **Fubini's theorem** with the variables indexed by a general finite type. -/
theorem integral_fintype_prod_eq_prod {E : ι → Type*} (f : (i : ι) → E i → 𝕜)
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] :
    ∫ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫ x, f i x ∂(μ i) := by
  let e := (equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).integral_comp']
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
    MeasureTheory.integral_fin_nat_prod_eq_prod]

/-- A version of **Fubini's theorem** with the variables indexed by a general finite type. -/
theorem integral_fintype_prod_volume_eq_prod {E : ι → Type*} (f : (i : ι) → E i → 𝕜)
    [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))] :
    ∫ x : (i : ι) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := integral_fintype_prod_eq_prod _

theorem integral_fintype_prod_eq_pow {E : Type*} (f : E → 𝕜) {mE : MeasurableSpace E}
    {μ : Measure E} [SigmaFinite μ] :
    ∫ x : ι → E, ∏ i, f (x i) ∂(Measure.pi (fun _ ↦ μ)) = (∫ x, f x ∂μ) ^ (card ι) := by
  rw [integral_fintype_prod_eq_prod, Finset.prod_const, card]

theorem integral_fintype_prod_volume_eq_pow {E : Type*} (f : E → 𝕜)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∫ x : ι → E, ∏ i, f (x i) = (∫ x, f x) ^ (card ι) := integral_fintype_prod_eq_pow _

variable {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    {E : Type*} [NormedAddCommGroup E]

lemma integrable_comp_eval [∀ i, IsFiniteMeasure (μ i)] {i : ι} {f : X i → E}
    (hf : Integrable f (μ i)) :
    Integrable (fun x ↦ f (x i)) (Measure.pi μ) := by
  refine Integrable.comp_measurable ?_ (by fun_prop)
  classical
  rw [Measure.pi_map_eval]
  exact hf.smul_measure <| ENNReal.prod_ne_top (by finiteness)

lemma integrable_eval [∀ i, NormedAddCommGroup (X i)] [∀ i, IsFiniteMeasure (μ i)] {i : ι}
    (h : Integrable id (μ i)) :
    Integrable (fun x ↦ x i) (Measure.pi μ) :=
  integrable_comp_eval h

lemma integral_comp_eval [NormedSpace ℝ E] [∀ i, IsProbabilityMeasure (μ i)] {i : ι} {f : X i → E}
    (hf : AEStronglyMeasurable f (μ i)) :
    ∫ x : Π i, X i, f (x i) ∂Measure.pi μ = ∫ x, f x ∂μ i := by
  rw [← (measurePreserving_eval μ i).map_eq, integral_map]
  · exact Measurable.aemeasurable (by fun_prop)
  · rwa [(measurePreserving_eval μ i).map_eq]

lemma integral_eval [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    [∀ i, IsProbabilityMeasure (μ i)] {i : ι} [OpensMeasurableSpace (X i)]
    [SecondCountableTopology (X i)] :
    ∫ x, x i ∂Measure.pi μ = ∫ x, x ∂μ i :=
  integral_comp_eval aestronglyMeasurable_id

end MeasureTheory
