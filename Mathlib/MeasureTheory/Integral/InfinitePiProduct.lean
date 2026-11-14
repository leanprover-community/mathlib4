/-
Copyright (c) 2026 darkhipo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: darkhipo
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.ProductMeasure

/-!
# Integration of product families over `Measure.infinitePi`

Mathlib has the finite-index identity `MeasureTheory.integral_fintype_prod_eq_prod`, and the
nonnegative infinite-index analogue follows from `lintegral_tsum`.  There is no analogue for
Bochner integrals: for a countable index type `ι`, a family of probability measures `μ i`, and
Bochner-integrable `f i : X i → ℂ`,

  `∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = ∏' i, ∫ x, f i x ∂(μ i)`.

Monotone convergence cannot be used because the integrands are not nonnegative; instead the proof
takes the limit of the finite-subset products along `atTop` on `Finset ι`, dominated by a constant.
The pointwise convergence comes from `multipliable_one_add_of_summable`, fed by a.e. summability of
`∑ i, ‖f i (x i) - 1‖`, which is Tonelli's theorem over the product measure.

The domination is stated for a **bound family** `‖f i x‖ ≤ C i` with `∑ i, ‖C i - 1‖` summable: the
partial products are bounded by `∏ i ∈ s, C i ≤ exp (∑ i ∈ s, (C i - 1)) ≤ exp (∑' i, ‖C i - 1‖)`,
a constant independent of `s`.  The flat `‖f i x‖ ≤ 1` case is the corollary with `C ≡ 1`, and it is
what the campaign consumes.

## Main results

* `MeasureTheory.integral_finset_prod_infinitePi` — the finite-subset case (the marginal of
  `Measure.infinitePi` on a `Finset` is `Measure.pi`, then `integral_fintype_prod_eq_prod`).
* `MeasureTheory.ae_summable_norm_sub_one_infinitePi` — a.e. summability of `‖f i (x i) - 1‖`.
* `MeasureTheory.hasProd_integral_tprod_infinitePi_of_norm_le` — the convergence form with a norm
  bound family `‖f i x‖ ≤ C i`, `∑ i, ‖C i - 1‖` summable.
* `MeasureTheory.hasProd_integral_tprod_infinitePi` — the convergence form for `‖f i x‖ ≤ 1`
  (the `C ≡ 1` corollary).
* `MeasureTheory.integral_tprod_infinitePi` — the equation form.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

public section

namespace MeasureTheory

variable {ι : Type*} [Countable ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : (i : ι) → Measure (X i)} [hμ : ∀ i, IsProbabilityMeasure (μ i)]

omit [Countable ι] in
/-- **The finite-subset product integral over `Measure.infinitePi`.**  For a `Finset` of
coordinates, the integral of the product family is the product of the integrals. -/
theorem integral_finset_prod_infinitePi {f : (i : ι) → X i → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i)) (s : Finset ι) :
    ∫ x, ∏ i ∈ s, f i (x i) ∂(Measure.infinitePi μ) = ∏ i ∈ s, ∫ x, f i x ∂(μ i) := by
  classical
  have hp : MeasurePreserving (Finset.restrict (π := X) s) (Measure.infinitePi μ)
      (Measure.pi fun i : s => μ i.1) :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict μ⟩
  have hgmeas : AEStronglyMeasurable (fun y : (i : s) → X i.1 => ∏ i, f i.1 (y i))
      (Measure.pi fun i : s => μ i.1) := by
    have := Finset.aestronglyMeasurable_fun_prod (μ := Measure.pi fun j : s => μ j.1)
      (s := (Finset.univ : Finset s)) (f := fun (i : s) (y : (j : s) → X j.1) => f i.1 (y i))
      (fun i _ => (hf i.1).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i))
    simpa using this
  have key : ∫ y : (i : s) → X i.1, ∏ i, f i.1 (y i) ∂(Measure.pi fun i : s => μ i.1)
      = ∏ i : s, ∫ x, f i.1 x ∂(μ i.1) :=
    integral_fintype_prod_eq_prod (f := fun (i : s) (y : X i.1) => f i.1 y)
  have hcomp : ∫ x : (i : ι) → X i, ∏ i ∈ s, f i (x i) ∂(Measure.infinitePi μ)
      = ∫ y : (i : s) → X i.1, ∏ i, f i.1 (y i) ∂(Measure.pi fun i : s => μ i.1) := by
    rw [← hp.map_eq, integral_map hp.aemeasurable (by rw [hp.map_eq]; exact hgmeas)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Finset.restrict]
    exact (Finset.prod_coe_sort s (fun i => f i (x i))).symm
  rw [hcomp, key, Finset.prod_coe_sort (s := s) (f := fun i => ∫ x, f i x ∂(μ i))]

/-- **A.e. summability of the deviations from `1`.**  Tonelli over the product measure turns the
hypothesis on the sum of the `∫⁻`-norms into a.e. summability of `∑ i, ‖f i (x i) - 1‖`. -/
theorem ae_summable_norm_sub_one_infinitePi {f : (i : ι) → X i → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hsum : (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ⊤) :
    ∀ᵐ x ∂(Measure.infinitePi μ), Summable fun i => ‖f i (x i) - 1‖ := by
  have hφ : ∀ i, AEMeasurable (fun y => (‖f i y - 1‖₊ : ℝ≥0∞)) (μ i) := fun i =>
    (((hf i).aemeasurable.sub aestronglyMeasurable_const.aemeasurable).nnNorm).coe_nnreal_ennreal
  have hmeas : ∀ i, AEMeasurable (fun x : (j : ι) → X j => (‖f i (x i) - 1‖₊ : ℝ≥0∞))
      (Measure.infinitePi μ) := by
    intro i
    exact ((((hf i).comp_quasiMeasurePreserving
      (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving).aemeasurable.sub
        aestronglyMeasurable_const.aemeasurable).nnNorm).coe_nnreal_ennreal
  have hcomp : ∀ i, ∫⁻ x : (j : ι) → X j, (‖f i (x i) - 1‖₊ : ℝ≥0∞) ∂(Measure.infinitePi μ)
      = ∫⁻ y, (‖f i y - 1‖₊ : ℝ≥0∞) ∂(μ i) := by
    intro i
    have hmap := Measure.infinitePi_map_eval (μ := μ) (i := i)
    rw [← hmap]
    have hf' : AEMeasurable (fun y => (‖f i y - 1‖₊ : ℝ≥0∞))
        (Measure.map (fun x : (j : ι) → X j => x i) (Measure.infinitePi μ)) := by
      rw [hmap]; exact hφ i
    exact (lintegral_map' hf' (measurable_pi_apply i).aemeasurable).symm
  have hfin :
      ∫⁻ x, ∑' i, (‖f i (x i) - 1‖₊ : ℝ≥0∞) ∂(Measure.infinitePi μ) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    simpa only [hcomp] using hsum
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) hfin] with x hx
  have hx' : Summable fun i => (‖f i (x i) - 1‖₊ : ℝ≥0) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp (ne_of_lt hx)
  simpa only [coe_nnNorm] using NNReal.summable_coe.mpr hx'

/-- **The dominated core**, shared by the two bounded versions below: if the partial products are
a.e. uniformly bounded by a constant `K`, the finite-subset integrals converge to the integral of
the pointwise product. -/
private theorem hasProd_integral_tprod_infinitePi_of_bound {f : (i : ι) → X i → ℂ} {K : ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hbdd : ∀ᵐ x ∂(Measure.infinitePi μ), ∀ s : Finset ι, ‖∏ i ∈ s, f i (x i)‖ ≤ K)
    (hsum : (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ⊤) :
    HasProd (fun i => ∫ x, f i x ∂(μ i))
      (∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ)) := by
  classical
  -- a.e. pointwise multipliability
  have hconv : ∀ᵐ x ∂(Measure.infinitePi μ),
      Tendsto (fun s : Finset ι => ∏ i ∈ s, f i (x i)) atTop (𝓝 (∏' i, f i (x i))) := by
    filter_upwards [ae_summable_norm_sub_one_infinitePi hf hsum] with x hx
    have hM : Multipliable fun i => f i (x i) := by
      have h := multipliable_one_add_of_summable (f := fun i => f i (x i) - 1) hx
      have hfun : (fun i => 1 + (f i (x i) - 1)) = fun i => f i (x i) := by
        funext i; ring
      rwa [hfun] at h
    exact hM.hasProd
  -- dominated convergence over the filter `atTop` on `Finset ι`
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (F := fun (s : Finset ι) (x : (i : ι) → X i) => ∏ i ∈ s, f i (x i))
    (f := fun x => ∏' i, f i (x i)) (bound := fun _ => K)
    (Filter.Eventually.of_forall fun s =>
      Finset.aestronglyMeasurable_fun_prod s fun i _ =>
        (hf i).comp_quasiMeasurePreserving
          (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving)
    (Filter.Eventually.of_forall fun s => hbdd.mono fun x hx => hx s)
    (integrable_const K) hconv
  rw [HasProd]
  refine hDCT.congr' (Filter.Eventually.of_forall fun s => ?_)
  exact integral_finset_prod_infinitePi hf s

/-- **The Bochner product integral over `Measure.infinitePi`, with a norm bound family.**

For a countable index type, probability measures `μ i`, measurable `f i : X i → ℂ` bounded in norm
by a family `C i ≥ 0` with `∑ i, ‖C i - 1‖` summable, and `∑ i, ∫⁻ x, ‖f i x - 1‖` finite, the
family of integrals is multipliable and its product is the integral of the pointwise infinite
product.

The bound family is what the dominated-convergence step needs: `‖∏ i ∈ s, f i (x i)‖` is at most
`∏ i ∈ s, C i`, and `C i ≤ exp (C i - 1)` turns the product of the bounds into
`exp (∑ i ∈ s, (C i - 1)) ≤ exp (∑' i, ‖C i - 1‖)`, a constant independent of `s`.  (The `≤ 1` case
`C ≡ 1` is the corollary below; a bare `∑ i, C i < ∞` would **not** suffice, since a product of
bounds is not additive in them.) -/
theorem hasProd_integral_tprod_infinitePi_of_norm_le {f : (i : ι) → X i → ℂ} {C : ι → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hC0 : ∀ i, 0 ≤ C i)
    (hb : ∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ C i)
    (hC : Summable fun i => ‖C i - 1‖)
    (hsum : (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ⊤) :
    HasProd (fun i => ∫ x, f i x ∂(μ i))
      (∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ)) := by
  classical
  refine hasProd_integral_tprod_infinitePi_of_bound
    (K := Real.exp (∑' i, ‖C i - 1‖)) hf ?_ hsum
  -- the a.e. norm bound `∀ i, ‖f i (x i)‖ ≤ C i`
  have hbnd : ∀ᵐ x ∂(Measure.infinitePi μ), ∀ i, ‖f i (x i)‖ ≤ C i := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving.ae (hb i)
  filter_upwards [hbnd] with x hx
  intro s
  -- ‖∏ f i‖ ≤ ∏ C i ≤ ∏ exp (C i - 1) = exp (∑ (C i - 1)) ≤ exp (∑' ‖C i - 1‖)
  have hnorm : ‖∏ i ∈ s, f i (x i)‖ = ∏ i ∈ s, ‖f i (x i)‖ := by simp
  rw [hnorm]
  calc ∏ i ∈ s, ‖f i (x i)‖
      ≤ ∏ i ∈ s, C i := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hx i
    _ ≤ ∏ i ∈ s, Real.exp (C i - 1) :=
        Finset.prod_le_prod₀ (fun i _ => hC0 i) fun i _ => by
          have h := Real.add_one_le_exp (C i - 1)
          linarith
    _ = Real.exp (∑ i ∈ s, (C i - 1)) := (Real.exp_sum s _).symm
    _ ≤ Real.exp (∑' i, ‖C i - 1‖) := Real.exp_le_exp.mpr <| by
        calc ∑ i ∈ s, (C i - 1) ≤ ∑ i ∈ s, ‖C i - 1‖ :=
              Finset.sum_le_sum fun i _ => le_abs_self _
          _ ≤ ∑' i, ‖C i - 1‖ := hC.sum_le_tsum s fun i _ => norm_nonneg _

/-- **The Bochner product integral over `Measure.infinitePi`, convergence form.**

For a countable index type, probability measures `μ i`, and measurable `f i : X i → ℂ` bounded by
`1` in norm, with `∑ i, ∫⁻ x, ‖f i x - 1‖` finite, the family of integrals is multipliable and its
product is the integral of the pointwise infinite product. -/
theorem hasProd_integral_tprod_infinitePi {f : (i : ι) → X i → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hb : ∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ 1)
    (hsum : (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ⊤) :
    HasProd (fun i => ∫ x, f i x ∂(μ i))
      (∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ)) :=
  have hC : Summable fun i => ‖((fun _ => (1 : ℝ)) i) - 1‖ := by
    have hzero : (fun i : ι => ‖((fun _ => (1 : ℝ)) i) - 1‖) = fun _ => 0 := by
      funext i; simp
    rw [hzero]; exact summable_zero
  hasProd_integral_tprod_infinitePi_of_norm_le (C := fun _ => 1) hf (fun _ => zero_le_one)
    (fun i => hb i) hC hsum

/-- **The Bochner product integral over `Measure.infinitePi`, equation form.** -/
theorem integral_tprod_infinitePi {f : (i : ι) → X i → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hb : ∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ 1)
    (hsum : (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ⊤) :
    ∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = ∏' i, ∫ x, f i x ∂(μ i) :=
  (hasProd_integral_tprod_infinitePi hf hb hsum).tprod_eq.symm

end MeasureTheory
