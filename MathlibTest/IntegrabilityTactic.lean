import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.NumberTheory.Chebyshev

/-!
# Integrability tactic examples

These examples collect small integrability goals found by grepping mathlib for `Integrable`.
The proofs are all `sorry`: this file is a goal suite for a future integrability tactic.

update by running: `scripts/update-integrability-tactic-counts.sh`
CURRENT PASSING TEST: 18 / 189

-/

open MeasureTheory Set
open Filter Asymptotics
open scoped Topology BoundedContinuousFunction Interval

section BasicClosure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

example : Integrable (fun _ : α => (0 : ℝ)) μ := by
  fail_if_success fun_prop
  sorry

example [IsFiniteMeasure μ] (c : ℝ) : Integrable (fun _ : α => c) μ := by
  fun_prop

example [IsFiniteMeasure μ] (c : ℂ) : Integrable (fun _ : α => c) μ := by
  fun_prop

example {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => f x + g x) μ := by
  fun_prop

example {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => f x - g x) μ := by
  fun_prop

example {f : α → ℝ} (hf : Integrable f μ) : Integrable (fun x => -f x) μ := by
  fun_prop

example {f : α → ℝ} (hf : Integrable f μ) (c : ℝ) :
    Integrable (fun x => c * f x) μ := by
  fun_prop

example {f : α → ℂ} (hf : Integrable f μ) (c : ℂ) :
    Integrable (fun x => c * f x) μ := by
  fun_prop

example {f : α → ℝ} (hf : Integrable f μ) (c : ℝ) :
    Integrable (fun x => f x / c) μ := by
  fun_prop

example {f : α → ℝ} (hf : Integrable f μ) : Integrable (fun x => ‖f x‖) μ := by
  fun_prop

example {f : α → ℂ} (hf : Integrable f μ) : Integrable (fun x => Complex.re (f x)) μ := by
  fail_if_success fun_prop
  sorry

example {f : α → ℂ} (hf : Integrable f μ) : Integrable (fun x => Complex.im (f x)) μ := by
  fail_if_success fun_prop
  sorry

example {f : α → ℝ} (hf : Integrable f μ) {s : Set α} : Integrable f (μ.restrict s) := by
  fail_if_success fun_prop
  sorry

example {β : Type*} [MeasurableSpace β] {ν : Measure β} {f : α → β} {g : β → ℝ}
    (hg : Integrable g (Measure.map f μ)) : Integrable (fun x => g (f x)) μ := by
  fail_if_success fun_prop
  sorry

example {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => (f x, g x)) μ := by
  fun_prop

end BasicClosure

section IntervalIntegrable

example (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => x ^ 2 + Real.sin x) volume a b := by
  fail_if_success fun_prop
  sorry

example (a b : ℝ) : IntervalIntegrable (fun x : ℝ => Real.exp x) volume a b := by
  fail_if_success fun_prop
  sorry

example (a b : ℝ) : IntervalIntegrable (fun x : ℝ => Real.cos x) volume a b := by
  fail_if_success fun_prop
  sorry

example (a b : ℝ) : IntervalIntegrable (fun x : ℝ => x ^ 5) volume a b := by
  fail_if_success fun_prop
  sorry

example (a b r : ℝ) : IntervalIntegrable (fun x : ℝ => Real.exp x * Real.sin (r * x)) volume a b := by
  fail_if_success fun_prop
  sorry

example (a b : ℝ) : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ 3) volume a b := by
  fail_if_success fun_prop
  sorry

example (a b : ℝ) : IntervalIntegrable (fun x : ℝ => (x : ℂ) * Complex.exp (x : ℂ)) volume a b := by
  fail_if_success fun_prop
  sorry

example (a b : ℝ) : IntervalIntegrable (fun x : ℝ => ‖Real.sin x‖) volume a b := by
  fail_if_success fun_prop
  sorry

end IntervalIntegrable

section IntegrableOn

example (a b : ℝ) : IntegrableOn (fun x : ℝ => Real.sin x + x ^ 2) (Icc a b) := by
  fail_if_success fun_prop
  sorry

example (a b : ℝ) : IntegrableOn (fun x : ℝ => Real.exp x) (Icc a b) := by
  fail_if_success fun_prop
  sorry

example (a b : ℝ) : IntegrableOn (fun x : ℝ => (x, Real.exp x)) (Icc a b) := by
  fail_if_success fun_prop
  sorry

example (a b : ℝ) : IntegrableOn (fun x : ℝ => (Real.sin x : ℂ)) (Icc a b) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} {s t : Set ℝ} (hf : IntegrableOn f t) (hst : s ⊆ t) : IntegrableOn f s := by
  fail_if_success fun_prop
  sorry

example : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
  fail_if_success fun_prop
  sorry

example (c : ℝ) : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi c) := by
  fail_if_success fun_prop
  sorry

example (c : ℝ) : IntegrableOn Real.exp (Iic c) := by
  fail_if_success fun_prop
  sorry

example {s : ℝ} (hs : s < -1) : IntegrableOn (fun x : ℝ => x ^ s) (Ioi 1) := by
  fail_if_success fun_prop
  sorry

example {s t : ℝ} (ht : 0 < t) (hs : -1 < s) : IntegrableOn (fun x : ℝ => x ^ s) (Ioo 0 t) := by
  fail_if_success fun_prop
  sorry

end IntegrableOn

section LocallyIntegrable

example : LocallyIntegrable (fun x : ℝ => Real.sin x + x ^ 2) := by
  fail_if_success fun_prop
  sorry

example : LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) := by
  fail_if_success fun_prop
  sorry

example : LocallyIntegrable (fun x : ℝ => (x : ℂ) * Complex.exp (x : ℂ)) := by
  fail_if_success fun_prop
  sorry

example : LocallyIntegrableOn (fun x : ℝ => Real.log x) (Ioi 0) := by
  fail_if_success fun_prop
  sorry

example : LocallyIntegrableOn (fun x : ℝ => x⁻¹) ({0}ᶜ : Set ℝ) := by
  fail_if_success fun_prop
  sorry

example (a b : ℝ) : IntegrableOn (fun x : ℝ => Real.sin x + x ^ 2) (Icc a b) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} (hf : LocallyIntegrable f) (a b : ℝ) : IntegrableOn f (Icc a b) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℝ} (hf : LocallyIntegrable f) (hg : LocallyIntegrable g) :
    LocallyIntegrable (fun x => f x + g x) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℂ} (hf : LocallyIntegrable f) (hg : LocallyIntegrable g) :
    LocallyIntegrable (fun x => f x - g x) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℂ} (hf : LocallyIntegrable f) : LocallyIntegrable (fun x => -f x) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℂ} (hf : LocallyIntegrable f) : LocallyIntegrable (fun x => ‖f x‖) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℂ} (hf : LocallyIntegrable f) (c : ℂ) :
    LocallyIntegrable (fun x => c * f x) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℂ} (hf : LocallyIntegrable f) (c : ℂ) :
    LocallyIntegrable (fun x => c • f x) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℝ} (hf : LocallyIntegrable f) (hg : LocallyIntegrable g) :
    LocallyIntegrable (fun x => (f x, g x)) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} (hf : Integrable f) : LocallyIntegrable f := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) : LocallyIntegrableOn f (Ioi 0) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} {s t : Set ℝ} (hf : LocallyIntegrableOn f t) (hst : s ⊆ t) :
    LocallyIntegrableOn f s := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℂ} {s : Set ℝ} (hf : LocallyIntegrableOn f s) :
    LocallyIntegrableOn (fun x => ‖f x‖) s := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℂ} {s : Set ℝ} (hf : LocallyIntegrableOn f s)
    (hg : LocallyIntegrableOn g s) : LocallyIntegrableOn (fun x => f x + g x) s := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℂ} {s : Set ℝ} (hf : LocallyIntegrableOn f s)
    (hg : LocallyIntegrableOn g s) : LocallyIntegrableOn (fun x => f x - g x) s := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℂ} {s : Set ℝ} (hf : LocallyIntegrableOn f s) :
    LocallyIntegrableOn (fun x => -f x) s := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} {s : Set ℝ} (hf : LocallyIntegrable f) : LocallyIntegrableOn f s := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} {s : Set ℝ} (hf : LocallyIntegrable f) (hs : MeasurableSet s) :
    LocallyIntegrable (s.indicator f) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} {s K : Set ℝ} (hf : LocallyIntegrableOn f s) (hK : IsCompact K)
    (hKs : K ⊆ s) : IntegrableOn f K := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℂ} (hf : LocallyIntegrable f) (a b : ℝ) : IntegrableOn f (Icc a b) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} (hf : LocallyIntegrable f) (a b : ℝ) : IntegrableOn (fun x => ‖f x‖) (Icc a b) := by
  fail_if_success fun_prop
  sorry

example {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    (hf : ∀ i, i ∈ s → LocallyIntegrable (f i)) :
    LocallyIntegrable (fun x => ∑ i ∈ s, f i x) := by
  fail_if_success fun_prop
  sorry

example {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℂ}
    (hf : ∀ i, i ∈ s → LocallyIntegrable (f i)) :
    LocallyIntegrable (fun x => ∑ i ∈ s, f i x) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} (hf : Monotone f) : LocallyIntegrable f := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} (hf : Antitone f) : LocallyIntegrable f := by
  fail_if_success fun_prop
  sorry

example : LocallyIntegrableOn (fun x : ℝ => Real.sqrt x) (Ioi 0) := by
  fail_if_success fun_prop
  sorry

example {r : ℝ} : LocallyIntegrableOn (fun x : ℝ => x ^ r) (Ioi 0) := by
  fail_if_success fun_prop
  sorry

example {r : ℂ} : LocallyIntegrableOn (fun x : ℝ => (x : ℂ) ^ r) (Ioi 0) := by
  fail_if_success fun_prop
  sorry

example : LocallyIntegrableOn (fun x : ℝ => Real.log ‖x‖) ({0}ᶜ : Set ℝ) := by
  fail_if_success fun_prop
  sorry

example : LocallyIntegrableOn (fun x : ℝ => (x : ℂ)⁻¹) ({0}ᶜ : Set ℝ) := by
  fail_if_success fun_prop
  sorry

example : LocallyIntegrableOn (fun x : ℝ => Real.exp (-x ^ 2) / (1 + x ^ 2)) univ := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} {s : Set ℝ} (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    LocallyIntegrableOn f s := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℂ} {s : Set ℝ} (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    LocallyIntegrableOn f s := by
  fail_if_success fun_prop
  sorry

end LocallyIntegrable

section DominationAndSpecialFunctions

example {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ (1 : ℝ)) [IsFiniteMeasure μ] :
    Integrable f μ := by
  fail_if_success fun_prop
  sorry

example {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    Integrable f μ := by
  fail_if_success fun_prop
  sorry

example {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ) (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖) :
    Integrable g μ := by
  fail_if_success fun_prop
  sorry

example : Integrable fun x : ℝ => Real.exp (-x ^ 2) := by
  fail_if_success fun_prop
  sorry

example {b : ℝ} (hb : 0 < b) : Integrable fun x : ℝ => Real.exp (-b * x ^ 2) := by
  fail_if_success fun_prop
  sorry

example {b : ℝ} (hb : 0 < b) : Integrable fun x : ℝ => x * Real.exp (-b * x ^ 2) := by
  fail_if_success fun_prop
  sorry

example {b : ℝ} (hb : 0 < b) : Integrable fun x : ℝ => Complex.exp (-b * (x : ℂ) ^ 2) := by
  fail_if_success fun_prop
  sorry

example : Integrable fun x : ℝ => (1 + x ^ 2)⁻¹ := by
  fail_if_success fun_prop
  sorry

example : Integrable fun x : ℝ => ‖(1 + x ^ 2)⁻¹‖ := by
  fail_if_success fun_prop
  sorry

end DominationAndSpecialFunctions

section BoundedMultipliersAndCompactSupport

example {f g : ℝ → ℝ} (hf : Integrable f) (hg : AEStronglyMeasurable g)
    (hbg : ∀ᵐ x ∂volume, ‖g x‖ ≤ (3 : ℝ)) : Integrable (fun x => f x * g x) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℂ} (hf : Integrable f) (hg : AEStronglyMeasurable g)
    (hbg : ∀ᵐ x ∂volume, ‖g x‖ ≤ (3 : ℝ)) : Integrable (fun x => f x * g x) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℝ} (hf : Integrable f) (hg : Continuous g)
    (hbg : BddAbove (range fun x => ‖g x‖)) : Integrable (fun x => f x * g x) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f)
    (hg : LocallyIntegrable g) : Integrable (fun x => f x * g x) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℂ} (hf : Continuous f) (hcf : HasCompactSupport f)
    (hg : LocallyIntegrable g) : Integrable (fun x => f x * g x) := by
  fail_if_success fun_prop
  sorry

example {K : Set ℝ} {f g : ℝ → ℝ} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hg : IntegrableOn g K) : IntegrableOn (fun x => f x * g x) K := by
  fail_if_success fun_prop
  sorry

example {K : Set ℝ} {f : ℝ → ℝ} {g : ℝ → ℂ} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hg : IntegrableOn g K) : IntegrableOn (fun x => (f x : ℂ) * g x) K := by
  fail_if_success fun_prop
  sorry

end BoundedMultipliersAndCompactSupport

section ProductMeasureAndConvolutionShapes

example {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => f p.2 * g (p.1 - p.2)) (volume.prod volume) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => f p.2 * g (p.1 - p.2)) (volume.prod volume) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => ‖f (p.1 - p.2)‖ * ‖g p.2‖) (volume.prod volume) := by
  fail_if_success fun_prop
  sorry

example {f g k : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (hk : Integrable k)
    (x₀ : ℝ) :
    Integrable (fun p : ℝ × ℝ => f p.2 * (g p.1 * k (x₀ - p.2 - p.1)))
      (volume.prod volume) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℝ} {s : Set ℝ} (x₀ : ℝ)
    (hsupp : Function.support (fun t => f t * g (x₀ - t)) ⊆ s) (hf : IntegrableOn f s)
    (hg : Continuous g) : Integrable (fun t => f t * g (x₀ - t)) := by
  fail_if_success fun_prop
  sorry

end ProductMeasureAndConvolutionShapes

section FiniteSumsAndFamilies

variable {ι : Type*} [Fintype ι]

example {f : ι → ℝ → ℝ} (hf : ∀ i, Integrable (f i)) :
    Integrable (fun x => ∑ i, f i x) := by
  fun_prop

example {f : ι → ℝ → ℂ} (hf : ∀ i, Integrable (f i)) :
    Integrable (fun x => ∑ i, f i x) := by
  fun_prop

example {a : ι → ℝ} {f : ι → ℝ → ℝ} (hf : ∀ i, Integrable (f i)) :
    Integrable (fun x => ∑ i, a i * f i x) := by
  fun_prop

example {a : ι → ℂ} {f : ι → ℝ → ℂ} (hf : ∀ i, Integrable (f i)) :
    Integrable (fun x => ∑ i, a i * f i x) := by
  fun_prop

example {s : Finset ι} {f : ι → ℝ → ℝ} (hf : ∀ i, i ∈ s → Integrable (f i)) :
    Integrable (fun x => ∑ i ∈ s, f i x) := by
  fail_if_success fun_prop
  sorry

end FiniteSumsAndFamilies

section ParametricDominatedShapes

example {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℝ → α → ℝ} {bound : α → ℝ}
    {x₀ ε : ℝ} (hε : 0 < ε) (hF_meas : ∀ x ∈ Metric.ball x₀ ε, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ Metric.ball x₀ ε, ‖F x a‖ ≤ bound a)
    (hbound : Integrable bound μ) : ∀ x ∈ Metric.ball x₀ ε, Integrable (F x) μ := by
  fail_if_success fun_prop
  sorry

example {α : Type*} [MeasurableSpace α] {μ : Measure α} {F' : ℝ → α → ℝ} {bound : α → ℝ}
    {s : Set ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ s) (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (hbound : Integrable bound μ) :
    Integrable (F' x₀) μ := by
  fail_if_success fun_prop
  sorry

example {F F' : ℝ → ℝ → ℝ} {bound : ℝ → ℝ} {a b x₀ : ℝ}
    (hF_int : IntervalIntegrable (F x₀) volume a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Ioc a b)))
    (h_bound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖F' x₀ t‖ ≤ bound t)
    (hbound : IntervalIntegrable bound volume a b) : IntervalIntegrable (F' x₀) volume a b := by
  fail_if_success fun_prop
  sorry

end ParametricDominatedShapes

section WeightedTailsAndSpecialFunctions

example {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (s - 1)) (Ioi 0) := by
  fail_if_success fun_prop
  sorry

example {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => ((Real.exp (-x) * x ^ (s - 1) : ℝ) : ℂ)) (Ioi 0) := by
  fail_if_success fun_prop
  sorry

example {s X : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun x : ℝ => ((Real.exp (-x) * x ^ (s - 1) : ℝ) : ℂ)) volume 0 X := by
  fail_if_success fun_prop
  sorry

example {s : ℝ} (hs : 0 < s) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ (s - 1) * Real.exp (-x)) (Ioi c) := by
  fail_if_success fun_prop
  sorry

example {a : ℂ} (ha : a.re < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Ioi c) := by
  fail_if_success fun_prop
  sorry

example {a : ℂ} (ha : 0 < a.re) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Iic c) := by
  fail_if_success fun_prop
  sorry

example {s t : ℝ} (ht : 0 < t) (hs : s < -1) :
    IntegrableOn (fun x : ℝ => x ^ s * Real.log x) (Ioi t) := by
  fail_if_success fun_prop
  sorry

example {s t : ℝ} (ht : 0 < t) (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s * Real.log x) (Ioo 0 t) := by
  fail_if_success fun_prop
  sorry

example {b s : ℝ} (hb : 0 < b) (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s * Real.exp (-b * x ^ 2)) (Ioi 0) := by
  fail_if_success fun_prop
  sorry

example {b s : ℝ} (hb : 0 < b) (hs : -1 < s) :
    Integrable fun x : ℝ => x ^ s * Real.exp (-b * x ^ 2) := by
  fail_if_success fun_prop
  sorry

end WeightedTailsAndSpecialFunctions

section ComplexPathStyleIntervalGoals

example {f : ℂ → ℂ} (hf : Continuous f) (a₁ a₂ b : ℝ) :
    IntervalIntegrable (fun x : ℝ => f (x + b * Complex.I)) volume a₁ a₂ := by
  fail_if_success fun_prop
  sorry

example {f : ℂ → ℂ} (hf : Continuous f) (a b₁ b₂ : ℝ) :
    IntervalIntegrable (fun y : ℝ => f (a + y * Complex.I)) volume b₁ b₂ := by
  fail_if_success fun_prop
  sorry

example {f f' : ℂ → ℂ → ℂ} {z w : ℂ} :
    IntegrableOn (fun u : ℂ => Complex.I • f' u 1 - f' u Complex.I)
      {u : ℂ | u.re ∈ Icc z.re w.re ∧ u.im ∈ Icc z.im w.im} := by
  fail_if_success fun_prop
  sorry

end ComplexPathStyleIntervalGoals

section Database1SelectedGoals

/-! Selected goals translated from `integrable_database1.txt`. -/

-- Asymptotics.IsBigO.integrableAtFilter / Asymptotics.IsBigO.integrable
example {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure α} {l : Filter α} [l.IsMeasurablyGenerated] {f : α → E} {g : α → F}
    (hf : f =O[l] g) (hfm : StronglyMeasurableAtFilter f l μ)
    (hg : IntegrableAtFilter g l μ) : IntegrableAtFilter f l μ := by
  fail_if_success fun_prop
  sorry

example {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure α} {f : α → E} {g : α → F} (hf : f =O[⊤] g)
    (hfm : AEStronglyMeasurable f μ) (hg : Integrable g μ) : Integrable f μ := by
  fail_if_success fun_prop
  sorry

-- BddAbove.convolutionExistsAt'
example {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {μ : Measure ℝ} {f : ℝ → E} {g : ℝ → F} (L : E →L[ℝ] F →L[ℝ] G) (x₀ : ℝ) :
    Integrable (fun t => L (f t) (g (x₀ - t))) μ := by
  fail_if_success fun_prop
  sorry

example {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → E} {g : ℝ → F}
    (L : E →L[ℝ] F →L[ℝ] G) (x₀ : ℝ) :
    IntegrableOn (fun t => L (f t) (g (x₀ - t))) s μ := by
  fail_if_success fun_prop
  sorry

example {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → E} {g : ℝ → F}
    (L : E →L[ℝ] F →L[ℝ] G) (C : ℝ) :
    Integrable (s.indicator fun t => ‖L‖ * ‖f t‖ * C) (μ.restrict s) := by
  fail_if_success fun_prop
  sorry

-- BoundedContinuousFunction.integrable / integrable_of_nnreal / norm_integral_le_mul_norm
example {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [ContinuousENorm E] [SecondCountableTopology E] {μ : Measure X} [IsFiniteMeasure μ] (f : X →ᵇ E) :
    Integrable (⇑f) μ := by
  fail_if_success fun_prop
  sorry

example {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (f : BoundedContinuousFunction X NNReal) :
    Integrable (NNReal.toReal ∘ ⇑f) μ := by
  fail_if_success fun_prop
  sorry

example {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [ContinuousENorm E] [SecondCountableTopology E] {μ : Measure X} [IsFiniteMeasure μ] (f : X →ᵇ E) :
    Integrable (fun x => ‖f x‖) μ := by
  fail_if_success fun_prop
  sorry

-- Continuous.integrableAt_nhds
example {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [NormedAddCommGroup E] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [ContinuousENorm E] [SecondCountableTopologyEither α E] {μ : Measure α} [IsLocallyFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) (a : α) : IntegrableAtFilter f (𝓝 a) μ := by
  fail_if_success fun_prop
  sorry

example {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [NormedAddCommGroup E] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [ContinuousENorm E] [SecondCountableTopologyEither α E] {μ : Measure α} [IsLocallyFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) (a : α) : IntegrableAtFilter f (𝓝[univ] a) μ := by
  fail_if_success fun_prop
  sorry

-- ContinuousOn.integrableOn_of_subset_isCompact
example {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [TopologicalSpace E] [ContinuousENorm E]
    {μ : Measure X} {K s : Set X} {f : X → E}
    (hf : ContinuousOn f K) (hK : IsCompact K) (hs : MeasurableSet s) (h's : s ⊆ K)
    (mus : (μ s) < ⊤) : IntegrableOn f s μ := by
  fail_if_success fun_prop
  sorry

-- ContinuousLinearMap.comp_condExp_comm / ContinuousLinearEquiv.integrable_comp_iff shapes
example {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {μ : Measure α} {f : α → E} (T : E →L[ℝ] F) (hf : Integrable f μ) :
    Integrable (fun x => T (f x)) μ := by
  fail_if_success fun_prop
  sorry

example {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {μ : Measure α} {φ : α → E} (L : E ≃L[ℝ] F)
    (h : Integrable (fun a => L (φ a)) μ) : Integrable φ μ := by
  fail_if_success fun_prop
  sorry

-- IntervalIntegrable.comp_add_right / comp_mul_left / continuous multiplier shapes
example {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => f (x + c)) volume (a - c) (b - c) := by
  fail_if_success fun_prop
  sorry

example {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => f (c * x)) volume (a / c) (b / c) := by
  fail_if_success fun_prop
  sorry

example {f g : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => f x * g x) volume a b := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} {g : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => f x • g x) volume a b := by
  fail_if_success fun_prop
  sorryfail_if_success fun_prop
  sorry

-- MeasureTheory.IntegrableAtFilter API shapes
example {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [ContinuousAdd E]
    {μ : Measure α} {l : Filter α} {f g : α → E}
    (hf : IntegrableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter (f + g) l μ := by
  fail_if_success fun_prop
  sorry

example {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {l : Filter α} {f : α → E} (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (-f) l μ := by
  fail_if_success fun_prop
  sorry

example {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {l : Filter α} {f : α → E} (c : ℝ)
    (hf : IntegrableAtFilter f l μ) : IntegrableAtFilter (c • f) l μ := by
  fail_if_success fun_prop
  sorry

example {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {l : Filter α} {f g : α → E}
    (hf : IntegrableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter (f - g) l μ := by
  fail_if_success fun_prop
  sorry

example {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {l l' : Filter α} {f : α → E} :
    IntegrableAtFilter f (l ⊔ l') μ ↔
      IntegrableAtFilter f l μ ∧ IntegrableAtFilter f l' μ := by
  fail_if_success fun_prop
  sorry

example {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {l : Filter α} {f : α → E} :
    IntegrableAtFilter f (l ⊓ ae μ) μ ↔ IntegrableAtFilter f l μ := by
  fail_if_success fun_prop
  sorry

example {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {s : Set α} {x : α} {f : α → E} :
    IntegrableAtFilter (s.indicator f) (𝓝 x) μ := by
  fail_if_success fun_prop
  sorry

-- Improper-integral / special-function AtFilter shapes
example {s : ℝ} :
    IntegrableAtFilter (fun t : ℝ => t ^ (-s)) atTop volume := by
  fail_if_success fun_prop
  sorry

example {s : ℝ} :
    IntegrableAtFilter (fun t : ℝ => t ^ s) atTop volume ↔ s < -1 := by
  fail_if_success fun_prop
  sorry

-- Gamma/Gaussian style goals from the database.
example {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi 0) volume := by
  fail_if_success fun_prop
  sorry

example {s Y : ℂ} :
    IntegrableOn (fun x : ℝ => s * (((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))) (Ioc 0 Y.re) volume := by
  fail_if_success fun_prop
  sorry

example {b : ℂ} (hb : 0 < b.re) :
    Integrable (fun x : ℝ => Real.exp (-b.re * x ^ 2)) volume := by
  fail_if_success fun_prop
  sorry

example {b c : ℂ} (hb : 0 < b.re) :
    Integrable (fun x : ℝ => Complex.exp (-b * ((x : ℂ) + c * Complex.I) ^ 2)) volume := by
  fail_if_success fun_prop
  sorry

example {ι : Type*} [Fintype ι] (b : ι → ℂ) (c : ι → ℂ) :
    Integrable (fun v : ι → ℝ =>
      Complex.exp (-∑ i, b i * (v i : ℂ) ^ 2 + ∑ i, c i * (v i : ℂ))) volume := by
  fail_if_success fun_prop
  sorry

-- Norm and indicator goals from measure restrictions.
example {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {s : Set α} {f : α → E} :
    IntegrableOn (fun a => ‖f a‖) s μ := by
  fail_if_success fun_prop
  sorry

example {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {f : α → ℝ} :
    Integrable (s.indicator f) (μ.restrict s) := by
  fail_if_success fun_prop
  sorry

end Database1SelectedGoals

section Database2RemainingGoals

/-! Additional distinctive goals from `integrable_database2.txt`. -/

-- CFC/rpow-integrand style: the real-variable integrability target behind the bundled CFC goal.
example {μ : Measure ℝ} {p : NNReal} {a : ℝ} :
    IntegrableOn (fun t : ℝ => ((p : ℝ) / (t ^ (1 - (p : ℝ)) * (1 + t)))) (Ioi 0) μ := by
  fail_if_success fun_prop
  sorry

example {μ : Measure ℝ} {p : NNReal} {a : ℝ} :
    IntegrableOn (fun t : ℝ => ((p : ℝ) * a / (t ^ (1 - (p : ℝ)) * (t + a)))) (Ioi 0) μ := by
  fail_if_success fun_prop
  sorry

-- Chebyshev/log derivative interval goals.
example (x : ℝ) :
    IntegrableOn
      (fun x : ℝ => 1 / (x * Real.log x ^ 2) *
        ∑ a ∈ Finset.Ioc 0 ⌊x⌋₊, if Nat.Prime a then Real.log (a : ℝ) else 0)
      (Icc 2 x) volume := by
  fail_if_success fun_prop
  sorry

example (x : ℝ) :
    IntegrableOn (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2)) (Icc 2 x) volume := by
  fail_if_success fun_prop
  sorry

example (x : ℝ) : IntegrableOn (deriv fun n : ℝ => (Real.log n)⁻¹) (Icc 2 x) volume := by
  fail_if_success fun_prop
  sorry

example (x : ℝ) : IntegrableOn (deriv Real.log) (Icc 2 x) volume := by
  fail_if_success fun_prop
  sorry

-- Circle-integral output multiplier.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) (c : ℂ) (R : ℝ)
    (hf : IntegrableOn (fun θ : ℝ => f (circleMap c R θ)) (Ι 0 (2 * Real.pi)) volume) :
    IntegrableOn (fun θ : ℝ => (circleMap 0 R θ * Complex.I) • f (circleMap c R θ))
      (Ι 0 (2 * Real.pi)) volume := by
  fail_if_success fun_prop
  sorry

-- Complex rectangle/Cauchy style goal.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (z w : ℂ) :
    IntegrableOn (fun x : ℝ × ℝ => (-(Complex.I • F' x)) (1, 0) + (F' x) (0, 1))
      ([[z.re, w.re]] ×ˢ [[w.im, z.im]]) volume := by
  fail_if_success fun_prop
  sorry

-- Gaussian Fourier goals in finite-dimensional spaces.
example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (b c : ℂ) (w : V) (hb : 0 < b.re) :
    Integrable (fun v : V => Complex.exp (-b * (‖v‖ : ℂ) ^ 2 + c * (inner ℝ w v : ℂ))) volume := by
  fail_if_success fun_prop
  sorry

example {ι : Type*} [Fintype ι] (b : ℂ) (c : ι → ℂ) (hb : 0 < b.re) :
    Integrable (fun v : ι → ℝ => Complex.exp (-b * ∑ i, (v i : ℂ) ^ 2 + ∑ i, c i * (v i : ℂ)))
      volume := by
  fail_if_success fun_prop
  sorry

example {ι : Type*} [Fintype ι] (b c : ι → ℂ) (hb : ∀ i, 0 < (b i).re) :
    Integrable (fun v : ι → ℝ => Complex.exp (-∑ i, b i * (v i : ℂ) ^ 2 + ∑ i, c i * (v i : ℂ)))
      volume := by
  fail_if_success fun_prop
  sorry

example {ι : Type*} [Fintype ι] (b c : ι → ℂ) (hb : ∀ i, 0 < (b i).re) :
    Integrable (fun v : ι → ℝ => ∏ i, Complex.exp (-b i * (v i : ℂ) ^ 2 + c i * (v i : ℂ)))
      volume := by
  fail_if_success fun_prop
  sorry

example {ι : Type*} [Fintype ι] (b c : ι → ℂ) (i : ι) (hb : ∀ i, 0 < (b i).re) :
    Integrable ((fun i v => Complex.exp (-b i * (v : ℂ) ^ 2 + c i * (v : ℂ))) i) volume := by
  fail_if_success fun_prop
  sorry

-- Compact-support convolution derivative bound shapes.
example {𝕜 E E' F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup E']
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E']
    [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] [NormedSpace ℝ F] [MeasurableSpace G]
    {μ : Measure G} {K' : Set G} (f : G → E) (g : G → E') (C : ℝ)
    (L' : E →L[𝕜] (G →L[𝕜] E') →L[𝕜] G →L[𝕜] F) :
    IntegrableOn (fun t : G => C * ‖f t‖ * ⨆ i : G, ‖fderiv 𝕜 g i‖) K' μ := by
  fail_if_success fun_prop
  sorry

example {𝕜 E E' F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup E']
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E']
    [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] [MeasurableSpace G]
    {μ : Measure G} (f : G → E) (g : G → E') (x₀ : G) (L : E →L[𝕜] E' →L[𝕜] F) :
    Integrable (fun t : G => L (f t) (g (x₀ - t))) μ := by
  fail_if_success fun_prop
  sorry

end Database2RemainingGoals

section DatabaseFullAdditionalGoals

/-! Additional goal families from `integrable_database_full.txt`. -/

-- Product-measure projection and map/product goals.
example {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure ν] {f : α → E} (hf : Integrable f μ) :
    Integrable (fun x : α × β => f x.1) (μ.prod ν) := by
  fail_if_success fun_prop
  sorry

example {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    {μ : Measure α} {ν : Measure β} [SFinite ν] [IsFiniteMeasure μ] {f : β → E}
    (hf : Integrable f ν) : Integrable (fun x : α × β => f x.2) (μ.prod ν) := by
  fail_if_success fun_prop
  sorry

example {Ω β F : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [NormedAddCommGroup F]
    {μ : Measure Ω} (X : Ω → β) {f : Ω → F} (hf : Integrable f μ) :
    Integrable (fun x : β × Ω => f x.2) (Measure.map (fun ω => (X ω, ω)) μ) := by
  fail_if_success fun_prop
  sorry

example {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {f : β → E} (hμ : μ ≠ 0)
    (hf : Integrable (fun x : α × β => f x.2) (μ.prod ν)) : Integrable f ν := by
  fail_if_success fun_prop
  sorry

-- Measure transformations and measure sums.
example {α ε : Type*} [MeasurableSpace α] [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    {μ μ' : Measure α} {c : ENNReal} {f : α → ε} (hf : Integrable f μ) (hc : c ≠ (⊤ : ENNReal))
    (hμ'_le : μ' ≤ c • μ) : Integrable f μ' := by
  fail_if_success fun_prop
  sorry

example {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {f : α → ℝ}
    (hμ : Integrable f μ) (hν : Integrable f ν) : Integrable f (μ + ν) := by
  fun_prop

example {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {f : α → ℝ}
    (h : Integrable f (μ + ν)) : Integrable f ν := by
  fail_if_success fun_prop
  sorry

-- Scalar, lattice, real/complex coordinate, and inner-product projections.
example {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => |f x|) μ := by
  fun_prop

example {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => max (f x) 0) μ := by
  fun_prop

example {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => ((f x).toNNReal : ℝ)) μ := by
  fun_prop

example {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜] {μ : Measure α} {f : α → 𝕜}
    (hf : Integrable f μ) : Integrable (fun x => RCLike.re (f x)) μ := by
  fun_prop

example {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜] {μ : Measure α} {f : α → 𝕜} :
    Integrable (fun x => RCLike.re (f x)) μ ∧ Integrable (fun x => RCLike.im (f x)) μ ↔
      Integrable f μ := by
  fail_if_success fun_prop
  sorry

example {α 𝕜 E : Type*} [MeasurableSpace α] [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {μ : Measure α} {f : α → E} (c : E) (hf : Integrable f μ) :
    Integrable (fun x => inner 𝕜 c (f x)) μ := by
  fail_if_success fun_prop
  sorry

-- Piecewise and simple-function multiplier goals.
example {α ε : Type*} [MeasurableSpace α] [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    {μ : Measure α} {s : Set α} {f g : α → ε} [∀ x, Decidable (x ∈ s)]
    (hs : MeasurableSet s) (hf : IntegrableOn f s μ) (hg : IntegrableOn g sᶜ μ) :
    Integrable (s.piecewise f g) μ := by
  fail_if_success fun_prop
  sorry

example {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (g : SimpleFunc X ℝ) (hf : Integrable f μ) : Integrable (⇑g * f) μ := by
  fail_if_success fun_prop
  sorry

example {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X} {f : X → ℝ}
    (c : ℝ) (hf : Integrable f μ) (hs : MeasurableSet s) :
    Integrable (s.indicator (fun x => c • f x)) μ := by
  fail_if_success fun_prop
  sorry

example {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X} {f : X → ℝ}
    (c : ℝ) (hf : Integrable f μ) (hs : MeasurableSet s) : IntegrableOn (c • f) s μ := by
  fail_if_success fun_prop
  sorry

-- At-filter and half-line equivalence shapes.
example {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} :
    IntegrableAtFilter f ⊤ μ ↔ Integrable f μ := by
  fail_if_success fun_prop
  sorry

example {μ : Measure ℝ} {f : ℝ → ℝ} :
    IntegrableAtFilter f atBot μ ↔ ∃ a, IntegrableOn f (Iic a) μ := by
  fail_if_success fun_prop
  sorry

example {μ : Measure ℝ} {f : ℝ → ℝ} :
    IntegrableAtFilter f atTop μ ↔ ∃ a, IntegrableOn f (Ici a) μ := by
  fail_if_success fun_prop
  sorry

example {μ : Measure ℝ} {f : ℝ → ℝ} {a : ℝ} :
    IntegrableOn f (Iic a) μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyIntegrableOn f (Iic a) μ := by
  fail_if_success fun_prop
  sorry

-- One-dimensional change-of-variable and improper-integral shapes.
example {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a c : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => f (a * x)) (Ioi c) volume ↔ IntegrableOn f (Ioi (a * c)) volume := by
  fail_if_success fun_prop
  sorry

example {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a c : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => f (x * a)) (Ioi c) volume ↔ IntegrableOn f (Ioi (c * a)) volume := by
  fail_if_success fun_prop
  sorry

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {p : ℝ} (hp : p ≠ 0) :
    IntegrableOn (fun x => (|p| * x ^ (p - 1)) • f (x ^ p)) (Ioi 0) volume ↔
      IntegrableOn f (Ioi 0) volume := by
  fail_if_success fun_prop
  sorry

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {p : ℝ} (hp : p ≠ 0) :
    IntegrableOn (fun x => x ^ (p - 1) • f (x ^ p)) (Ioi 0) volume ↔
      IntegrableOn f (Ioi 0) volume := by
  fail_if_success fun_prop
  sorry

-- Derivative criteria on half-lines.
example {g g' : ℝ → ℝ} {a l : ℝ}
    (hg : Tendsto g atTop (𝓝 l)) (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x) : IntegrableOn g' (Ioi a) volume := by
  fail_if_success fun_prop
  sorry

example {g g' : ℝ → ℝ} {a l : ℝ}
    (hg : Tendsto g atTop (𝓝 l)) (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0) : IntegrableOn g' (Ioi a) volume := by
  fail_if_success fun_prop
  sorry

example {g g' : ℝ → ℝ} {a l : ℝ}
    (hg : Tendsto g atTop (𝓝 l)) (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0) : Integrable (-g') (volume.restrict (Ioi a)) := by
  fail_if_success fun_prop
  sorry

end DatabaseFullAdditionalGoals
