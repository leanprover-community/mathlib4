/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Topology
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Integral over an interval

In this file we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ` if `a ≤ b` and
`-∫ x in Ioc b a, f x ∂μ` if `b ≤ a`.

## Implementation notes

### Avoiding `if`, `min`, and `max`

In order to avoid `if`s in the definition, we define `IntervalIntegrable f μ a b` as
`IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ`. For any `a`, `b` one of these
intervals is empty and the other coincides with `Set.uIoc a b = Set.Ioc (min a b) (max a b)`.

Similarly, we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
Again, for any `a`, `b` one of these integrals is zero, and the other gives the expected result.

This way some properties can be translated from integrals over sets without dealing with
the cases `a ≤ b` and `b ≤ a` separately.

### Choice of the interval

We use integral over `Set.uIoc a b = Set.Ioc (min a b) (max a b)` instead of one of the other
three possible intervals with the same endpoints for two reasons:

* this way `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ` holds whenever
  `f` is integrable on each interval; in particular, it works even if the measure `μ` has an atom
  at `b`; this rules out `Set.Ioo` and `Set.Icc` intervals;
* with this definition for a probability measure `μ`, the integral `∫ x in a..b, 1 ∂μ` equals
  the difference $F_μ(b)-F_μ(a)$, where $F_μ(a)=μ(-∞, a]$ is the
  [cumulative distribution function](https://en.wikipedia.org/wiki/Cumulative_distribution_function)
  of `μ`.

## Tags

integral
-/

@[expose] public section


noncomputable section

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {ι 𝕜 ε ε' E F A : Type*} [NormedAddCommGroup E]
  [TopologicalSpace ε] [ENormedAddMonoid ε] [TopologicalSpace ε'] [ENormedAddMonoid ε']

/-!
### Integrability on an interval
-/


/-- A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered
interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these
intervals is always empty, so this property is equivalent to `f` being integrable on
`(min a b, max a b]`. -/
def IntervalIntegrable (f : ℝ → ε) (μ : Measure ℝ) (a b : ℝ) : Prop :=
  IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ

/-!
## Basic iff's for `IntervalIntegrable`
-/
section

variable [PseudoMetrizableSpace ε] {f : ℝ → ε} {a b : ℝ} {μ : Measure ℝ}

/-- A function is interval integrable with respect to a given measure `μ` on `a..b` if and
  only if it is integrable on `uIoc a b` with respect to `μ`. This is an equivalent
  definition of `IntervalIntegrable`. -/
theorem intervalIntegrable_iff : IntervalIntegrable f μ a b ↔ IntegrableOn f (Ι a b) μ := by
  rw [uIoc_eq_union, integrableOn_union, IntervalIntegrable]

/-- If a function is interval integrable with respect to a given measure `μ` on `a..b` then
  it is integrable on `uIoc a b` with respect to `μ`. -/
theorem IntervalIntegrable.def' (h : IntervalIntegrable f μ a b) : IntegrableOn f (Ι a b) μ :=
  intervalIntegrable_iff.mp h

theorem intervalIntegrable_congr_ae {g : ℝ → ε} (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b := by
  rw [intervalIntegrable_iff, integrableOn_congr_fun_ae h, intervalIntegrable_iff]

theorem IntervalIntegrable.congr_ae {g : ℝ → ε} (hf : IntervalIntegrable f μ a b)
    (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    IntervalIntegrable g μ a b := by
  rwa [← intervalIntegrable_congr_ae h]

theorem intervalIntegrable_congr {g : ℝ → ε} (h : EqOn f g (Ι a b)) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b :=
  intervalIntegrable_congr_ae <| (ae_restrict_mem measurableSet_uIoc).mono h

alias ⟨IntervalIntegrable.congr, _⟩ := intervalIntegrable_congr

/-- Interval integrability is invariant when functions change along discrete sets. -/
theorem IntervalIntegrable.congr_codiscreteWithin {g : ℝ → ε} [NoAtoms μ]
    (h : f =ᶠ[codiscreteWithin (Ι a b)] g) (hf : IntervalIntegrable f μ a b) :
    IntervalIntegrable g μ a b :=
  hf.congr_ae (ae_restrict_le_codiscreteWithin measurableSet_Ioc h)

/-- Interval integrability is invariant when functions change along discrete sets. -/
theorem intervalIntegrable_congr_codiscreteWithin {g : ℝ → ε} [NoAtoms μ]
    (h : f =ᶠ[codiscreteWithin (Ι a b)] g) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b :=
  ⟨(IntervalIntegrable.congr_codiscreteWithin h ·),
    (IntervalIntegrable.congr_codiscreteWithin h.symm ·)⟩

theorem intervalIntegrable_iff_integrableOn_Ioc_of_le (hab : a ≤ b) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioc a b) μ := by
  rw [intervalIntegrable_iff, uIoc_of_le hab]

theorem intervalIntegrable_iff' [NoAtoms μ] (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (uIcc a b) μ := by
  rw [intervalIntegrable_iff, ← Icc_min_max, uIoc, integrableOn_Icc_iff_integrableOn_Ioc h]

theorem intervalIntegrable_iff_integrableOn_Icc_of_le [NoAtoms μ]
    (hab : a ≤ b) (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Icc a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab, integrableOn_Icc_iff_integrableOn_Ioc ha]

theorem intervalIntegrable_iff_integrableOn_Ico_of_le [NoAtoms μ]
    (hab : a ≤ b) (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ico a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha,
    integrableOn_Icc_iff_integrableOn_Ico hb]

theorem intervalIntegrable_iff_integrableOn_Ioo_of_le [NoAtoms μ]
    (hab : a ≤ b) (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioo a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha,
    integrableOn_Icc_iff_integrableOn_Ioo ha hb]

omit [PseudoMetrizableSpace ε] in
/-- If a function is integrable with respect to a given measure `μ` then it is interval integrable
  with respect to `μ` on `uIcc a b`. -/
theorem MeasureTheory.Integrable.intervalIntegrable (hf : Integrable f μ) :
    IntervalIntegrable f μ a b :=
  ⟨hf.integrableOn, hf.integrableOn⟩

omit [PseudoMetrizableSpace ε] in
theorem MeasureTheory.IntegrableOn.intervalIntegrable (hf : IntegrableOn f [[a, b]] μ) :
    IntervalIntegrable f μ a b :=
  ⟨hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc),
    hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc')⟩

theorem intervalIntegrable_const_iff {c : ε} (hc : ‖c‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun _ => c) μ a b ↔ c = 0 ∨ μ (Ι a b) < ∞ := by
  simp [intervalIntegrable_iff, integrableOn_const_iff hc]

@[simp]
theorem intervalIntegrable_const [IsLocallyFiniteMeasure μ]
    {c : E} (hc : ‖c‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun _ => c) μ a b :=
  intervalIntegrable_const_iff hc |>.2 <| Or.inr measure_Ioc_lt_top

protected theorem IntervalIntegrable.zero : IntervalIntegrable (0 : ℝ → E) μ a b :=
  (intervalIntegrable_const_iff <| by finiteness).mpr <| .inl rfl

end

/-!
## Basic properties of interval integrability
- interval integrability is symmetric, reflexive, transitive
- monotonicity and strong measurability of the interval integral
- if `f` is interval integrable, so are its absolute value and norm
- arithmetic properties
-/
namespace IntervalIntegrable

section

variable {f : ℝ → ε} {a b c d : ℝ} {μ ν : Measure ℝ}

@[symm]
nonrec theorem symm (h : IntervalIntegrable f μ a b) : IntervalIntegrable f μ b a :=
  h.symm

theorem symm_iff : IntervalIntegrable f μ a b ↔ IntervalIntegrable f μ b a := ⟨.symm, .symm⟩

@[refl, simp]
theorem refl : IntervalIntegrable f μ a a := by constructor <;> simp

variable [PseudoMetrizableSpace ε]

@[trans]
theorem trans {a b c : ℝ} (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) :
    IntervalIntegrable f μ a c :=
  ⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
    (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩

theorem trans_iff (h : b ∈ [[a, c]]) :
    IntervalIntegrable f μ a c ↔ IntervalIntegrable f μ a b ∧ IntervalIntegrable f μ b c := by
  simp only [intervalIntegrable_iff, ← integrableOn_union, uIoc_union_uIoc h]

theorem trans_iterate_Ico {a : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hint : ∀ k ∈ Ico m n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    IntervalIntegrable f μ (a m) (a n) := by
  revert hint
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro p hp IH h
    exact (IH fun k hk => h k (Ico_subset_Ico_right p.le_succ hk)).trans (h p (by simp [hp]))

theorem trans_iterate {a : ℕ → ℝ} {n : ℕ}
    (hint : ∀ k < n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    IntervalIntegrable f μ (a 0) (a n) :=
  trans_iterate_Ico bot_le fun k hk => hint k hk.2

theorem neg {f : ℝ → E} (h : IntervalIntegrable f μ a b) : IntervalIntegrable (-f) μ a b :=
  ⟨h.1.neg, h.2.neg⟩

omit [PseudoMetrizableSpace ε] in
theorem enorm (h : IntervalIntegrable f μ a b) : IntervalIntegrable (‖f ·‖ₑ) μ a b :=
  ⟨h.1.enorm, h.2.enorm⟩

theorem norm {f : ℝ → E} (h : IntervalIntegrable f μ a b) : IntervalIntegrable (‖f ·‖) μ a b :=
  ⟨h.1.norm, h.2.norm⟩

theorem intervalIntegrable_enorm_iff {μ : Measure ℝ} {a b : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    IntervalIntegrable (fun t => ‖f t‖ₑ) μ a b ↔ IntervalIntegrable f μ a b := by
  simp_rw [intervalIntegrable_iff, IntegrableOn, integrable_enorm_iff hf]

theorem intervalIntegrable_norm_iff {f : ℝ → E} {μ : Measure ℝ} {a b : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    IntervalIntegrable (fun t => ‖f t‖) μ a b ↔ IntervalIntegrable f μ a b := by
  simp_rw [intervalIntegrable_iff, IntegrableOn, integrable_norm_iff hf]

theorem abs {f : ℝ → ℝ} (h : IntervalIntegrable f μ a b) :
    IntervalIntegrable (fun x => |f x|) μ a b :=
  h.norm

theorem mono (hf : IntervalIntegrable f ν a b) (h1 : [[c, d]] ⊆ [[a, b]]) (h2 : μ ≤ ν) :
    IntervalIntegrable f μ c d :=
  intervalIntegrable_iff.mpr <| hf.def'.mono (uIoc_subset_uIoc_of_uIcc_subset_uIcc h1) h2

theorem mono_measure (hf : IntervalIntegrable f ν a b) (h : μ ≤ ν) : IntervalIntegrable f μ a b :=
  hf.mono Subset.rfl h

theorem mono_set (hf : IntervalIntegrable f μ a b) (h : [[c, d]] ⊆ [[a, b]]) :
    IntervalIntegrable f μ c d :=
  hf.mono h le_rfl

theorem mono_set_ae (hf : IntervalIntegrable f μ a b) (h : Ι c d ≤ᵐ[μ] Ι a b) :
    IntervalIntegrable f μ c d :=
  intervalIntegrable_iff.mpr <| hf.def'.mono_set_ae h

theorem mono_set' (hf : IntervalIntegrable f μ a b) (hsub : Ι c d ⊆ Ι a b) :
    IntervalIntegrable f μ c d :=
  hf.mono_set_ae <| Eventually.of_forall hsub

theorem mono_fun_enorm [PseudoMetrizableSpace ε'] {g : ℝ → ε'}
    (hf : IntervalIntegrable f μ a b) (hgm : AEStronglyMeasurable g (μ.restrict (Ι a b)))
    (hle : (‖g ·‖ₑ) ≤ᵐ[μ.restrict (Ι a b)] (‖f ·‖ₑ)) : IntervalIntegrable g μ a b :=
  intervalIntegrable_iff.2 <| hf.def'.integrable.mono_enorm hgm hle

theorem mono_fun {f : ℝ → E} [NormedAddCommGroup F] {g : ℝ → F} (hf : IntervalIntegrable f μ a b)
    (hgm : AEStronglyMeasurable g (μ.restrict (Ι a b)))
    (hle : (fun x => ‖g x‖) ≤ᵐ[μ.restrict (Ι a b)] fun x => ‖f x‖) : IntervalIntegrable g μ a b :=
  intervalIntegrable_iff.2 <| hf.def'.integrable.mono hgm hle

-- XXX: the best spelling of this lemma may look slightly different (e.gl, with different domain)
theorem mono_fun_enorm' {f : ℝ → ε} {g : ℝ → ℝ≥0∞} (hg : IntervalIntegrable g μ a b)
    (hfm : AEStronglyMeasurable f (μ.restrict (Ι a b)))
    (hle : (fun x => ‖f x‖ₑ) ≤ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b :=
  intervalIntegrable_iff.2 <| hg.def'.integrable.mono_enorm hfm hle

theorem mono_fun' {f : ℝ → E} {g : ℝ → ℝ} (hg : IntervalIntegrable g μ a b)
    (hfm : AEStronglyMeasurable f (μ.restrict (Ι a b)))
    (hle : (fun x => ‖f x‖) ≤ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b :=
  intervalIntegrable_iff.2 <| hg.def'.integrable.mono' hfm hle

omit [PseudoMetrizableSpace ε] in
protected theorem aestronglyMeasurable (h : IntervalIntegrable f μ a b) :
    AEStronglyMeasurable f (μ.restrict (Ioc a b)) :=
  h.1.aestronglyMeasurable

omit [PseudoMetrizableSpace ε] in
protected theorem aestronglyMeasurable' (h : IntervalIntegrable f μ a b) :
    AEStronglyMeasurable f (μ.restrict (Ioc b a)) :=
  h.2.aestronglyMeasurable

omit [PseudoMetrizableSpace ε] in
protected theorem aestronglyMeasurable_restrict_uIoc (h : IntervalIntegrable f μ a b) :
    AEStronglyMeasurable f (μ.restrict (uIoc a b)) := by
  by_cases hab : a ≤ b
  · rw [uIoc_of_le hab]; exact h.aestronglyMeasurable
  · rw [uIoc_of_ge (by linarith)]; exact h.aestronglyMeasurable'

end

variable [NormedRing A] {f g : ℝ → ε} {a b : ℝ} {μ : Measure ℝ}

@[to_fun]
theorem smul {R : Type*} [NormedAddCommGroup R] [SMulZeroClass R E] [IsBoundedSMul R E] {f : ℝ → E}
    (h : IntervalIntegrable f μ a b) (r : R) :
    IntervalIntegrable (r • f) μ a b :=
  ⟨h.1.smul r, h.2.smul r⟩

@[simp]
theorem _root_.intervalIntegrable_smul_iff {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : ℝ → E} {c : 𝕜} :
    IntervalIntegrable (c • f) μ a b ↔ c = 0 ∨ IntervalIntegrable f μ a b := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [IntervalIntegrable.zero]
  · simp only [hc, false_or]
    refine ⟨fun h ↦ ?_, (.smul · c)⟩
    simpa [hc] using h.smul c⁻¹

@[simp]
theorem _root_.intervalIntegrable_fun_smul_iff {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : ℝ → E} {c : 𝕜} :
    IntervalIntegrable (c • f ·) μ a b ↔ c = 0 ∨ IntervalIntegrable f μ a b :=
  intervalIntegrable_smul_iff

@[simp]
theorem add [ContinuousAdd ε] (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    IntervalIntegrable (fun x => f x + g x) μ a b :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

@[simp]
theorem sub {f g : ℝ → E} (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    IntervalIntegrable (fun x => f x - g x) μ a b :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem sum {ε} [TopologicalSpace ε] [ENormedAddCommMonoid ε] [ContinuousAdd ε]
    (s : Finset ι) {f : ι → ℝ → ε} (h : ∀ i ∈ s, IntervalIntegrable (f i) μ a b) :
    IntervalIntegrable (∑ i ∈ s, f i) μ a b :=
  ⟨integrable_finsetSum' s fun i hi => (h i hi).1, integrable_finsetSum' s fun i hi => (h i hi).2⟩

/-- Finite sums of interval integrable functions are interval integrable. -/
@[simp]
protected theorem finsum
    {ε} [TopologicalSpace ε] [ENormedAddCommMonoid ε] [ContinuousAdd ε] [PseudoMetrizableSpace ε]
    {f : ι → ℝ → ε} (h : ∀ i, IntervalIntegrable (f i) μ a b) :
    IntervalIntegrable (∑ᶠ i, f i) μ a b := by
  by_cases h₁ : f.support.Finite
  · simp [finsum_eq_sum _ h₁, IntervalIntegrable.sum h₁.toFinset (fun i _ ↦ h i)]
  · rw [finsum_of_infinite_support h₁]
    apply intervalIntegrable_const_iff (c := 0) (by simp) |>.2
    tauto

section Mul

theorem mul_continuousOn {f g : ℝ → A} (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => f x * g x) μ a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.mul_continuousOn_of_subset hg measurableSet_Ioc isCompact_uIcc Ioc_subset_Icc_self

theorem continuousOn_mul {f g : ℝ → A} (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => g x * f x) μ a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.continuousOn_mul_of_subset hg isCompact_uIcc measurableSet_Ioc Ioc_subset_Icc_self

@[simp]
theorem const_mul {f : ℝ → A} (hf : IntervalIntegrable f μ a b) (c : A) :
    IntervalIntegrable (fun x => c * f x) μ a b :=
  hf.continuousOn_mul continuousOn_const

@[simp]
theorem mul_const {f : ℝ → A} (hf : IntervalIntegrable f μ a b) (c : A) :
    IntervalIntegrable (fun x => f x * c) μ a b :=
  hf.mul_continuousOn continuousOn_const

end Mul

section SMul

variable {f : ℝ → 𝕜} {g : ℝ → E} [NormedRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]

theorem smul_continuousOn (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => f x • g x) μ a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.smul_continuousOn_of_subset hg measurableSet_Ioc isCompact_uIcc Ioc_subset_Icc_self

theorem continuousOn_smul (hg : IntervalIntegrable g μ a b)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => f x • g x) μ a b := by
  rw [intervalIntegrable_iff] at hg ⊢
  exact hg.continuousOn_smul_of_subset hf isCompact_uIcc measurableSet_Ioc Ioc_subset_Icc_self

end SMul

@[simp]
theorem div_const {𝕜 : Type*} {f : ℝ → 𝕜} [NormedDivisionRing 𝕜] (h : IntervalIntegrable f μ a b)
    (c : 𝕜) : IntervalIntegrable (fun x => f x / c) μ a b := by
  simpa only [div_eq_mul_inv] using mul_const h c⁻¹

variable [PseudoMetrizableSpace ε]

theorem comp_mul_left (hf : IntervalIntegrable f volume a b) {c : ℝ}
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness)
    (h' : ‖f (c * min (a / c) (b / c))‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (c * x)) volume (a / c) (b / c) := by
  rcases eq_or_ne c 0 with (hc | hc); · rw [hc]; simp
  rw [intervalIntegrable_iff' h] at hf
  rw [intervalIntegrable_iff' h'] at ⊢
  have A : MeasurableEmbedding fun x => x * c⁻¹ :=
    (Homeomorph.mulRight₀ _ (inv_ne_zero hc)).isClosedEmbedding.measurableEmbedding
  rw [← Real.smul_map_volume_mul_right (inv_ne_zero hc), IntegrableOn, Measure.restrict_smul,
    integrable_smul_measure (by simpa : ENNReal.ofReal |c⁻¹| ≠ 0) ENNReal.ofReal_ne_top,
    ← IntegrableOn, MeasurableEmbedding.integrableOn_map_iff A]
  convert hf using 1
  · ext; simp only [comp_apply]; congr 1; field
  · rw [preimage_mul_const_uIcc (inv_ne_zero hc)]; field_simp

-- Note that `h'` is **not** implied by `h` if `c` is negative.
-- TODO: generalise this lemma to enorms!
theorem comp_mul_left_iff {f : ℝ → E} {c : ℝ} (hc : c ≠ 0) (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness)
    (h' : ‖f (c * min (a / c) (b / c))‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (c * x)) volume (a / c) (b / c) ↔
      IntervalIntegrable f volume a b := by
  exact ⟨fun h ↦ by simpa [hc] using h.comp_mul_left (c := c⁻¹) h' (by simp),
    (comp_mul_left · h h')⟩

theorem comp_mul_right (hf : IntervalIntegrable f volume a b) {c : ℝ}
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness)
    (h' : ‖f (c * min (a / c) (b / c))‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (x * c)) volume (a / c) (b / c) := by
  simpa only [mul_comm] using comp_mul_left hf h h'

theorem comp_add_right (hf : IntervalIntegrable f volume a b) (c : ℝ)
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x + c)) volume (a - c) (b - c) := by
  have h' : ‖f (min (a - c) (b - c) + c)‖ₑ ≠ ⊤ := by
    rw [min_sub_sub_right, sub_add, sub_self, sub_zero]
    exact h
  wlog hab : a ≤ b generalizing a b
  · apply IntervalIntegrable.symm (this hf.symm ?_ ?_ (le_of_not_ge hab))
    · rw [min_comm]; exact h
    · rw [min_comm]; exact h'
  rw [intervalIntegrable_iff' h] at hf
  rw [intervalIntegrable_iff' h'] at ⊢
  have A : MeasurableEmbedding fun x => x + c :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  rw [← map_add_right_eq_self volume c] at hf
  convert (MeasurableEmbedding.integrableOn_map_iff A).mp hf using 1
  rw [preimage_add_const_uIcc]

theorem comp_add_right_iff {c : ℝ} (h : ‖f (min a b + c)‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x + c)) volume a b
      ↔ IntervalIntegrable f volume (a + c) (b + c) where
  mp hf := by simpa using hf.comp_add_right (-c)
  mpr hf := by
    have : ‖f (min (a + c) (b + c))‖ₑ ≠ ⊤ := by rwa [min_add_add_right]
    simpa using hf.comp_add_right c

theorem comp_add_left (hf : IntervalIntegrable f volume a b) (c : ℝ)
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (c + x)) volume (a - c) (b - c) := by
  simpa [add_comm] using IntervalIntegrable.comp_add_right hf c h

theorem comp_add_left_iff {c : ℝ} (h : ‖f (min a b)‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (c + x)) volume (a - c) (b - c)
      ↔ IntervalIntegrable f volume a b := by
  simp_rw [add_comm c]
  rw [IntervalIntegrable.comp_add_right_iff (by grind)]
  simp

theorem comp_sub_right (hf : IntervalIntegrable f volume a b) (c : ℝ)
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x - c)) volume (a + c) (b + c) := by
  simpa only [sub_neg_eq_add] using IntervalIntegrable.comp_add_right hf (-c) h

theorem comp_sub_right_iff {c : ℝ} (h : ‖f (min a b)‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x - c)) volume (a + c) (b + c)
      ↔ IntervalIntegrable f volume a b := by
  simp_rw [sub_eq_add_neg]
  rw [IntervalIntegrable.comp_add_right_iff (by grind)]
  simp

-- TODO: generalise this lemma to enorms!
theorem iff_comp_neg {f : ℝ → E} (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f volume a b ↔ IntervalIntegrable (fun x ↦ f (-x)) volume (-a) (-b) := by
  rw [← comp_mul_left_iff (neg_ne_zero.2 one_ne_zero) h (by simp)]; simp [div_neg]

-- TODO: generalise this lemma to enorms!
theorem comp_sub_left {f : ℝ → E} (hf : IntervalIntegrable f volume a b) (c : ℝ)
    (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (c - x)) volume (c - a) (c - b) := by
  simpa only [neg_sub, ← sub_eq_add_neg] using (iff_comp_neg (by simp)).mp (hf.comp_add_left c h)

-- TODO: generalise this lemma to enorms!
theorem comp_sub_left_iff {f : ℝ → E} (c : ℝ) (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (c - x)) volume (c - a) (c - b) ↔
      IntervalIntegrable f volume a b :=
  ⟨fun h ↦ by simpa using h.comp_sub_left c, (.comp_sub_left · c h)⟩

end IntervalIntegrable

/-!
## Continuous functions are interval integrable
-/
section

variable {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

theorem ContinuousOn.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : ContinuousOn u (uIcc a b)) :
    IntervalIntegrable u μ a b :=
  (ContinuousOn.integrableOn_Icc hu).intervalIntegrable

theorem ContinuousOn.intervalIntegrable_of_Icc {u : ℝ → E} {a b : ℝ} (h : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) : IntervalIntegrable u μ a b :=
  ContinuousOn.intervalIntegrable ((uIcc_of_le h).symm ▸ hu)

/-- A continuous function on `ℝ` is `IntervalIntegrable` with respect to any locally finite measure
`ν` on ℝ. -/
theorem Continuous.intervalIntegrable {u : ℝ → E} (hu : Continuous u) (a b : ℝ) :
    IntervalIntegrable u μ a b :=
  hu.continuousOn.intervalIntegrable

end

/-!
## Monotone and antitone functions are integral integrable
-/
section

variable {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] [ConditionallyCompleteLinearOrder E]
  [OrderTopology E] [SecondCountableTopology E]

theorem MonotoneOn.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : MonotoneOn u (uIcc a b)) :
    IntervalIntegrable u μ a b := by
  rw [intervalIntegrable_iff]
  exact (hu.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self

theorem AntitoneOn.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : AntitoneOn u (uIcc a b)) :
    IntervalIntegrable u μ a b :=
  hu.dual_right.intervalIntegrable

theorem Monotone.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : Monotone u) :
    IntervalIntegrable u μ a b :=
  (hu.monotoneOn _).intervalIntegrable

theorem Antitone.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : Antitone u) :
    IntervalIntegrable u μ a b :=
  (hu.antitoneOn _).intervalIntegrable

end

/-!
## Interval integrability of functions with even or odd parity
-/
section

variable {f : ℝ → E}

/-- An even function is interval integrable (with respect to the volume measure) on every interval
of the form `0..x` if it is interval integrable (with respect to the volume measure) on every
interval of the form `0..x`, for positive `x`.

See `intervalIntegrable_of_even` for a stronger result. -/
lemma intervalIntegrable_of_even₀ (h₁f : ∀ x, f x = f (-x))
    (h₂f : ∀ x, 0 < x → IntervalIntegrable f volume 0 x)
    {t : ℝ} (ht : ‖f (min 0 t)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f volume 0 t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [IntervalIntegrable.iff_comp_neg ht]
    conv => arg 1; intro t; rw [← h₁f]
    simp [h₂f (-t) (by simp [h])]
  · rw [h]
  · exact h₂f t h

/-- An even function is interval integrable (with respect to the volume measure) on every interval
if it is interval integrable (with respect to the volume measure) on every interval of the form
`0..x`, for positive `x`. -/
theorem intervalIntegrable_of_even
    (h₁f : ∀ x, f x = f (-x)) (h₂f : ∀ x, 0 < x → IntervalIntegrable f volume 0 x) {a b : ℝ}
    (ha : ‖f (min 0 a)‖ₑ ≠ ∞ := by finiteness) (hb : ‖f (min 0 b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f volume a b :=
  -- Split integral and apply lemma
  (intervalIntegrable_of_even₀ h₁f h₂f ha).symm.trans (b := 0)
    (intervalIntegrable_of_even₀ h₁f h₂f hb)

/-- An odd function is interval integrable (with respect to the volume measure) on every interval
of the form `0..x` if it is interval integrable (with respect to the volume measure) on every
interval of the form `0..x`, for positive `x`.

See `intervalIntegrable_of_odd` for a stronger result. -/
lemma intervalIntegrable_of_odd₀ (h₁f : ∀ x, -f x = f (-x))
    (h₂f : ∀ x, 0 < x → IntervalIntegrable f volume 0 x) {t : ℝ}
    (ht : ‖f (min 0 t)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f volume 0 t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [IntervalIntegrable.iff_comp_neg]
    conv => arg 1; intro t; rw [← h₁f]
    apply IntervalIntegrable.neg
    simp [h₂f (-t) (by simp [h])]
  · rw [h]
  · exact h₂f t h

/-- An odd function is interval integrable (with respect to the volume measure) on every interval
iff it is interval integrable (with respect to the volume measure) on every interval of the form
`0..x`, for positive `x`. -/
theorem intervalIntegrable_of_odd
    (h₁f : ∀ x, -f x = f (-x)) (h₂f : ∀ x, 0 < x → IntervalIntegrable f volume 0 x) {a b : ℝ}
    (ha : ‖f (min 0 a)‖ₑ ≠ ∞ := by finiteness) (hb : ‖f (min 0 b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f volume a b :=
  -- Split integral and apply lemma
  (intervalIntegrable_of_odd₀ h₁f h₂f ha).symm.trans (intervalIntegrable_of_odd₀ h₁f h₂f hb)

end

/-!
## Limits of intervals
-/

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : ℝ → E` has a finite limit at `l' ⊓ ae μ`. Then `f` is interval integrable on
`u..v` provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply Tendsto.eventually_intervalIntegrable_ae` will generate goals `Filter ℝ` and
`TendstoIxxClass Ioc ?m_1 l'`. -/
theorem Filter.Tendsto.eventually_intervalIntegrable_ae {f : ℝ → E} {μ : Measure ℝ}
    {l l' : Filter ℝ} (hfm : StronglyMeasurableAtFilter f l' μ) [TendstoIxxClass Ioc l l']
    [IsMeasurablyGenerated l'] (hμ : μ.FiniteAtFilter l') {c : E} (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    {u v : ι → ℝ} {lt : Filter ι} (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    ∀ᶠ t in lt, IntervalIntegrable f μ (u t) (v t) :=
  have := (hf.integrableAtFilter_ae hfm hμ).eventually
  ((hu.Ioc hv).eventually this).and <| (hv.Ioc hu).eventually this

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : ℝ → E` has a finite limit at `l`. Then `f` is interval integrable on `u..v`
provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply Tendsto.eventually_intervalIntegrable` will generate goals `Filter ℝ` and
`TendstoIxxClass Ioc ?m_1 l'`. -/
theorem Filter.Tendsto.eventually_intervalIntegrable {f : ℝ → E} {μ : Measure ℝ} {l l' : Filter ℝ}
    (hfm : StronglyMeasurableAtFilter f l' μ) [TendstoIxxClass Ioc l l'] [IsMeasurablyGenerated l']
    (hμ : μ.FiniteAtFilter l') {c : E} (hf : Tendsto f l' (𝓝 c)) {u v : ι → ℝ} {lt : Filter ι}
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) : ∀ᶠ t in lt, IntervalIntegrable f μ (u t) (v t) :=
  (hf.mono_left inf_le_left).eventually_intervalIntegrable_ae hfm hμ hu hv

/-!
### Interval integral: definition and basic properties

In this section we define `∫ x in a..b, f x ∂μ` as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`
and prove some basic properties.
-/

variable [NormedSpace ℝ E]

/-- The interval integral `∫ x in a..b, f x ∂μ` is defined
as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`. -/
def intervalIntegral (f : ℝ → E) (a b : ℝ) (μ : Measure ℝ) : E :=
  (∫ x in Ioc a b, f x ∂μ) - ∫ x in Ioc b a, f x ∂μ

@[inherit_doc intervalIntegral]
notation3"∫ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂"μ:70 => intervalIntegral r a b μ

/-- The interval integral `∫ x in a..b, f x` is defined
as `∫ x in Ioc a b, f x - ∫ x in Ioc b a, f x`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x`, otherwise it equals `-∫ x in Ioc b a, f x`. -/
notation3"∫ "(...)" in "a".."b", "r:60:(scoped f => intervalIntegral f a b volume) => r

namespace intervalIntegral

section Basic

variable {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ}

@[simp]
theorem integral_zero : (∫ _ in a..b, (0 : E) ∂μ) = 0 := by simp [intervalIntegral]

theorem integral_of_le (h : a ≤ b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ := by
  simp [intervalIntegral, h]

@[simp]
theorem integral_same : ∫ x in a..a, f x ∂μ = 0 :=
  sub_self _

theorem integral_symm (a b) : ∫ x in b..a, f x ∂μ = -∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, neg_sub]

theorem integral_of_ge (h : b ≤ a) : ∫ x in a..b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ := by
  simp only [integral_symm b, integral_of_le h]

theorem intervalIntegral_eq_integral_uIoc (f : ℝ → E) (a b : ℝ) (μ : Measure ℝ) :
    ∫ x in a..b, f x ∂μ = (if a ≤ b then 1 else -1 : ℝ) • ∫ x in Ι a b, f x ∂μ := by
  split_ifs with h
  · simp only [integral_of_le h, uIoc_of_le h, one_smul]
  · simp only [integral_of_ge (not_le.1 h).le, uIoc_of_ge (not_le.1 h).le, neg_one_smul]

theorem norm_intervalIntegral_eq (f : ℝ → E) (a b : ℝ) (μ : Measure ℝ) :
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := by
  simp_rw [intervalIntegral_eq_integral_uIoc, norm_smul]
  split_ifs <;> simp only [norm_neg, norm_one, one_mul]

theorem abs_intervalIntegral_eq (f : ℝ → ℝ) (a b : ℝ) (μ : Measure ℝ) :
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
  norm_intervalIntegral_eq f a b μ

theorem integral_cases (f : ℝ → E) (a b) :
    (∫ x in a..b, f x ∂μ) ∈ ({∫ x in Ι a b, f x ∂μ, -∫ x in Ι a b, f x ∂μ} : Set E) := by
  rw [intervalIntegral_eq_integral_uIoc]; split_ifs <;> simp

nonrec theorem integral_undef (h : ¬IntervalIntegrable f μ a b) : ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegrable_iff] at h
  rw [intervalIntegral_eq_integral_uIoc, integral_undef h, smul_zero]

theorem intervalIntegrable_of_integral_ne_zero {a b : ℝ} {f : ℝ → E} {μ : Measure ℝ}
    (h : (∫ x in a..b, f x ∂μ) ≠ 0) : IntervalIntegrable f μ a b :=
  not_imp_comm.1 integral_undef h

nonrec theorem integral_non_aestronglyMeasurable
    (hf : ¬AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegral_eq_integral_uIoc, integral_non_aestronglyMeasurable hf, smul_zero]

theorem integral_non_aestronglyMeasurable_of_le (h : a ≤ b)
    (hf : ¬AEStronglyMeasurable f (μ.restrict (Ioc a b))) : ∫ x in a..b, f x ∂μ = 0 :=
  integral_non_aestronglyMeasurable <| by rwa [uIoc_of_le h]

theorem norm_integral_min_max (f : ℝ → E) :
    ‖∫ x in min a b..max a b, f x ∂μ‖ = ‖∫ x in a..b, f x ∂μ‖ := by
  cases le_total a b <;> simp [*, integral_symm a b]

theorem norm_integral_eq_norm_integral_uIoc (f : ℝ → E) :
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := by
  rw [← norm_integral_min_max, integral_of_le min_le_max, uIoc]

theorem abs_integral_eq_abs_integral_uIoc (f : ℝ → ℝ) :
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
  norm_integral_eq_norm_integral_uIoc f

theorem norm_integral_le_integral_norm_uIoc : ‖∫ x in a..b, f x ∂μ‖ ≤ ∫ x in Ι a b, ‖f x‖ ∂μ :=
  calc
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := norm_integral_eq_norm_integral_uIoc f
    _ ≤ ∫ x in Ι a b, ‖f x‖ ∂μ := norm_integral_le_integral_norm f

theorem norm_integral_le_abs_integral_norm : ‖∫ x in a..b, f x ∂μ‖ ≤ |∫ x in a..b, ‖f x‖ ∂μ| := by
  simp only [← Real.norm_eq_abs, norm_integral_eq_norm_integral_uIoc]
  exact le_trans (norm_integral_le_integral_norm _) (le_abs_self _)

theorem norm_integral_le_integral_norm (h : a ≤ b) :
    ‖∫ x in a..b, f x ∂μ‖ ≤ ∫ x in a..b, ‖f x‖ ∂μ :=
  norm_integral_le_integral_norm_uIoc.trans_eq <| by rw [uIoc_of_le h, integral_of_le h]

theorem norm_integral_le_abs_of_norm_le {g : ℝ → ℝ} (h : ∀ᵐ t ∂μ.restrict <| Ι a b, ‖f t‖ ≤ g t)
    (hbound : IntervalIntegrable g μ a b) : ‖∫ t in a..b, f t ∂μ‖ ≤ |∫ t in a..b, g t ∂μ| := by
  rw [norm_intervalIntegral_eq, abs_intervalIntegral_eq]
  exact (norm_integral_le_of_norm_le hbound.def' h).trans (le_abs_self _)

theorem norm_integral_le_of_norm_le {g : ℝ → ℝ} (hab : a ≤ b)
    (h : ∀ᵐ t ∂μ, t ∈ Set.Ioc a b → ‖f t‖ ≤ g t) (hbound : IntervalIntegrable g μ a b) :
    ‖∫ t in a..b, f t ∂μ‖ ≤ ∫ t in a..b, g t ∂μ := by
  simp only [integral_of_le hab, ← ae_restrict_iff' measurableSet_Ioc] at *
  exact MeasureTheory.norm_integral_le_of_norm_le hbound.1 h

theorem norm_integral_le_of_norm_le_const_ae {a b C : ℝ} {f : ℝ → E}
    (h : ∀ᵐ x, x ∈ Ι a b → ‖f x‖ ≤ C) : ‖∫ x in a..b, f x‖ ≤ C * |b - a| := by
  rw [norm_integral_eq_norm_integral_uIoc]
  convert norm_setIntegral_le_of_norm_le_const_ae' _ h using 1
  · rw [uIoc, Real.volume_real_Ioc_of_le inf_le_sup, max_sub_min_eq_abs]
  · simp [uIoc, Real.volume_Ioc]

theorem norm_integral_le_of_norm_le_const {a b C : ℝ} {f : ℝ → E} (h : ∀ x ∈ Ι a b, ‖f x‖ ≤ C) :
    ‖∫ x in a..b, f x‖ ≤ C * |b - a| :=
  norm_integral_le_of_norm_le_const_ae <| Eventually.of_forall h

@[simp]
nonrec theorem integral_add (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    ∫ x in a..b, f x + g x ∂μ = (∫ x in a..b, f x ∂μ) + ∫ x in a..b, g x ∂μ := by
  simp only [intervalIntegral_eq_integral_uIoc, integral_add hf.def' hg.def', smul_add]

nonrec theorem integral_finsetSum {ι} {s : Finset ι} {f : ι → ℝ → E}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) μ a b) :
    ∫ x in a..b, ∑ i ∈ s, f i x ∂μ = ∑ i ∈ s, ∫ x in a..b, f i x ∂μ := by
  simp only [intervalIntegral_eq_integral_uIoc, integral_finsetSum s fun i hi => (h i hi).def',
    Finset.smul_sum]

@[deprecated (since := "2026-04-08")] alias integral_finset_sum := integral_finsetSum

@[simp]
nonrec theorem integral_neg : ∫ x in a..b, -f x ∂μ = -∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, integral_neg]; abel

@[simp]
theorem integral_sub (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    ∫ x in a..b, f x - g x ∂μ = (∫ x in a..b, f x ∂μ) - ∫ x in a..b, g x ∂μ := by
  simpa only [sub_eq_add_neg] using (integral_add hf hg.neg).trans (congr_arg _ integral_neg)

/-- Compatibility with scalar multiplication. Note this assumes `𝕜` is a division ring in order to
ensure that for `c ≠ 0`, `c • f` is integrable iff `f` is. For scalar multiplication by more
general rings assuming integrability, see `IntervalIntegrable.integral_smul`. -/
@[simp]
nonrec theorem integral_smul [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (r : 𝕜) (f : ℝ → E) :
    ∫ x in a..b, r • f x ∂μ = r • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, integral_smul, smul_sub]

theorem _root_.IntervalIntegrable.integral_smul
    {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E] [SMulCommClass ℝ R E]
    {f : ℝ → E} (r : R) (hf : IntervalIntegrable f μ a b) :
    ∫ x in a..b, r • f x ∂μ = r • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, smul_sub, hf.1.integral_smul, hf.2.integral_smul]

@[simp]
nonrec theorem integral_smul_const [CompleteSpace E]
    {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (f : ℝ → 𝕜) (c : E) :
    ∫ x in a..b, f x • c ∂μ = (∫ x in a..b, f x ∂μ) • c := by
  simp only [intervalIntegral_eq_integral_uIoc, integral_smul_const, smul_assoc]

@[simp]
theorem integral_const_mul [NormedDivisionRing 𝕜] [NormedAlgebra ℝ 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
    ∫ x in a..b, r * f x ∂μ = r * ∫ x in a..b, f x ∂μ :=
  integral_smul r f

@[simp]
theorem integral_mul_const {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
    ∫ x in a..b, f x * r ∂μ = (∫ x in a..b, f x ∂μ) * r := by
  simpa only [mul_comm r] using integral_const_mul r f

@[simp]
theorem integral_div {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
    ∫ x in a..b, f x / r ∂μ = (∫ x in a..b, f x ∂μ) / r := by
  simpa only [div_eq_mul_inv] using integral_mul_const r⁻¹ f

theorem integral_const' [CompleteSpace E] (c : E) :
    ∫ _ in a..b, c ∂μ = (μ.real (Ioc a b) - μ.real (Ioc b a)) • c := by
  simp only [measureReal_def, intervalIntegral, setIntegral_const, sub_smul]

@[simp]
theorem integral_const [CompleteSpace E] (c : E) : ∫ _ in a..b, c = (b - a) • c := by
  simp only [integral_const', Real.volume_Ioc, ENNReal.toReal_ofReal', ← neg_sub b,
    max_zero_sub_eq_self, measureReal_def]

nonrec theorem integral_smul_measure (c : ℝ≥0∞) :
    ∫ x in a..b, f x ∂c • μ = c.toReal • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, Measure.restrict_smul, integral_smul_measure, smul_sub]

end Basic

-- TODO: add `Complex.ofReal` version of `_root_.integral_ofReal`

nonrec theorem _root_.RCLike.intervalIntegral_ofReal {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}
    {μ : Measure ℝ} {f : ℝ → ℝ} : (∫ x in a..b, (f x : 𝕜) ∂μ) = ↑(∫ x in a..b, f x ∂μ) := by
  simp only [intervalIntegral, integral_ofReal, RCLike.ofReal_sub]

nonrec theorem integral_ofReal {a b : ℝ} {μ : Measure ℝ} {f : ℝ → ℝ} :
    (∫ x in a..b, (f x : ℂ) ∂μ) = ↑(∫ x in a..b, f x ∂μ) :=
  RCLike.intervalIntegral_ofReal

section ContinuousLinearMap

variable {a b : ℝ} {μ : Measure ℝ} {f : ℝ → E}
variable [RCLike 𝕜] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open ContinuousLinearMap

theorem _root_.ContinuousLinearMap.intervalIntegral_apply {a b : ℝ} {φ : ℝ → F →L[𝕜] E}
    (hφ : IntervalIntegrable φ μ a b) (v : F) :
    (∫ x in a..b, φ x ∂μ) v = ∫ x in a..b, φ x v ∂μ := by
  simp_rw [intervalIntegral_eq_integral_uIoc, ← integral_apply hφ.def' v, coe_smul', Pi.smul_apply]

variable [NormedSpace ℝ F] [CompleteSpace F]

theorem _root_.ContinuousLinearMap.intervalIntegral_comp_comm [CompleteSpace E] (L : E →L[𝕜] F)
    (hf : IntervalIntegrable f μ a b) : (∫ x in a..b, L (f x) ∂μ) = L (∫ x in a..b, f x ∂μ) := by
  simp_rw [intervalIntegral, L.integral_comp_comm hf.1, L.integral_comp_comm hf.2, L.map_sub]

end ContinuousLinearMap

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ} {μ : Measure ℝ}

theorem intervalIntegral_re (hf : IntervalIntegrable f μ a b) :
    ∫ x in a..b, RCLike.re (f x) ∂μ = RCLike.re (∫ x in a..b, f x ∂μ) :=
  RCLike.reCLM.intervalIntegral_comp_comm hf

theorem intervalIntegral_im (hf : IntervalIntegrable f μ a b) :
    ∫ x in a..b, RCLike.im (f x) ∂μ = RCLike.im (∫ x in a..b, f x ∂μ) :=
  RCLike.imCLM.intervalIntegral_comp_comm hf

end RCLike

/-!
## Basic arithmetic
Includes addition, scalar multiplication and affine transformations.
-/
section Comp

variable {a b c d : ℝ} (f : ℝ → E)

@[simp]
theorem integral_comp_mul_right (hc : c ≠ 0) :
    (∫ x in a..b, f (x * c)) = c⁻¹ • ∫ x in a * c..b * c, f x := by
  have A : MeasurableEmbedding fun x => x * c :=
    (Homeomorph.mulRight₀ c hc).isClosedEmbedding.measurableEmbedding
  conv_rhs => rw [← Real.smul_map_volume_mul_right hc]
  simp_rw [integral_smul_measure, intervalIntegral, A.setIntegral_map,
    ENNReal.toReal_ofReal (abs_nonneg c)]
  rcases hc.lt_or_gt with h | h
  · simp [h, mul_div_cancel_right₀, hc, abs_of_neg,
      Measure.restrict_congr_set (α := ℝ) (μ := volume) Ico_ae_eq_Ioc]
  · simp [h, mul_div_cancel_right₀, hc, abs_of_pos]

@[simp]
theorem smul_integral_comp_mul_right (c) :
    (c • ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_right]

@[simp]
theorem integral_comp_mul_left (hc : c ≠ 0) :
    (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ x in c * a..c * b, f x := by
  simpa only [mul_comm c] using integral_comp_mul_right f hc

@[simp]
theorem smul_integral_comp_mul_left (c) :
    (c • ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_left]

@[simp]
theorem integral_comp_div (hc : c ≠ 0) :
    (∫ x in a..b, f (x / c)) = c • ∫ x in a / c..b / c, f x := by
  simpa only [inv_inv] using integral_comp_mul_right f (inv_ne_zero hc)

@[simp]
theorem inv_smul_integral_comp_div (c) :
    (c⁻¹ • ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div]

@[simp]
theorem integral_comp_add_right (d) : (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x :=
  have A : MeasurableEmbedding fun x => x + d :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  calc
    (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x ∂Measure.map (fun x => x + d) volume := by
      simp [intervalIntegral, A.setIntegral_map]
    _ = ∫ x in a + d..b + d, f x := by rw [map_add_right_eq_self]

@[simp]
nonrec theorem integral_comp_add_left (d) :
    (∫ x in a..b, f (d + x)) = ∫ x in d + a..d + b, f x := by
  simpa only [add_comm d] using integral_comp_add_right f d

@[simp]
theorem integral_comp_mul_add (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (c * x + d)) = c⁻¹ • ∫ x in c * a + d..c * b + d, f x := by
  rw [← integral_comp_add_right, ← integral_comp_mul_left _ hc]

@[simp]
theorem smul_integral_comp_mul_add (c d) :
    (c • ∫ x in a..b, f (c * x + d)) = ∫ x in c * a + d..c * b + d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_add]

@[simp]
theorem integral_comp_add_mul (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (d + c * x)) = c⁻¹ • ∫ x in d + c * a..d + c * b, f x := by
  rw [← integral_comp_add_left, ← integral_comp_mul_left _ hc]

@[simp]
theorem smul_integral_comp_add_mul (c d) :
    (c • ∫ x in a..b, f (d + c * x)) = ∫ x in d + c * a..d + c * b, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_mul]

@[simp]
theorem integral_comp_div_add (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (x / c + d)) = c • ∫ x in a / c + d..b / c + d, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_add f (inv_ne_zero hc) d

@[simp]
theorem inv_smul_integral_comp_div_add (c d) :
    (c⁻¹ • ∫ x in a..b, f (x / c + d)) = ∫ x in a / c + d..b / c + d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_add]

@[simp]
theorem integral_comp_add_div (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (d + x / c)) = c • ∫ x in d + a / c..d + b / c, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_add_mul f (inv_ne_zero hc) d

@[simp]
theorem inv_smul_integral_comp_add_div (c d) :
    (c⁻¹ • ∫ x in a..b, f (d + x / c)) = ∫ x in d + a / c..d + b / c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_div]

@[simp]
theorem integral_comp_mul_sub (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (c * x - d)) = c⁻¹ • ∫ x in c * a - d..c * b - d, f x := by
  simpa only [sub_eq_add_neg] using integral_comp_mul_add f hc (-d)

@[simp]
theorem smul_integral_comp_mul_sub (c d) :
    (c • ∫ x in a..b, f (c * x - d)) = ∫ x in c * a - d..c * b - d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_sub]

@[simp]
theorem integral_comp_sub_mul (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (d - c * x)) = c⁻¹ • ∫ x in d - c * b..d - c * a, f x := by
  simp only [sub_eq_add_neg, neg_mul_eq_neg_mul]
  rw [integral_comp_add_mul f (neg_ne_zero.mpr hc) d, integral_symm]
  simp only [inv_neg, smul_neg, neg_neg, neg_smul]

@[simp]
theorem smul_integral_comp_sub_mul (c d) :
    (c • ∫ x in a..b, f (d - c * x)) = ∫ x in d - c * b..d - c * a, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_mul]

@[simp]
theorem integral_comp_div_sub (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (x / c - d)) = c • ∫ x in a / c - d..b / c - d, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_sub f (inv_ne_zero hc) d

@[simp]
theorem inv_smul_integral_comp_div_sub (c d) :
    (c⁻¹ • ∫ x in a..b, f (x / c - d)) = ∫ x in a / c - d..b / c - d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_sub]

@[simp]
theorem integral_comp_sub_div (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (d - x / c)) = c • ∫ x in d - b / c..d - a / c, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_sub_mul f (inv_ne_zero hc) d

@[simp]
theorem inv_smul_integral_comp_sub_div (c d) :
    (c⁻¹ • ∫ x in a..b, f (d - x / c)) = ∫ x in d - b / c..d - a / c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_div]

@[simp]
theorem integral_comp_sub_right (d) : (∫ x in a..b, f (x - d)) = ∫ x in a - d..b - d, f x := by
  simpa only [sub_eq_add_neg] using integral_comp_add_right f (-d)

@[simp]
theorem integral_comp_sub_left (d) : (∫ x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x := by
  simpa only [one_mul, one_smul, inv_one] using integral_comp_sub_mul f one_ne_zero d

@[simp]
theorem integral_comp_neg : (∫ x in a..b, f (-x)) = ∫ x in -b..-a, f x := by
  simpa only [zero_sub] using integral_comp_sub_left f 0

end Comp

/-!
### Integral is an additive function of the interval

In this section we prove that `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ`
as well as a few other identities trivially equivalent to this one. We also prove that
`∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ` provided that `support f ⊆ Ioc a b`.

-/

section OrderClosedTopology

variable {a b c d : ℝ} {f g : ℝ → E} {μ : Measure ℝ}

/-- If two functions are equal in the relevant interval, their interval integrals are also equal. -/
theorem integral_congr {a b : ℝ} (h : EqOn f g [[a, b]]) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ := by
  rcases le_total a b with hab | hab <;>
    simpa [hab, integral_of_le, integral_of_ge] using
      setIntegral_congr_fun measurableSet_Ioc (h.mono Ioc_subset_Icc_self)

theorem integral_add_adjacent_intervals_cancel (hab : IntervalIntegrable f μ a b)
    (hbc : IntervalIntegrable f μ b c) :
    (((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ) + ∫ x in c..a, f x ∂μ) = 0 := by
  have hac := hab.trans hbc
  simp only [intervalIntegral, sub_add_sub_comm, sub_eq_zero]
  iterate 4 rw [← setIntegral_union]
  · suffices Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc b a ∪ Ioc c b ∪ Ioc a c by rw [this]
    rw [Ioc_union_Ioc_union_Ioc_cycle, union_right_comm, Ioc_union_Ioc_union_Ioc_cycle,
      min_left_comm, max_left_comm]
  all_goals
    simp [*, hab.1, hab.2, hbc.1, hbc.2, hac.1, hac.2]

theorem integral_add_adjacent_intervals (hab : IntervalIntegrable f μ a b)
    (hbc : IntervalIntegrable f μ b c) :
    ((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ) = ∫ x in a..c, f x ∂μ := by
  rw [← add_neg_eq_zero, ← integral_symm, integral_add_adjacent_intervals_cancel hab hbc]

theorem sum_integral_adjacent_intervals_Ico {a : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hint : ∀ k ∈ Ico m n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    ∑ k ∈ Finset.Ico m n, ∫ x in a k..a <| k + 1, f x ∂μ = ∫ x in a m..a n, f x ∂μ := by
  revert hint
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro p hmp IH h
    rw [Finset.sum_Ico_succ_top hmp, IH, integral_add_adjacent_intervals]
    · refine IntervalIntegrable.trans_iterate_Ico hmp fun k hk => h k ?_
      exact (Ico_subset_Ico le_rfl (Nat.le_succ _)) hk
    · apply h
      simp [hmp]
    · intro k hk
      exact h _ (Ico_subset_Ico_right p.le_succ hk)

theorem sum_integral_adjacent_intervals {a : ℕ → ℝ} {n : ℕ}
    (hint : ∀ k < n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    ∑ k ∈ Finset.range n, ∫ x in a k..a <| k + 1, f x ∂μ = ∫ x in (a 0)..(a n), f x ∂μ := by
  rw [← Nat.Ico_zero_eq_range]
  exact sum_integral_adjacent_intervals_Ico zero_le fun k hk => hint k hk.2

theorem integral_interval_sub_left (hab : IntervalIntegrable f μ a b)
    (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in a..c, f x ∂μ) = ∫ x in c..b, f x ∂μ :=
  sub_eq_of_eq_add' <| Eq.symm <| integral_add_adjacent_intervals hac (hac.symm.trans hab)

theorem integral_interval_add_interval_comm (hab : IntervalIntegrable f μ a b)
    (hcd : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) + ∫ x in c..d, f x ∂μ) =
      (∫ x in a..d, f x ∂μ) + ∫ x in c..b, f x ∂μ := by
  rw [← integral_add_adjacent_intervals hac hcd, add_assoc, add_left_comm,
    integral_add_adjacent_intervals hac (hac.symm.trans hab), add_comm]

theorem integral_interval_sub_interval_comm (hab : IntervalIntegrable f μ a b)
    (hcd : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in c..d, f x ∂μ) =
      (∫ x in a..c, f x ∂μ) - ∫ x in b..d, f x ∂μ := by
  simp only [sub_eq_add_neg, ← integral_symm,
    integral_interval_add_interval_comm hab hcd.symm (hac.trans hcd)]

theorem integral_interval_sub_interval_comm' (hab : IntervalIntegrable f μ a b)
    (hcd : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in c..d, f x ∂μ) =
      (∫ x in d..b, f x ∂μ) - ∫ x in c..a, f x ∂μ := by
  rw [integral_interval_sub_interval_comm hab hcd hac, integral_symm b d, integral_symm a c,
    sub_neg_eq_add, sub_eq_neg_add]

theorem integral_Iic_sub_Iic (ha : IntegrableOn f (Iic a) μ) (hb : IntegrableOn f (Iic b) μ) :
    ((∫ x in Iic b, f x ∂μ) - ∫ x in Iic a, f x ∂μ) = ∫ x in a..b, f x ∂μ := by
  wlog hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab), neg_sub]
  rw [sub_eq_iff_eq_add', integral_of_le hab, ← setIntegral_union (Iic_disjoint_Ioc le_rfl),
    Iic_union_Ioc_eq_Iic hab]
  exacts [measurableSet_Ioc, ha, hb.mono_set fun _ => And.right]

theorem integral_interval_add_Ioi (ha : IntegrableOn f (Ioi a) μ)
    (hb : IntegrableOn f (Ioi b) μ) :
    ∫ (x : ℝ) in a..b, f x ∂μ + ∫ (x : ℝ) in Ioi b, f x ∂μ
    = ∫ (x : ℝ) in Ioi a, f x ∂μ := by
  wlog hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab)]; grind
  rw [integral_of_le hab, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (ha.mono_set Ioc_subset_Ioi_self) hb, Ioc_union_Ioi_eq_Ioi hab]

theorem integral_interval_add_Ioi' (ha : IntervalIntegrable f μ a b)
    (hb : IntegrableOn f (Ioi b) μ) :
    ∫ (x : ℝ) in a..b, f x ∂μ + ∫ (x : ℝ) in Ioi b, f x ∂μ
    = ∫ (x : ℝ) in Ioi a, f x ∂μ := by
  rw [integral_interval_add_Ioi _ hb]
  by_cases! h : a ≤ b
  · exact (Ioc_union_Ioi_eq_Ioi h) ▸ IntegrableOn.union
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h).1 ha) hb
  · exact hb.mono_set <| Ioi_subset_Ioi h.le

theorem integral_Ioi_sub_Ioi (hf : IntegrableOn f (Ioi a) μ) (hab : a ≤ b) :
    ∫ x in Ioi a, f x ∂μ - ∫ x in Ioi b, f x ∂μ = ∫ x in a..b, f x ∂μ :=
  sub_eq_of_eq_add (integral_interval_add_Ioi hf (hf.mono_set (Ioi_subset_Ioi hab))).symm

theorem integral_Ioi_sub_Ioi' (hf : IntegrableOn f (Ioi a) μ) (hg : IntegrableOn f (Ioi b) μ) :
    ∫ x in Ioi a, f x ∂μ - ∫ x in Ioi b, f x ∂μ = ∫ x in a..b, f x ∂μ := by
  wlog! hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  exact integral_Ioi_sub_Ioi hf hab

theorem integral_Iio_sub_Iio (hf : IntegrableOn f (Iio b) μ) (hab : a ≤ b) :
    ∫ x in Iio b, f x ∂μ - ∫ x in Iio a, f x ∂μ = ∫ x in Ico a b, f x ∂μ := by
  have ha : IntegrableOn f (Iio a) μ := hf.mono_set (Iio_subset_Iio hab)
  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Iio_self
  rw [sub_eq_iff_eq_add', ← setIntegral_union (by grind) measurableSet_Ico ha h,
      Iio_union_Ico_eq_Iio hab]

theorem integral_Iio_sub_Iio' [NoAtoms μ] (hf : IntegrableOn f (Iio b) μ)
    (hg : IntegrableOn f (Iio a) μ) :
    ∫ x in Iio b, f x ∂μ - ∫ x in Iio a, f x ∂μ = ∫ x in a..b, f x ∂μ := by
  wlog! hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  rw [integral_Iio_sub_Iio hf hab, integral_of_le hab, integral_Ico_eq_integral_Ioc]

theorem integral_Ici_sub_Ici (hf : IntegrableOn f (Ici a) μ) (hab : a ≤ b) :
    ∫ x in Ici a, f x ∂μ - ∫ x in Ici b, f x ∂μ = ∫ x in Ico a b, f x ∂μ := by
  have ha : IntegrableOn f (Ici b) μ := hf.mono_set (Ici_subset_Ici.2 hab)
  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Ici_self
  rw [sub_eq_iff_eq_add', ← setIntegral_union (by grind) measurableSet_Ico ha h, union_comm,
    Ico_union_Ici_eq_Ici hab]

theorem integral_Ici_sub_Ici' [NoAtoms μ] (hf : IntegrableOn f (Ici a) μ)
    (hg : IntegrableOn f (Ici b) μ) :
    ∫ x in Ici a, f x ∂μ - ∫ x in Ici b, f x ∂μ = ∫ x in a..b, f x ∂μ := by
  wlog! hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  rw [integral_Ici_sub_Ici hf hab, integral_of_le hab, integral_Ico_eq_integral_Ioc]

theorem integral_Iic_add_Ioi (h_left : IntegrableOn f (Iic b) μ)
    (h_right : IntegrableOn f (Ioi b) μ) :
    (∫ x in Iic b, f x ∂μ) + (∫ x in Ioi b, f x ∂μ) = ∫ (x : ℝ), f x ∂μ := by
  convert (setIntegral_union (Iic_disjoint_Ioi <| Eq.le rfl) measurableSet_Ioi h_left h_right).symm
  rw [Iic_union_Ioi, Measure.restrict_univ]

theorem integral_Iio_add_Ici (h_left : IntegrableOn f (Iio b) μ)
    (h_right : IntegrableOn f (Ici b) μ) :
    (∫ x in Iio b, f x ∂μ) + (∫ x in Ici b, f x ∂μ) = ∫ (x : ℝ), f x ∂μ := by
  convert (setIntegral_union (Iio_disjoint_Ici <| Eq.le rfl) measurableSet_Ici h_left h_right).symm
  rw [Iio_union_Ici, Measure.restrict_univ]

/-- If `μ` is a finite measure then `∫ x in a..b, c ∂μ = (μ (Iic b) - μ (Iic a)) • c`. -/
theorem integral_const_of_cdf [CompleteSpace E] [IsFiniteMeasure μ] (c : E) :
    ∫ _ in a..b, c ∂μ = (μ.real (Iic b) - μ.real (Iic a)) • c := by
  simp only [sub_smul, ← setIntegral_const]
  refine (integral_Iic_sub_Iic ?_ ?_).symm <;> simp

theorem integral_eq_integral_of_support_subset {a b} (h : support f ⊆ Ioc a b) :
    ∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ := by
  rcases le_total a b with hab | hab
  · rw [integral_of_le hab, ← integral_indicator measurableSet_Ioc, indicator_eq_self.2 h]
  · rw [Ioc_eq_empty hab.not_gt, subset_empty_iff, support_eq_empty_iff] at h
    simp [h]

theorem integral_congr_ae' (h : ∀ᵐ x ∂μ, x ∈ Ioc a b → f x = g x)
    (h' : ∀ᵐ x ∂μ, x ∈ Ioc b a → f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ := by
  simp only [intervalIntegral, setIntegral_congr_ae measurableSet_Ioc h,
    setIntegral_congr_ae measurableSet_Ioc h']

theorem integral_congr_ae (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = g x) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
  integral_congr_ae' (ae_uIoc_iff.mp h).1 (ae_uIoc_iff.mp h).2

/-- Integrals are equal for functions that agree almost everywhere for the restricted measure. -/
theorem integral_congr_ae_restrict {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ}
    (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
  integral_congr_ae (ae_imp_of_ae_restrict h)

/-- Integrals are invariant when functions change along discrete sets. -/
theorem integral_congr_codiscreteWithin {a b : ℝ} {f₁ f₂ : ℝ → ℝ}
    (hf : f₁ =ᶠ[codiscreteWithin (Ι a b)] f₂) :
    ∫ (x : ℝ) in a..b, f₁ x = ∫ (x : ℝ) in a..b, f₂ x :=
  integral_congr_ae_restrict (ae_restrict_le_codiscreteWithin measurableSet_uIoc hf)

theorem integral_zero_ae (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = 0) : ∫ x in a..b, f x ∂μ = 0 :=
  calc
    ∫ x in a..b, f x ∂μ = ∫ _ in a..b, 0 ∂μ := integral_congr_ae h
    _ = 0 := integral_zero

nonrec theorem integral_indicator {a₁ a₂ a₃ : ℝ} (h : a₂ ∈ Icc a₁ a₃) :
    ∫ x in a₁..a₃, indicator {x | x ≤ a₂} f x ∂μ = ∫ x in a₁..a₂, f x ∂μ := by
  have : {x | x ≤ a₂} ∩ Ioc a₁ a₃ = Ioc a₁ a₂ := Iic_inter_Ioc_of_le h.2
  rw [integral_of_le h.1, integral_of_le (h.1.trans h.2), integral_indicator,
    Measure.restrict_restrict, this]
  · exact measurableSet_Iic
  all_goals apply measurableSet_Iic

end OrderClosedTopology

section

variable {f g : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ}

theorem integral_eq_zero_iff_of_le_of_nonneg_ae (hab : a ≤ b) (hf : 0 ≤ᵐ[μ.restrict (Ioc a b)] f)
    (hfi : IntervalIntegrable f μ a b) :
    ∫ x in a..b, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b)] 0 := by
  rw [integral_of_le hab, integral_eq_zero_iff_of_nonneg_ae hf hfi.1]

theorem integral_eq_zero_iff_of_nonneg_ae (hf : 0 ≤ᵐ[μ.restrict (Ioc a b ∪ Ioc b a)] f)
    (hfi : IntervalIntegrable f μ a b) :
    ∫ x in a..b, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b ∪ Ioc b a)] 0 := by
  rcases le_total a b with hab | hab <;>
    simp only [Ioc_eq_empty hab.not_gt, empty_union, union_empty] at hf ⊢
  · exact integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi
  · rw [integral_symm, neg_eq_zero, integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi.symm]

/-- If `f` is nonnegative and integrable on the unordered interval `Set.uIoc a b`, then its
integral over `a..b` is positive if and only if `a < b` and the measure of
`Function.support f ∩ Set.Ioc a b` is positive. -/
theorem integral_pos_iff_support_of_nonneg_ae' (hf : 0 ≤ᵐ[μ.restrict (Ι a b)] f)
    (hfi : IntervalIntegrable f μ a b) :
    (0 < ∫ x in a..b, f x ∂μ) ↔ a < b ∧ 0 < μ (support f ∩ Ioc a b) := by
  rcases lt_or_ge a b with hab | hba
  · rw [uIoc_of_le hab.le] at hf
    simp only [hab, true_and, integral_of_le hab.le,
      setIntegral_pos_iff_support_of_nonneg_ae hf hfi.1]
  · suffices (∫ x in a..b, f x ∂μ) ≤ 0 by simp only [this.not_gt, hba.not_gt, false_and]
    rw [integral_of_ge hba, neg_nonpos]
    rw [uIoc_comm, uIoc_of_le hba] at hf
    exact integral_nonneg_of_ae hf

/-- If `f` is nonnegative a.e.-everywhere and it is integrable on the unordered interval
`Set.uIoc a b`, then its integral over `a..b` is positive if and only if `a < b` and the
measure of `Function.support f ∩ Set.Ioc a b` is positive. -/
theorem integral_pos_iff_support_of_nonneg_ae (hf : 0 ≤ᵐ[μ] f) (hfi : IntervalIntegrable f μ a b) :
    (0 < ∫ x in a..b, f x ∂μ) ↔ a < b ∧ 0 < μ (support f ∩ Ioc a b) :=
  integral_pos_iff_support_of_nonneg_ae' (ae_mono Measure.restrict_le_self hf) hfi

/-- If `f : ℝ → ℝ` is integrable on `(a, b]` for real numbers `a < b`, and positive on the interior
of the interval, then its integral over `a..b` is strictly positive. -/
theorem intervalIntegral_pos_of_pos_on {f : ℝ → ℝ} {a b : ℝ} (hfi : IntervalIntegrable f volume a b)
    (hpos : ∀ x : ℝ, x ∈ Ioo a b → 0 < f x) (hab : a < b) : 0 < ∫ x : ℝ in a..b, f x := by
  have hsupp : Ioo a b ⊆ support f ∩ Ioc a b := fun x hx =>
    ⟨mem_support.mpr (hpos x hx).ne', Ioo_subset_Ioc_self hx⟩
  have h₀ : 0 ≤ᵐ[volume.restrict (uIoc a b)] f := by
    rw [EventuallyLE, uIoc_of_le hab.le]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with x hx using (hpos x hx).le
  rw [integral_pos_iff_support_of_nonneg_ae' h₀ hfi]
  exact ⟨hab, ((Measure.measure_Ioo_pos _).mpr hab).trans_le (measure_mono hsupp)⟩

/-- If `f : ℝ → ℝ` is strictly positive everywhere, and integrable on `(a, b]` for real numbers
`a < b`, then its integral over `a..b` is strictly positive. (See `intervalIntegral_pos_of_pos_on`
for a version only assuming positivity of `f` on `(a, b)` rather than everywhere.) -/
theorem intervalIntegral_pos_of_pos {f : ℝ → ℝ} {a b : ℝ}
    (hfi : IntervalIntegrable f MeasureSpace.volume a b) (hpos : ∀ x, 0 < f x) (hab : a < b) :
    0 < ∫ x in a..b, f x :=
  intervalIntegral_pos_of_pos_on hfi (fun x _ => hpos x) hab

/-- If `f` and `g` are two functions that are interval integrable on `a..b`, `a ≤ b`,
`f x ≤ g x` for a.e. `x ∈ Set.Ioc a b`, and `f x < g x` on a subset of `Set.Ioc a b`
of nonzero measure, then `∫ x in a..b, f x ∂μ < ∫ x in a..b, g x ∂μ`. -/
theorem integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero (hab : a ≤ b)
    (hfi : IntervalIntegrable f μ a b) (hgi : IntervalIntegrable g μ a b)
    (hle : f ≤ᵐ[μ.restrict (Ioc a b)] g) (hlt : μ.restrict (Ioc a b) {x | f x < g x} ≠ 0) :
    (∫ x in a..b, f x ∂μ) < ∫ x in a..b, g x ∂μ := by
  rw [← sub_pos, ← integral_sub hgi hfi, integral_of_le hab,
    MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · refine pos_iff_ne_zero.2 (mt (measure_mono_null ?_) hlt)
    exact fun x hx => (sub_pos.2 hx.out).ne'
  exacts [hle.mono fun x => sub_nonneg.2, hgi.1.sub hfi.1]

/-- If `f` and `g` are continuous on `[a, b]`, `a < b`, `f x ≤ g x` on this interval, and
`f c < g c` at some point `c ∈ [a, b]`, then `∫ x in a..b, f x < ∫ x in a..b, g x`. -/
theorem integral_lt_integral_of_continuousOn_of_le_of_exists_lt {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hle : ∀ x ∈ Ioc a b, f x ≤ g x) (hlt : ∃ c ∈ Icc a b, f c < g c) :
    (∫ x in a..b, f x) < ∫ x in a..b, g x := by
  apply integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero hab.le
    (hfc.intervalIntegrable_of_Icc hab.le) (hgc.intervalIntegrable_of_Icc hab.le)
  · simpa only [measurableSet_Ioc, ae_restrict_eq]
      using (ae_restrict_mem measurableSet_Ioc).mono hle
  contrapose! hlt
  have h_eq : f =ᵐ[volume.restrict (Ioc a b)] g := by
    simp only [← not_le, ← ae_iff] at hlt
    exact EventuallyLE.antisymm ((ae_restrict_iff' measurableSet_Ioc).2 <|
      Eventually.of_forall hle) hlt
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at h_eq
  exact fun c hc ↦ (Measure.eqOn_Icc_of_ae_eq volume hab.ne h_eq hfc hgc hc).ge

theorem integral_nonneg_of_ae_restrict (hab : a ≤ b) (hf : 0 ≤ᵐ[μ.restrict (Icc a b)] f) :
    0 ≤ ∫ u in a..b, f u ∂μ := by
  let H := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hf
  simpa only [integral_of_le hab] using setIntegral_nonneg_of_ae_restrict H

theorem integral_nonneg_of_ae (hab : a ≤ b) (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ u in a..b, f u ∂μ :=
  integral_nonneg_of_ae_restrict hab <| ae_restrict_of_ae hf

theorem integral_nonneg_of_forall (hab : a ≤ b) (hf : ∀ u, 0 ≤ f u) : 0 ≤ ∫ u in a..b, f u ∂μ :=
  integral_nonneg_of_ae hab <| Eventually.of_forall hf

theorem integral_nonneg (hab : a ≤ b) (hf : ∀ u, u ∈ Icc a b → 0 ≤ f u) : 0 ≤ ∫ u in a..b, f u ∂μ :=
  integral_nonneg_of_ae_restrict hab <| (ae_restrict_iff' measurableSet_Icc).mpr <| ae_of_all μ hf

theorem abs_integral_le_integral_abs (hab : a ≤ b) :
    |∫ x in a..b, f x ∂μ| ≤ ∫ x in a..b, |f x| ∂μ := by
  simpa only [← Real.norm_eq_abs] using norm_integral_le_integral_norm hab

lemma integral_pos (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hle : ∀ x ∈ Ioc a b, 0 ≤ f x) (hlt : ∃ c ∈ Icc a b, 0 < f c) :
    0 < ∫ x in a..b, f x :=
  (integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    continuousOn_const hfc hle hlt).trans_eq' (by simp)

section Mono

theorem integral_mono_interval {c d} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    (hf : 0 ≤ᵐ[μ.restrict (Ioc c d)] f) (hfi : IntervalIntegrable f μ c d) :
    (∫ x in a..b, f x ∂μ) ≤ ∫ x in c..d, f x ∂μ := by
  rw [integral_of_le hab, integral_of_le (hca.trans (hab.trans hbd))]
  exact setIntegral_mono_set hfi.1 hf (Ioc_subset_Ioc hca hbd).eventuallyLE

theorem abs_integral_mono_interval {c d} (h : Ι a b ⊆ Ι c d) (hf : 0 ≤ᵐ[μ.restrict (Ι c d)] f)
    (hfi : IntervalIntegrable f μ c d) : |∫ x in a..b, f x ∂μ| ≤ |∫ x in c..d, f x ∂μ| :=
  have hf' : 0 ≤ᵐ[μ.restrict (Ι a b)] f := ae_mono (Measure.restrict_mono h le_rfl) hf
  calc
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| := abs_integral_eq_abs_integral_uIoc f
    _ = ∫ x in Ι a b, f x ∂μ := abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae hf')
    _ ≤ ∫ x in Ι c d, f x ∂μ := setIntegral_mono_set hfi.def' hf h.eventuallyLE
    _ ≤ |∫ x in Ι c d, f x ∂μ| := le_abs_self _
    _ = |∫ x in c..d, f x ∂μ| := (abs_integral_eq_abs_integral_uIoc f).symm

variable (hab : a ≤ b) (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b)
include hab hf hg

theorem integral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict (Icc a b)] g) :
    (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  let H := h.filter_mono <| ae_mono <| Measure.restrict_mono Ioc_subset_Icc_self <| le_refl μ
  simpa only [integral_of_le hab] using setIntegral_mono_ae_restrict hf.1 hg.1 H

theorem integral_mono_ae (h : f ≤ᵐ[μ] g) : (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  simpa only [integral_of_le hab] using setIntegral_mono_ae hf.1 hg.1 h

theorem integral_mono_on (h : ∀ x ∈ Icc a b, f x ≤ g x) :
    (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  let H x hx := h x <| Ioc_subset_Icc_self hx
  simpa only [integral_of_le hab] using setIntegral_mono_on hf.1 hg.1 measurableSet_Ioc H

theorem integral_mono_on_of_le_Ioo [NoAtoms μ] (h : ∀ x ∈ Ioo a b, f x ≤ g x) :
    (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  simp only [integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_mono_on
  · apply hf.1.mono Ioo_subset_Ioc_self le_rfl
  · apply hg.1.mono Ioo_subset_Ioc_self le_rfl
  · exact measurableSet_Ioo
  · exact h

theorem integral_mono (h : f ≤ g) : (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ :=
  integral_mono_ae hab hf hg <| ae_of_all _ h

end Mono

end

section HasSum

variable {μ : Measure ℝ} {f : ℝ → E}

theorem _root_.MeasureTheory.Integrable.hasSum_intervalIntegral (hfi : Integrable f μ) (y : ℝ) :
    HasSum (fun n : ℤ => ∫ x in y + n..y + n + 1, f x ∂μ) (∫ x, f x ∂μ) := by
  simp_rw [integral_of_le (le_add_of_nonneg_right zero_le_one)]
  rw [← setIntegral_univ, ← iUnion_Ioc_add_intCast y]
  exact
    hasSum_integral_iUnion (fun i => measurableSet_Ioc) (pairwise_disjoint_Ioc_add_intCast y)
      hfi.integrableOn

theorem _root_.MeasureTheory.Integrable.hasSum_intervalIntegral_comp_add_int (hfi : Integrable f) :
    HasSum (fun n : ℤ => ∫ x in (0 : ℝ)..(1 : ℝ), f (x + n)) (∫ x, f x) := by
  simpa only [integral_comp_add_right, zero_add, add_comm (1 : ℝ)] using
    hfi.hasSum_intervalIntegral 0

end HasSum

end intervalIntegral
