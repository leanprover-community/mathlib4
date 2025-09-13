/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# With Density

For an s-finite kernel `κ : Kernel α β` and a function `f : α → β → ℝ≥0∞` which is finite
everywhere, we define `withDensity κ f` as the kernel `a ↦ (κ a).withDensity (f a)`. This is
an s-finite kernel.

## Main definitions

* `ProbabilityTheory.Kernel.withDensity κ (f : α → β → ℝ≥0∞)`:
  kernel `a ↦ (κ a).withDensity (f a)`. It is defined if `κ` is s-finite. If `f` is finite
  everywhere, then this is also an s-finite kernel. The class of s-finite kernels is the smallest
  class of kernels that contains finite kernels and which is stable by `withDensity`.
  Integral: `∫⁻ b, g b ∂(withDensity κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

## Main statements

* `ProbabilityTheory.Kernel.lintegral_withDensity`:
  `∫⁻ b, g b ∂(withDensity κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

-/


open MeasureTheory ProbabilityTheory

open scoped MeasureTheory ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {κ : Kernel α β} {f : α → β → ℝ≥0∞}

/-- Kernel with image `(κ a).withDensity (f a)` if `Function.uncurry f` is measurable, and
with image 0 otherwise. If `Function.uncurry f` is measurable, it satisfies
`∫⁻ b, g b ∂(withDensity κ f hf a) = ∫⁻ b, f a b * g b ∂(κ a)`. -/
noncomputable def withDensity (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → β → ℝ≥0∞) :
    Kernel α β :=
  @dite _ (Measurable (Function.uncurry f)) (Classical.dec _) (fun hf =>
    (⟨fun a => (κ a).withDensity (f a),
      by
        refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
        simp_rw [withDensity_apply _ hs]
        exact hf.setLIntegral_kernel_prod_right hs⟩ : Kernel α β)) fun _ => 0

theorem withDensity_of_not_measurable (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : ¬Measurable (Function.uncurry f)) : withDensity κ f = 0 := by classical exact dif_neg hf

protected theorem withDensity_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) :
    withDensity κ f a = (κ a).withDensity (f a) := by
  classical
  rw [withDensity, dif_pos hf]
  rfl

protected theorem withDensity_apply' (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) (s : Set β) :
    withDensity κ f a s = ∫⁻ b in s, f a b ∂κ a := by
  rw [Kernel.withDensity_apply κ hf, withDensity_apply' _ s]

nonrec lemma withDensity_congr_ae (κ : Kernel α β) [IsSFiniteKernel κ] {f g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfg : ∀ a, f a =ᵐ[κ a] g a) :
    withDensity κ f = withDensity κ g := by
  ext a
  rw [Kernel.withDensity_apply _ hf,Kernel.withDensity_apply _ hg, withDensity_congr_ae (hfg a)]

nonrec lemma withDensity_absolutelyContinuous [IsSFiniteKernel κ]
    (f : α → β → ℝ≥0∞) (a : α) :
    Kernel.withDensity κ f a ≪ κ a := by
  by_cases hf : Measurable (Function.uncurry f)
  · rw [Kernel.withDensity_apply _ hf]
    exact withDensity_absolutelyContinuous _ _
  · rw [withDensity_of_not_measurable _ hf]
    simp [Measure.AbsolutelyContinuous.zero]

@[simp]
lemma withDensity_one (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ 1 = κ := by
  ext; rw [Kernel.withDensity_apply _ measurable_const]; simp

@[simp]
lemma withDensity_one' (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ (fun _ _ ↦ 1) = κ := Kernel.withDensity_one _

@[simp]
lemma withDensity_zero (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ 0 = 0 := by
  ext; rw [Kernel.withDensity_apply _ measurable_const]; simp

@[simp]
lemma withDensity_zero' (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ (fun _ _ ↦ 0) = 0 := Kernel.withDensity_zero _

theorem lintegral_withDensity (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) {g : β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ b, g b ∂withDensity κ f a = ∫⁻ b, f a b * g b ∂κ a := by
  rw [Kernel.withDensity_apply _ hf,
    lintegral_withDensity_eq_lintegral_mul _ (Measurable.of_uncurry_left hf) hg]
  simp_rw [Pi.mul_apply]

theorem integral_withDensity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : β → E} [IsSFiniteKernel κ] {a : α} {g : α → β → ℝ≥0}
    (hg : Measurable (Function.uncurry g)) :
    ∫ b, f b ∂withDensity κ (fun a b => g a b) a = ∫ b, g a b • f b ∂κ a := by
  rw [Kernel.withDensity_apply, integral_withDensity_eq_integral_smul]
  · fun_prop
  · fun_prop

theorem withDensity_add_left (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (f : α → β → ℝ≥0∞) : withDensity (κ + η) f = withDensity κ f + withDensity η f := by
  by_cases hf : Measurable (Function.uncurry f)
  · ext a s
    simp only [Kernel.withDensity_apply _ hf, coe_add, Pi.add_apply, withDensity_add_measure,
      Measure.add_apply]
  · simp_rw [withDensity_of_not_measurable _ hf]
    rw [zero_add]

theorem withDensity_kernel_sum [Countable ι] (κ : ι → Kernel α β) (hκ : ∀ i, IsSFiniteKernel (κ i))
    (f : α → β → ℝ≥0∞) :
    withDensity (Kernel.sum κ) f = Kernel.sum fun i => withDensity (κ i) f := by
  by_cases hf : Measurable (Function.uncurry f)
  · ext1 a
    simp_rw [sum_apply, Kernel.withDensity_apply _ hf, sum_apply,
      withDensity_sum (fun n => κ n a) (f a)]
  · simp_rw [withDensity_of_not_measurable _ hf]
    exact sum_zero.symm

lemma withDensity_add_right [IsSFiniteKernel κ] {f g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    withDensity κ (f + g) = withDensity κ f + withDensity κ g := by
  ext a
  rw [coe_add, Pi.add_apply, Kernel.withDensity_apply _ hf, Kernel.withDensity_apply _ hg,
    Kernel.withDensity_apply, Pi.add_apply, MeasureTheory.withDensity_add_right]
  · fun_prop
  · exact hf.add hg

lemma withDensity_sub_add_cancel [IsSFiniteKernel κ] {f g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfg : ∀ a, g a ≤ᵐ[κ a] f a) :
    withDensity κ (fun a x ↦ f a x - g a x) + withDensity κ g = withDensity κ f := by
  rw [← withDensity_add_right _ hg]
  swap; · exact hf.sub hg
  refine withDensity_congr_ae κ ((hf.sub hg).add hg) hf (fun a ↦ ?_)
  filter_upwards [hfg a] with x hx
  rwa [Pi.add_apply, Pi.add_apply, tsub_add_cancel_iff_le]

theorem withDensity_tsum [Countable ι] (κ : Kernel α β) [IsSFiniteKernel κ] {f : ι → α → β → ℝ≥0∞}
    (hf : ∀ i, Measurable (Function.uncurry (f i))) :
    withDensity κ (∑' n, f n) = Kernel.sum fun n => withDensity κ (f n) := by
  have h_sum_a : ∀ a, Summable fun n => f n a := fun a => Pi.summable.mpr fun b => ENNReal.summable
  have h_sum : Summable fun n => f n := Pi.summable.mpr h_sum_a
  ext a s hs
  rw [sum_apply' _ a hs, Kernel.withDensity_apply' κ _ a s]
  swap
  · have : Function.uncurry (∑' n, f n) = ∑' n, Function.uncurry (f n) := by
      ext1 p
      simp only [Function.uncurry_def]
      rw [tsum_apply h_sum, tsum_apply (h_sum_a _), tsum_apply]
      exact Pi.summable.mpr fun p => ENNReal.summable
    rw [this]
    fun_prop
  have : ∫⁻ b in s, (∑' n, f n) a b ∂κ a = ∫⁻ b in s, ∑' n, (fun b => f n a b) b ∂κ a := by
    congr with b
    rw [tsum_apply h_sum, tsum_apply (h_sum_a a)]
  rw [this, lintegral_tsum fun n => by fun_prop]
  congr with n
  rw [Kernel.withDensity_apply' _ (hf n) a s]

/-- If a kernel `κ` is finite and a function `f : α → β → ℝ≥0∞` is bounded, then `withDensity κ f`
is finite. -/
theorem isFiniteKernel_withDensity_of_bounded (κ : Kernel α β) [IsFiniteKernel κ] {B : ℝ≥0∞}
    (hB_top : B ≠ ∞) (hf_B : ∀ a b, f a b ≤ B) : IsFiniteKernel (withDensity κ f) := by
  by_cases hf : Measurable (Function.uncurry f)
  · exact ⟨⟨B * κ.bound, ENNReal.mul_lt_top hB_top.lt_top κ.bound_lt_top, fun a => by
        rw [Kernel.withDensity_apply' κ hf a Set.univ]
        calc
          ∫⁻ b in Set.univ, f a b ∂κ a ≤ ∫⁻ _ in Set.univ, B ∂κ a := lintegral_mono (hf_B a)
          _ = B * κ a Set.univ := by
            simp only [Measure.restrict_univ, MeasureTheory.lintegral_const]
          _ ≤ B * κ.bound := mul_le_mul_left' (measure_le_bound κ a Set.univ) _⟩⟩
  · rw [withDensity_of_not_measurable _ hf]
    infer_instance

/-- Auxiliary lemma for `IsSFiniteKernel.withDensity`.
If a kernel `κ` is finite, then `withDensity κ f` is s-finite. -/
theorem isSFiniteKernel_withDensity_of_isFiniteKernel (κ : Kernel α β) [IsFiniteKernel κ]
    (hf_ne_top : ∀ a b, f a b ≠ ∞) : IsSFiniteKernel (withDensity κ f) := by
  -- We already have that for `f` bounded from above and a `κ` a finite kernel,
  -- `withDensity κ f` is finite. We write any function as a countable sum of bounded
  -- functions, and decompose an s-finite kernel as a sum of finite kernels. We then use that
  -- `withDensity` commutes with sums for both arguments and get a sum of finite kernels.
  by_cases hf : Measurable (Function.uncurry f)
  swap; · rw [withDensity_of_not_measurable _ hf]; infer_instance
  let fs : ℕ → α → β → ℝ≥0∞ := fun n a b => min (f a b) (n + 1) - min (f a b) n
  have h_le : ∀ a b n, ⌈(f a b).toReal⌉₊ ≤ n → f a b ≤ n := by
    intro a b n hn
    have : (f a b).toReal ≤ n := Nat.le_of_ceil_le hn
    rw [← ENNReal.le_ofReal_iff_toReal_le (hf_ne_top a b) _] at this
    · refine this.trans (le_of_eq ?_)
      rw [ENNReal.ofReal_natCast]
    · norm_cast
      exact zero_le _
  have h_zero : ∀ a b n, ⌈(f a b).toReal⌉₊ ≤ n → fs n a b = 0 := by
    intro a b n hn
    suffices min (f a b) (n + 1) = f a b ∧ min (f a b) n = f a b by
      simp_rw [fs, this.1, this.2, tsub_self (f a b)]
    exact ⟨min_eq_left ((h_le a b n hn).trans (le_add_of_nonneg_right zero_le_one)),
      min_eq_left (h_le a b n hn)⟩
  have hf_eq_tsum : f = ∑' n, fs n := by
    have h_sum_a : ∀ a, Summable fun n => fs n a := by
      refine fun a => Pi.summable.mpr fun b => ?_
      suffices ∀ n, n ∉ Finset.range ⌈(f a b).toReal⌉₊ → fs n a b = 0 from
        summable_of_ne_finset_zero this
      intro n hn_notMem
      rw [Finset.mem_range, not_lt] at hn_notMem
      exact h_zero a b n hn_notMem
    ext a b : 2
    rw [tsum_apply (Pi.summable.mpr h_sum_a), tsum_apply (h_sum_a a),
      ENNReal.tsum_eq_liminf_sum_nat]
    have h_finset_sum : ∀ n, ∑ i ∈ Finset.range n, fs i a b = min (f a b) n := fun n ↦ by
      induction n with
      | zero => simp
      | succ n hn =>
        rw [Finset.sum_range_succ, hn]
        simp [fs]
    simp_rw [h_finset_sum]
    refine (Filter.Tendsto.liminf_eq ?_).symm
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨⌈(f a b).toReal⌉₊, fun n hn => (min_eq_left (h_le a b n hn)).symm⟩
  rw [hf_eq_tsum, withDensity_tsum _ fun n : ℕ => _]
  swap; · fun_prop
  refine isSFiniteKernel_sum (hκs := fun n => ?_)
  suffices IsFiniteKernel (withDensity κ (fs n)) by haveI := this; infer_instance
  refine isFiniteKernel_withDensity_of_bounded _ (ENNReal.coe_ne_top : ↑n + 1 ≠ ∞) fun a b => ?_
  -- After https://github.com/leanprover/lean4/pull/2734, we need to do beta reduction before `norm_cast`
  beta_reduce
  norm_cast
  calc
    fs n a b ≤ min (f a b) (n + 1) := tsub_le_self
    _ ≤ n + 1 := min_le_right _ _
    _ = ↑(n + 1) := by norm_cast

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is everywhere finite,
`withDensity κ f` is s-finite. -/
nonrec theorem IsSFiniteKernel.withDensity (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf_ne_top : ∀ a b, f a b ≠ ∞) : IsSFiniteKernel (withDensity κ f) := by
  have h_eq_sum : withDensity κ f = Kernel.sum fun i => withDensity (seq κ i) f := by
    rw [← withDensity_kernel_sum _ _]
    congr
    exact (kernel_sum_seq κ).symm
  rw [h_eq_sum]
  exact isSFiniteKernel_sum (hκs := fun n =>
    isSFiniteKernel_withDensity_of_isFiniteKernel (seq κ n) hf_ne_top)

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0`, `withDensity κ f` is s-finite. -/
instance (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → β → ℝ≥0) :
    IsSFiniteKernel (withDensity κ fun a b => f a b) :=
  IsSFiniteKernel.withDensity κ fun _ _ => ENNReal.coe_ne_top

nonrec lemma withDensity_mul [IsSFiniteKernel κ] {f : α → β → ℝ≥0} {g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    withDensity κ (fun a x ↦ f a x * g a x)
      = withDensity (withDensity κ fun a x ↦ f a x) g := by
  ext a : 1
  rw [Kernel.withDensity_apply]
  swap; · fun_prop
  change (Measure.withDensity (κ a) ((fun x ↦ (f a x : ℝ≥0∞)) * (fun x ↦ (g a x : ℝ≥0∞)))) =
      (withDensity (withDensity κ fun a x ↦ f a x) g) a
  rw [withDensity_mul]
  · rw [Kernel.withDensity_apply _ hg, Kernel.withDensity_apply]
    exact measurable_coe_nnreal_ennreal.comp hf
  · fun_prop
  · fun_prop

end ProbabilityTheory.Kernel
