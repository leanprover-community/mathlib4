/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module probability.martingale.centering
! leanprover-community/mathlib commit bea6c853b6edbd15e9d0941825abd04d77933ed0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Probability.Martingale.Basic

/-!
# Centering lemma for stochastic processes

Any `ℕ`-indexed stochastic process which is adapted and integrable can be written as the sum of a
martingale and a predictable process. This result is also known as **Doob's decomposition theorem**.
From a process `f`, a filtration `ℱ` and a measure `μ`, we define two processes
`martingale_part f ℱ μ` and `predictable_part f ℱ μ`.

## Main definitions

* `measure_theory.predictable_part f ℱ μ`: a predictable process such that
  `f = predictable_part f ℱ μ + martingale_part f ℱ μ`
* `measure_theory.martingale_part f ℱ μ`: a martingale such that
  `f = predictable_part f ℱ μ + martingale_part f ℱ μ`

## Main statements

* `measure_theory.adapted_predictable_part`: `(λ n, predictable_part f ℱ μ (n+1))` is adapted. That
  is, `predictable_part` is predictable.
* `measure_theory.martingale_martingale_part`: `martingale_part f ℱ μ` is a martingale.

-/


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory BigOperators

namespace MeasureTheory

variable {Ω E : Type _} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {f : ℕ → Ω → E} {ℱ : Filtration ℕ m0} {n : ℕ}

/-- Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and a predictable
process. This is the predictable process. See `martingale_part` for the martingale. -/
noncomputable def predictablePart {m0 : MeasurableSpace Ω} (f : ℕ → Ω → E) (ℱ : Filtration ℕ m0)
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : ℕ → Ω → E := fun n =>
  ∑ i in Finset.range n, μ[f (i + 1) - f i|ℱ i]
#align measure_theory.predictable_part MeasureTheory.predictablePart

@[simp]
theorem predictablePart_zero : predictablePart f ℱ μ 0 = 0 := by
  simp_rw [predictable_part, Finset.range_zero, Finset.sum_empty]
#align measure_theory.predictable_part_zero MeasureTheory.predictablePart_zero

theorem adapted_predictablePart : Adapted ℱ fun n => predictablePart f ℱ μ (n + 1) := fun n =>
  Finset.stronglyMeasurable_sum' _ fun i hin =>
    stronglyMeasurable_condexp.mono (ℱ.mono (Finset.mem_range_succ_iff.mp hin))
#align measure_theory.adapted_predictable_part MeasureTheory.adapted_predictablePart

theorem adapted_predictable_part' : Adapted ℱ fun n => predictablePart f ℱ μ n := fun n =>
  Finset.stronglyMeasurable_sum' _ fun i hin =>
    stronglyMeasurable_condexp.mono (ℱ.mono (Finset.mem_range_le hin))
#align measure_theory.adapted_predictable_part' MeasureTheory.adapted_predictable_part'

/-- Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and a predictable
process. This is the martingale. See `predictable_part` for the predictable process. -/
noncomputable def martingalePart {m0 : MeasurableSpace Ω} (f : ℕ → Ω → E) (ℱ : Filtration ℕ m0)
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : ℕ → Ω → E := fun n =>
  f n - predictablePart f ℱ μ n
#align measure_theory.martingale_part MeasureTheory.martingalePart

theorem martingalePart_add_predictablePart (ℱ : Filtration ℕ m0) (μ : Measure Ω) (f : ℕ → Ω → E) :
    martingalePart f ℱ μ + predictablePart f ℱ μ = f :=
  sub_add_cancel _ _
#align measure_theory.martingale_part_add_predictable_part MeasureTheory.martingalePart_add_predictablePart

theorem martingalePart_eq_sum :
    martingalePart f ℱ μ = fun n =>
      f 0 + ∑ i in Finset.range n, (f (i + 1) - f i - μ[f (i + 1) - f i|ℱ i]) :=
  by
  rw [martingale_part, predictable_part]
  ext1 n
  rw [Finset.eq_sum_range_sub f n, ← add_sub, ← Finset.sum_sub_distrib]
#align measure_theory.martingale_part_eq_sum MeasureTheory.martingalePart_eq_sum

theorem adapted_martingalePart (hf : Adapted ℱ f) : Adapted ℱ (martingalePart f ℱ μ) :=
  Adapted.sub hf adapted_predictable_part'
#align measure_theory.adapted_martingale_part MeasureTheory.adapted_martingalePart

theorem integrable_martingalePart (hf_int : ∀ n, Integrable (f n) μ) (n : ℕ) :
    Integrable (martingalePart f ℱ μ n) μ :=
  by
  rw [martingale_part_eq_sum]
  exact
    (hf_int 0).add
      (integrable_finset_sum' _ fun i hi => ((hf_int _).sub (hf_int _)).sub integrable_condexp)
#align measure_theory.integrable_martingale_part MeasureTheory.integrable_martingalePart

theorem martingale_martingalePart (hf : Adapted ℱ f) (hf_int : ∀ n, Integrable (f n) μ)
    [SigmaFiniteFiltration μ ℱ] : Martingale (martingalePart f ℱ μ) ℱ μ :=
  by
  refine' ⟨adapted_martingale_part hf, fun i j hij => _⟩
  -- ⊢ μ[martingale_part f ℱ μ j | ℱ i] =ᵐ[μ] martingale_part f ℱ μ i
  have h_eq_sum :
    μ[martingale_part f ℱ μ j|ℱ i] =ᵐ[μ]
      f 0 + ∑ k in Finset.range j, (μ[f (k + 1) - f k|ℱ i] - μ[μ[f (k + 1) - f k|ℱ k]|ℱ i]) :=
    by
    rw [martingale_part_eq_sum]
    refine' (condexp_add (hf_int 0) _).trans _
    · exact integrable_finset_sum' _ fun i hij => ((hf_int _).sub (hf_int _)).sub integrable_condexp
    refine' (eventually_eq.add eventually_eq.rfl (condexp_finset_sum fun i hij => _)).trans _
    · exact ((hf_int _).sub (hf_int _)).sub integrable_condexp
    refine' eventually_eq.add _ _
    · rw [condexp_of_strongly_measurable (ℱ.le _) _ (hf_int 0)]
      · infer_instance
      · exact (hf 0).mono (ℱ.mono (zero_le i))
    · exact eventuallyEq_sum fun k hkj => condexp_sub ((hf_int _).sub (hf_int _)) integrable_condexp
  refine' h_eq_sum.trans _
  have h_ge : ∀ k, i ≤ k → μ[f (k + 1) - f k|ℱ i] - μ[μ[f (k + 1) - f k|ℱ k]|ℱ i] =ᵐ[μ] 0 :=
    by
    intro k hk
    have : μ[μ[f (k + 1) - f k|ℱ k]|ℱ i] =ᵐ[μ] μ[f (k + 1) - f k|ℱ i] :=
      condexp_condexp_of_le (ℱ.mono hk) (ℱ.le k)
    filter_upwards [this] with x hx
    rw [Pi.sub_apply, Pi.zero_apply, hx, sub_self]
  have h_lt :
    ∀ k,
      k < i →
        μ[f (k + 1) - f k|ℱ i] - μ[μ[f (k + 1) - f k|ℱ k]|ℱ i] =ᵐ[μ]
          f (k + 1) - f k - μ[f (k + 1) - f k|ℱ k] :=
    by
    refine' fun k hk => eventually_eq.sub _ _
    · rw [condexp_of_strongly_measurable]
      · exact ((hf (k + 1)).mono (ℱ.mono (Nat.succ_le_of_lt hk))).sub ((hf k).mono (ℱ.mono hk.le))
      · exact (hf_int _).sub (hf_int _)
    · rw [condexp_of_strongly_measurable]
      · exact strongly_measurable_condexp.mono (ℱ.mono hk.le)
      · exact integrable_condexp
  rw [martingale_part_eq_sum]
  refine' eventually_eq.add eventually_eq.rfl _
  rw [← Finset.sum_range_add_sum_Ico _ hij, ←
    add_zero (∑ i in Finset.range i, (f (i + 1) - f i - μ[f (i + 1) - f i|ℱ i]))]
  refine' (eventuallyEq_sum fun k hk => h_lt k (finset.mem_range.mp hk)).add _
  refine' (eventuallyEq_sum fun k hk => h_ge k (finset.mem_Ico.mp hk).1).trans _
  simp only [Finset.sum_const_zero, Pi.zero_apply]
  rfl
#align measure_theory.martingale_martingale_part MeasureTheory.martingale_martingalePart

-- The following two lemmas demonstrate the essential uniqueness of the decomposition
theorem martingalePart_add_ae_eq [SigmaFiniteFiltration μ ℱ] {f g : ℕ → Ω → E}
    (hf : Martingale f ℱ μ) (hg : Adapted ℱ fun n => g (n + 1)) (hg0 : g 0 = 0)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) : martingalePart (f + g) ℱ μ n =ᵐ[μ] f n :=
  by
  set h := f - martingale_part (f + g) ℱ μ with hhdef
  have hh : h = predictable_part (f + g) ℱ μ - g := by
    rw [hhdef, sub_eq_sub_iff_add_eq_add, add_comm (predictable_part (f + g) ℱ μ),
      martingale_part_add_predictable_part]
  have hhpred : adapted ℱ fun n => h (n + 1) :=
    by
    rw [hh]
    exact adapted_predictable_part.sub hg
  have hhmgle : martingale h ℱ μ :=
    hf.sub
      (martingale_martingale_part
        (hf.adapted.add <| predictable.adapted hg <| hg0.symm ▸ strongly_measurable_zero) fun n =>
        (hf.integrable n).add <| hgint n)
  refine' (eventually_eq_iff_sub.2 _).symm
  filter_upwards [hhmgle.eq_zero_of_predictable hhpred n] with ω hω
  rw [hhdef, Pi.sub_apply] at hω 
  rw [hω, Pi.sub_apply, martingale_part]
  simp [hg0]
#align measure_theory.martingale_part_add_ae_eq MeasureTheory.martingalePart_add_ae_eq

theorem predictablePart_add_ae_eq [SigmaFiniteFiltration μ ℱ] {f g : ℕ → Ω → E}
    (hf : Martingale f ℱ μ) (hg : Adapted ℱ fun n => g (n + 1)) (hg0 : g 0 = 0)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) : predictablePart (f + g) ℱ μ n =ᵐ[μ] g n :=
  by
  filter_upwards [martingale_part_add_ae_eq hf hg hg0 hgint n] with ω hω
  rw [← add_right_inj (f n ω)]
  conv_rhs =>
    rw [← Pi.add_apply, ← Pi.add_apply, ← martingale_part_add_predictable_part ℱ μ (f + g)]
  rw [Pi.add_apply, Pi.add_apply, hω]
#align measure_theory.predictable_part_add_ae_eq MeasureTheory.predictablePart_add_ae_eq

section Difference

theorem predictablePart_bdd_difference {R : ℝ≥0} {f : ℕ → Ω → ℝ} (ℱ : Filtration ℕ m0)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, ∀ i, |predictablePart f ℱ μ (i + 1) ω - predictablePart f ℱ μ i ω| ≤ R :=
  by
  simp_rw [predictable_part, Finset.sum_apply, Finset.sum_range_succ_sub_sum]
  exact ae_all_iff.2 fun i => ae_bdd_condexp_of_ae_bdd <| ae_all_iff.1 hbdd i
#align measure_theory.predictable_part_bdd_difference MeasureTheory.predictablePart_bdd_difference

theorem martingalePart_bdd_difference {R : ℝ≥0} {f : ℕ → Ω → ℝ} (ℱ : Filtration ℕ m0)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, ∀ i, |martingalePart f ℱ μ (i + 1) ω - martingalePart f ℱ μ i ω| ≤ ↑(2 * R) :=
  by
  filter_upwards [hbdd, predictable_part_bdd_difference ℱ hbdd] with ω hω₁ hω₂ i
  simp only [two_mul, martingale_part, Pi.sub_apply]
  have :
    |f (i + 1) ω - predictable_part f ℱ μ (i + 1) ω - (f i ω - predictable_part f ℱ μ i ω)| =
      |f (i + 1) ω - f i ω - (predictable_part f ℱ μ (i + 1) ω - predictable_part f ℱ μ i ω)| :=
    by ring_nf
  -- `ring` suggests `ring_nf` despite proving the goal
  rw [this]
  exact (abs_sub _ _).trans (add_le_add (hω₁ i) (hω₂ i))
#align measure_theory.martingale_part_bdd_difference MeasureTheory.martingalePart_bdd_difference

end Difference

end MeasureTheory

