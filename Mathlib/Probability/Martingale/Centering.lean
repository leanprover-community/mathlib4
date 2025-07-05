/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Martingale.Basic

/-!
# Centering lemma for stochastic processes

Any `ℕ`-indexed stochastic process which is adapted and integrable can be written as the sum of a
martingale and a predictable process. This result is also known as **Doob's decomposition theorem**.
From a process `f`, a filtration `ℱ` and a measure `μ`, we define two processes
`martingalePart f ℱ μ` and `predictablePart f ℱ μ`.

## Main definitions

* `MeasureTheory.predictablePart f ℱ μ`: a predictable process such that
  `f = predictablePart f ℱ μ + martingalePart f ℱ μ`
* `MeasureTheory.martingalePart f ℱ μ`: a martingale such that
  `f = predictablePart f ℱ μ + martingalePart f ℱ μ`

## Main statements

* `MeasureTheory.adapted_predictablePart`: `(fun n => predictablePart f ℱ μ (n+1))` is adapted.
  That is, `predictablePart` is predictable.
* `MeasureTheory.martingale_martingalePart`: `martingalePart f ℱ μ` is a martingale.

-/


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {f : ℕ → Ω → E} {ℱ : Filtration ℕ m0}

/-- Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and a predictable
process. This is the predictable process. See `martingalePart` for the martingale. -/
noncomputable def predictablePart {m0 : MeasurableSpace Ω} (f : ℕ → Ω → E) (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) : ℕ → Ω → E := fun n => ∑ i ∈ Finset.range n, μ[f (i + 1) - f i|ℱ i]

@[simp]
theorem predictablePart_zero : predictablePart f ℱ μ 0 = 0 := by
  simp_rw [predictablePart, Finset.range_zero, Finset.sum_empty]

theorem adapted_predictablePart : Adapted ℱ fun n => predictablePart f ℱ μ (n + 1) := fun _ =>
  Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_succ_iff.mp hin))

theorem adapted_predictablePart' : Adapted ℱ fun n => predictablePart f ℱ μ n := fun _ =>
  Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_le hin))

/-- Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and a predictable
process. This is the martingale. See `predictablePart` for the predictable process. -/
noncomputable def martingalePart {m0 : MeasurableSpace Ω} (f : ℕ → Ω → E) (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) : ℕ → Ω → E := fun n => f n - predictablePart f ℱ μ n

theorem martingalePart_add_predictablePart (ℱ : Filtration ℕ m0) (μ : Measure Ω) (f : ℕ → Ω → E) :
    martingalePart f ℱ μ + predictablePart f ℱ μ = f :=
  sub_add_cancel _ _

theorem martingalePart_eq_sum : martingalePart f ℱ μ = fun n =>
    f 0 + ∑ i ∈ Finset.range n, (f (i + 1) - f i - μ[f (i + 1) - f i|ℱ i]) := by
  unfold martingalePart predictablePart
  ext1 n
  rw [Finset.eq_sum_range_sub f n, ← add_sub, ← Finset.sum_sub_distrib]

theorem adapted_martingalePart (hf : Adapted ℱ f) : Adapted ℱ (martingalePart f ℱ μ) :=
  Adapted.sub hf adapted_predictablePart'

theorem integrable_martingalePart (hf_int : ∀ n, Integrable (f n) μ) (n : ℕ) :
    Integrable (martingalePart f ℱ μ n) μ := by
  rw [martingalePart_eq_sum]
  fun_prop

theorem martingale_martingalePart (hf : Adapted ℱ f) (hf_int : ∀ n, Integrable (f n) μ)
    [SigmaFiniteFiltration μ ℱ] : Martingale (martingalePart f ℱ μ) ℱ μ := by
  refine ⟨adapted_martingalePart hf, fun i j hij => ?_⟩
  -- ⊢ μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ] martingalePart f ℱ μ i
  have h_eq_sum : μ[martingalePart f ℱ μ j|ℱ i] =ᵐ[μ]
      f 0 + ∑ k ∈ Finset.range j, (μ[f (k + 1) - f k|ℱ i] - μ[μ[f (k + 1) - f k|ℱ k]|ℱ i]) := by
    rw [martingalePart_eq_sum]
    refine (condExp_add (hf_int 0) (by fun_prop) _).trans ?_
    refine (EventuallyEq.rfl.add (condExp_finset_sum (fun i _ => by fun_prop) _)).trans ?_
    refine EventuallyEq.add ?_ ?_
    · rw [condExp_of_stronglyMeasurable (ℱ.le _) _ (hf_int 0)]
      · exact (hf 0).mono (ℱ.mono (zero_le i))
    · exact eventuallyEq_sum fun k _ => condExp_sub (by fun_prop) integrable_condExp _
  refine h_eq_sum.trans ?_
  have h_ge : ∀ k, i ≤ k → μ[f (k + 1) - f k|ℱ i] - μ[μ[f (k + 1) - f k|ℱ k]|ℱ i] =ᵐ[μ] 0 := by
    intro k hk
    have : μ[μ[f (k + 1) - f k|ℱ k]|ℱ i] =ᵐ[μ] μ[f (k + 1) - f k|ℱ i] :=
      condExp_condExp_of_le (ℱ.mono hk) (ℱ.le k)
    filter_upwards [this] with x hx
    rw [Pi.sub_apply, Pi.zero_apply, hx, sub_self]
  have h_lt : ∀ k, k < i → μ[f (k + 1) - f k|ℱ i] - μ[μ[f (k + 1) - f k|ℱ k]|ℱ i] =ᵐ[μ]
      f (k + 1) - f k - μ[f (k + 1) - f k|ℱ k] := by
    refine fun k hk => EventuallyEq.sub ?_ ?_
    · rw [condExp_of_stronglyMeasurable]
      · exact ((hf (k + 1)).mono (ℱ.mono (Nat.succ_le_of_lt hk))).sub ((hf k).mono (ℱ.mono hk.le))
      · exact (hf_int _).sub (hf_int _)
    · rw [condExp_of_stronglyMeasurable]
      · exact stronglyMeasurable_condExp.mono (ℱ.mono hk.le)
      · exact integrable_condExp
  rw [martingalePart_eq_sum]
  refine EventuallyEq.add EventuallyEq.rfl ?_
  rw [← Finset.sum_range_add_sum_Ico _ hij, ←
    add_zero (∑ i ∈ Finset.range i, (f (i + 1) - f i - μ[f (i + 1) - f i|ℱ i]))]
  refine (eventuallyEq_sum fun k hk => h_lt k (Finset.mem_range.mp hk)).add ?_
  refine (eventuallyEq_sum fun k hk => h_ge k (Finset.mem_Ico.mp hk).1).trans ?_
  simp only [Finset.sum_const_zero]
  rfl

-- The following two lemmas demonstrate the essential uniqueness of the decomposition
theorem martingalePart_add_ae_eq [SigmaFiniteFiltration μ ℱ] {f g : ℕ → Ω → E}
    (hf : Martingale f ℱ μ) (hg : Adapted ℱ fun n => g (n + 1)) (hg0 : g 0 = 0)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) : martingalePart (f + g) ℱ μ n =ᵐ[μ] f n := by
  set h := f - martingalePart (f + g) ℱ μ with hhdef
  have hh : h = predictablePart (f + g) ℱ μ - g := by
    rw [hhdef, sub_eq_sub_iff_add_eq_add, add_comm (predictablePart (f + g) ℱ μ),
      martingalePart_add_predictablePart]
  have hhpred : Adapted ℱ fun n => h (n + 1) := by
    rw [hh]
    exact adapted_predictablePart.sub hg
  have hhmgle : Martingale h ℱ μ := hf.sub (martingale_martingalePart
    (hf.adapted.add <| Predictable.adapted hg <| hg0.symm ▸ stronglyMeasurable_zero) fun n =>
    (hf.integrable n).add <| hgint n)
  refine (eventuallyEq_iff_sub.2 ?_).symm
  filter_upwards [hhmgle.eq_zero_of_predictable hhpred n] with ω hω
  unfold h at hω
  rw [Pi.sub_apply] at hω
  rw [hω, Pi.sub_apply, martingalePart]
  simp [hg0]

theorem predictablePart_add_ae_eq [SigmaFiniteFiltration μ ℱ] {f g : ℕ → Ω → E}
    (hf : Martingale f ℱ μ) (hg : Adapted ℱ fun n => g (n + 1)) (hg0 : g 0 = 0)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) : predictablePart (f + g) ℱ μ n =ᵐ[μ] g n := by
  filter_upwards [martingalePart_add_ae_eq hf hg hg0 hgint n] with ω hω
  rw [← add_right_inj (f n ω)]
  conv_rhs => rw [← Pi.add_apply, ← Pi.add_apply, ← martingalePart_add_predictablePart ℱ μ (f + g)]
  rw [Pi.add_apply, Pi.add_apply, hω]

section Difference

theorem predictablePart_bdd_difference {R : ℝ≥0} {f : ℕ → Ω → ℝ} (ℱ : Filtration ℕ m0)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, ∀ i, |predictablePart f ℱ μ (i + 1) ω - predictablePart f ℱ μ i ω| ≤ R := by
  simp_rw [predictablePart, Finset.sum_apply, Finset.sum_range_succ_sub_sum]
  exact ae_all_iff.2 fun i => ae_bdd_condExp_of_ae_bdd <| ae_all_iff.1 hbdd i

theorem martingalePart_bdd_difference {R : ℝ≥0} {f : ℕ → Ω → ℝ} (ℱ : Filtration ℕ m0)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, ∀ i, |martingalePart f ℱ μ (i + 1) ω - martingalePart f ℱ μ i ω| ≤ ↑(2 * R) := by
  filter_upwards [hbdd, predictablePart_bdd_difference ℱ hbdd] with ω hω₁ hω₂ i
  simp only [two_mul, martingalePart, Pi.sub_apply]
  have : |f (i + 1) ω - predictablePart f ℱ μ (i + 1) ω - (f i ω - predictablePart f ℱ μ i ω)| =
      |f (i + 1) ω - f i ω - (predictablePart f ℱ μ (i + 1) ω - predictablePart f ℱ μ i ω)| := by
    ring_nf -- `ring` suggests `ring_nf` despite proving the goal
  rw [this]
  exact (abs_sub _ _).trans (add_le_add (hω₁ i) (hω₂ i))

end Difference

end MeasureTheory
