/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# Centering lemma for stochastic processes

Any `ℕ`-indexed stochastic process which is strongly adapted and integrable can be written as the
sum of a martingale and a predictable process. This result is also known as
**Doob's decomposition theorem**. From a process `f`, a filtration `ℱ` and a measure `μ`, we define
two processes `martingalePart f ℱ μ` and `predictablePart f ℱ μ`.

## Main definitions

* `MeasureTheory.predictablePart f ℱ μ`: a predictable process such that
  `f = predictablePart f ℱ μ + martingalePart f ℱ μ`
* `MeasureTheory.martingalePart f ℱ μ`: a martingale such that
  `f = predictablePart f ℱ μ + martingalePart f ℱ μ`

## Main statements

* `MeasureTheory.stronglyAdapted_predictablePart`: `(fun n => predictablePart f ℱ μ (n+1))`
  is strongly adapted.
  That is, `predictablePart` is predictable.
* `MeasureTheory.martingale_martingalePart`: `martingalePart f ℱ μ` is a martingale.

-/

@[expose] public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {f g : ℕ → Ω → E} {ℱ : Filtration ℕ m0}

/-- Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and a predictable
process. This is the predictable process. See `martingalePart` for the martingale. -/
noncomputable def predictablePart {m0 : MeasurableSpace Ω} (f : ℕ → Ω → E) (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) : ℕ → Ω → E := fun n => ∑ i ∈ Finset.range n, μ[f (i + 1) - f i | ℱ i]

@[simp]
theorem predictablePart_zero : predictablePart f ℱ μ 0 = 0 := by
  simp_rw [predictablePart, Finset.range_zero, Finset.sum_empty]

lemma predictablePart_add_one (n : ℕ) :
    predictablePart f ℱ μ (n + 1) =
      predictablePart f ℱ μ n + μ[f (n + 1) - f n | ℱ n] := by
  simp [predictablePart, Finset.sum_range_add]

lemma predictablePart_smul (c : ℝ) (n : ℕ) :
    predictablePart (c • f) ℱ μ n =ᵐ[μ] c • predictablePart f ℱ μ n := by
  simp only [predictablePart, Finset.smul_sum]
  refine eventuallyEq_sum fun i hi => ?_
  simp [← smul_sub, condExp_smul]

lemma predictablePart_add (hfint : ∀ n, Integrable (f n) μ)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    predictablePart (f + g) ℱ μ n =ᵐ[μ] predictablePart f ℱ μ n + predictablePart g ℱ μ n := by
  simp only [predictablePart, ← Finset.sum_add_distrib]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[(f (i + 1) - f i) + (g (i + 1) - g i) | ℱ i] := by simp; abel_nf; rfl
  _ =ᵐ[μ] _ := by apply condExp_add ((hfint (i + 1)).sub (hfint i)) ((hgint (i + 1)).sub (hgint i))

lemma Martingale.predictablePart_eq_zero (hf : Martingale f ℱ μ) (n : ℕ) :
    predictablePart f ℱ μ n =ᵐ[μ] 0 := by
  rw [predictablePart, ← Finset.sum_const_zero (s := Finset.range n)]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[f (i + 1) | ℱ i] - μ[f i | ℱ i] := by
    simp [condExp_sub (hf.integrable (i + 1)) (hf.integrable i) (ℱ i)]
  _ =ᵐ[μ] f i - f i := (hf.condExp_ae_eq (Nat.le_succ i)).sub (hf.condExp_ae_eq le_rfl)
  _ =ᵐ[μ] 0 := by simp

lemma Submartingale.monotone_predictablePart [PartialOrder E] [IsOrderedAddMonoid E]
    (hf : Submartingale f ℱ μ) :
    ∀ᵐ ω ∂μ, Monotone (predictablePart f ℱ μ · ω) := by
  have := ae_all_iff.2 <| fun n : ℕ ↦ hf.condExp_sub_nonneg n.le_succ
  filter_upwards [this] with ω h
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, ← ge_iff_le] at h
  refine monotone_nat_of_le_succ fun n ↦ (?_ : _ ≥ _)
  grw [predictablePart_add_one, Pi.add_apply, h n, add_zero]

lemma Submartingale.predictablePart_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    (hf : Submartingale f ℱ μ) :
    ∀ᵐ ω ∂μ, ∀ n, 0 ≤ predictablePart f ℱ μ n ω := by
  filter_upwards [hf.monotone_predictablePart] with ω hω n
  simpa [predictablePart_zero] using hω (Nat.zero_le n)

lemma IsPredictable.predictablePart_eq [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] [SigmaFiniteFiltration μ ℱ] (hf : IsPredictable ℱ f)
    (hfint : ∀ n, Integrable (f n) μ) (n : ℕ) :
    predictablePart f ℱ μ n =ᵐ[μ] f n - f 0 := by
  simp only [predictablePart, ← Finset.sum_range_sub]
  exact eventuallyEq_sum fun i hi => (condExp_of_stronglyMeasurable (ℱ.le i)
    ((hf.measurable_add_one i).stronglyMeasurable.sub (hf.adapted i))
    ((hfint (i + 1)).sub (hfint i))).eventuallyEq

theorem stronglyAdapted_predictablePart :
    StronglyAdapted ℱ fun n => predictablePart f ℱ μ (n + 1) :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_succ_iff.mp hin))

lemma isPredictable_predictablePart [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] :
    IsPredictable ℱ (predictablePart f ℱ μ) :=
  isPredictable_of_measurable_add_one (by simp [measurable_const'])
    fun n ↦ (stronglyAdapted_predictablePart n).measurable

theorem stronglyAdapted_predictablePart' : StronglyAdapted ℱ fun n => predictablePart f ℱ μ n :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_le hin))

/-- Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and a predictable
process. This is the martingale. See `predictablePart` for the predictable process. -/
noncomputable def martingalePart {m0 : MeasurableSpace Ω} (f : ℕ → Ω → E) (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) : ℕ → Ω → E := fun n => f n - predictablePart f ℱ μ n

@[simp]
lemma martingalePart_zero : martingalePart f ℱ μ 0 = f 0 := by
  simp [martingalePart]

lemma martingalePart_smul (c : ℝ) (n : ℕ) :
    martingalePart (c • f) ℱ μ n =ᵐ[μ] c • martingalePart f ℱ μ n := by
  filter_upwards [predictablePart_smul (f := f) c n] with ω hω
  simpa [martingalePart, smul_sub]

lemma martingalePart_add (hfint : ∀ n, Integrable (f n) μ)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    martingalePart (f + g) ℱ μ n =ᵐ[μ] martingalePart f ℱ μ n + martingalePart g ℱ μ n := by
  filter_upwards [predictablePart_add (ℱ := ℱ) hfint hgint n] with ω hω
  simp_all [martingalePart]
  abel

lemma Martingale.martingalePart_eq (hf : Martingale f ℱ μ) (n : ℕ) :
    martingalePart f ℱ μ n =ᵐ[μ] f n := by
  filter_upwards [hf.predictablePart_eq_zero n] with ω hω
  simp [martingalePart, hω]

lemma IsPredictable.martingalePart_eq [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] [SigmaFiniteFiltration μ ℱ] (hf : IsPredictable ℱ f)
    (hfint : ∀ n, Integrable (f n) μ) (n : ℕ) :
    martingalePart f ℱ μ n =ᵐ[μ] f 0 := by
  filter_upwards [hf.predictablePart_eq (μ := μ) hfint n] with ω hω
  simp [martingalePart, hω, sub_eq_add_neg]

theorem martingalePart_add_predictablePart (ℱ : Filtration ℕ m0) (μ : Measure Ω) (f : ℕ → Ω → E) :
    martingalePart f ℱ μ + predictablePart f ℱ μ = f :=
  sub_add_cancel _ _

theorem martingalePart_eq_sum : martingalePart f ℱ μ = fun n =>
    f 0 + ∑ i ∈ Finset.range n, (f (i + 1) - f i - μ[f (i + 1) - f i | ℱ i]) := by
  unfold martingalePart predictablePart
  ext1 n
  rw [Finset.eq_sum_range_sub f n, ← add_sub, ← Finset.sum_sub_distrib]

theorem stronglyAdapted_martingalePart (hf : StronglyAdapted ℱ f) :
  StronglyAdapted ℱ (martingalePart f ℱ μ) := hf.sub stronglyAdapted_predictablePart'

theorem integrable_martingalePart (hf_int : ∀ n, Integrable (f n) μ) (n : ℕ) :
    Integrable (martingalePart f ℱ μ n) μ := by
  rw [martingalePart_eq_sum]
  fun_prop

theorem martingale_martingalePart (hf : StronglyAdapted ℱ f) (hf_int : ∀ n, Integrable (f n) μ)
    [SigmaFiniteFiltration μ ℱ] : Martingale (martingalePart f ℱ μ) ℱ μ := by
  refine ⟨stronglyAdapted_martingalePart hf, fun i j hij => ?_⟩
  -- ⊢ μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ] martingalePart f ℱ μ i
  have h_eq_sum : μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ]
      f 0 + ∑ k ∈ Finset.range j,
        (μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i]) := by
    rw [martingalePart_eq_sum]
    refine (condExp_add (hf_int 0) (by fun_prop) _).trans ?_
    refine (EventuallyEq.rfl.add (condExp_finsetSum (fun i _ => by fun_prop) _)).trans ?_
    refine EventuallyEq.add ?_ ?_
    · rw [condExp_of_stronglyMeasurable (ℱ.le _) _ (hf_int 0)]
      · exact (hf 0).mono (ℱ.mono (zero_le i))
    · exact eventuallyEq_sum fun k _ => condExp_sub (by fun_prop) integrable_condExp _
  refine h_eq_sum.trans ?_
  have h_ge : ∀ k, i ≤ k →
      μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ] 0 := by
    intro k hk
    have : μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ] μ[f (k + 1) - f k | ℱ i] :=
      condExp_condExp_of_le (ℱ.mono hk) (ℱ.le k)
    filter_upwards [this] with x hx
    rw [Pi.sub_apply, Pi.zero_apply, hx, sub_self]
  have h_lt : ∀ k, k < i → μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ]
      f (k + 1) - f k - μ[f (k + 1) - f k | ℱ k] := by
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
    add_zero (∑ i ∈ Finset.range i, (f (i + 1) - f i - μ[f (i + 1) - f i | ℱ i]))]
  refine (eventuallyEq_sum fun k hk => h_lt k (Finset.mem_range.mp hk)).add ?_
  refine (eventuallyEq_sum fun k hk => h_ge k (Finset.mem_Ico.mp hk).1).trans ?_
  simp only [Finset.sum_const_zero]
  rfl

-- The following two lemmas demonstrate the essential uniqueness of the decomposition
theorem martingalePart_add_ae_eq [SigmaFiniteFiltration μ ℱ] {f g : ℕ → Ω → E}
    (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ fun n => g (n + 1)) (hg0 : g 0 = 0)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) : martingalePart (f + g) ℱ μ n =ᵐ[μ] f n := by
  set h := f - martingalePart (f + g) ℱ μ with hhdef
  have hh : h = predictablePart (f + g) ℱ μ - g := by
    rw [hhdef, sub_eq_sub_iff_add_eq_add, add_comm (predictablePart (f + g) ℱ μ),
      martingalePart_add_predictablePart]
  have hhpred : StronglyAdapted ℱ fun n => h (n + 1) := by
    rw [hh]
    exact stronglyAdapted_predictablePart.sub hg
  have hhmgle : Martingale h ℱ μ := hf.sub (martingale_martingalePart
    (hf.stronglyAdapted.add <| Predictable.stronglyAdapted hg <| hg0.symm ▸ stronglyMeasurable_zero)
    fun n => (hf.integrable n).add <| hgint n)
  refine (eventuallyEq_iff_sub.2 ?_).symm
  filter_upwards [hhmgle.eq_zero_of_predictable hhpred n] with ω hω
  unfold h at hω
  rw [Pi.sub_apply] at hω
  rw [hω, Pi.sub_apply, martingalePart]
  simp [hg0]

theorem predictablePart_add_ae_eq [SigmaFiniteFiltration μ ℱ] {f g : ℕ → Ω → E}
    (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ fun n => g (n + 1)) (hg0 : g 0 = 0)
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
