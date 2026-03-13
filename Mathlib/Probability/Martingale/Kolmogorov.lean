/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Probability.BorelCantelli

/-!
### Results

* `kolmogorov_ineq_wiki_version_of_iIndepFun`:

### References

* https://en.wikipedia.org/wiki/Kolmogorov%27s_inequality
-/

@[expose] public section


open MeasureTheory ProbabilityTheory Finset

section

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem kolmogorov_ineq_wiki_version_of_iIndepFun {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, StronglyMeasurable (X i)) (hXind : iIndepFun X μ)
    (hXmean : ∀ i, μ[X (i + 1)] = 0) (hXL2 : ∀ i, MemLp (X i) 2 μ) (n : ℕ) (ε : NNReal) :
    ε ^ 2 * μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one
      (fun k => |∑ j ∈ range k, X (j + 1) ω|)}
    ≤ ENNReal.ofReal (∑ k ∈ range n, ∫ ω, (X (k + 1) ω) ^ 2 ∂μ) := by
  let ℱ : Filtration ℕ m0 := Filtration.natural X hXm
  let S : ℕ → Ω → ℝ := fun m => ∑ k ∈ range m, X (k + 1)
  have hXadp : StronglyAdapted ℱ X := id (Filtration.stronglyAdapted_natural hXm)
  have hSadp : StronglyAdapted ℱ S := fun m => (Finset.stronglyMeasurable_sum (range m) fun k hk =>
    hXadp.stronglyMeasurable_le (Nat.succ_le_of_lt (mem_range.mp hk)))
  have hSL2 : ∀ m, MemLp (S m) 2 μ := fun m =>
    id (memLp_finset_sum' (range m) fun k hk => hXL2 (k + 1))
  have hSint : ∀ m, Integrable (S m) μ := fun m => (hSL2 m).integrable (by norm_num)
  have hSmart : Martingale S ℱ μ := by
    refine martingale_of_condExp_sub_eq_zero_nat hSadp hSint fun i => ?_
    calc
      _ =ᵐ[μ] μ[X (i + 1) | ℱ i] := condExp_congr_ae <| by simp [S, sum_range_succ_sub_sum]
      _ =ᵐ[μ] fun _ => μ[X (i + 1)] := id
        (iIndepFun.condExp_natural_ae_eq_of_lt hXm hXind (i.lt_succ_self))
      _ =ᵐ[μ] _ := by
        filter_upwards [] with ω
        exact id (hXmean i)
  calc
    _ ≤ ENNReal.ofReal (Var[S n; μ]) := by
      have hSmean : μ[S n] = 0 := by
        rw [show S n = ∑ k ∈ range n, X (k + 1) by rfl]
        simp only [Finset.sum_apply]
        rw [integral_finset_sum _ (fun k hk => (hXL2 (k + 1)).integrable (by norm_num))]
        exact sum_eq_zero fun k hk => hXmean k
      simpa [S] using kolmogorov_ineq_wiki_version hSmart hSL2 n ε hSmean
    _ = _ := by
      have hVarSum : Var[S n; μ] = ∑ k ∈ range n, Var[X (k + 1); μ] := id
        (IndepFun.variance_sum (fun i hi => hXL2 (i + 1)) fun ⦃i⦄ hi ⦃j⦄ hj hij =>
          iIndepFun.indepFun hXind (Function.Injective.ne Nat.succ_injective hij))
      have hVarSq : (∑ k ∈ range n, Var[X (k + 1); μ]) = ∑ k ∈ range n, ∫ ω, (X (k + 1) ω) ^ 2 ∂μ :=
        sum_congr rfl fun k hk =>
          variance_of_integral_eq_zero (MemLp.aemeasurable (hXL2 (k + 1))) (hXmean k)
      rw [hVarSum, hVarSq]

end
