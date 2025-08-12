/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace  intervalIntegral
  Metric Filter Function Complex MatrixGroups Finset

open scoped Interval Real Topology BigOperators Nat

noncomputable section


/-- This is an auxilary summand used to define the Eisenstein serires `G2`. -/
def e2Summand (m : ℤ) (z : ℍ) : ℂ := ∑' (n : ℤ), eisSummand 2 ![m, n] z

lemma e2Summand_summable (m : ℤ) (z : ℍ) : Summable (fun n => eisSummand 2 ![m, n] z) := by
  apply (linear_right_summable z m (k := 2) (by omega)).congr
  simp [eisSummand]

/-- The Eisenstein series of weight `2` and level `1` defined as the limit as `N` tends to
infinity of the partial sum of `m` in `[N,N)` of `e2Summand m`. This sum over symmetric
intervals is handy in showing it is Cauchy. -/
def G2 : ℍ → ℂ := fun z => limUnder (atTop) (fun N : ℕ => ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z)

def E2 : ℍ → ℂ := (1 / (2 * riemannZeta 2)) •  G2

def D2 (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * Complex.I * γ 1 0) / (denom γ z)


lemma t8 (z : ℍ) :
  (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2))) =
  (fun _ : ℕ => 2*((riemannZeta 2))) +
  (fun N : ℕ => ∑ m ∈ Finset.range (N), 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n)) := by
  sorry

lemma t9 (z : ℍ) : ∑' m : ℕ,
  ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n))  =  -
    8 * π ^ 2 * ∑' (n : ℕ+), (sigma 1 n) * cexp (2 * π * Complex.I * n * z) := by sorry

theorem G2_c_tendsto (z : ℍ) :
  Tendsto
    (fun N ↦
      ∑ x ∈ Finset.range N,
        2 * (2 * ↑π * Complex.I) ^ 2 * ∑' (n : ℕ+), ↑↑n * cexp (2 * ↑π * Complex.I * (↑x + 1) * ↑z * ↑↑n))
    atTop (𝓝 (-8 * ↑π ^ 2 * ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) := by
    rw [← t9]
    have hf : Summable fun m : ℕ => ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
        ∑' n : ℕ+, n ^ ((2 - 1)) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n)) := by
        conv =>
          enter [1]
          ext m
          rw [show (m : ℂ) +  1 = (((m + 1) : ℕ) : ℂ) by simp]
        have := nat_pos_tsum2' (f := fun m : ℕ => ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
        ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m) * z * n)) )
        rw  [← this]
        have := (a4 2 z).prod_symm.prod
        apply Summable.mul_left
        apply this.congr
        intro b
        congr
    have := hf.hasSum
    have V := this.comp tendsto_finset_range
    simp at *
    apply V

lemma G2_cauchy (z : ℍ) : CauchySeq (fun N : ℕ => ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z) := by

  sorry



/- lemma Asymptotics.IsBigO.map {α β ι γ : Type*} [Norm α] [Norm β] {f : ι → α} {g : ι → β}
  {p : Filter ι} (hf : f =O[p] g) (c : γ → ι) :
    (fun (n : γ) => f (c n)) =O[p.comap c] fun n => g (c n) := by
  rw [isBigO_iff] at *
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  simp only [eventually_comap] at *
  filter_upwards [hC] with n hn
  exact fun a ha ↦ Eq.mpr (id (congrArg (fun _a ↦ ‖f _a‖ ≤ C * ‖g _a‖) ha)) hn

lemma Asymptotics.IsBigO.nat_of_int {α β : Type*} [Norm α] [SeminormedAddCommGroup β] {f : ℤ → α}
    {g : ℤ → β} (hf : f =O[cofinite] g) : (fun (n : ℕ) => f n) =O[cofinite] fun n => g n := by
  have := Asymptotics.IsBigO.map hf Nat.cast
  simp only [Int.cofinite_eq, isBigO_sup, comap_sup, Asymptotics.isBigO_sup] at *
  rw [Nat.cofinite_eq_atTop]
  simpa using this.2 -/
