import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Riemann zeta function is meromorphic

We prove that the Riemann zeta function `riemannZeta : ℂ → ℂ` is meromorphic at
every point of the complex plane, including its pole at `s = 1`.

* `meromorphicAt_riemannZeta_of_ne_one`: analytic away from `s = 1`, via
  `analyticOn_riemannZeta`;
* `meromorphicAt_riemannZeta_one`: meromorphic at the pole, via the decomposition
  `ζ(s) = (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) /
     (2 * π ^ (-s / 2) * Γ (s / 2 + 1))`
  (see `riemannZeta_eq_mul_completedRiemannZeta₀`);
* `meromorphicAt_riemannZeta`: the global statement.
-/

noncomputable section

open Complex

open scoped Topology

open Set

/-- The Riemann zeta function is meromorphic at every point different from `1`. -/
lemma meromorphicAt_riemannZeta_of_ne_one {x : ℂ} (hx : x ≠ 1) :
    MeromorphicAt riemannZeta x := by
  exact analyticOn_riemannZeta.meromorphicOn x hx

/-- The Riemann zeta function is meromorphic at `1` (its unique pole). -/
lemma meromorphicAt_riemannZeta_one : MeromorphicAt riemannZeta 1 := by
  have hM : MeromorphicAt (fun s : ℂ => s * completedRiemannZeta₀ s - 1 - s / (1 - s)) 1 := by
    have h1 : MeromorphicAt (fun s : ℂ => s * completedRiemannZeta₀ s) 1 := by
      have hCR : Differentiable ℂ completedRiemannZeta₀ := by
        change Differentiable ℂ (HurwitzZeta.completedHurwitzZetaEven₀ (0 : UnitAddCircle))
        exact HurwitzZeta.differentiable_completedHurwitzZetaEven₀ (0 : UnitAddCircle)
      have hCRan : AnalyticAt ℂ completedRiemannZeta₀ 1 :=
        (hCR.differentiableOn.analyticOnNhd isOpen_univ) 1 (by simp)
      exact (analyticAt_id.meromorphicAt).mul hCRan.meromorphicAt
    have h2 : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) 1 := MeromorphicAt.const (1 : ℂ) 1
    have h3 : MeromorphicAt (fun s : ℂ => s / (1 - s)) 1 := by
      have hA : AnalyticAt ℂ (fun s : ℂ => (1 : ℂ) - s) 1 := analyticAt_const.sub analyticAt_id
      have hInv : MeromorphicAt (fun s : ℂ => ((1 : ℂ) - s)⁻¹) 1 :=
        MeromorphicAt.inv hA.meromorphicAt
      exact (analyticAt_id.meromorphicAt).mul hInv
    exact (h1.sub h2).sub h3
  have hD : MeromorphicAt
      (fun s : ℂ => (2 : ℂ) * (↑Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2 + 1)) 1 := by
    have hc2 : MeromorphicAt (fun _ : ℂ => (2 : ℂ)) 1 := MeromorphicAt.const (2 : ℂ) 1
    have hpi : MeromorphicAt (fun s : ℂ => (↑Real.pi : ℂ) ^ (-s / 2)) 1 := by
      have han : AnalyticAt ℂ (fun s : ℂ => (↑Real.pi : ℂ) ^ (-s / 2)) 1 := by
        refine AnalyticAt.cpow analyticAt_const (analyticAt_id.neg.div_const (c := (2 : ℂ))) ?_
        exact ofReal_mem_slitPlane.mpr Real.pi_pos
      exact han.meromorphicAt
    have hG : MeromorphicAt (fun s : ℂ => Gamma (s / 2 + 1)) 1 := by
      have hg : AnalyticAt ℂ (fun s : ℂ => s / 2 + 1) 1 :=
        (analyticAt_id.div_const (c := (2 : ℂ))).add analyticAt_const
      have hΓ : MeromorphicAt (fun s : ℂ => Gamma s) (1 / 2 + 1) := by
        have h1Γ : MeromorphicAt (fun s : ℂ => (Gamma s)⁻¹) (1 / 2 + 1) := by
          have hdiff : DifferentiableOn ℂ (fun s : ℂ => (Gamma s)⁻¹) univ :=
            Complex.differentiable_one_div_Gamma.differentiableOn
          have han : AnalyticOnNhd ℂ (fun s : ℂ => (Gamma s)⁻¹) univ :=
            hdiff.analyticOnNhd isOpen_univ
          exact han.meromorphicOn (1 / 2 + 1) (by simp)
        exact (MeromorphicAt.inv_iff.mp h1Γ)
      exact MeromorphicAt.comp_analyticAt (f := fun s : ℂ => Gamma s)
        (g := fun s : ℂ => s / 2 + 1) hΓ hg
    exact (hc2.mul hpi).mul hG
  have hdiv : MeromorphicAt
      (fun s : ℂ => (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) /
        (2 * (↑Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2 + 1))) 1 :=
    MeromorphicAt.div hM hD
  convert hdiv using 1
  funext s
  exact riemannZeta_eq_mul_completedRiemannZeta₀ s

/-- The Riemann zeta function is meromorphic at every point of the complex plane. -/
lemma meromorphicAt_riemannZeta (x : ℂ) : MeromorphicAt riemannZeta x := by
  by_cases hx : x = 1
  · subst hx
    exact meromorphicAt_riemannZeta_one
  · exact meromorphicAt_riemannZeta_of_ne_one hx
