import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousFunction.Bounded

open MeasureTheory MeasureTheory.Measure Filter Topology BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable (φ : C(E, ℝ)) (hφ_int : ∫ x, φ x ∂μ = 1)

/-- For `φ : E → ℝ` with `∫ x, φ x ∂μ = 1` and `f : E →ᵇ F`, we have that
`∫ n ^ d • φ(n • x) • f x ∂μ` converges to `f 0`. -/
theorem foo (f : E →ᵇ F) :
    Tendsto (fun n : ℕ ↦ ∫ x, ((n : ℝ) ^ FiniteDimensional.finrank ℝ E) • φ (n • x) • f x ∂ μ)
      atTop (𝓝 (f 0)) := by
  have h1 : (fun n : ℕ ↦ ∫ x, ((n : ℝ) ^ FiniteDimensional.finrank ℝ E) • φ (n • x) • f x ∂ μ)
      =ᶠ[atTop] fun n ↦ ∫ x, φ x • f ((n : ℝ)⁻¹ • x) ∂ μ := by
    unfold EventuallyEq
    simp only [eventually_atTop, ge_iff_le]
    use 1
    intro n hn
    rw [integral_smul, ← integral_comp_inv_smul_of_nonneg]
    congr
    ext x
    congr
    rw [← smul_assoc, nsmul_eq_mul, mul_inv_cancel (by positivity), one_smul]
    positivity
  have h2 : ∫ x, φ x • f 0 ∂μ = f 0 := by rw [integral_smul_const, hφ_int, one_smul]
  rw [Filter.tendsto_congr' h1, ← h2]
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖φ x‖ * ‖f‖)
  · intro n
    apply (φ.continuous.smul <| f.continuous.comp <| continuous_const_smul _).aestronglyMeasurable
  · apply Integrable.mul_const
    have hφ' := integrable_of_integral_eq_one hφ_int
    rw [integrable_norm_iff hφ'.aestronglyMeasurable]
    exact hφ'
  · intro n
    apply eventually_of_forall
    intro x
    rw [norm_smul]
    gcongr
    apply norm_coe_le_norm
  apply eventually_of_forall
  intro x
  apply Tendsto.const_smul
  apply Tendsto.comp (f.continuousAt 0)
  rw [← zero_smul ℝ x]
  apply tendsto_inverse_atTop_nhds_zero_nat.smul_const
