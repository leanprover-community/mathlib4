import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Instances.Real
import Mathlib.LinearAlgebra.Finrank
import Mathlib.Analysis.Convolution
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.SetTheory.Cardinal.CountableCover

set_option autoImplicit false

open LinearMap Set

open BigOperators Classical Convex Pointwise Filter

universe u v

open Filter Set

open scoped Cardinal Topology

/-- In a topological vector space over a nontrivially normed field, any neighborhood of zero has
the same cardinality as the whole space. -/
lemma cardinal_eq_of_mem_nhds_zero
    {E 𝕜 : Type _} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} (hs : s ∈ 𝓝 (0 : E)) : #s = #E := by
  obtain ⟨c, hc⟩ : ∃ x : 𝕜 , 1 < ‖x‖ := NormedField.exists_lt_norm 𝕜 1
  have cn_ne : ∀ n, c^n ≠ 0 := by
    intro n
    apply pow_ne_zero
    rintro rfl
    simp only [norm_zero] at hc
    exact lt_irrefl _ (hc.trans zero_lt_one)
  have A : ∀ (x : E), ∀ᶠ n in (atTop : Filter ℕ), x ∈ c^n • s := by
    intro x
    have : Tendsto (fun n ↦ (c^n) ⁻¹ • x) atTop (𝓝 ((0 : 𝕜) • x)) := by
      have : Tendsto (fun n ↦ (c^n)⁻¹) atTop (𝓝 0) := by
        simp_rw [← inv_pow]
        apply tendsto_pow_atTop_nhds_0_of_norm_lt_1
        rw [norm_inv]
        exact inv_lt_one hc
      exact Tendsto.smul_const this x
    rw [zero_smul] at this
    filter_upwards [this hs] with n (hn : (c ^ n)⁻¹ • x ∈ s)
    exact (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).2 hn
  have B : ∀ n, #(c^n • s) = #s := by
    intro n
    have : c^n • s ≃ s :=
    { toFun := fun x ↦ ⟨(c^n)⁻¹ • x.1, (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).1 x.2⟩
      invFun := fun x ↦ ⟨(c^n) • x.1, smul_mem_smul_set x.2⟩
      left_inv := fun x ↦ by simp [smul_smul, mul_inv_cancel (cn_ne n)]
      right_inv := fun x ↦ by simp [smul_smul, inv_mul_cancel (cn_ne n)] }
    exact Cardinal.mk_congr this
  apply (Cardinal.mk_of_countable_eventually_mem A B).symm

lemma cardinal_eq_of_mem_nhds
    {E 𝕜 : Type _} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousSMul 𝕜 E] [ContinuousAdd E]
    {s : Set E} {x : E} (hs : s ∈ 𝓝 x) : #s = #E := by
  let t := s - {x}
  have : t ∈ 𝓝 0 := by


#exit

  have A : ∀ n, #(c^n • s) = #s := sorry
  have B : univ ⊆ ⋃ (n : ℕ), c^n • s := by
    intro x hx
    have Z : Tendsto (fun n ↦ (c^n) ⁻¹ • x) atTop (𝓝 0) := sorry
    obtain ⟨n, hn⟩ : ∃ n, (c ^ n)⁻¹ • x ∈ s := by
      have : ∀ᶠ n in atTop, (c ^ n)⁻¹ • x ∈ s := Z hs
      exact this.exists
    apply mem_iUnion_of_mem n
    apply (mem_smul_set_iff_inv_smul_mem₀ _ _ _).2 hn
    apply pow_ne_zero
    rintro rfl
    simp only [norm_zero] at hc
    exact lt_irrefl _ (hc.trans zero_lt_one)
  apply (Cardinal.mk_of_monotone_countable _ A B).symm




#exit

lemma foo {E : Type _} [AddCommGroup E] [Module ℝ E] (x y : E) (h : LinearIndependent ℝ ![x, y])
    (s t : ℝ) (hs : s ≠ t) : [x -[ℝ]- t • y] ∩ [x -[ℝ]- s • y] ⊆ {x} := by
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image, mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  simp only [smul_smul] at H
  obtain rfl : q = p := by simpa using (h.eq_of_pair H).1
  rcases q0.eq_or_gt with rfl|hq0'
  · simp
  · have A : s = t := by simpa [mul_eq_mul_left_iff, hq0'.ne'] using (h.eq_of_pair H).2
    exact (hs A).elim




theorem glouglou1 {E : Type _} [TopologicalSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (s : Set E) (hs : s.Countable) : Dense sᶜ := by
  exact?



theorem glouglou {E : Type _} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (h : 2 ≤ Module.rank ℝ E) (s : Set E) (hs : s.Countable) :
    IsConnected sᶜ := by
  sorry
