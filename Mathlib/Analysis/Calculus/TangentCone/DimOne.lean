import Mathlib.Analysis.Calculus.TangentCone.Basic

open Filter Metric Set
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The tangent cone at a non-isolated point in dimension 1 is the whole space. -/
theorem tangentConeAt_eq_univ {s : Set 𝕜} {x : 𝕜} (hx : AccPt x (𝓟 s)) :
    tangentConeAt 𝕜 s x = univ := by
  apply eq_univ_iff_forall.2 (fun y ↦ ?_)
  -- first deal with the case of `0`, which has to be handled separately.
  rcases eq_or_ne y 0 with rfl | hy
  · exact zero_mem_tangentCone (mem_closure_iff_clusterPt.mpr hx.clusterPt)
  /- Assume now `y` is a fixed nonzero scalar. Take a sequence `d n` tending to `0` such
  that `x + d n ∈ s`. Let `c n = y / d n`. Then `‖c n‖` tends to infinity, and `c n • d n`
  converges to `y` (as it is equal to `y`). By definition, this shows that `y` belongs to the
  tangent cone. -/
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have A n : ∃ y ∈ closedBall x (u n) ∩ s, y ≠ x :=
    accPt_iff_nhds.mp hx _ (closedBall_mem_nhds _ (u_pos n))
  choose v hv hvx using A
  choose hvu hvs using hv
  let d := fun n ↦ v n - x
  have d_ne n : d n ≠ 0 := by simpa [d, sub_eq_zero] using hvx n
  refine ⟨fun n ↦ y * (d n)⁻¹, d, .of_forall ?_, ?_, ?_⟩
  · simpa [d] using hvs
  · simp only [norm_mul, norm_inv]
    apply (tendsto_const_mul_atTop_of_pos (by simpa using hy)).2
    apply tendsto_inv_nhdsGT_zero.comp
    simp only [nhdsWithin, tendsto_inf, tendsto_principal, mem_Ioi, norm_pos_iff, ne_eq,
      eventually_atTop, ge_iff_le]
    have B (n : ℕ) : ‖d n‖ ≤ u n := by simpa [dist_eq_norm] using hvu n
    refine ⟨?_, 0, fun n hn ↦ by simpa using d_ne n⟩
    exact squeeze_zero (fun n ↦ by positivity) B u_lim
  · convert tendsto_const_nhds (α := ℕ) (x := y) with n
    simp [mul_assoc, inv_mul_cancel₀ (d_ne n)]

@[deprecated (since := "2025-04-27")] alias tangentCone_eq_univ := tangentConeAt_eq_univ

/-- In one dimension, a point is a point of unique differentiability of a set
iff it is an accumulation point of the set. -/
theorem uniqueDiffWithinAt_iff_accPt {s : Set 𝕜} {x : 𝕜} :
    UniqueDiffWithinAt 𝕜 s x ↔ AccPt x (𝓟 s) :=
  ⟨UniqueDiffWithinAt.accPt, fun h ↦
    ⟨by simp [tangentConeAt_eq_univ h], mem_closure_iff_clusterPt.mpr h.clusterPt⟩⟩

alias ⟨_, AccPt.uniqueDiffWithinAt⟩ := uniqueDiffWithinAt_iff_accPt

/-- In one dimension, every point is either a point of unique differentiability, or isolated. -/
@[deprecated uniqueDiffWithinAt_iff_accPt (since := "2025-04-20")]
theorem uniqueDiffWithinAt_or_nhdsWithin_eq_bot (s : Set 𝕜) (x : 𝕜) :
    UniqueDiffWithinAt 𝕜 s x ∨ 𝓝[s \ {x}] x = ⊥ :=
  (em (AccPt x (𝓟 s))).imp AccPt.uniqueDiffWithinAt fun h ↦ by
    rwa [accPt_principal_iff_nhdsWithin, not_neBot] at h
