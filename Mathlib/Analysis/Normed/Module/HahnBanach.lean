/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Hahn-Banach extension theorem

In this file, we prove the analytic Hahn-Banach theorem for normed vector spaces. For any continuous
linear functional on a subspace, we can extend it to the entire space without changing
its norm. For Hahn-Banach theorems for locally convex spaces, see
`Mathlib.Analysis.LocallyConvex.HahnBanach`.

We prove
* `exists_extension_norm_eq`: Hahn-Banach theorem for continuous linear functionals on normed spaces
  over `ℝ` or `ℂ`.

In order to state and prove the corollaries uniformly, we prove the statements for a field `𝕜`
satisfying `RCLike 𝕜`.

In this setting, `exists_dual_vector` states that, for any nonzero `x`, there exists a continuous
linear form `g` of norm `1` with `g x = ‖x‖` (where the norm has to be interpreted as an element
of `𝕜`).
-/

public section


universe u v

section RCLike

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] {E : Type*}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Hahn-Banach theorem** for continuous linear functions over `𝕜`
satisfying `IsRCLikeNormedField 𝕜`. -/
@[wikidata Q866116]
theorem exists_extension_norm_eq (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) :
    ∃ g : StrongDual 𝕜 E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ := by
  obtain ⟨g, hg, hl⟩ := by
    refine Module.Dual.exists_continuous_extension_of_le_seminorm p f
      (show Continuous (‖f‖₊ • (normSeminorm 𝕜 E)) from ?_) fun x => f.le_opNorm x
    exact continuous_norm.const_smul ‖f‖₊
  refine ⟨g, hg, le_antisymm (g.opNorm_le_bound (norm_nonneg f) hl) ?_⟩
  exact f.opNorm_le_bound (norm_nonneg _) fun x => by simpa [hg x] using g.le_opNorm x

/-- A linear form `A` which is dominated by the norm of a linear map `L` factors through `L`: there
is a continuous linear form `Λ` of norm at most `1` such that `Λ (L c) = A c` for all `c`.
This is a consequence of the Hahn-Banach theorem. -/
theorem exists_strongDual_forall_apply_eq_of_forall_norm_le {V X : Type*}
    [AddCommGroup V] [Module 𝕜 V] [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] (L : V →ₗ[𝕜] X)
    (A : V →ₗ[𝕜] 𝕜) (h : ∀ c, ‖A c‖ ≤ ‖L c‖) :
    ∃ Λ : StrongDual 𝕜 X, ‖Λ‖ ≤ 1 ∧ ∀ c, Λ (L c) = A c := by
  have h_ker : LinearMap.ker L ≤ LinearMap.ker A := fun c hc ↦ by
    simpa [LinearMap.mem_ker.1 hc] using h c
  -- the linear form `L c ↦ A c` on the range of `L` has norm at most `1`
  let f₀ : LinearMap.range L →ₗ[𝕜] 𝕜 :=
    (LinearMap.ker L).liftQ A h_ker ∘ₗ L.quotKerEquivRange.symm.toLinearMap
  have hf₀ (c : V) : f₀ ⟨L c, LinearMap.mem_range_self L c⟩ = A c := by
    simp [f₀, LinearMap.quotKerEquivRange_symm_apply_image]
  have hf₀_le (x : LinearMap.range L) : ‖f₀ x‖ ≤ 1 * ‖x‖ := by
    obtain ⟨_, c, rfl⟩ := x
    rw [hf₀, one_mul]
    exact h c
  obtain ⟨Λ, hΛ, hΛ_norm⟩ :=
    exists_extension_norm_eq (LinearMap.range L) (f₀.mkContinuous 1 hf₀_le)
  exact ⟨Λ, hΛ_norm.trans_le (f₀.mkContinuous_norm_le zero_le_one _),
    fun c ↦ (hΛ ⟨_, LinearMap.mem_range_self L c⟩).trans (hf₀ c)⟩

end RCLike

section DualVector

variable (𝕜 : Type v) [RCLike 𝕜]

open ContinuousLinearEquiv Submodule

section Seminormed

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Corollary of Hahn-Banach. Given an element `x` of a normed space with `‖x‖ ≠ 0`, there
exists an element of the dual space, of norm `1`, whose value on `x` is `‖x‖`. -/
theorem exists_dual_vector (x : E) (h : ‖x‖ ≠ 0) : ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  have hhomothety := LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x (ne_zero_of_norm_ne_zero h)
  let coord : span 𝕜 {x} →L[𝕜] 𝕜 := (ofHomothety _ _ (by positivity) hhomothety).symm
  obtain ⟨g, hg⟩ := exists_extension_norm_eq (span 𝕜 {x}) ((‖x‖ : 𝕜) • coord)
  have hval : g x = ‖x‖ := by
    have hgx : g x = g (⟨x, by simp⟩ : span 𝕜 {x}) := by rw [Submodule.coe_mk]
    have hcx : coord ⟨x, _⟩ = 1 := LinearEquiv.coord_self 𝕜 E x (ne_zero_of_norm_ne_zero h)
    simp [-algebraMap_smul, hgx, ↓hg.left, hcx]
  refine ⟨g, le_antisymm ?_ ?_, hval⟩
  · simp only [hg.right, norm_smul, norm_algebraMap', norm_norm]
    grw [coord.opNorm_le_bound (by positivity)
      (fun y ↦ (homothety_inverse _ (by positivity) _ hhomothety y).le), mul_inv_cancel₀ h]
  · have hle := g.le_opNorm x
    simp only [hval, norm_algebraMap', norm_norm] at hle
    exact one_le_of_le_mul_right₀ (by positivity) hle

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, but only ensuring that
the dual element has norm at most `1` (this cannot be improved for the trivial
vector space). -/
theorem exists_dual_vector'' (x : E) : ∃ g : StrongDual 𝕜 E, ‖g‖ ≤ 1 ∧ g x = ‖x‖ := by
  by_cases hx : ‖x‖ = 0
  · exact ⟨0, by simp, by simp [hx]⟩
  · obtain ⟨g, hg⟩ := exists_dual_vector 𝕜 x hx
    exact ⟨g, hg.left.le, hg.right⟩

end Seminormed

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [Nontrivial E] (x : E) : ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  by_cases hx : x = 0
  · obtain ⟨y, hy⟩ := exists_norm_ne_zero E
    obtain ⟨g, hg⟩ := exists_dual_vector 𝕜 y hy
    exact ⟨g, hg.left, by simp [hx]⟩
  · exact exists_dual_vector 𝕜 x (norm_ne_zero_iff.mpr hx)

/-- For a separable set `t` in a normed space, there is a sequence of continuous linear forms
which separates the points of `t` from `0`: the only point of `t` at which all of them vanish
is `0`. -/
theorem TopologicalSpace.IsSeparable.exists_seq_strongDual_eq_zero_of_forall_apply_eq_zero
    {t : Set E} (ht : IsSeparable t) :
    ∃ φ : ℕ → StrongDual 𝕜 E, ∀ y ∈ t, (∀ k, φ k y = 0) → y = 0 := by
  -- `t` is contained in the closure of the range of a sequence `u`
  obtain ⟨c, hc, htc⟩ := ht
  obtain ⟨u, hu⟩ := (hc.insert 0).exists_eq_range (Set.insert_nonempty 0 c)
  have htu : t ⊆ closure (Set.range u) :=
    hu ▸ htc.trans (closure_mono (Set.subset_insert 0 c))
  -- `φ k` is a continuous linear form of norm at most `1` such that `φ k (u k) = ‖u k‖`
  choose φ hφ_norm hφ using fun k ↦ exists_dual_vector'' 𝕜 (u k)
  refine ⟨φ, fun y hyt hy ↦ ?_⟩
  have h (k : ℕ) : ‖u k‖ ≤ ‖y - u k‖ := by
    calc ‖u k‖ = ‖φ k (y - u k)‖ := by simp [hy k, hφ k]
      _ ≤ ‖φ k‖ * ‖y - u k‖ := (φ k).le_opNorm _
      _ ≤ ‖y - u k‖ := mul_le_of_le_one_left (norm_nonneg _) (hφ_norm k)
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Metric.mem_closure_iff.1 (htu hyt) (ε / 2) (half_pos hε)
  rw [dist_eq_norm] at hk
  linarith [norm_le_insert' y (u k), h k]

end DualVector
