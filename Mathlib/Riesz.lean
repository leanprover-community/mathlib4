/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib.Analysis.NormedSpace.FiniteDimension

/-!
# An introduction to Lean via Riesz' Theorem

I will explain the proof of Riesz' Theorem to the computer.

This theorem asserts that if a real normed vector space has a compact ball, then the space
is finite-dimensional.

We prove the contrapositive: if the space is not finite-dimensional, we will construct a sequence
in the ball of radius `2` whose points are all at distance at least `1`, contradicting the
compactness of the ball.

We construct the sequence by induction. Assume that the first `n` points `xᵢ` have been constructed.
They span a subspace `F` which is finite-dimensional and therefore complete (by equivalence of
norms), hence closed. Let `x ∉ F`. Denote by `d` its distance to `F` (which is positive by
closedness). Let us choose `y ∈ F` with `dist x y < 2 d`. I claim that `d⁻¹ * (x - y)` can be
chosen as the next point of the sequence. Its norm is indeed at most `2`. Moreover, as `x∩ ∈ F`, we
have `y + d * xᵢ ∈ F`. Therefore,
`d ≤ dist x (y + d * xᵢ)`, i.e., `d ≤ ‖d * (d⁻¹ * (x - y) - xᵢ)‖`,
which gives `1 ≤ ‖d⁻¹ * (x - y) - xᵢ‖` as claimed.

To explain this 10 lines proof to Lean, we will cut it in several sublemmas.
-/

open Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Given a closed subspace which is not the whole space, one can find a point with norm at most `2`
which is at distance `1` of every point in the subspace. -/
lemma exists_point_away_from_subspace
    (F : Submodule ℝ E) (hF : ∃ x, x ∉ F) (hFc : IsClosed (F : Set E)) :
    ∃ (z : E), ‖z‖ < 2 ∧ (∀ y ∈ F, 1 ≤ ‖z - y‖) := by
  obtain ⟨x, x_pas_dans_F⟩ := hF
  let d := infDist x F
  have hFn : (F : Set E).Nonempty := ⟨0, F.zero_mem⟩
  have d_pos : 0 < d := (IsClosed.not_mem_iff_infDist_pos hFc hFn).1 x_pas_dans_F
  obtain ⟨y₀, hy₀F, hxy₀⟩ : ∃ y ∈ F, dist x y < 2 * d := by
    apply (infDist_lt_iff hFn).1
    exact lt_two_mul_self d_pos
    -- linarith
  let z := d⁻¹ • (x - y₀)
  have Nz : ‖z‖ < 2 := by
    simpa [z, norm_smul, abs_of_nonneg d_pos.le, ← div_eq_inv_mul, div_lt_iff d_pos, ← dist_eq_norm]
  have I : ∀ y ∈ F, 1 ≤ ‖z - y‖ := by
    intro y hyF
    have A : d ≤ dist x (y₀ + d • y) := by
      apply infDist_le_dist_of_mem
      exact F.add_mem hy₀F (F.smul_mem _ hyF)
    have B : d⁻¹ * d = 1 := by field_simp [d_pos.ne']
    calc
      1 = d⁻¹ * d                    := B.symm
      _ ≤ d⁻¹ * dist x (y₀ + d • y)  := mul_le_mul_of_nonneg_left A (inv_nonneg.2 d_pos.le)
      _ = d⁻¹ * ‖(x - y₀) - d • y‖   := by rw [dist_eq_norm, sub_sub]
      _ = ‖d⁻¹ • ((x - y₀) - d • y)‖ := by simp [norm_smul, abs_of_nonneg d_pos.le]
      _ = ‖z - y‖                    := by simp_rw [z, smul_sub, smul_smul, B, one_smul]
  exact ⟨z, Nz, I⟩

/-- In an infinite-dimensional real normed vector space, given a finite number of points, one can
find a point with norm at most `2` whose distance to all these points is at least `1`. -/
lemma exists_point_away_from_finite
    (s : Set E) (hs : Set.Finite s) (h : ¬(FiniteDimensional ℝ E)) :
    ∃ (z : E), ‖z‖ < 2 ∧ (∀ y ∈ s, 1 ≤ ‖z - y‖) := by
  let F := Submodule.span ℝ s
  have : FiniteDimensional ℝ F := Module.finite_def.2
    ((Submodule.fg_top _).2 (Submodule.fg_def.2 ⟨s, hs, rfl⟩))
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finiteDimensional _
  have hF : ∃ x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule ℝ E) = F := by ext x; simp [h]
    have : FiniteDimensional ℝ (⊤ : Submodule ℝ E) := by rwa [this]
    refine Module.finite_def.2 ((Submodule.fg_top _).1 (Module.finite_def.1 this))
  obtain ⟨x, x_lt_2, hx⟩ : ∃ (x : E), ‖x‖ < 2 ∧ ∀ (y : E), y ∈ F → 1 ≤ ‖x - y‖ :=
    exists_point_away_from_subspace F hF Fclosed
  exact ⟨x, x_lt_2, fun y hy ↦ hx _ (Submodule.subset_span hy)⟩

/-- In an infinite-dimensional real normed vector space, one can find a sequence of points of norm
at most `2`, all of them separated by at least `1`. -/
lemma exists_sequence_separated (h : ¬(FiniteDimensional ℝ E)) :
    ∃ (u : ℕ → E), (∀ n, ‖u n‖ < 2) ∧ (∀ m n, m ≠ n → 1 ≤ ‖u n - u m‖) := by
  have : IsSymm E (fun (x y : E) ↦ 1 ≤ ‖y - x‖) := by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply exists_seq_of_forall_finset_exists' (fun (x : E) ↦ ‖x‖ < 2)
    (fun (x : E) (y : E) ↦ 1 ≤ ‖y - x‖)
  intro s _hs
  exact exists_point_away_from_finite (s : Set E) s.finite_toSet h

/-- Consider a real normed  vector space in which the closed ball of radius `2` is compact. Then
this space is finite-dimensional. -/
theorem my_riesz_version (h : IsCompact (closedBall (0 : E) 2)) :
    FiniteDimensional ℝ E := by
  by_contra hfin
  obtain ⟨u, u_lt_two, u_far⟩ :
    ∃ (u : ℕ → E), (∀ n, ‖u n‖ < 2) ∧ (∀ m n, m ≠ n → 1 ≤ ‖u n - u m‖) :=
    exists_sequence_separated hfin
  have A : ∀ n, u n ∈ closedBall (0 : E) 2 := by
    intro n
    simpa only [norm_smul, dist_zero_right, mem_closedBall] using (u_lt_two n).le
  obtain ⟨x, _hx, φ, φmono, φlim⟩ : ∃ x ∈ closedBall (0 : E) 2, ∃ (φ : ℕ → ℕ),
    StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) := h.tendsto_subseq A
  have B : CauchySeq (u ∘ φ) := φlim.cauchySeq
  obtain ⟨N, hN⟩ : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → dist ((u ∘ φ) n) ((u ∘ φ) N) < 1 :=
    cauchySeq_iff'.1 B 1 zero_lt_one
  apply lt_irrefl (1 : ℝ)
  calc
  1 ≤ dist (u (φ (N+1))) (u (φ N)) := by
    simp only [dist_eq_norm, ← smul_sub, norm_smul]
    apply u_far
    exact (φmono (Nat.lt_succ_self N)).ne
  _ < 1 := hN (N+1) (Nat.le_succ N)

/- The proof is over. It takes roughly 100 lines, 10 times more than the informal proof. This is
quite typical.  -/

theorem the_real_riesz_version
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace 𝕜] {r : ℝ}
    (r_pos : 0 < r)  {c : F} (hc : IsCompact (closedBall c r)) :
    FiniteDimensional 𝕜 F :=
  .of_isCompact_closedBall 𝕜 r_pos hc
-- by exact?

/- Pour l'énoncé précédent :
  have : (0 : ℝ) < 2 := zero_lt_two
  exact?
-/

/- The proofs are checked by the "kernel". But how can one be convinced that the definitions are
good? With wrong definitions, one could prove anything. -/

def IsSGCompact {α : Type*} (_s : Set α) : Prop := False

theorem riesz_with_isSGCompact (h : IsSGCompact (closedBall (0 : E) 2)) :
  FiniteDimensional ℝ E :=
False.elim h

theorem antiriesz_with_isSGCompact (h : IsSGCompact (closedBall (0 : E) 2)) :
  ¬(FiniteDimensional ℝ E) :=
False.elim h

/- We can try unfolding the definitions to see if they look reasonable. -/

#check IsCompact
#check FiniteDimensional

/- We can try to see if the definitions make it possible to prove reasonable theorems. -/

example (n : ℕ) : FiniteDimensional ℝ (Fin n → ℝ) := by infer_instance

example (n : ℕ) : IsCompact (closedBall (0 : Fin n → ℝ) 1) := isCompact_closedBall _ _

example : ¬(IsCompact (Set.univ : Set ℝ)) := noncompact_univ ℝ

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] :
  ¬(IsCompact (Set.univ : Set E)) := noncompact_univ E
