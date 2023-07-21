/-
Copyright (c) 2023 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module geometry.manifold.whitney_embedding
! leanprover-community/mathlib commit 86c29aefdba50b3f33e86e52e3b2f51a0d8f0282
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
# Functions with prescribed support in manifolds
-/

universe uι uE uH uM

variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  {s t : Set M}
open Function Filter FiniteDimensional Set

open scoped Topology Manifold Classical Filter BigOperators

open SmoothManifoldWithCorners

noncomputable section

variable (I)

theorem IsOpen.exists_smooth_support_eq_of_model {s : Set H} (hs : IsOpen s) :
    ∃ f : H → ℝ, f.support = s ∧ Smooth I 𝓘(ℝ) f ∧ Set.range f ⊆ Set.Icc 0 1 := by
  have h's : IsOpen (I.symm ⁻¹' s) := I.continuous_symm.isOpen_preimage _ hs
  rcases h's.exists_smooth_support_eq with ⟨f, f_supp, f_diff, f_range⟩
  refine ⟨f ∘ I, ?_, ?_, ?_⟩
  · rw [support_comp_eq_preimage, f_supp, ← preimage_comp]
    simp only [ModelWithCorners.symm_comp_self, preimage_id_eq, id_eq]
  · exact f_diff.comp_contMDiff contMDiff_model
  · exact Subset.trans (range_comp_subset_range _ _) f_range


theorem IsOpen.exists_smooth_support_eq' (hs : IsOpen s) :
    ∃ f : M → ℝ, f.support = s ∧ Smooth I 𝓘(ℝ) f ∧ ∀ x, 0 ≤ f x := by
  have : ∀ x ∈ (univ : Set M), univ ∈ 𝓝 x := fun x hx ↦ univ_mem
  rcases SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M with ⟨f, hf⟩
  have A : ∀ (c : M), ∃ g : H → ℝ,
      g.support = (chartAt H c).target ∩ (chartAt H c).symm ⁻¹' s ∧
      Smooth I 𝓘(ℝ) g ∧ Set.range g ⊆ Set.Icc 0 1 := by
    intro i
    apply IsOpen.exists_smooth_support_eq_of_model
    exact LocalHomeomorph.preimage_open_of_open_symm _ hs
  choose g g_supp g_diff hg using A
  refine ⟨fun x ↦ ∑ᶠ c, f c x * g c (chartAt H c x), ?_, ?_, ?_⟩
  · refine support_eq_iff.2 ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · apply ne_of_gt
      sorry
    · apply finsum_eq_zero_of_forall_eq_zero
      intro c
      by_cases Hx : x ∈ tsupport (f c)
      · suffices g c (chartAt H c x) = 0 by simp only [this, mul_zero]
        rw [← nmem_support, g_supp, ← mem_preimage, preimage_inter]
        contrapose! hx
        simp only [mem_inter_iff, mem_preimage, (chartAt H c).left_inv (hf c Hx)] at hx
        exact hx.2
      · have : x ∉ support (f c) := by contrapose! Hx; exact subset_tsupport _ Hx
        rw [nmem_support] at this
        simp [this]
  · apply SmoothPartitionOfUnity.smooth_finsum_smul
    intro c x hx
    apply (g_diff c (chartAt H c x)).comp
    exact contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas I _) (hf c hx)
  · intro x
    apply finsum_nonneg (fun c ↦ ?_)
    apply mul_nonneg (f.nonneg c x)
    exact (hg c (mem_range_self (f := g c) (chartAt H c x))).1






#exit

contMDiff_finsum_smul

preimage_open_of_open_symm

-- variable [NormalSpace M]

/-- Given an open set `s` containing a closed subset `t` in a finite-dimensional real normed
vector space, there exists a smooth function with values in `[0, 1]` whose support is
contained in `s` and equal to `1` on `t`.
Superseded by `IsOpen.exists_smooth_support_eq_eq_one_iff`, ensuring that the support is
exactly `s`. -/
theorem IsOpen.exists_smooth_support_subset (hs : IsOpen s) (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : M → ℝ, f.support ⊆ s ∧ Smooth I 𝓘(ℝ) f ∧ (∀ x, 0 ≤ f x)
      ∧ ∀ x ∈ t, f x = 1 := by
  /- Consider `u` an open set between `t` and `s`. Take `f` with support `u`, and `g` with support
  `s \ t`. Then `f / (f + g)` works. The only nontrivial fact is that it is smooth. This follows
  from the fact that `f + g` is strictly positive on a neighborhood of the topological support of
  `f`, by construction. -/
  have : LocallyCompactSpace H := I.locally_compact
  have : LocallyCompactSpace M := ChartedSpace.locallyCompact H M
  have : NormalSpace M := normal_of_paracompact_t2
  obtain ⟨u, u_open, tu, us⟩ : ∃ u, IsOpen u ∧ t ⊆ u ∧ closure u ⊆ s :=
    normal_exists_closure_subset ht hs h
  rcases u_open.exists_smooth_support_eq' I with ⟨f, f_supp, f_diff, f_range⟩
  have A : IsOpen (s \ t) := hs.sdiff ht
  rcases A.exists_smooth_support_eq' I with ⟨g, g_supp, g_diff, g_range⟩
  refine ⟨fun x ↦ f x / (f x + g x), ?_, ?_, ?_, ?_⟩
  -- check that the support is included in `s`.
  · apply support_subset_iff'.2 (fun x hx ↦ ?_)
    have : x ∉ support f := by
      contrapose! hx
      rw [f_supp] at hx
      exact us (subset_closure hx)
    simp only [nmem_support.1 this, zero_add, zero_div]
  /- check that the function is smooth around each `x`, by separating the case where `x ∈ s`
  (in this case, the denominator `f x + g x` is nonzero) and the case where `x ∉ s` (in this
  case, the function vanishes in a neighborhood of `x` as this is the case of `f`). -/
  · intro x
    have : 0 ≤ f x := (f_range (mem_range_self (i := x))).1
    have : 0 ≤ g x := (g_range (mem_range_self (i := x))).1
    by_cases H : x ∈ s
    · apply f_diff.contMDiffAt.div₀ (f_diff.contMDiffAt.add g_diff.contMDiffAt)
      simp only [Pi.add_apply]
      apply ne_of_gt
      by_cases H' : x ∈ t
      · have : f x ≠ 0 := by rw [← mem_support, f_supp]; exact tu H'
        positivity
      · have : g x ≠ 0 := by rw [← mem_support, g_supp]; exact ⟨H, H'⟩
        positivity
    · have B : (closure u)ᶜ ∈ 𝓝 x := by
        apply (isOpen_compl_iff.2 (isClosed_closure)).mem_nhds
        contrapose! H
        simp only [mem_compl_iff, not_not] at H
        exact us H
      apply ContMDiffOn.contMDiffAt _ B
      apply (contMDiffOn_const (c := 0)).congr (fun y hy ↦ ?_)
      have : f y = 0 := by
        rw [← nmem_support, f_supp]
        contrapose! hy
        simpa using subset_closure hy
      simp [this]
  -- check that the function is nonnegative
  · intros x
    have : 0 ≤ f x := (f_range (mem_range_self (i := x))).1
    have : 0 ≤ g x := (g_range (mem_range_self (i := x))).1
    positivity
  -- check that the function is equal to `1` on `t`.
  · intros x hx
    have A : g x = 0 := by
      rw [← nmem_support, g_supp]
      simp [hx]
    have B : f x ≠ 0 := by
      rw [← mem_support, f_supp]
      exact tu hx
    simp [A, B]

/-- Given an open set `s` containing a closed subset `t` in a finite-dimensional real normed
vector space, there exists a smooth function with nonnegative values whose support is
exactly `s` and at least `1` on `t`.
Superseded by `IsOpen.exists_smooth_support_eq_eq_one_iff`, ensuring that the function
is exactly equal to `1` on `t`. -/
theorem IsOpen.exists_smooth_support_eq_le_one (hs : IsOpen s) (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : M → ℝ, f.support = s ∧ Smooth I 𝓘(ℝ) f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x ∈ t, 1 ≤ f x) := by
  /- We start from a nonnegative function supported inside `s` and equal to `1` on `t`, and add
  to it a nonegative function with support exactly `s`. -/
  rcases hs.exists_smooth_support_subset I ht h with ⟨f, f_supp, f_diff, f_nonneg, ft⟩
  rcases (hs.sdiff ht).exists_smooth_support_eq' I with ⟨g, g_supp, g_diff, g_range⟩
  refine ⟨f + g, ?_, f_diff.add g_diff, ?_, ?_⟩
  · apply Subset.antisymm
    · apply (support_add _ _).trans
      apply union_subset f_supp
      rw [g_supp]
      exact diff_subset s t
    · intros x hx
      rw [mem_support, Pi.add_apply]
      apply ne_of_gt
      specialize f_nonneg x
      have B : 0 ≤ g x := (g_range (mem_range_self (i := x))).1
      by_cases H : x ∈ t
      · have Z := ft x H
        positivity
      · have : g x ≠ 0 := by rw [← mem_support, g_supp]; exact ⟨hx, H⟩
        positivity
  · intros x
    specialize f_nonneg x
    have B : 0 ≤ g x := (g_range (mem_range_self (i := x))).1
    simp only [Pi.add_apply, ge_iff_le]
    positivity
  · intros x hx
    simpa [Pi.add_apply, ge_iff_le, ft x hx] using (g_range (mem_range_self (i := x))).1

/-- Given an open set `s` containing a closed subset `t` in a finite-dimensional real normed
vector space, there exists a smooth function with values in `[0, 1]` whose support is exactly `s`
and equal to `1` on `t`.
Superseded by `IsOpen.exists_smooth_support_eq_eq_one_iff`, ensuring that the function
is equal to `1` just on `t`. -/
theorem IsOpen.exists_smooth_support_eq_eq_one
    (hs : IsOpen s) (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : M → ℝ, f.support = s ∧ Smooth I 𝓘(ℝ) f ∧ range f ⊆ Icc 0 1 ∧ (∀ x ∈ t, f x = 1) := by
  /- We start from a function with support equal to `s` and at least equal to `1` on `t`, and
  compose it with a smooth function equal to `1` on `[1, ∞)`. -/
  rcases hs.exists_smooth_support_eq_le_one I ht h with ⟨f, f_supp, f_diff, f_nonneg, ft⟩
  refine ⟨Real.smoothTransition ∘ f, ?_, ?_, ?_, ?_⟩
  · rw [support_comp_eq_of_range_subset, f_supp]
    rintro - ⟨x, rfl⟩
    simp [LE.le.le_iff_eq (f_nonneg x)]
  · exact Real.smoothTransition.contDiff.comp_contMDiff f_diff
  · apply (range_comp_subset_range _ _).trans
    rintro - ⟨y, rfl⟩
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro x hx
    exact Real.smoothTransition.one_of_one_le (ft x hx)

/-- Given an open set `s` containing a closed subset `t` in a finite-dimensional real normed
vector space, there exists a smooth function with values in `[0, 1]` whose support is exactly `s`
and equal to `1` exactly on `t`. -/
theorem IsOpen.exists_smooth_support_eq_eq_one_iff (hs : IsOpen s) (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : M → ℝ, f.support = s ∧ Smooth I 𝓘(ℝ) f ∧ range f ⊆ Icc 0 1 ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  /- Start from a function `f` with support `s` and equal to `1` on `t`, and subtract to it a
  function `g/2` taking values in `[0, 1/2]` and supported on the complement of `t`, to make sure
  that `f - g/2` can only take the value `1` on `t`. We should also make sure that this function is
  positive on `s`, so we take `g` supported on the points where `f > 1/2`. -/
  rcases hs.exists_smooth_support_eq_eq_one I ht h with ⟨f, f_supp, f_diff, f_range, hf⟩
  have A : IsOpen (f ⁻¹' (Ioi ((1:ℝ)/2))) := f_diff.continuous.isOpen_preimage _ isOpen_Ioi
  rcases (A.sdiff ht).exists_smooth_support_eq' I with ⟨g, g_supp, g_diff, g_range⟩
  refine ⟨fun x ↦ f x - (g x)/2, ?_, f_diff.sub (g_diff.div_const _), ?_, fun x ↦ ?_⟩
  -- show that the support is exactly `s`
  · refine support_eq_iff.2 ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · apply ne_of_gt
      have : g x ≤ 1 := (g_range (mem_range_self x)).2
      by_cases H : (1:ℝ)/2 < f x
      · dsimp; linarith
      · have : 0 ≤ f x := (f_range (mem_range_self x)).1
        have : f x ≠ 0 := by rwa [← mem_support, f_supp]
        have : 0 < f x := by positivity
        have : g x = 0 := by
          rw [← nmem_support, g_supp]
          simp only [mem_diff, mem_preimage, mem_Ioi, not_and_or, H, true_or]
        dsimp
        linarith
    · have If : f x = 0 := by rwa [← nmem_support, f_supp]
      have Ig : g x = 0 := by
        rw [← nmem_support, g_supp]
        have A : ¬ (2 : ℝ) < (0 : ℝ) := by norm_num
        simp [If, A]
      simp [If, Ig]
  -- show that the range is included in `[0, 1]`
  · rintro - ⟨x, rfl⟩
    have : 0 ≤ f x := (f_range (mem_range_self x)).1
    have : f x ≤ 1 := (f_range (mem_range_self x)).2
    have : 0 ≤ g x := (g_range (mem_range_self x)).1
    have : g x ≤ 1 := (g_range (mem_range_self x)).2
    refine' ⟨?_, by dsimp; linarith⟩
    by_cases H : (1:ℝ)/2 < f x
    · dsimp; linarith
    · have : g x = 0 := by
        rw [← nmem_support, g_supp]
        simp only [mem_diff, mem_preimage, mem_Ioi, not_and_or, H, true_or]
      dsimp; linarith
  -- show that the function is equal to `1` exactly on `t`
  · refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · have : g x = 0 := by rw [← nmem_support, g_supp]; simp [hx]
      simp [this, hf x hx]
    · contrapose! hx
      have : 0 ≤ g x := (g_range (mem_range_self x)).1
      apply ne_of_lt
      by_cases H : (1:ℝ)/2 < f x
      · have : f x ≤ 1 := (f_range (mem_range_self x)).2
        have : g x ≠ 0 := by rw [← mem_support, g_supp]; exact ⟨H, hx⟩
        have : 0 < g x := by positivity
        linarith
      · simp only [not_lt] at H
        linarith
