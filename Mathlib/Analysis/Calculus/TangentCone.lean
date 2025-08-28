/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tangent cone

In this file, we define two predicates `UniqueDiffWithinAt 𝕜 s x` and `UniqueDiffOn 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangentConeAt`,
and express `UniqueDiffWithinAt` and `UniqueDiffOn` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `UniqueDiffWithinAt` and `UniqueDiffOn` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. Hence, derivatives
are not defined yet. The property of uniqueness of the derivative is therefore proved in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`, but based on the properties of the tangent cone we
prove here.
-/


variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

open Filter Set Metric
open scoped Topology Pointwise

section TangentCone

variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- The set of all tangent directions to the set `s` at the point `x`. -/
def tangentConeAt (s : Set E) (x : E) : Set E :=
  { y : E | ∃ (c : ℕ → 𝕜) (d : ℕ → E),
    (∀ᶠ n in atTop, x + d n ∈ s) ∧
    Tendsto (fun n => ‖c n‖) atTop atTop ∧
    Tendsto (fun n => c n • d n) atTop (𝓝 y) }

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `UniqueDiffWithinAt.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional). -/
@[mk_iff]
structure UniqueDiffWithinAt (s : Set E) (x : E) : Prop where
  dense_tangentConeAt : Dense (Submodule.span 𝕜 (tangentConeAt 𝕜 s x) : Set E)
  mem_closure : x ∈ closure s

@[deprecated (since := "2025-04-27")]
alias UniqueDiffWithinAt.dense_tangentCone := UniqueDiffWithinAt.dense_tangentConeAt

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space. The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `UniqueDiffOn.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. -/
def UniqueDiffOn (s : Set E) : Prop :=
  ∀ x ∈ s, UniqueDiffWithinAt 𝕜 s x

end TangentCone

variable {𝕜}
variable {E F G : Type*}

section TangentCone

-- This section is devoted to the properties of the tangent cone.

open NormedField
section TVS
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}

theorem mem_tangentConeAt_of_pow_smul {r : 𝕜} (hr₀ : r ≠ 0) (hr : ‖r‖ < 1)
    (hs : ∀ᶠ n : ℕ in atTop, x + r ^ n • y ∈ s) : y ∈ tangentConeAt 𝕜 s x := by
  refine ⟨fun n ↦ (r ^ n)⁻¹, fun n ↦ r ^ n • y, hs, ?_, ?_⟩
  · simp only [norm_inv, norm_pow, ← inv_pow]
    exact tendsto_pow_atTop_atTop_of_one_lt <| (one_lt_inv₀ (norm_pos_iff.2 hr₀)).2 hr
  · simp only [inv_smul_smul₀ (pow_ne_zero _ hr₀), tendsto_const_nhds]

@[simp]
theorem tangentConeAt_univ : tangentConeAt 𝕜 univ x = univ :=
  let ⟨_r, hr₀, hr⟩ := exists_norm_lt_one 𝕜
  eq_univ_of_forall fun _ ↦ mem_tangentConeAt_of_pow_smul (norm_pos_iff.1 hr₀) hr <|
    Eventually.of_forall fun _ ↦ mem_univ _

@[deprecated (since := "2025-04-27")] alias tangentCone_univ := tangentConeAt_univ

@[gcongr]
theorem tangentConeAt_mono (h : s ⊆ t) : tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := by
  rintro y ⟨c, d, ds, ctop, clim⟩
  exact ⟨c, d, mem_of_superset ds fun n hn => h hn, ctop, clim⟩

@[deprecated (since := "2025-04-27")] alias tangentCone_mono := tangentConeAt_mono

end TVS

section Normed
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {x y : E} {s t : Set E}

@[simp]
theorem tangentConeAt_closure : tangentConeAt 𝕜 (closure s) x = tangentConeAt 𝕜 s x := by
  refine Subset.antisymm ?_ (tangentConeAt_mono subset_closure)
  rintro y ⟨c, d, ds, ctop, clim⟩
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have : ∀ᶠ n in atTop, ∃ d', x + d' ∈ s ∧ dist (c n • d n) (c n • d') < u n := by
    filter_upwards [ctop.eventually_gt_atTop 0, ds] with n hn hns
    rcases Metric.mem_closure_iff.mp hns (u n / ‖c n‖) (div_pos (u_pos n) hn) with ⟨y, hys, hy⟩
    refine ⟨y - x, by simpa, ?_⟩
    rwa [dist_smul₀, ← dist_add_left x, add_sub_cancel, ← lt_div_iff₀' hn]
  simp only [Filter.skolem, eventually_and] at this
  rcases this with ⟨d', hd's, hd'⟩
  exact ⟨c, d', hd's, ctop, clim.congr_dist
    (squeeze_zero' (.of_forall fun _ ↦ dist_nonneg) (hd'.mono fun _ ↦ le_of_lt) u_lim)⟩

/-- Auxiliary lemma ensuring that, under the assumptions defining the tangent cone,
the sequence `d` tends to 0 at infinity. -/
theorem tangentConeAt.lim_zero {α : Type*} (l : Filter α) {c : α → 𝕜} {d : α → E}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) (hd : Tendsto (fun n => c n • d n) l (𝓝 y)) :
    Tendsto d l (𝓝 0) := by
  have A : Tendsto (fun n => ‖c n‖⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hc
  have B : Tendsto (fun n => ‖c n • d n‖) l (𝓝 ‖y‖) := (continuous_norm.tendsto _).comp hd
  have C : Tendsto (fun n => ‖c n‖⁻¹ * ‖c n • d n‖) l (𝓝 (0 * ‖y‖)) := A.mul B
  rw [zero_mul] at C
  have : ∀ᶠ n in l, ‖c n‖⁻¹ * ‖c n • d n‖ = ‖d n‖ := by
    refine (eventually_ne_of_tendsto_norm_atTop hc 0).mono fun n hn => ?_
    rw [norm_smul, ← mul_assoc, inv_mul_cancel₀, one_mul]
    rwa [Ne, norm_eq_zero]
  have D : Tendsto (fun n => ‖d n‖) l (𝓝 0) := Tendsto.congr' this C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact D

theorem tangentConeAt_mono_nhds (h : 𝓝[s] x ≤ 𝓝[t] x) :
    tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := by
  rintro y ⟨c, d, ds, ctop, clim⟩
  refine ⟨c, d, ?_, ctop, clim⟩
  suffices Tendsto (fun n => x + d n) atTop (𝓝[t] x) from
    tendsto_principal.1 (tendsto_inf.1 this).2
  refine (tendsto_inf.2 ⟨?_, tendsto_principal.2 ds⟩).mono_right h
  simpa only [add_zero] using tendsto_const_nhds.add (tangentConeAt.lim_zero atTop ctop clim)

@[deprecated (since := "2025-04-27")] alias tangentCone_mono_nhds := tangentConeAt_mono_nhds

/-- Tangent cone of `s` at `x` depends only on `𝓝[s] x`. -/
theorem tangentConeAt_congr (h : 𝓝[s] x = 𝓝[t] x) : tangentConeAt 𝕜 s x = tangentConeAt 𝕜 t x :=
  Subset.antisymm (tangentConeAt_mono_nhds h.le) (tangentConeAt_mono_nhds h.ge)

@[deprecated (since := "2025-04-27")] alias tangentCone_congr := tangentConeAt_congr

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
theorem tangentConeAt_inter_nhds (ht : t ∈ 𝓝 x) : tangentConeAt 𝕜 (s ∩ t) x = tangentConeAt 𝕜 s x :=
  tangentConeAt_congr (nhdsWithin_restrict' _ ht).symm

@[deprecated (since := "2025-04-27")] alias tangentCone_inter_nhds := tangentConeAt_inter_nhds

/-- The tangent cone of a product contains the tangent cone of its left factor. -/
theorem subset_tangentConeAt_prod_left {t : Set F} {y : F} (ht : y ∈ closure t) :
    LinearMap.inl 𝕜 E F '' tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 (s ×ˢ t) (x, y) := by
  rintro _ ⟨v, ⟨c, d, hd, hc, hy⟩, rfl⟩
  have : ∀ n, ∃ d', y + d' ∈ t ∧ ‖c n • d'‖ < ((1 : ℝ) / 2) ^ n := by
    intro n
    rcases mem_closure_iff_nhds.1 ht _
        (eventually_nhds_norm_smul_sub_lt (c n) y (pow_pos one_half_pos n)) with
      ⟨z, hz, hzt⟩
    exact ⟨z - y, by simpa using hzt, by simpa using hz⟩
  choose d' hd' using this
  refine ⟨c, fun n => (d n, d' n), ?_, hc, ?_⟩
  · change ∀ᶠ n in atTop, (x, y) + (d n, d' n) ∈ s ×ˢ t
    filter_upwards [hd] with n hn
    simp [hn, (hd' n).1]
  · apply Tendsto.prodMk_nhds hy _
    refine squeeze_zero_norm (fun n => (hd' n).2.le) ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one one_half_pos.le one_half_lt_one

@[deprecated (since := "2025-04-27")]
alias subset_tangentCone_prod_left := subset_tangentConeAt_prod_left

/-- The tangent cone of a product contains the tangent cone of its right factor. -/
theorem subset_tangentConeAt_prod_right {t : Set F} {y : F} (hs : x ∈ closure s) :
    LinearMap.inr 𝕜 E F '' tangentConeAt 𝕜 t y ⊆ tangentConeAt 𝕜 (s ×ˢ t) (x, y) := by
  rintro _ ⟨w, ⟨c, d, hd, hc, hy⟩, rfl⟩
  have : ∀ n, ∃ d', x + d' ∈ s ∧ ‖c n • d'‖ < ((1 : ℝ) / 2) ^ n := by
    intro n
    rcases mem_closure_iff_nhds.1 hs _
        (eventually_nhds_norm_smul_sub_lt (c n) x (pow_pos one_half_pos n)) with
      ⟨z, hz, hzs⟩
    exact ⟨z - x, by simpa using hzs, by simpa using hz⟩
  choose d' hd' using this
  refine ⟨c, fun n => (d' n, d n), ?_, hc, ?_⟩
  · change ∀ᶠ n in atTop, (x, y) + (d' n, d n) ∈ s ×ˢ t
    filter_upwards [hd] with n hn
    simp [hn, (hd' n).1]
  · apply Tendsto.prodMk_nhds _ hy
    refine squeeze_zero_norm (fun n => (hd' n).2.le) ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one one_half_pos.le one_half_lt_one

@[deprecated (since := "2025-04-27")]
alias subset_tangentCone_prod_right := subset_tangentConeAt_prod_right

/-- The tangent cone of a product contains the tangent cone of each factor. -/
theorem mapsTo_tangentConeAt_pi {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {s : ∀ i, Set (E i)} {x : ∀ i, E i}
    {i : ι} (hi : ∀ j ≠ i, x j ∈ closure (s j)) :
    MapsTo (LinearMap.single 𝕜 E i) (tangentConeAt 𝕜 (s i) (x i))
      (tangentConeAt 𝕜 (Set.pi univ s) x) := by
  rintro w ⟨c, d, hd, hc, hy⟩
  have : ∀ n, ∀ j ≠ i, ∃ d', x j + d' ∈ s j ∧ ‖c n • d'‖ < (1 / 2 : ℝ) ^ n := fun n j hj ↦ by
    rcases mem_closure_iff_nhds.1 (hi j hj) _
        (eventually_nhds_norm_smul_sub_lt (c n) (x j) (pow_pos one_half_pos n)) with
      ⟨z, hz, hzs⟩
    exact ⟨z - x j, by simpa using hzs, by simpa using hz⟩
  choose! d' hd's hcd' using this
  refine ⟨c, fun n => Function.update (d' n) i (d n), hd.mono fun n hn j _ => ?_, hc,
      tendsto_pi_nhds.2 fun j => ?_⟩
  · rcases em (j = i) with (rfl | hj) <;> simp [*]
  · rcases em (j = i) with (rfl | hj)
    · simp [hy]
    · suffices Tendsto (fun n => c n • d' n j) atTop (𝓝 0) by simpa [hj]
      refine squeeze_zero_norm (fun n => (hcd' n j hj).le) ?_
      exact tendsto_pow_atTop_nhds_zero_of_lt_one one_half_pos.le one_half_lt_one

@[deprecated (since := "2025-04-27")] alias mapsTo_tangentCone_pi := mapsTo_tangentConeAt_pi

/-- If a subset of a real vector space contains an open segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
theorem mem_tangentConeAt_of_openSegment_subset {s : Set G} {x y : G} (h : openSegment ℝ x y ⊆ s) :
    y - x ∈ tangentConeAt ℝ s x := by
  refine mem_tangentConeAt_of_pow_smul one_half_pos.ne' (by norm_num) ?_
  refine (eventually_ne_atTop 0).mono fun n hn ↦ (h ?_)
  rw [openSegment_eq_image]
  refine ⟨(1 / 2) ^ n, ⟨?_, ?_⟩, ?_⟩
  · exact pow_pos one_half_pos _
  · exact pow_lt_one₀ one_half_pos.le one_half_lt_one hn
  · simp only [sub_smul, one_smul, smul_sub]; abel

@[deprecated (since := "2025-04-27")]
alias mem_tangentCone_of_openSegment_subset := mem_tangentConeAt_of_openSegment_subset

/-- If a subset of a real vector space contains a segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
theorem mem_tangentConeAt_of_segment_subset {s : Set G} {x y : G} (h : segment ℝ x y ⊆ s) :
    y - x ∈ tangentConeAt ℝ s x :=
  mem_tangentConeAt_of_openSegment_subset ((openSegment_subset_segment ℝ x y).trans h)

@[deprecated (since := "2025-04-27")]
alias mem_tangentCone_of_segment_subset := mem_tangentConeAt_of_segment_subset

/-- The tangent cone at a non-isolated point contains `0`. -/
theorem zero_mem_tangentCone {s : Set E} {x : E} (hx : x ∈ closure s) :
    0 ∈ tangentConeAt 𝕜 s x := by
  /- Take a sequence `d n` tending to `0` such that `x + d n ∈ s`. Taking `c n` of the order
  of `1 / (d n) ^ (1/2)`, then `c n` tends to infinity, but `c n • d n` tends to `0`. By definition,
  this shows that `0` belongs to the tangent cone. -/
  obtain ⟨u, -, hu, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n ∧ u n < 1) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto' one_pos
  choose u_pos u_lt_one using hu
  choose v hvs hvu using fun n ↦ Metric.mem_closure_iff.mp hx _ (mul_pos (u_pos n) (u_pos n))
  let d n := v n - x
  let ⟨r, hr⟩ := exists_one_lt_norm 𝕜
  have A n := exists_nat_pow_near (one_le_inv_iff₀.mpr ⟨u_pos n, (u_lt_one n).le⟩) hr
  choose m hm_le hlt_m using A
  set c := fun n ↦ r ^ (m n + 1)
  have c_lim : Tendsto (fun n ↦ ‖c n‖) atTop atTop := by
    simp only [c, norm_pow]
    refine tendsto_atTop_mono (fun n ↦ (hlt_m n).le) <| .inv_tendsto_nhdsGT_zero ?_
    exact tendsto_nhdsWithin_iff.mpr ⟨u_lim, .of_forall u_pos⟩
  refine ⟨c, d, .of_forall <| by simpa [d], c_lim, ?_⟩
  have Hle n : ‖c n • d n‖ ≤ ‖r‖ * u n := by
    specialize u_pos n
    calc
      ‖c n • d n‖ ≤ (u n)⁻¹ * ‖r‖ * (u n * u n) := by
        simp only [c, norm_smul, norm_pow, pow_succ, norm_mul, d, ← dist_eq_norm']
        gcongr
        exacts [hm_le n, (hvu n).le]
      _ = ‖r‖ * u n := by field_simp
  refine squeeze_zero_norm Hle ?_
  simpa using tendsto_const_nhds.mul u_lim

/-- If `x` is not an accumulation point of `s, then the tangent cone of `s` at `x`
is a subset of `{0}`. -/
theorem tangentConeAt_subset_zero (hx : ¬AccPt x (𝓟 s)) : tangentConeAt 𝕜 s x ⊆ 0 := by
  rintro y ⟨c, d, hds, hc, hcd⟩
  suffices ∀ᶠ n in .atTop, d n = 0 from
    tendsto_nhds_unique hcd <| tendsto_const_nhds.congr' <| this.mono fun n hn ↦ by simp [hn]
  simp only [accPt_iff_frequently, not_frequently, not_and', ne_eq, not_not] at hx
  have : Tendsto (x + d ·) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tangentConeAt.lim_zero _ hc hcd)
  filter_upwards [this.eventually hx, hds] with n h₁ h₂
  simpa using h₁ h₂

theorem UniqueDiffWithinAt.accPt [Nontrivial E] (h : UniqueDiffWithinAt 𝕜 s x) : AccPt x (𝓟 s) := by
  by_contra! h'
  have : Dense (Submodule.span 𝕜 (0 : Set E) : Set E) :=
    h.1.mono <| by gcongr; exact tangentConeAt_subset_zero h'
  simp [dense_iff_closure_eq] at this

/-- In a proper space, the tangent cone at a non-isolated point is nontrivial. -/
theorem tangentConeAt_nonempty_of_properSpace [ProperSpace E]
    {s : Set E} {x : E} (hx : AccPt x (𝓟 s)) :
    (tangentConeAt 𝕜 s x ∩ {0}ᶜ).Nonempty := by
  /- Take a sequence `d n` tending to `0` such that `x + d n ∈ s`. Taking `c n` of the order
  of `1 / d n`. Then `c n • d n` belongs to a fixed annulus. By compactness, one can extract
  a subsequence converging to a limit `l`. Then `l` is nonzero, and by definition it belongs to
  the tangent cone. -/
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have A n : ∃ y ∈ closedBall x (u n) ∩ s, y ≠ x :=
    (accPt_iff_nhds).mp hx _ (closedBall_mem_nhds _ (u_pos n))
  choose v hv hvx using A
  choose hvu hvs using hv
  let d := fun n ↦ v n - x
  have M n : x + d n ∈ s \ {x} := by simp [d, hvs, hvx]
  let ⟨r, hr⟩ := exists_one_lt_norm 𝕜
  have W n := rescale_to_shell hr zero_lt_one (x := d n) (by simpa using (M n).2)
  choose c c_ne c_le le_c hc using W
  have c_lim : Tendsto (fun n ↦ ‖c n‖) atTop atTop := by
    suffices Tendsto (fun n ↦ ‖c n‖⁻¹ ⁻¹ ) atTop atTop by simpa
    apply tendsto_inv_nhdsGT_zero.comp
    simp only [nhdsWithin, tendsto_inf, tendsto_principal, mem_Ioi, eventually_atTop, ge_iff_le]
    have B (n : ℕ) : ‖c n‖⁻¹ ≤ 1⁻¹ * ‖r‖ * u n := by
      apply (hc n).trans
      gcongr
      simpa [d, dist_eq_norm] using hvu n
    refine ⟨?_, 0, fun n hn ↦ by simpa using c_ne n⟩
    apply squeeze_zero (fun n ↦ by positivity) B
    simpa using u_lim.const_mul _
  obtain ⟨l, l_mem, φ, φ_strict, hφ⟩ :
      ∃ l ∈ Metric.closedBall (0 : E) 1 \ Metric.ball (0 : E) (1 / ‖r‖),
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto ((fun n ↦ c n • d n) ∘ φ) atTop (𝓝 l) := by
    apply IsCompact.tendsto_subseq _ (fun n ↦ ?_)
    · exact (isCompact_closedBall 0 1).diff Metric.isOpen_ball
    simp only [mem_diff, Metric.mem_closedBall, dist_zero_right, (c_le n).le,
      Metric.mem_ball, not_lt, true_and, le_c n]
  refine ⟨l, ?_, ?_⟩; swap
  · simp only [mem_compl_iff, mem_singleton_iff]
    contrapose! l_mem
    simp only [one_div, l_mem, mem_diff, Metric.mem_closedBall, dist_self, zero_le_one,
      Metric.mem_ball, inv_pos, norm_pos_iff, ne_eq, not_not, true_and]
    contrapose! hr
    simp [hr]
  refine ⟨c ∘ φ, d ∘ φ, .of_forall fun n ↦ ?_, ?_, hφ⟩
  · simpa [d] using hvs (φ n)
  · exact c_lim.comp φ_strict.tendsto_atTop

@[deprecated (since := "2025-04-27")]
alias tangentCone_nonempty_of_properSpace := tangentConeAt_nonempty_of_properSpace

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

end Normed

end TangentCone

section UniqueDiff

/-!
### Properties of `UniqueDiffWithinAt` and `UniqueDiffOn`

This section is devoted to properties of the predicates `UniqueDiffWithinAt` and `UniqueDiffOn`. -/

section TVS
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}

theorem UniqueDiffOn.uniqueDiffWithinAt {s : Set E} {x} (hs : UniqueDiffOn 𝕜 s) (h : x ∈ s) :
    UniqueDiffWithinAt 𝕜 s x :=
  hs x h

theorem uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 univ x := by
  rw [uniqueDiffWithinAt_iff, tangentConeAt_univ]
  simp

theorem uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E) :=
  fun _ _ => uniqueDiffWithinAt_univ

theorem uniqueDiffOn_empty : UniqueDiffOn 𝕜 (∅ : Set E) :=
  fun _ hx => hx.elim

theorem UniqueDiffWithinAt.congr_pt (h : UniqueDiffWithinAt 𝕜 s x) (hy : x = y) :
    UniqueDiffWithinAt 𝕜 s y := hy ▸ h

end TVS

section Normed
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {x y : E} {s t : Set E}

@[simp]
theorem uniqueDiffWithinAt_closure :
    UniqueDiffWithinAt 𝕜 (closure s) x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp [uniqueDiffWithinAt_iff]

protected alias ⟨UniqueDiffWithinAt.of_closure, UniqueDiffWithinAt.closure⟩ :=
  uniqueDiffWithinAt_closure

theorem UniqueDiffWithinAt.mono_nhds (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x ≤ 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 t x := by
  simp only [uniqueDiffWithinAt_iff] at *
  rw [mem_closure_iff_nhdsWithin_neBot] at h ⊢
  exact ⟨h.1.mono <| Submodule.span_mono <| tangentConeAt_mono_nhds st, h.2.mono st⟩

theorem UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ t) :
    UniqueDiffWithinAt 𝕜 t x :=
  h.mono_nhds <| nhdsWithin_mono _ st

theorem UniqueDiffWithinAt.mono_closure (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ closure t) :
    UniqueDiffWithinAt 𝕜 t x :=
  (h.mono st).of_closure

theorem uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x :=
  ⟨fun h => h.mono_nhds <| le_of_eq st, fun h => h.mono_nhds <| le_of_eq st.symm⟩

theorem uniqueDiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict' _ ht).symm

theorem UniqueDiffWithinAt.inter (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter ht).2 hs

theorem uniqueDiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict'' _ ht).symm

theorem UniqueDiffWithinAt.inter' (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter' ht).2 hs

theorem uniqueDiffWithinAt_of_mem_nhds (h : s ∈ 𝓝 x) : UniqueDiffWithinAt 𝕜 s x := by
  simpa only [univ_inter] using uniqueDiffWithinAt_univ.inter h

theorem IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds hs xs)

theorem UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsOpen t) : UniqueDiffOn 𝕜 (s ∩ t) :=
  fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)

theorem IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 𝕜 s :=
  fun _ hx => IsOpen.uniqueDiffWithinAt hs hx

/-- The product of two sets of unique differentiability at points `x` and `y` has unique
differentiability at `(x, y)`. -/
theorem UniqueDiffWithinAt.prod {t : Set F} {y : F} (hs : UniqueDiffWithinAt 𝕜 s x)
    (ht : UniqueDiffWithinAt 𝕜 t y) : UniqueDiffWithinAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [uniqueDiffWithinAt_iff] at hs ht ⊢
  rw [closure_prod_eq]
  refine ⟨?_, hs.2, ht.2⟩
  have : _ ≤ Submodule.span 𝕜 (tangentConeAt 𝕜 (s ×ˢ t) (x, y)) := Submodule.span_mono
    (union_subset (subset_tangentConeAt_prod_left ht.2) (subset_tangentConeAt_prod_right hs.2))
  rw [LinearMap.span_inl_union_inr, SetLike.le_def] at this
  exact (hs.1.prod ht.1).mono this

theorem UniqueDiffWithinAt.univ_pi (ι : Type*) [Finite ι] (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i)) (x : ∀ i, E i)
    (h : ∀ i, UniqueDiffWithinAt 𝕜 (s i) (x i)) : UniqueDiffWithinAt 𝕜 (Set.pi univ s) x := by
  classical
  simp only [uniqueDiffWithinAt_iff, closure_pi_set] at h ⊢
  refine ⟨(dense_pi univ fun i _ => (h i).1).mono ?_, fun i _ => (h i).2⟩
  norm_cast
  simp only [← Submodule.iSup_map_single, iSup_le_iff, LinearMap.map_span, Submodule.span_le,
    ← mapsTo']
  exact fun i => (mapsTo_tangentConeAt_pi fun j _ => (h j).2).mono Subset.rfl Submodule.subset_span

theorem UniqueDiffWithinAt.pi (ι : Type*) [Finite ι] (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i)) (x : ∀ i, E i)
    (I : Set ι) (h : ∀ i ∈ I, UniqueDiffWithinAt 𝕜 (s i) (x i)) :
    UniqueDiffWithinAt 𝕜 (Set.pi I s) x := by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi ι E _ _ fun i => ?_
  by_cases hi : i ∈ I <;> simp [*, uniqueDiffWithinAt_univ]

/-- The product of two sets of unique differentiability is a set of unique differentiability. -/
theorem UniqueDiffOn.prod {t : Set F} (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) :
    UniqueDiffOn 𝕜 (s ×ˢ t) :=
  fun ⟨x, y⟩ h => UniqueDiffWithinAt.prod (hs x h.1) (ht y h.2)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.pi (ι : Type*) [Finite ι] (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i)) (I : Set ι)
    (h : ∀ i ∈ I, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi I s) :=
  fun x hx => UniqueDiffWithinAt.pi _ _ _ _ _ fun i hi => h i hi (x i) (hx i hi)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.univ_pi (ι : Type*) [Finite ι] (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i))
    (h : ∀ i, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi univ s) :=
  UniqueDiffOn.pi _ _ _ _ fun i _ => h i

/--
Given `x ∈ s` and a field extension `𝕜 ⊆ 𝕜'`, the tangent cone of `s` at `x` with
respect to `𝕜` is contained in the tangent cone of `s` at `x` with respect to `𝕜'`.
-/
theorem tangentConeAt_mono_field : tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜' s x := by
  intro α hα
  simp only [tangentConeAt, eventually_atTop, ge_iff_le, tendsto_norm_atTop_iff_cobounded,
    mem_setOf_eq] at hα ⊢
  obtain ⟨c, d, ⟨a, h₁a⟩, h₁, h₂⟩ := hα
  use ((algebraMap 𝕜 𝕜') ∘ c), d
  constructor
  · use a
  · constructor
    · intro β hβ
      rw [mem_map, mem_atTop_sets]
      obtain ⟨n, hn⟩ := mem_atTop_sets.1
        (mem_map.1 (h₁ (algebraMap_cobounded_le_cobounded (𝕜 := 𝕜) (𝕜' := 𝕜') hβ)))
      use n, fun _ _ ↦ by simp_all
    · simpa

/--
Assume that `E` is a normed vector space over normed fields `𝕜 ⊆ 𝕜'` and that `x ∈ s` is a point
of unique differentiability with respect to the set `s` and the smaller field `𝕜`, then `x` is also
a point of unique differentiability with respect to the set `s` and the larger field `𝕜'`.
-/
theorem UniqueDiffWithinAt.mono_field (h₂s : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜' s x := by
  simp_all only [uniqueDiffWithinAt_iff, and_true]
  apply Dense.mono _ h₂s.1
  trans ↑(Submodule.span 𝕜 (tangentConeAt 𝕜' s x))
  <;> simp [Submodule.span_mono tangentConeAt_mono_field]

/--
Assume that `E` is a normed vector space over normed fields `𝕜 ⊆ 𝕜'` and all points of `s` are
points of unique differentiability with respect to the smaller field `𝕜`, then they are also points
of unique differentiability with respect to the larger field `𝕜`.
-/
theorem UniqueDiffOn.mono_field (h₂s : UniqueDiffOn 𝕜 s) :
    UniqueDiffOn 𝕜' s := fun x hx ↦ (h₂s x hx).mono_field

end Normed

section RealNormed
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability at every point of its closure. -/
theorem uniqueDiffWithinAt_convex {s : Set G} (conv : Convex ℝ s) (hs : (interior s).Nonempty)
    {x : G} (hx : x ∈ closure s) : UniqueDiffWithinAt ℝ s x := by
  rcases hs with ⟨y, hy⟩
  suffices y - x ∈ interior (tangentConeAt ℝ s x) by
    refine ⟨Dense.of_closure ?_, hx⟩
    simp [(Submodule.span ℝ (tangentConeAt ℝ s x)).eq_top_of_nonempty_interior'
        ⟨y - x, interior_mono Submodule.subset_span this⟩]
  rw [mem_interior_iff_mem_nhds]
  replace hy : interior s ∈ 𝓝 y := IsOpen.mem_nhds isOpen_interior hy
  apply mem_of_superset ((isOpenMap_sub_right x).image_mem_nhds hy)
  rintro _ ⟨z, zs, rfl⟩
  refine mem_tangentConeAt_of_openSegment_subset (Subset.trans ?_ interior_subset)
  exact conv.openSegment_closure_interior_subset_interior hx zs

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem uniqueDiffOn_convex {s : Set G} (conv : Convex ℝ s) (hs : (interior s).Nonempty) :
    UniqueDiffOn ℝ s :=
  fun _ xs => uniqueDiffWithinAt_convex conv hs (subset_closure xs)

end RealNormed

section Real

theorem uniqueDiffOn_Ici (a : ℝ) : UniqueDiffOn ℝ (Ici a) :=
  uniqueDiffOn_convex (convex_Ici a) <| by simp only [interior_Ici, nonempty_Ioi]

theorem uniqueDiffOn_Iic (a : ℝ) : UniqueDiffOn ℝ (Iic a) :=
  uniqueDiffOn_convex (convex_Iic a) <| by simp only [interior_Iic, nonempty_Iio]

theorem uniqueDiffOn_Ioi (a : ℝ) : UniqueDiffOn ℝ (Ioi a) :=
  isOpen_Ioi.uniqueDiffOn

theorem uniqueDiffOn_Iio (a : ℝ) : UniqueDiffOn ℝ (Iio a) :=
  isOpen_Iio.uniqueDiffOn

theorem uniqueDiffOn_Icc {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ (Icc a b) :=
  uniqueDiffOn_convex (convex_Icc a b) <| by simp only [interior_Icc, nonempty_Ioo, hab]

theorem uniqueDiffOn_Ico (a b : ℝ) : UniqueDiffOn ℝ (Ico a b) :=
  if hab : a < b then
    uniqueDiffOn_convex (convex_Ico a b) <| by simp only [interior_Ico, nonempty_Ioo, hab]
  else by simp only [Ico_eq_empty hab, uniqueDiffOn_empty]

theorem uniqueDiffOn_Ioc (a b : ℝ) : UniqueDiffOn ℝ (Ioc a b) :=
  if hab : a < b then
    uniqueDiffOn_convex (convex_Ioc a b) <| by simp only [interior_Ioc, nonempty_Ioo, hab]
  else by simp only [Ioc_eq_empty hab, uniqueDiffOn_empty]

theorem uniqueDiffOn_Ioo (a b : ℝ) : UniqueDiffOn ℝ (Ioo a b) :=
  isOpen_Ioo.uniqueDiffOn

/-- The real interval `[0, 1]` is a set of unique differentiability. -/
theorem uniqueDiffOn_Icc_zero_one : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) :=
  uniqueDiffOn_Icc zero_lt_one

theorem uniqueDiffWithinAt_Ioo {a b t : ℝ} (ht : t ∈ Set.Ioo a b) :
    UniqueDiffWithinAt ℝ (Set.Ioo a b) t :=
  IsOpen.uniqueDiffWithinAt isOpen_Ioo ht

theorem uniqueDiffWithinAt_Ioi (a : ℝ) : UniqueDiffWithinAt ℝ (Ioi a) a :=
  uniqueDiffWithinAt_convex (convex_Ioi a) (by simp) (by simp)

theorem uniqueDiffWithinAt_Iio (a : ℝ) : UniqueDiffWithinAt ℝ (Iio a) a :=
  uniqueDiffWithinAt_convex (convex_Iio a) (by simp) (by simp)

theorem uniqueDiffWithinAt_Ici (x : ℝ) : UniqueDiffWithinAt ℝ (Ici x) x :=
  (uniqueDiffWithinAt_Ioi x).mono Set.Ioi_subset_Ici_self

theorem uniqueDiffWithinAt_Iic (x : ℝ) : UniqueDiffWithinAt ℝ (Iic x) x :=
  (uniqueDiffWithinAt_Iio x).mono Set.Iio_subset_Iic_self

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

end Real

end UniqueDiff
