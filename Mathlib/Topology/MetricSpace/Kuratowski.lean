/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Sets.Compacts

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℕ, ℝ)`.
Any partially defined Lipschitz map into `ℓ^∞` can be extended to the whole space.

-/

noncomputable section


open Set Metric TopologicalSpace NNReal ENNReal lp Function

universe u

variable {α : Type u}

namespace KuratowskiEmbedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℕ, ℝ) -/


variable {n : ℕ} [MetricSpace α] (x : ℕ → α) (a : α)

/-- A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in `kuratowskiEmbedding`,
without density assumptions. -/
def embeddingOfSubset : ℓ^∞(ℕ) :=
  ⟨fun n => dist a (x n) - dist (x 0) (x n), by
    apply memℓp_infty
    use dist a (x 0)
    rintro - ⟨n, rfl⟩
    exact abs_dist_sub_le _ _ _⟩

theorem embeddingOfSubset_coe : embeddingOfSubset x a n = dist a (x n) - dist (x 0) (x n) :=
  rfl

/-- The embedding map is always a semi-contraction. -/
theorem embeddingOfSubset_dist_le (a b : α) :
    dist (embeddingOfSubset x a) (embeddingOfSubset x b) ≤ dist a b := by
  refine lp.norm_le_of_forall_le dist_nonneg fun n => ?_
  simp only [lp.coeFn_sub, Pi.sub_apply, embeddingOfSubset_coe]
  convert abs_dist_sub_le a b (x n) using 2
  ring

/-- When the reference set is dense, the embedding map is an isometry on its image. -/
theorem embeddingOfSubset_isometry (H : DenseRange x) : Isometry (embeddingOfSubset x) := by
  refine Isometry.of_dist_eq fun a b => ?_
  refine (embeddingOfSubset_dist_le x a b).antisymm (le_of_forall_pos_le_add fun e epos => ?_)
  -- First step: find n with dist a (x n) < e
  rcases Metric.mem_closure_range_iff.1 (H a) (e / 2) (half_pos epos) with ⟨n, hn⟩
  -- Second step: use the norm control at index n to conclude
  have C : dist b (x n) - dist a (x n) = embeddingOfSubset x b n - embeddingOfSubset x a n := by
    simp only [embeddingOfSubset_coe, sub_sub_sub_cancel_right]
  have :=
    calc
      dist a b ≤ dist a (x n) + dist (x n) b := dist_triangle _ _ _
      _ = 2 * dist a (x n) + (dist b (x n) - dist a (x n)) := by simp [dist_comm]; ring
      _ ≤ 2 * dist a (x n) + |dist b (x n) - dist a (x n)| := by grw [← le_abs_self]
      _ ≤ 2 * (e / 2) + |embeddingOfSubset x b n - embeddingOfSubset x a n| := by
        rw [C]
        gcongr
      _ ≤ 2 * (e / 2) + dist (embeddingOfSubset x b) (embeddingOfSubset x a) := by
        gcongr
        simp only [dist_eq_norm]
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero
          (embeddingOfSubset x b - embeddingOfSubset x a) n
      _ = dist (embeddingOfSubset x b) (embeddingOfSubset x a) + e := by ring
  simpa [dist_comm] using this

/-- Every separable metric space embeds isometrically in `ℓ^∞(ℕ)`. -/
theorem exists_isometric_embedding (α : Type u) [MetricSpace α] [SeparableSpace α] :
    ∃ f : α → ℓ^∞(ℕ), Isometry f := by
  rcases (univ : Set α).eq_empty_or_nonempty with h | h
  · use fun _ => 0; intro x; exact absurd h (Nonempty.ne_empty ⟨x, mem_univ x⟩)
  · -- We construct a map x : ℕ → α with dense image
    rcases h with ⟨basepoint⟩
    haveI : Inhabited α := ⟨basepoint⟩
    have : ∃ s : Set α, s.Countable ∧ Dense s := exists_countable_dense α
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩
    rcases Set.countable_iff_exists_subset_range.1 S_countable with ⟨x, x_range⟩
    -- Use embeddingOfSubset to construct the desired isometry
    exact ⟨embeddingOfSubset x, embeddingOfSubset_isometry x (S_dense.mono x_range)⟩

end KuratowskiEmbedding

open KuratowskiEmbedding

/-- The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℕ, ℝ)`.
-/
def kuratowskiEmbedding (α : Type u) [MetricSpace α] [SeparableSpace α] : α → ℓ^∞(ℕ) :=
  Classical.choose (KuratowskiEmbedding.exists_isometric_embedding α)

/--
The Kuratowski embedding is an isometry.
Theorem 2.1 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2015]. -/
protected theorem kuratowskiEmbedding.isometry (α : Type u) [MetricSpace α] [SeparableSpace α] :
    Isometry (kuratowskiEmbedding α) :=
  Classical.choose_spec (exists_isometric_embedding α)

/-- Version of the Kuratowski embedding for nonempty compacts -/
nonrec def NonemptyCompacts.kuratowskiEmbedding (α : Type u) [MetricSpace α] [CompactSpace α]
    [Nonempty α] : NonemptyCompacts ℓ^∞(ℕ) where
  carrier := range (kuratowskiEmbedding α)
  isCompact' := isCompact_range (kuratowskiEmbedding.isometry α).continuous
  nonempty' := range_nonempty _

/--
A function `f : α → ℓ^∞(ι, ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space.

Theorem 2.2 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2015]

The same result for the case of a finite type `ι` is implemented in
`LipschitzOnWith.extend_pi`.
-/
theorem LipschitzOnWith.extend_lp_infty [PseudoMetricSpace α] {s : Set α} {ι : Type*}
    {f : α → ℓ^∞(ι)} {K : ℝ≥0} (hfl : LipschitzOnWith K f s) :
    ∃ g : α → ℓ^∞(ι), LipschitzWith K g ∧ EqOn f g s := by
  -- Construct the coordinate-wise extensions
  rw [LipschitzOnWith.coordinate] at hfl
  have (i : ι) : ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s :=
    LipschitzOnWith.extend_real (hfl i) -- use the nonlinear Hahn-Banach theorem here!
  choose g hgl hgeq using this
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀_in_s⟩
  · exact ⟨0, LipschitzWith.const' 0, by simp⟩
  · -- Show that the extensions are uniformly bounded
    have hf_extb : ∀ a : α, Memℓp (swap g a) ∞ := by
      apply LipschitzWith.uniformly_bounded (swap g) hgl a₀
      use ‖f a₀‖
      rintro - ⟨i, rfl⟩
      simp_rw [← hgeq i ha₀_in_s]
      exact lp.norm_apply_le_norm top_ne_zero (f a₀) i
    -- Construct witness by bundling the function with its certificate of membership in ℓ^∞
    let f_ext' : α → ℓ^∞(ι) := fun i ↦ ⟨swap g i, hf_extb i⟩
    refine ⟨f_ext', ?_, ?_⟩
    · rw [LipschitzWith.coordinate]
      exact hgl
    · intro a hyp
      ext i
      exact (hgeq i) hyp
