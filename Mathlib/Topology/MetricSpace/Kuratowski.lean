/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Topology.Sets.Compacts

#align_import topology.metric_space.kuratowski from "leanprover-community/mathlib"@"95d4f6586d313c8c28e00f36621d2a6a66893aa6"

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℕ, ℝ)`.
Any partially defined Lipschitz map into `ℓ^∞` can be extended to the whole space.

-/

set_option autoImplicit true


noncomputable section

set_option linter.uppercaseLean3 false

open Set Metric TopologicalSpace NNReal ENNReal lp Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace KuratowskiEmbedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℕ, ℝ) -/


variable {f g : ℓ^∞(ℕ)} {n : ℕ} {C : ℝ} [MetricSpace α] (x : ℕ → α) (a b : α)

/-- A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in `kuratowskiEmbedding`,
without density assumptions. -/
def embeddingOfSubset : ℓ^∞(ℕ) :=
  ⟨fun n => dist a (x n) - dist (x 0) (x n), by
    apply memℓp_infty
    -- ⊢ BddAbove (range fun i => ‖(fun n => dist a (x n) - dist (x 0) (x n)) i‖)
    use dist a (x 0)
    -- ⊢ dist a (x 0) ∈ upperBounds (range fun i => ‖(fun n => dist a (x n) - dist (x …
    rintro - ⟨n, rfl⟩
    -- ⊢ (fun i => ‖(fun n => dist a (x n) - dist (x 0) (x n)) i‖) n ≤ dist a (x 0)
    exact abs_dist_sub_le _ _ _⟩
    -- 🎉 no goals
#align Kuratowski_embedding.embedding_of_subset KuratowskiEmbedding.embeddingOfSubset

theorem embeddingOfSubset_coe : embeddingOfSubset x a n = dist a (x n) - dist (x 0) (x n) :=
  rfl
#align Kuratowski_embedding.embedding_of_subset_coe KuratowskiEmbedding.embeddingOfSubset_coe

/-- The embedding map is always a semi-contraction. -/
theorem embeddingOfSubset_dist_le (a b : α) :
    dist (embeddingOfSubset x a) (embeddingOfSubset x b) ≤ dist a b := by
  refine' lp.norm_le_of_forall_le dist_nonneg fun n => _
  -- ⊢ ‖↑(embeddingOfSubset x a - embeddingOfSubset x b) n‖ ≤ dist a b
  simp only [lp.coeFn_sub, Pi.sub_apply, embeddingOfSubset_coe, Real.dist_eq]
  -- ⊢ ‖dist a (x n) - dist (x 0) (x n) - (dist b (x n) - dist (x 0) (x n))‖ ≤ dist …
  convert abs_dist_sub_le a b (x n) using 2
  -- ⊢ dist a (x n) - dist (x 0) (x n) - (dist b (x n) - dist (x 0) (x n)) = dist a …
  ring
  -- 🎉 no goals
#align Kuratowski_embedding.embedding_of_subset_dist_le KuratowskiEmbedding.embeddingOfSubset_dist_le

/-- When the reference set is dense, the embedding map is an isometry on its image. -/
theorem embeddingOfSubset_isometry (H : DenseRange x) : Isometry (embeddingOfSubset x) := by
  refine' Isometry.of_dist_eq fun a b => _
  -- ⊢ dist (embeddingOfSubset x a) (embeddingOfSubset x b) = dist a b
  refine' (embeddingOfSubset_dist_le x a b).antisymm (le_of_forall_pos_le_add fun e epos => _)
  -- ⊢ dist a b ≤ dist (embeddingOfSubset x a) (embeddingOfSubset x b) + e
  -- First step: find n with dist a (x n) < e
  rcases Metric.mem_closure_range_iff.1 (H a) (e / 2) (half_pos epos) with ⟨n, hn⟩
  -- ⊢ dist a b ≤ dist (embeddingOfSubset x a) (embeddingOfSubset x b) + e
  -- Second step: use the norm control at index n to conclude
  have C : dist b (x n) - dist a (x n) = embeddingOfSubset x b n - embeddingOfSubset x a n := by
    simp only [embeddingOfSubset_coe, sub_sub_sub_cancel_right]
  have :=
    calc
      dist a b ≤ dist a (x n) + dist (x n) b := dist_triangle _ _ _
      _ = 2 * dist a (x n) + (dist b (x n) - dist a (x n)) := by simp [dist_comm]; ring
      _ ≤ 2 * dist a (x n) + |dist b (x n) - dist a (x n)| := by
        apply_rules [add_le_add_left, le_abs_self]
      _ ≤ 2 * (e / 2) + |embeddingOfSubset x b n - embeddingOfSubset x a n| := by
        rw [C]
        apply_rules [add_le_add, mul_le_mul_of_nonneg_left, hn.le, le_refl]
        norm_num
      _ ≤ 2 * (e / 2) + dist (embeddingOfSubset x b) (embeddingOfSubset x a) := by
        have : |embeddingOfSubset x b n - embeddingOfSubset x a n| ≤
            dist (embeddingOfSubset x b) (embeddingOfSubset x a) := by
          simp only [dist_eq_norm]
          exact lp.norm_apply_le_norm ENNReal.top_ne_zero
            (embeddingOfSubset x b - embeddingOfSubset x a) n
        nlinarith
      _ = dist (embeddingOfSubset x b) (embeddingOfSubset x a) + e := by ring
  simpa [dist_comm] using this
  -- 🎉 no goals
#align Kuratowski_embedding.embedding_of_subset_isometry KuratowskiEmbedding.embeddingOfSubset_isometry

/-- Every separable metric space embeds isometrically in `ℓ^∞(ℕ)`. -/
theorem exists_isometric_embedding (α : Type u) [MetricSpace α] [SeparableSpace α] :
    ∃ f : α → ℓ^∞(ℕ), Isometry f := by
  cases' (univ : Set α).eq_empty_or_nonempty with h h
  -- ⊢ ∃ f, Isometry f
  · use fun _ => 0; intro x; exact absurd h (Nonempty.ne_empty ⟨x, mem_univ x⟩)
    -- ⊢ Isometry fun x => 0
                    -- ⊢ ∀ (x2 : α), edist ((fun x => 0) x) ((fun x => 0) x2) = edist x x2
                             -- 🎉 no goals
  · -- We construct a map x : ℕ → α with dense image
    rcases h with ⟨basepoint⟩
    -- ⊢ ∃ f, Isometry f
    haveI : Inhabited α := ⟨basepoint⟩
    -- ⊢ ∃ f, Isometry f
    have : ∃ s : Set α, s.Countable ∧ Dense s := exists_countable_dense α
    -- ⊢ ∃ f, Isometry f
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩
    -- ⊢ ∃ f, Isometry f
    rcases Set.countable_iff_exists_subset_range.1 S_countable with ⟨x, x_range⟩
    -- ⊢ ∃ f, Isometry f
    -- Use embeddingOfSubset to construct the desired isometry
    exact ⟨embeddingOfSubset x, embeddingOfSubset_isometry x (S_dense.mono x_range)⟩
    -- 🎉 no goals
#align Kuratowski_embedding.exists_isometric_embedding KuratowskiEmbedding.exists_isometric_embedding

end KuratowskiEmbedding

open TopologicalSpace KuratowskiEmbedding

/-- The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℕ, ℝ)`.
-/
def kuratowskiEmbedding (α : Type u) [MetricSpace α] [SeparableSpace α] : α → ℓ^∞(ℕ) :=
  Classical.choose (KuratowskiEmbedding.exists_isometric_embedding α)
#align Kuratowski_embedding kuratowskiEmbedding

/--
The Kuratowski embedding is an isometry.
Theorem 2.1 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2015]. -/
protected theorem kuratowskiEmbedding.isometry (α : Type u) [MetricSpace α] [SeparableSpace α] :
    Isometry (kuratowskiEmbedding α) :=
  Classical.choose_spec (exists_isometric_embedding α)
#align Kuratowski_embedding.isometry kuratowskiEmbedding.isometry

/-- Version of the Kuratowski embedding for nonempty compacts -/
nonrec def NonemptyCompacts.kuratowskiEmbedding (α : Type u) [MetricSpace α] [CompactSpace α]
    [Nonempty α] : NonemptyCompacts ℓ^∞(ℕ) where
  carrier := range (kuratowskiEmbedding α)
  isCompact' := isCompact_range (kuratowskiEmbedding.isometry α).continuous
  nonempty' := range_nonempty _
#align nonempty_compacts.Kuratowski_embedding NonemptyCompacts.kuratowskiEmbedding

/--
A function `f : α → ℓ^∞(ι, ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space.

Theorem 2.2 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2015]

The same result for the case of a finite type `ι` is implemented in
`LipschitzOnWith.extend_pi`.
-/
theorem LipschitzOnWith.extend_lp_infty [PseudoMetricSpace α] {s : Set α} {f : α → ℓ^∞(ι)}
    {K : ℝ≥0} (hfl : LipschitzOnWith K f s): ∃ g : α → ℓ^∞(ι), LipschitzWith K g ∧ EqOn f g s := by
  -- Construct the coordinate-wise extensions
  rw [LipschitzOnWith.coordinate] at hfl
  -- ⊢ ∃ g, LipschitzWith K g ∧ EqOn f g s
  have : ∀ i : ι, ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s
  -- ⊢ ∀ (i : ι), ∃ g, LipschitzWith K g ∧ EqOn (fun x => ↑(f x) i) g s
  · intro i
    -- ⊢ ∃ g, LipschitzWith K g ∧ EqOn (fun x => ↑(f x) i) g s
    exact LipschitzOnWith.extend_real (hfl i) -- use the nonlinear Hahn-Banach theorem here!
    -- 🎉 no goals
  choose g hgl hgeq using this
  -- ⊢ ∃ g, LipschitzWith K g ∧ EqOn f g s
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀_in_s⟩
  -- ⊢ ∃ g, LipschitzWith K g ∧ EqOn f g ∅
  · exact ⟨0, LipschitzWith.const' 0, by simp⟩
    -- 🎉 no goals
  · -- Show that the extensions are uniformly bounded
    have hf_extb : ∀ a : α, Memℓp (swap g a) ∞
    -- ⊢ ∀ (a : α), Memℓp (swap g a) ⊤
    · apply LipschitzWith.uniformly_bounded (swap g) hgl a₀
      -- ⊢ Memℓp (swap g a₀) ⊤
      use ‖f a₀‖
      -- ⊢ ‖f a₀‖ ∈ upperBounds (range fun i => ‖swap g a₀ i‖)
      rintro - ⟨i, rfl⟩
      -- ⊢ (fun i => ‖swap g a₀ i‖) i ≤ ‖f a₀‖
      simp_rw [←hgeq i ha₀_in_s]
      -- ⊢ ‖↑(f a₀) i‖ ≤ ‖f a₀‖
      exact lp.norm_apply_le_norm top_ne_zero (f a₀) i
      -- 🎉 no goals
    -- Construct witness by bundling the function with its certificate of membership in ℓ^∞
    let f_ext' : α → ℓ^∞(ι) := fun i ↦ ⟨swap g i, hf_extb i⟩
    -- ⊢ ∃ g, LipschitzWith K g ∧ EqOn f g s
    refine ⟨f_ext', ?_, ?_⟩
    -- ⊢ LipschitzWith K f_ext'
    · rw [LipschitzWith.coordinate]
      -- ⊢ ∀ (i : ι), LipschitzWith K fun a => ↑(f_ext' a) i
      exact hgl
      -- 🎉 no goals
    · intro a hyp
      -- ⊢ f a = f_ext' a
      ext i
      -- ⊢ ↑(f a) i = ↑(f_ext' a) i
      exact (hgeq i) hyp
      -- 🎉 no goals
