/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Intervals.IsoIoo
import Mathlib.Topology.Algebra.Order.MonotoneContinuity
import Mathlib.Topology.UrysohnsBounded

#align_import topology.tietze_extension from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Tietze extension theorem

In this file we prove a few version of the Tietze extension theorem. The theorem says that a
continuous function `s → ℝ` defined on a closed set in a normal topological space `Y` can be
extended to a continuous function on the whole space. Moreover, if all values of the original
function belong to some (finite or infinite, open or closed) interval, then the extension can be
chosen so that it takes values in the same interval. In particular, if the original function is a
bounded function, then there exists a bounded extension of the same norm.

The proof mostly follows <https://ncatlab.org/nlab/show/Tietze+extension+theorem>. We patch a small
gap in the proof for unbounded functions, see
`exists_extension_forall_exists_le_ge_of_closedEmbedding`.

## Implementation notes

We first prove the theorems for a closed embedding `e : X → Y` of a topological space into a normal
topological space, then specialize them to the case `X = s : Set Y`, `e = (↑)`.

## Tags

Tietze extension theorem, Urysohn's lemma, normal topological space
-/


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace Y]

open Metric Set Filter

open BoundedContinuousFunction Topology

noncomputable section

namespace BoundedContinuousFunction

/-- One step in the proof of the Tietze extension theorem. If `e : C(X, Y)` is a closed embedding
of a topological space into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous
function, then there exists a bounded continuous function `g : Y →ᵇ ℝ` of the norm `‖g‖ ≤ ‖f‖ / 3`
such that the distance between `g ∘ e` and `f` is at most `(2 / 3) * ‖f‖`. -/
theorem tietze_extension_step (f : X →ᵇ ℝ) (e : C(X, Y)) (he : ClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, ‖g‖ ≤ ‖f‖ / 3 ∧ dist (g.compContinuous e) f ≤ 2 / 3 * ‖f‖ := by
  have h3 : (0 : ℝ) < 3 := by norm_num1
  -- ⊢ ∃ g, ‖g‖ ≤ ‖f‖ / 3 ∧ dist (compContinuous g e) f ≤ 2 / 3 * ‖f‖
  have h23 : 0 < (2 / 3 : ℝ) := by norm_num1
  -- ⊢ ∃ g, ‖g‖ ≤ ‖f‖ / 3 ∧ dist (compContinuous g e) f ≤ 2 / 3 * ‖f‖
  -- In the trivial case `f = 0`, we take `g = 0`
  rcases eq_or_ne f 0 with (rfl | hf)
  -- ⊢ ∃ g, ‖g‖ ≤ ‖0‖ / 3 ∧ dist (compContinuous g e) 0 ≤ 2 / 3 * ‖0‖
  · use 0
    -- ⊢ ‖0‖ ≤ ‖0‖ / 3 ∧ dist (compContinuous 0 e) 0 ≤ 2 / 3 * ‖0‖
    simp
    -- 🎉 no goals
  replace hf : 0 < ‖f‖ := norm_pos_iff.2 hf
  -- ⊢ ∃ g, ‖g‖ ≤ ‖f‖ / 3 ∧ dist (compContinuous g e) f ≤ 2 / 3 * ‖f‖
  /- Otherwise, the closed sets `e '' (f ⁻¹' (Iic (-‖f‖ / 3)))` and `e '' (f ⁻¹' (Ici (‖f‖ / 3)))`
    are disjoint, hence by Urysohn's lemma there exists a function `g` that is equal to `-‖f‖ / 3`
    on the former set and is equal to `‖f‖ / 3` on the latter set. This function `g` satisfies the
    assertions of the lemma. -/
  have hf3 : -‖f‖ / 3 < ‖f‖ / 3 := (div_lt_div_right h3).2 (Left.neg_lt_self hf)
  -- ⊢ ∃ g, ‖g‖ ≤ ‖f‖ / 3 ∧ dist (compContinuous g e) f ≤ 2 / 3 * ‖f‖
  have hc₁ : IsClosed (e '' (f ⁻¹' Iic (-‖f‖ / 3))) :=
    he.isClosedMap _ (isClosed_Iic.preimage f.continuous)
  have hc₂ : IsClosed (e '' (f ⁻¹' Ici (‖f‖ / 3))) :=
    he.isClosedMap _ (isClosed_Ici.preimage f.continuous)
  have hd : Disjoint (e '' (f ⁻¹' Iic (-‖f‖ / 3))) (e '' (f ⁻¹' Ici (‖f‖ / 3))) := by
    refine' disjoint_image_of_injective he.inj (Disjoint.preimage _ _)
    rwa [Iic_disjoint_Ici, not_le]
  rcases exists_bounded_mem_Icc_of_closed_of_le hc₁ hc₂ hd hf3.le with ⟨g, hg₁, hg₂, hgf⟩
  -- ⊢ ∃ g, ‖g‖ ≤ ‖f‖ / 3 ∧ dist (compContinuous g e) f ≤ 2 / 3 * ‖f‖
  refine' ⟨g, _, _⟩
  -- ⊢ ‖g‖ ≤ ‖f‖ / 3
  · refine' (norm_le <| div_nonneg hf.le h3.le).mpr fun y => _
    -- ⊢ ‖↑g y‖ ≤ ‖f‖ / 3
    simpa [abs_le, neg_div] using hgf y
    -- 🎉 no goals
  · refine' (dist_le <| mul_nonneg h23.le hf.le).mpr fun x => _
    -- ⊢ dist (↑(compContinuous g e) x) (↑f x) ≤ 2 / 3 * ‖f‖
    have hfx : -‖f‖ ≤ f x ∧ f x ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs, abs_le] using f.norm_coe_le_norm x
    cases' le_total (f x) (-‖f‖ / 3) with hle₁ hle₁
    -- ⊢ dist (↑(compContinuous g e) x) (↑f x) ≤ 2 / 3 * ‖f‖
    · calc
        |g (e x) - f x| = -‖f‖ / 3 - f x := by
          rw [hg₁ (mem_image_of_mem _ hle₁), Function.const_apply,
            abs_of_nonneg (sub_nonneg.2 hle₁)]
        _ ≤ 2 / 3 * ‖f‖ := by linarith
    · cases' le_total (f x) (‖f‖ / 3) with hle₂ hle₂
      -- ⊢ dist (↑(compContinuous g e) x) (↑f x) ≤ 2 / 3 * ‖f‖
      · simp only [neg_div] at *
        -- ⊢ dist (↑(compContinuous g e) x) (↑f x) ≤ 2 / 3 * ‖f‖
        calc
          dist (g (e x)) (f x) ≤ |g (e x)| + |f x| := dist_le_norm_add_norm _ _
          _ ≤ ‖f‖ / 3 + ‖f‖ / 3 := (add_le_add (abs_le.2 <| hgf _) (abs_le.2 ⟨hle₁, hle₂⟩))
          _ = 2 / 3 * ‖f‖ := by linarith
      · calc
          |g (e x) - f x| = f x - ‖f‖ / 3 := by
            rw [hg₂ (mem_image_of_mem _ hle₂), abs_sub_comm, Function.const_apply,
              abs_of_nonneg (sub_nonneg.2 hle₂)]
          _ ≤ 2 / 3 * ‖f‖ := by linarith
#align bounded_continuous_function.tietze_extension_step BoundedContinuousFunction.tietze_extension_step

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and bundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
theorem exists_extension_norm_eq_of_closedEmbedding' (f : X →ᵇ ℝ) (e : C(X, Y))
    (he : ClosedEmbedding e) : ∃ g : Y →ᵇ ℝ, ‖g‖ = ‖f‖ ∧ g.compContinuous e = f := by
  /- For the proof, we iterate `tietze_extension_step`. Each time we apply it to the difference
    between the previous approximation and `f`. -/
  choose F hF_norm hF_dist using fun f : X →ᵇ ℝ => tietze_extension_step f e he
  -- ⊢ ∃ g, ‖g‖ = ‖f‖ ∧ compContinuous g e = f
  set g : ℕ → Y →ᵇ ℝ := fun n => (fun g => g + F (f - g.compContinuous e))^[n] 0
  -- ⊢ ∃ g, ‖g‖ = ‖f‖ ∧ compContinuous g e = f
  have g0 : g 0 = 0 := rfl
  -- ⊢ ∃ g, ‖g‖ = ‖f‖ ∧ compContinuous g e = f
  have g_succ : ∀ n, g (n + 1) = g n + F (f - (g n).compContinuous e) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have hgf : ∀ n, dist ((g n).compContinuous e) f ≤ (2 / 3) ^ n * ‖f‖ := by
    intro n
    induction' n with n ihn
    · simp [g0]
    · rw [g_succ n, add_compContinuous, ← dist_sub_right, add_sub_cancel', pow_succ, mul_assoc]
      refine' (hF_dist _).trans (mul_le_mul_of_nonneg_left _ (by norm_num1))
      rwa [← dist_eq_norm']
  have hg_dist : ∀ n, dist (g n) (g (n + 1)) ≤ 1 / 3 * ‖f‖ * (2 / 3) ^ n := by
    intro n
    calc
      dist (g n) (g (n + 1)) = ‖F (f - (g n).compContinuous e)‖ := by
        rw [g_succ, dist_eq_norm', add_sub_cancel']
      _ ≤ ‖f - (g n).compContinuous e‖ / 3 := (hF_norm _)
      _ = 1 / 3 * dist ((g n).compContinuous e) f := by rw [dist_eq_norm', one_div, div_eq_inv_mul]
      _ ≤ 1 / 3 * ((2 / 3) ^ n * ‖f‖) := (mul_le_mul_of_nonneg_left (hgf n) (by norm_num1))
      _ = 1 / 3 * ‖f‖ * (2 / 3) ^ n := by ac_rfl
  have hg_cau : CauchySeq g := cauchySeq_of_le_geometric _ _ (by norm_num1) hg_dist
  -- ⊢ ∃ g, ‖g‖ = ‖f‖ ∧ compContinuous g e = f
  have :
    Tendsto (fun n => (g n).compContinuous e) atTop
      (𝓝 <| (limUnder atTop g).compContinuous e) :=
    ((continuous_compContinuous e).tendsto _).comp hg_cau.tendsto_limUnder
  have hge : (limUnder atTop g).compContinuous e = f := by
    refine' tendsto_nhds_unique this (tendsto_iff_dist_tendsto_zero.2 _)
    refine' squeeze_zero (fun _ => dist_nonneg) hgf _
    rw [← zero_mul ‖f‖]
    refine' (tendsto_pow_atTop_nhds_0_of_lt_1 _ _).mul tendsto_const_nhds <;> norm_num1
  refine' ⟨limUnder atTop g, le_antisymm _ _, hge⟩
  -- ⊢ ‖limUnder atTop g‖ ≤ ‖f‖
  · rw [← dist_zero_left, ← g0]
    -- ⊢ dist (g 0) (limUnder atTop g) ≤ ‖f‖
    refine'
      (dist_le_of_le_geometric_of_tendsto₀ _ _ (by norm_num1)
        hg_dist hg_cau.tendsto_limUnder).trans_eq _
    field_simp [show (3 - 2 : ℝ) = 1 by norm_num1]
    -- 🎉 no goals
  · rw [← hge]
    -- ⊢ ‖compContinuous (limUnder atTop g) e‖ ≤ ‖limUnder atTop g‖
    exact norm_compContinuous_le _ _
    -- 🎉 no goals
#align bounded_continuous_function.exists_extension_norm_eq_of_closed_embedding' BoundedContinuousFunction.exists_extension_norm_eq_of_closedEmbedding'

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and unbundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
theorem exists_extension_norm_eq_of_closedEmbedding (f : X →ᵇ ℝ) {e : X → Y}
    (he : ClosedEmbedding e) : ∃ g : Y →ᵇ ℝ, ‖g‖ = ‖f‖ ∧ g ∘ e = f := by
  rcases exists_extension_norm_eq_of_closedEmbedding' f ⟨e, he.continuous⟩ he with ⟨g, hg, rfl⟩
  -- ⊢ ∃ g_1, ‖g_1‖ = ‖compContinuous g (ContinuousMap.mk e)‖ ∧ ↑g_1 ∘ e = ↑(compCo …
  exact ⟨g, hg, rfl⟩
  -- 🎉 no goals
#align bounded_continuous_function.exists_extension_norm_eq_of_closed_embedding BoundedContinuousFunction.exists_extension_norm_eq_of_closedEmbedding

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
set. If `f` is a bounded continuous real-valued function defined on a closed set in a normal
topological space, then it can be extended to a bounded continuous function of the same norm defined
on the whole space. -/
theorem exists_norm_eq_restrict_eq_of_closed {s : Set Y} (f : s →ᵇ ℝ) (hs : IsClosed s) :
    ∃ g : Y →ᵇ ℝ, ‖g‖ = ‖f‖ ∧ g.restrict s = f :=
  exists_extension_norm_eq_of_closedEmbedding' f ((ContinuousMap.id _).restrict s)
    (closedEmbedding_subtype_val hs)
#align bounded_continuous_function.exists_norm_eq_restrict_eq_of_closed BoundedContinuousFunction.exists_norm_eq_restrict_eq_of_closed

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding and a bounded continuous function that takes values in a non-trivial closed interval.
See also `exists_extension_forall_mem_of_closedEmbedding` for a more general statement that works
for any interval (finite or infinite, open or closed).

If `e : X → Y` is a closed embedding and `f : X →ᵇ ℝ` is a bounded continuous function such that
`f x ∈ [a, b]` for all `x`, where `a ≤ b`, then there exists a bounded continuous function
`g : Y →ᵇ ℝ` such that `g y ∈ [a, b]` for all `y` and `g ∘ e = f`. -/
theorem exists_extension_forall_mem_Icc_of_closedEmbedding (f : X →ᵇ ℝ) {a b : ℝ} {e : X → Y}
    (hf : ∀ x, f x ∈ Icc a b) (hle : a ≤ b) (he : ClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ Icc a b) ∧ g ∘ e = f := by
  rcases exists_extension_norm_eq_of_closedEmbedding (f - const X ((a + b) / 2)) he with
    ⟨g, hgf, hge⟩
  refine' ⟨const Y ((a + b) / 2) + g, fun y => _, _⟩
  -- ⊢ ↑(const Y ((a + b) / 2) + g) y ∈ Icc a b
  · suffices ‖f - const X ((a + b) / 2)‖ ≤ (b - a) / 2 by
      simpa [Real.Icc_eq_closedBall, add_mem_closedBall_iff_norm] using
        (norm_coe_le_norm g y).trans (hgf.trans_le this)
    refine' (norm_le <| div_nonneg (sub_nonneg.2 hle) zero_le_two).2 fun x => _
    -- ⊢ ‖↑(f - const X ((a + b) / 2)) x‖ ≤ (b - a) / 2
    simpa only [Real.Icc_eq_closedBall] using hf x
    -- 🎉 no goals
  · ext x
    -- ⊢ (↑(const Y ((a + b) / 2) + g) ∘ e) x = ↑f x
    have : g (e x) = f x - (a + b) / 2 := congr_fun hge x
    -- ⊢ (↑(const Y ((a + b) / 2) + g) ∘ e) x = ↑f x
    simp [this]
    -- 🎉 no goals
#align bounded_continuous_function.exists_extension_forall_mem_Icc_of_closed_embedding BoundedContinuousFunction.exists_extension_forall_mem_Icc_of_closedEmbedding

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a bounded continuous real-valued function on `X`. Then there
exists a bounded continuous function `g : Y →ᵇ ℝ` such that `g ∘ e = f` and each value `g y` belongs
to a closed interval `[f x₁, f x₂]` for some `x₁` and `x₂`.  -/
theorem exists_extension_forall_exists_le_ge_of_closedEmbedding [Nonempty X] (f : X →ᵇ ℝ)
    {e : X → Y} (he : ClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, (∀ y, ∃ x₁ x₂, g y ∈ Icc (f x₁) (f x₂)) ∧ g ∘ e = f := by
  inhabit X
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  -- Put `a = ⨅ x, f x` and `b = ⨆ x, f x`
  obtain ⟨a, ha⟩ : ∃ a, IsGLB (range f) a
  -- ⊢ ∃ a, IsGLB (range ↑f) a
  exact ⟨_, isGLB_ciInf (Real.bounded_iff_bddBelow_bddAbove.1 f.bounded_range).1⟩
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  obtain ⟨b, hb⟩ : ∃ b, IsLUB (range f) b
  -- ⊢ ∃ b, IsLUB (range ↑f) b
  exact ⟨_, isLUB_ciSup (Real.bounded_iff_bddBelow_bddAbove.1 f.bounded_range).2⟩
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  -- Then `f x ∈ [a, b]` for all `x`
  have hmem : ∀ x, f x ∈ Icc a b := fun x => ⟨ha.1 ⟨x, rfl⟩, hb.1 ⟨x, rfl⟩⟩
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  -- Rule out the trivial case `a = b`
  have hle : a ≤ b := (hmem default).1.trans (hmem default).2
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  rcases hle.eq_or_lt with (rfl | hlt)
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  · have : ∀ x, f x = a := by simpa using hmem
    -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
    use const Y a
    -- ⊢ (∀ (y : Y), ∃ x₁ x₂, ↑(const Y a) y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑(const Y a) ∘  …
    simp [this, Function.funext_iff]
    -- 🎉 no goals
  -- Put `c = (a + b) / 2`. Then `a < c < b` and `c - a = b - c`.
  set c := (a + b) / 2
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  have hac : a < c := left_lt_add_div_two.2 hlt
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  have hcb : c < b := add_div_two_lt_right.2 hlt
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  have hsub : c - a = b - c := by
    field_simp
    ring
  /- Due to `exists_extension_forall_mem_Icc_of_closedEmbedding`, there exists an extension `g`
    such that `g y ∈ [a, b]` for all `y`. However, if `a` and/or `b` do not belong to the range of
    `f`, then we need to ensure that these points do not belong to the range of `g`. This is done
    in two almost identical steps. First we deal with the case `∀ x, f x ≠ a`. -/
  obtain ⟨g, hg_mem, hgf⟩ : ∃ g : Y →ᵇ ℝ, (∀ y, ∃ x, g y ∈ Icc (f x) b) ∧ g ∘ e = f := by
    rcases exists_extension_forall_mem_Icc_of_closedEmbedding f hmem hle he with ⟨g, hg_mem, hgf⟩
    -- If `a ∈ range f`, then we are done.
    rcases em (∃ x, f x = a) with (⟨x, rfl⟩ | ha')
    · exact ⟨g, fun y => ⟨x, hg_mem _⟩, hgf⟩
    /- Otherwise, `g ⁻¹' {a}` is disjoint with `range e ∪ g ⁻¹' (Ici c)`, hence there exists a
        function `dg : Y → ℝ` such that `dg ∘ e = 0`, `dg y = 0` whenever `c ≤ g y`, `dg y = c - a`
        whenever `g y = a`, and `0 ≤ dg y ≤ c - a` for all `y`.  -/
    have hd : Disjoint (range e ∪ g ⁻¹' Ici c) (g ⁻¹' {a}) := by
      refine' disjoint_union_left.2 ⟨_, Disjoint.preimage _ _⟩
      · rw [Set.disjoint_left]
        rintro _ ⟨x, rfl⟩ (rfl : g (e x) = a)
        exact ha' ⟨x, (congr_fun hgf x).symm⟩
      · exact Set.disjoint_singleton_right.2 hac.not_le
    rcases exists_bounded_mem_Icc_of_closed_of_le
        (he.closed_range.union <| isClosed_Ici.preimage g.continuous)
        (isClosed_singleton.preimage g.continuous) hd (sub_nonneg.2 hac.le) with
      ⟨dg, dg0, dga, dgmem⟩
    replace hgf : ∀ x, (g + dg) (e x) = f x
    · intro x
      simp [dg0 (Or.inl <| mem_range_self _), ← hgf]
    refine' ⟨g + dg, fun y => _, funext hgf⟩
    · have hay : a < (g + dg) y := by
        rcases(hg_mem y).1.eq_or_lt with (rfl | hlt)
        · refine' (lt_add_iff_pos_right _).2 _
          calc
            0 < c - g y := sub_pos.2 hac
            _ = dg y := (dga rfl).symm
        · exact hlt.trans_le ((le_add_iff_nonneg_right _).2 <| (dgmem y).1)
      rcases ha.exists_between hay with ⟨_, ⟨x, rfl⟩, _, hxy⟩
      refine' ⟨x, hxy.le, _⟩
      cases' le_total c (g y) with hc hc
      · simp [dg0 (Or.inr hc), (hg_mem y).2]
      · calc
          g y + dg y ≤ c + (c - a) := add_le_add hc (dgmem _).2
          _ = b := by rw [hsub, add_sub_cancel'_right]
  /- Now we deal with the case `∀ x, f x ≠ b`. The proof is the same as in the first case, with
    minor modifications that make it hard to deduplicate code. -/
  choose xl hxl hgb using hg_mem
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  rcases em (∃ x, f x = b) with (⟨x, rfl⟩ | hb')
  -- ⊢ ∃ g, (∀ (y : Y), ∃ x₁ x₂, ↑g y ∈ Icc (↑f x₁) (↑f x₂)) ∧ ↑g ∘ e = ↑f
  · exact ⟨g, fun y => ⟨xl y, x, hxl y, hgb y⟩, hgf⟩
    -- 🎉 no goals
  have hd : Disjoint (range e ∪ g ⁻¹' Iic c) (g ⁻¹' {b}) := by
    refine' disjoint_union_left.2 ⟨_, Disjoint.preimage _ _⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨x, rfl⟩ (rfl : g (e x) = b)
      exact hb' ⟨x, (congr_fun hgf x).symm⟩
    · exact Set.disjoint_singleton_right.2 hcb.not_le
  rcases exists_bounded_mem_Icc_of_closed_of_le
      (he.closed_range.union <| isClosed_Iic.preimage g.continuous)
      (isClosed_singleton.preimage g.continuous) hd (sub_nonneg.2 hcb.le) with
    ⟨dg, dg0, dgb, dgmem⟩
  replace hgf : ∀ x, (g - dg) (e x) = f x
  -- ⊢ ∀ (x : X), ↑(g - dg) (e x) = ↑f x
  · intro x
    -- ⊢ ↑(g - dg) (e x) = ↑f x
    simp [dg0 (Or.inl <| mem_range_self _), ← hgf]
    -- 🎉 no goals
  refine' ⟨g - dg, fun y => _, funext hgf⟩
  -- ⊢ ∃ x₁ x₂, ↑(g - dg) y ∈ Icc (↑f x₁) (↑f x₂)
  · have hyb : (g - dg) y < b := by
      rcases(hgb y).eq_or_lt with (rfl | hlt)
      · refine' (sub_lt_self_iff _).2 _
        calc
          0 < g y - c := sub_pos.2 hcb
          _ = dg y := (dgb rfl).symm
      · exact ((sub_le_self_iff _).2 (dgmem _).1).trans_lt hlt
    rcases hb.exists_between hyb with ⟨_, ⟨xu, rfl⟩, hyxu, _⟩
    -- ⊢ ∃ x₁ x₂, ↑(g - dg) y ∈ Icc (↑f x₁) (↑f x₂)
    cases' lt_or_le c (g y) with hc hc
    -- ⊢ ∃ x₁ x₂, ↑(g - dg) y ∈ Icc (↑f x₁) (↑f x₂)
    · rcases em (a ∈ range f) with (⟨x, rfl⟩ | _)
      -- ⊢ ∃ x₁ x₂, ↑(g - dg) y ∈ Icc (↑f x₁) (↑f x₂)
      · refine' ⟨x, xu, _, hyxu.le⟩
        -- ⊢ ↑f x ≤ ↑(g - dg) y
        calc
          f x = c - (b - c) := by rw [← hsub, sub_sub_cancel]
          _ ≤ g y - dg y := sub_le_sub hc.le (dgmem _).2
      · have hay : a < (g - dg) y := by
          calc
            a = c - (b - c) := by rw [← hsub, sub_sub_cancel]
            _ < g y - (b - c) := (sub_lt_sub_right hc _)
            _ ≤ g y - dg y := sub_le_sub_left (dgmem _).2 _
        rcases ha.exists_between hay with ⟨_, ⟨x, rfl⟩, _, hxy⟩
        -- ⊢ ∃ x₁ x₂, ↑(g - dg) y ∈ Icc (↑f x₁) (↑f x₂)
        exact ⟨x, xu, hxy.le, hyxu.le⟩
        -- 🎉 no goals
    · refine' ⟨xl y, xu, _, hyxu.le⟩
      -- ⊢ ↑f (xl y) ≤ ↑(g - dg) y
      simp [dg0 (Or.inr hc), hxl]
      -- 🎉 no goals
#align bounded_continuous_function.exists_extension_forall_exists_le_ge_of_closed_embedding BoundedContinuousFunction.exists_extension_forall_exists_le_ge_of_closedEmbedding

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a bounded continuous real-valued function on `X`. Let `t` be
a nonempty convex set of real numbers (we use `OrdConnected` instead of `Convex` to automatically
deduce this argument by typeclass search) such that `f x ∈ t` for all `x`. Then there exists
a bounded continuous real-valued function `g : Y →ᵇ ℝ` such that `g y ∈ t` for all `y` and
`g ∘ e = f`. -/
theorem exists_extension_forall_mem_of_closedEmbedding (f : X →ᵇ ℝ) {t : Set ℝ} {e : X → Y}
    [hs : OrdConnected t] (hf : ∀ x, f x ∈ t) (hne : t.Nonempty) (he : ClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ t) ∧ g ∘ e = f := by
  cases isEmpty_or_nonempty X
  -- ⊢ ∃ g, (∀ (y : Y), ↑g y ∈ t) ∧ ↑g ∘ e = ↑f
  · rcases hne with ⟨c, hc⟩
    -- ⊢ ∃ g, (∀ (y : Y), ↑g y ∈ t) ∧ ↑g ∘ e = ↑f
    refine' ⟨const Y c, fun _ => hc, funext fun x => isEmptyElim x⟩
    -- 🎉 no goals
  rcases exists_extension_forall_exists_le_ge_of_closedEmbedding f he with ⟨g, hg, hgf⟩
  -- ⊢ ∃ g, (∀ (y : Y), ↑g y ∈ t) ∧ ↑g ∘ e = ↑f
  refine' ⟨g, fun y => _, hgf⟩
  -- ⊢ ↑g y ∈ t
  rcases hg y with ⟨xl, xu, h⟩
  -- ⊢ ↑g y ∈ t
  exact hs.out (hf _) (hf _) h
  -- 🎉 no goals
#align bounded_continuous_function.exists_extension_forall_mem_of_closed_embedding BoundedContinuousFunction.exists_extension_forall_mem_of_closedEmbedding

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
set. Let `s` be a closed set in a normal topological space `Y`. Let `f` be a bounded continuous
real-valued function on `s`. Let `t` be a nonempty convex set of real numbers (we use
`OrdConnected` instead of `Convex` to automatically deduce this argument by typeclass search) such
that `f x ∈ t` for all `x : s`. Then there exists a bounded continuous real-valued function
`g : Y →ᵇ ℝ` such that `g y ∈ t` for all `y` and `g.restrict s = f`. -/
theorem exists_forall_mem_restrict_eq_of_closed {s : Set Y} (f : s →ᵇ ℝ) (hs : IsClosed s)
    {t : Set ℝ} [OrdConnected t] (hf : ∀ x, f x ∈ t) (hne : t.Nonempty) :
    ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ t) ∧ g.restrict s = f := by
  rcases exists_extension_forall_mem_of_closedEmbedding f hf hne
      (closedEmbedding_subtype_val hs) with
    ⟨g, hg, hgf⟩
  exact ⟨g, hg, FunLike.coe_injective hgf⟩
  -- 🎉 no goals
#align bounded_continuous_function.exists_forall_mem_restrict_eq_of_closed BoundedContinuousFunction.exists_forall_mem_restrict_eq_of_closed

end BoundedContinuousFunction

namespace ContinuousMap

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a continuous real-valued function on `X`. Let `t` be a nonempty
convex set of real numbers (we use `OrdConnected` instead of `Convex` to automatically deduce this
argument by typeclass search) such that `f x ∈ t` for all `x`. Then there exists a continuous
real-valued function `g : C(Y, ℝ)` such that `g y ∈ t` for all `y` and `g ∘ e = f`. -/
theorem exists_extension_forall_mem_of_closedEmbedding (f : C(X, ℝ)) {t : Set ℝ} {e : X → Y}
    [hs : OrdConnected t] (hf : ∀ x, f x ∈ t) (hne : t.Nonempty) (he : ClosedEmbedding e) :
    ∃ g : C(Y, ℝ), (∀ y, g y ∈ t) ∧ g ∘ e = f := by
  have h : ℝ ≃o Ioo (-1 : ℝ) 1 := orderIsoIooNegOneOne ℝ
  -- ⊢ ∃ g, (∀ (y : Y), ↑g y ∈ t) ∧ ↑g ∘ e = ↑f
  let F : X →ᵇ ℝ :=
    { toFun := (↑) ∘ h ∘ f
      continuous_toFun := continuous_subtype_val.comp (h.continuous.comp f.continuous)
      map_bounded' :=
        bounded_range_iff.1
          ((bounded_Ioo (-1 : ℝ) 1).mono <| forall_range_iff.2 fun x => (h (f x)).2) }
  let t' : Set ℝ := (↑) ∘ h '' t
  -- ⊢ ∃ g, (∀ (y : Y), ↑g y ∈ t) ∧ ↑g ∘ e = ↑f
  have ht_sub : t' ⊆ Ioo (-1 : ℝ) 1 := image_subset_iff.2 fun x _ => (h x).2
  -- ⊢ ∃ g, (∀ (y : Y), ↑g y ∈ t) ∧ ↑g ∘ e = ↑f
  have : OrdConnected t' := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz
    lift z to Ioo (-1 : ℝ) 1 using Icc_subset_Ioo (h x).2.1 (h y).2.2 hz
    change z ∈ Icc (h x) (h y) at hz
    rw [← h.image_Icc] at hz
    rcases hz with ⟨z, hz, rfl⟩
    exact ⟨z, hs.out hx hy hz, rfl⟩
  have hFt : ∀ x, F x ∈ t' := fun x => mem_image_of_mem _ (hf x)
  -- ⊢ ∃ g, (∀ (y : Y), ↑g y ∈ t) ∧ ↑g ∘ e = ↑f
  rcases F.exists_extension_forall_mem_of_closedEmbedding hFt (hne.image _) he with ⟨G, hG, hGF⟩
  -- ⊢ ∃ g, (∀ (y : Y), ↑g y ∈ t) ∧ ↑g ∘ e = ↑f
  let g : C(Y, ℝ) :=
    ⟨h.symm ∘ codRestrict G _ fun y => ht_sub (hG y),
      h.symm.continuous.comp <| G.continuous.subtype_mk _⟩
  have hgG : ∀ {y a}, g y = a ↔ G y = h a := @fun y a =>
    h.toEquiv.symm_apply_eq.trans Subtype.ext_iff
  refine' ⟨g, fun y => _, _⟩
  -- ⊢ ↑g y ∈ t
  · rcases hG y with ⟨a, ha, hay⟩
    -- ⊢ ↑g y ∈ t
    convert ha
    -- ⊢ ↑g y = a
    exact hgG.2 hay.symm
    -- 🎉 no goals
  · ext x
    -- ⊢ (↑g ∘ e) x = ↑f x
    exact hgG.2 (congr_fun hGF _)
    -- 🎉 no goals
#align continuous_map.exists_extension_forall_mem_of_closed_embedding ContinuousMap.exists_extension_forall_mem_of_closedEmbedding

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a continuous real-valued function on `X`. Then there exists a
continuous real-valued function `g : C(Y, ℝ)` such that `g ∘ e = f`. -/
theorem exists_extension_of_closedEmbedding (f : C(X, ℝ)) (e : X → Y) (he : ClosedEmbedding e) :
    ∃ g : C(Y, ℝ), g ∘ e = f :=
  (exists_extension_forall_mem_of_closedEmbedding f (fun _ => mem_univ _) univ_nonempty he).imp
    fun _ => And.right
#align continuous_map.exists_extension_of_closed_embedding ContinuousMap.exists_extension_of_closedEmbedding

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed set. Let
`s` be a closed set in a normal topological space `Y`. Let `f` be a continuous real-valued function
on `s`. Let `t` be a nonempty convex set of real numbers (we use `ord_connected` instead of `convex`
to automatically deduce this argument by typeclass search) such that `f x ∈ t` for all `x : s`. Then
there exists a continuous real-valued function `g : C(Y, ℝ)` such that `g y ∈ t` for all `y` and
`g.restrict s = f`. -/
theorem exists_restrict_eq_forall_mem_of_closed {s : Set Y} (f : C(s, ℝ)) {t : Set ℝ}
    [OrdConnected t] (ht : ∀ x, f x ∈ t) (hne : t.Nonempty) (hs : IsClosed s) :
    ∃ g : C(Y, ℝ), (∀ y, g y ∈ t) ∧ g.restrict s = f :=
  let ⟨g, hgt, hgf⟩ :=
    exists_extension_forall_mem_of_closedEmbedding f ht hne (closedEmbedding_subtype_val hs)
  ⟨g, hgt, coe_injective hgf⟩
#align continuous_map.exists_restrict_eq_forall_mem_of_closed ContinuousMap.exists_restrict_eq_forall_mem_of_closed

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed set. Let
`s` be a closed set in a normal topological space `Y`. Let `f` be a continuous real-valued function
on `s`. Then there exists a continuous real-valued function `g : C(Y, ℝ)` such that
`g.restrict s = f`. -/
theorem exists_restrict_eq_of_closed {s : Set Y} (f : C(s, ℝ)) (hs : IsClosed s) :
    ∃ g : C(Y, ℝ), g.restrict s = f :=
  let ⟨g, _, hgf⟩ :=
    exists_restrict_eq_forall_mem_of_closed f (fun _ => mem_univ _) univ_nonempty hs
  ⟨g, hgf⟩
#align continuous_map.exists_restrict_eq_of_closed ContinuousMap.exists_restrict_eq_of_closed

end ContinuousMap
