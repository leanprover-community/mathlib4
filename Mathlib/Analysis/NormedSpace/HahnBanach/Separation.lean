/-
Copyright (c) 2022 Bhavik Mehta All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LocallyConvex

#align_import analysis.normed_space.hahn_banach.separation from "leanprover-community/mathlib"@"915591b2bb3ea303648db07284a161a7f2a9e3d4"

/-!
# Separation Hahn-Banach theorem

In this file we prove the geometric Hahn-Banach theorem. For any two disjoint convex sets, there
exists a continuous linear functional separating them, geometrically meaning that we can intercalate
a plane between them.

We provide many variations to stricten the result under more assumptions on the convex sets:
* `geometric_hahn_banach_open`: One set is open. Weak separation.
* `geometric_hahn_banach_open_point`, `geometric_hahn_banach_point_open`: One set is open, the
  other is a singleton. Weak separation.
* `geometric_hahn_banach_open_open`: Both sets are open. Semistrict separation.
* `geometric_hahn_banach_compact_closed`, `geometric_hahn_banach_closed_compact`: One set is closed,
  the other one is compact. Strict separation.
* `geometric_hahn_banach_point_closed`, `geometric_hahn_banach_closed_point`: One set is closed, the
  other one is a singleton. Strict separation.
* `geometric_hahn_banach_point_point`: Both sets are singletons. Strict separation.

## TODO

* Eidelheit's theorem
* `Convex ℝ s → interior (closure s) ⊆ s`
-/


open Set

open Pointwise

variable {𝕜 E : Type*}

/-- Given a set `s` which is a convex neighbourhood of `0` and a point `x₀` outside of it, there is
a continuous linear functional `f` separating `x₀` and `s`, in the sense that it sends `x₀` to 1 and
all of `s` to values strictly below `1`. -/
theorem separate_convex_open_set [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E] {s : Set E} (hs₀ : (0 : E) ∈ s) (hs₁ : Convex ℝ s)
    (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) : ∃ f : E →L[ℝ] ℝ, f x₀ = 1 ∧ ∀ x ∈ s, f x < 1 := by
  let f : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x₀ 1 (ne_of_mem_of_not_mem hs₀ hx₀).symm
  -- ⊢ ∃ f, ↑f x₀ = 1 ∧ ∀ (x : E), x ∈ s → ↑f x < 1
  have := exists_extension_of_le_sublinear f (gauge s) (fun c hc => gauge_smul_of_nonneg hc.le)
    (gauge_add_le hs₁ <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀) ?_
  obtain ⟨φ, hφ₁, hφ₂⟩ := this
  -- ⊢ ∃ f, ↑f x₀ = 1 ∧ ∀ (x : E), x ∈ s → ↑f x < 1
  have hφ₃ : φ x₀ = 1 := by
    rw [← f.domain.coe_mk x₀ (Submodule.mem_span_singleton_self _), hφ₁,
      LinearPMap.mkSpanSingleton'_apply_self]
  have hφ₄ : ∀ x ∈ s, φ x < 1 := fun x hx =>
    (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_open hs₂ hx)
  · refine' ⟨⟨φ, _⟩, hφ₃, hφ₄⟩
    -- ⊢ Continuous φ.toFun
    refine'
      φ.continuous_of_nonzero_on_open _ (hs₂.vadd (-x₀)) (Nonempty.vadd_set ⟨0, hs₀⟩)
        (vadd_set_subset_iff.mpr fun x hx => _)
    change φ (-x₀ + x) ≠ 0
    -- ⊢ ↑φ (-x₀ + x) ≠ 0
    rw [map_add, map_neg]
    -- ⊢ -↑φ x₀ + ↑φ x ≠ 0
    specialize hφ₄ x hx
    -- ⊢ -↑φ x₀ + ↑φ x ≠ 0
    linarith
    -- 🎉 no goals
  rintro ⟨x, hx⟩
  -- ⊢ ↑f { val := x, property := hx } ≤ gauge s ↑{ val := x, property := hx }
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.1 hx
  -- ⊢ ↑f { val := y • x₀, property := hx } ≤ gauge s ↑{ val := y • x₀, property := …
  rw [LinearPMap.mkSpanSingleton'_apply]
  -- ⊢ y • 1 ≤ gauge s ↑{ val := y • x₀, property := hx }
  simp only [mul_one, Algebra.id.smul_eq_mul, Submodule.coe_mk]
  -- ⊢ y ≤ gauge s (y • x₀)
  obtain h | h := le_or_lt y 0
  -- ⊢ y ≤ gauge s (y • x₀)
  · exact h.trans (gauge_nonneg _)
    -- 🎉 no goals
  · rw [gauge_smul_of_nonneg h.le, smul_eq_mul, le_mul_iff_one_le_right h]
    -- ⊢ 1 ≤ gauge s x₀
    exact
      one_le_gauge_of_not_mem (hs₁.starConvex hs₀)
        (absorbent_nhds_zero <| hs₂.mem_nhds hs₀).absorbs hx₀
#align separate_convex_open_set separate_convex_open_set

variable [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E] [Module ℝ E]
  [ContinuousSMul ℝ E] {s t : Set E} {x y : E}

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is open,
there is a continuous linear functional which separates them. -/
theorem geometric_hahn_banach_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht : Convex ℝ t)
    (disj : Disjoint s t) : ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u ≤ f b := by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  -- ⊢ ∃ f u, (∀ (a : E), a ∈ ∅ → ↑f a < u) ∧ ∀ (b : E), b ∈ t → u ≤ ↑f b
  · exact ⟨0, 0, by simp, fun b _hb => le_rfl⟩
    -- 🎉 no goals
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  -- ⊢ ∃ f u, (∀ (a : E), a ∈ s → ↑f a < u) ∧ ∀ (b : E), b ∈ ∅ → u ≤ ↑f b
  · exact ⟨0, 1, fun a _ha => zero_lt_one, by simp⟩
    -- 🎉 no goals
  let x₀ := b₀ - a₀
  -- ⊢ ∃ f u, (∀ (a : E), a ∈ s → ↑f a < u) ∧ ∀ (b : E), b ∈ t → u ≤ ↑f b
  let C := x₀ +ᵥ (s - t)
  -- ⊢ ∃ f u, (∀ (a : E), a ∈ s → ↑f a < u) ∧ ∀ (b : E), b ∈ t → u ≤ ↑f b
  have : (0 : E) ∈ C :=
    ⟨a₀ - b₀, sub_mem_sub ha₀ hb₀, by simp_rw [vadd_eq_add, sub_add_sub_cancel', sub_self]⟩
  have : Convex ℝ C := (hs₁.sub ht).vadd _
  -- ⊢ ∃ f u, (∀ (a : E), a ∈ s → ↑f a < u) ∧ ∀ (b : E), b ∈ t → u ≤ ↑f b
  have : x₀ ∉ C := by
    intro hx₀
    rw [← add_zero x₀] at hx₀
    exact disj.zero_not_mem_sub_set (vadd_mem_vadd_set_iff.1 hx₀)
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 ∈ C› ‹_› (hs₂.sub_right.vadd _) ‹x₀ ∉ C›
  -- ⊢ ∃ f u, (∀ (a : E), a ∈ s → ↑f a < u) ∧ ∀ (b : E), b ∈ t → u ≤ ↑f b
  have : f b₀ = f a₀ + 1 := by simp [← hf₁]
  -- ⊢ ∃ f u, (∀ (a : E), a ∈ s → ↑f a < u) ∧ ∀ (b : E), b ∈ t → u ≤ ↑f b
  have forall_le : ∀ a ∈ s, ∀ b ∈ t, f a ≤ f b := by
    intro a ha b hb
    have := hf₂ (x₀ + (a - b)) (vadd_mem_vadd_set <| sub_mem_sub ha hb)
    simp only [f.map_add, f.map_sub, hf₁] at this
    linarith
  refine' ⟨f, sInf (f '' t), image_subset_iff.1 (_ : f '' s ⊆ Iio (sInf (f '' t))), fun b hb => _⟩
  -- ⊢ ↑f '' s ⊆ Iio (sInf (↑f '' t))
  · rw [← interior_Iic]
    -- ⊢ ↑f '' s ⊆ interior (Iic (sInf (↑f '' t)))
    refine' interior_maximal (image_subset_iff.2 fun a ha => _) (f.isOpenMap_of_ne_zero _ _ hs₂)
    -- ⊢ a ∈ ↑f ⁻¹' Iic (sInf (↑f '' t))
    · exact le_csInf (Nonempty.image _ ⟨_, hb₀⟩) (ball_image_of_ball <| forall_le _ ha)
      -- 🎉 no goals
    · rintro rfl
      -- ⊢ False
      simp at hf₁
      -- 🎉 no goals
  · exact csInf_le ⟨f a₀, ball_image_of_ball <| forall_le _ ha₀⟩ (mem_image_of_mem _ hb)
    -- 🎉 no goals
#align geometric_hahn_banach_open geometric_hahn_banach_open

theorem geometric_hahn_banach_open_point (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (disj : x ∉ s) :
    ∃ f : E →L[ℝ] ℝ, ∀ a ∈ s, f a < f x :=
  let ⟨f, _s, hs, hx⟩ :=
    geometric_hahn_banach_open hs₁ hs₂ (convex_singleton x) (disjoint_singleton_right.2 disj)
  ⟨f, fun a ha => lt_of_lt_of_le (hs a ha) (hx x (mem_singleton _))⟩
#align geometric_hahn_banach_open_point geometric_hahn_banach_open_point

theorem geometric_hahn_banach_point_open (ht₁ : Convex ℝ t) (ht₂ : IsOpen t) (disj : x ∉ t) :
    ∃ f : E →L[ℝ] ℝ, ∀ b ∈ t, f x < f b :=
  let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩
          -- 🎉 no goals
#align geometric_hahn_banach_point_open geometric_hahn_banach_point_open

theorem geometric_hahn_banach_open_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht₁ : Convex ℝ t)
    (ht₃ : IsOpen t) (disj : Disjoint s t) :
    ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u < f b := by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  -- ⊢ ∃ f u, (∀ (a : E), a ∈ ∅ → ↑f a < u) ∧ ∀ (b : E), b ∈ t → u < ↑f b
  · exact ⟨0, -1, by simp, fun b _hb => by norm_num⟩
    -- 🎉 no goals
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  -- ⊢ ∃ f u, (∀ (a : E), a ∈ s → ↑f a < u) ∧ ∀ (b : E), b ∈ ∅ → u < ↑f b
  · exact ⟨0, 1, fun a _ha => by norm_num, by simp⟩
    -- 🎉 no goals
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open hs₁ hs₂ ht₁ disj
  -- ⊢ ∃ f u, (∀ (a : E), a ∈ s✝ → ↑f a < u) ∧ ∀ (b : E), b ∈ t → u < ↑f b
  have hf : IsOpenMap f := by
    refine' f.isOpenMap_of_ne_zero _
    rintro rfl
    simp_rw [ContinuousLinearMap.zero_apply] at hf₁ hf₂
    exact (hf₁ _ ha₀).not_le (hf₂ _ hb₀)
  refine' ⟨f, s, hf₁, image_subset_iff.1 (_ : f '' t ⊆ Ioi s)⟩
  -- ⊢ ↑f '' t ⊆ Ioi s
  rw [← interior_Ici]
  -- ⊢ ↑f '' t ⊆ interior (Ici s)
  refine' interior_maximal (image_subset_iff.2 hf₂) (f.isOpenMap_of_ne_zero _ _ ht₃)
  -- ⊢ f ≠ 0
  rintro rfl
  -- ⊢ False
  simp_rw [ContinuousLinearMap.zero_apply] at hf₁ hf₂
  -- ⊢ False
  exact (hf₁ _ ha₀).not_le (hf₂ _ hb₀)
  -- 🎉 no goals
#align geometric_hahn_banach_open_open geometric_hahn_banach_open_open

variable [LocallyConvexSpace ℝ E]

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
compact and `t` is closed, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_compact_closed (hs₁ : Convex ℝ s) (hs₂ : IsCompact s)
    (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (disj : Disjoint s t) :
    ∃ (f : E →L[ℝ] ℝ) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  -- ⊢ ∃ f u v, (∀ (a : E), a ∈ ∅ → ↑f a < u) ∧ u < v ∧ ∀ (b : E), b ∈ t → v < ↑f b
  · exact ⟨0, -2, -1, by simp, by norm_num, fun b _hb => by norm_num⟩
    -- 🎉 no goals
  obtain rfl | _ht := t.eq_empty_or_nonempty
  -- ⊢ ∃ f u v, (∀ (a : E), a ∈ s → ↑f a < u) ∧ u < v ∧ ∀ (b : E), b ∈ ∅ → v < ↑f b
  · exact ⟨0, 1, 2, fun a _ha => by norm_num, by norm_num, by simp⟩
    -- 🎉 no goals
  obtain ⟨U, V, hU, hV, hU₁, hV₁, sU, tV, disj'⟩ := disj.exists_open_convexes hs₁ hs₂ ht₁ ht₂
  -- ⊢ ∃ f u v, (∀ (a : E), a ∈ s → ↑f a < u) ∧ u < v ∧ ∀ (b : E), b ∈ t → v < ↑f b
  obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj'
  -- ⊢ ∃ f u v, (∀ (a : E), a ∈ s → ↑f a < u) ∧ u < v ∧ ∀ (b : E), b ∈ t → v < ↑f b
  obtain ⟨x, hx₁, hx₂⟩ := hs₂.exists_forall_ge hs f.continuous.continuousOn
  -- ⊢ ∃ f u v, (∀ (a : E), a ∈ s → ↑f a < u) ∧ u < v ∧ ∀ (b : E), b ∈ t → v < ↑f b
  have : f x < u := hf₁ x (sU hx₁)
  -- ⊢ ∃ f u v, (∀ (a : E), a ∈ s → ↑f a < u) ∧ u < v ∧ ∀ (b : E), b ∈ t → v < ↑f b
  exact
    ⟨f, (f x + u) / 2, u, fun a ha => by linarith [hx₂ a ha], by linarith, fun b hb =>
      hf₂ b (tV hb)⟩
#align geometric_hahn_banach_compact_closed geometric_hahn_banach_compact_closed

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
closed, and `t` is compact, there is a continuous linear functional which strongly separates them.
-/
theorem geometric_hahn_banach_closed_compact (hs₁ : Convex ℝ s) (hs₂ : IsClosed s)
    (ht₁ : Convex ℝ t) (ht₂ : IsCompact t) (disj : Disjoint s t) :
    ∃ (f : E →L[ℝ] ℝ) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b :=
  let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩
                  -- 🎉 no goals
                                     -- 🎉 no goals
                                                        -- 🎉 no goals
#align geometric_hahn_banach_closed_compact geometric_hahn_banach_closed_compact

theorem geometric_hahn_banach_point_closed (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (disj : x ∉ t) :
    ∃ (f : E →L[ℝ] ℝ) (u : ℝ), f x < u ∧ ∀ b ∈ t, u < f b :=
  let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
  ⟨f, v, hst.trans' <| ha x <| mem_singleton _, hb⟩
#align geometric_hahn_banach_point_closed geometric_hahn_banach_point_closed

theorem geometric_hahn_banach_closed_point (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (disj : x ∉ s) :
    ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ s, f a < u) ∧ u < f x :=
  let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
  ⟨f, s, ha, hst.trans <| hb x <| mem_singleton _⟩
#align geometric_hahn_banach_closed_point geometric_hahn_banach_closed_point

/-- See also `NormedSpace.eq_iff_forall_dual_eq`. -/
theorem geometric_hahn_banach_point_point [T1Space E] (hxy : x ≠ y) :
    ∃ f : E →L[ℝ] ℝ, f x < f y := by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩
  -- 🎉 no goals
#align geometric_hahn_banach_point_point geometric_hahn_banach_point_point

/-- A closed convex set is the intersection of the halfspaces containing it. -/
theorem iInter_halfspaces_eq (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    ⋂ l : E →L[ℝ] ℝ, { x | ∃ y ∈ s, l x ≤ l y } = s := by
  rw [Set.iInter_setOf]
  -- ⊢ {x | ∀ (i : E →L[ℝ] ℝ), ∃ y, y ∈ s ∧ ↑i x ≤ ↑i y} = s
  refine' Set.Subset.antisymm (fun x hx => _) fun x hx l => ⟨x, hx, le_rfl⟩
  -- ⊢ x ∈ s
  by_contra h
  -- ⊢ False
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point hs₁ hs₂ h
  -- ⊢ False
  obtain ⟨y, hy, hxy⟩ := hx l
  -- ⊢ False
  exact ((hxy.trans_lt (hlA y hy)).trans hl).not_le le_rfl
  -- 🎉 no goals
#align Inter_halfspaces_eq iInter_halfspaces_eq
