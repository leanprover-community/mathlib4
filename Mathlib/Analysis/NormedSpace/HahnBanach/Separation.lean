/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.NormedSpace.Extend
import Mathlib.Analysis.RCLike.Lemmas

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
theorem separate_convex_open_set [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E] {s : Set E} (hs₀ : (0 : E) ∈ s) (hs₁ : Convex ℝ s)
    (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) :
    ∃ f : StrongDual ℝ E, f x₀ = 1 ∧ ∀ x ∈ s, f x < 1 := by
  let f : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x₀ 1 (ne_of_mem_of_not_mem hs₀ hx₀).symm
  have := exists_extension_of_le_sublinear f (gauge s) (fun c hc => gauge_smul_of_nonneg hc.le)
    (gauge_add_le hs₁ <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀) ?_
  · obtain ⟨φ, hφ₁, hφ₂⟩ := this
    have hφ₃ : φ x₀ = 1 := by
      rw [← f.domain.coe_mk x₀ (Submodule.mem_span_singleton_self _), hφ₁,
        LinearPMap.mkSpanSingleton'_apply_self]
    have hφ₄ : ∀ x ∈ s, φ x < 1 := fun x hx =>
      (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_isOpen hs₂ hx)
    refine ⟨⟨φ, ?_⟩, hφ₃, hφ₄⟩
    refine
      φ.continuous_of_nonzero_on_open _ (hs₂.vadd (-x₀)) (Nonempty.vadd_set ⟨0, hs₀⟩)
        (vadd_set_subset_iff.mpr fun x hx => ?_)
    change φ (-x₀ + x) ≠ 0
    rw [map_add, map_neg]
    specialize hφ₄ x hx
    linarith
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [LinearPMap.mkSpanSingleton'_apply]
  simp only [mul_one, Algebra.id.smul_eq_mul]
  obtain h | h := le_or_gt y 0
  · exact h.trans (gauge_nonneg _)
  · rw [gauge_smul_of_nonneg h.le, smul_eq_mul, le_mul_iff_one_le_right h]
    exact
      one_le_gauge_of_notMem (hs₁.starConvex hs₀)
        (absorbent_nhds_zero <| hs₂.mem_nhds hs₀).absorbs hx₀

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {s t : Set E} {x y : E}
section

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is open,
there is a continuous linear functional which separates them. -/
theorem geometric_hahn_banach_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht : Convex ℝ t)
    (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u ≤ f b := by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, 0, by simp, fun b _hb => le_rfl⟩
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact ⟨0, 1, fun a _ha => zero_lt_one, by simp⟩
  let x₀ := b₀ - a₀
  let C := x₀ +ᵥ (s - t)
  have : (0 : E) ∈ C :=
    ⟨a₀ - b₀, sub_mem_sub ha₀ hb₀, by simp_rw [x₀, vadd_eq_add, sub_add_sub_cancel', sub_self]⟩
  have : Convex ℝ C := (hs₁.sub ht).vadd _
  have : x₀ ∉ C := by
    intro hx₀
    rw [← add_zero x₀] at hx₀
    exact disj.zero_notMem_sub_set (vadd_mem_vadd_set_iff.1 hx₀)
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 ∈ C› ‹_› (hs₂.sub_right.vadd _) ‹x₀ ∉ C›
  have : f b₀ = f a₀ + 1 := by simp [x₀, ← hf₁]
  have forall_le : ∀ a ∈ s, ∀ b ∈ t, f a ≤ f b := by
    intro a ha b hb
    have := hf₂ (x₀ + (a - b)) (vadd_mem_vadd_set <| sub_mem_sub ha hb)
    simp only [f.map_add, f.map_sub, hf₁] at this
    linarith
  refine ⟨f, sInf (f '' t), image_subset_iff.1 (?_ : f '' s ⊆ Iio (sInf (f '' t))), fun b hb => ?_⟩
  · rw [← interior_Iic]
    refine interior_maximal (image_subset_iff.2 fun a ha => ?_) (f.isOpenMap_of_ne_zero ?_ _ hs₂)
    · exact le_csInf (Nonempty.image _ ⟨_, hb₀⟩) (forall_mem_image.2 <| forall_le _ ha)
    · rintro rfl
      simp at hf₁
  · exact csInf_le ⟨f a₀, forall_mem_image.2 <| forall_le _ ha₀⟩ (mem_image_of_mem _ hb)

theorem geometric_hahn_banach_open_point (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (disj : x ∉ s) :
    ∃ f : StrongDual ℝ E, ∀ a ∈ s, f a < f x :=
  let ⟨f, _s, hs, hx⟩ :=
    geometric_hahn_banach_open hs₁ hs₂ (convex_singleton x) (disjoint_singleton_right.2 disj)
  ⟨f, fun a ha => lt_of_lt_of_le (hs a ha) (hx x (mem_singleton _))⟩

theorem geometric_hahn_banach_point_open (ht₁ : Convex ℝ t) (ht₂ : IsOpen t) (disj : x ∉ t) :
    ∃ f : StrongDual ℝ E, ∀ b ∈ t, f x < f b :=
  let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩

theorem geometric_hahn_banach_open_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht₁ : Convex ℝ t)
    (ht₃ : IsOpen t) (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u < f b := by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, -1, by simp, fun b _hb => by simp⟩
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact ⟨0, 1, fun a _ha => by simp, by simp⟩
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open hs₁ hs₂ ht₁ disj
  have hf : IsOpenMap f := by
    refine f.isOpenMap_of_ne_zero ?_
    rintro rfl
    simp_rw [ContinuousLinearMap.zero_apply] at hf₁ hf₂
    exact (hf₁ _ ha₀).not_ge (hf₂ _ hb₀)
  refine ⟨f, s, hf₁, image_subset_iff.1 (?_ : f '' t ⊆ Ioi s)⟩
  rw [← interior_Ici]
  refine interior_maximal (image_subset_iff.2 hf₂) (f.isOpenMap_of_ne_zero ?_ _ ht₃)
  rintro rfl
  simp_rw [ContinuousLinearMap.zero_apply] at hf₁ hf₂
  exact (hf₁ _ ha₀).not_ge (hf₂ _ hb₀)

variable [LocallyConvexSpace ℝ E]

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
compact and `t` is closed, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_compact_closed (hs₁ : Convex ℝ s) (hs₂ : IsCompact s)
    (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨0, -2, -1, by simp⟩
  obtain rfl | _ht := t.eq_empty_or_nonempty
  · exact ⟨0, 1, 2, by simp⟩
  obtain ⟨U, V, hU, hV, hU₁, hV₁, sU, tV, disj'⟩ := disj.exists_open_convexes hs₁ hs₂ ht₁ ht₂
  obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj'
  obtain ⟨x, hx₁, hx₂⟩ := hs₂.exists_isMaxOn hs f.continuous.continuousOn
  have : f x < u := hf₁ x (sU hx₁)
  exact
    ⟨f, (f x + u) / 2, u,
      fun a ha => by have := hx₂ ha; dsimp at this; linarith,
      by linarith,
      fun b hb => hf₂ b (tV hb)⟩

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
closed, and `t` is compact, there is a continuous linear functional which strongly separates them.
-/
theorem geometric_hahn_banach_closed_compact (hs₁ : Convex ℝ s) (hs₂ : IsClosed s)
    (ht₁ : Convex ℝ t) (ht₂ : IsCompact t) (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b :=
  let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

theorem geometric_hahn_banach_point_closed (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (disj : x ∉ t) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), f x < u ∧ ∀ b ∈ t, u < f b :=
  let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
  ⟨f, v, hst.trans' <| ha x <| mem_singleton _, hb⟩

theorem geometric_hahn_banach_closed_point (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (disj : x ∉ s) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ u < f x :=
  let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
  ⟨f, s, ha, hst.trans <| hb x <| mem_singleton _⟩

/-- See also `NormedSpace.eq_iff_forall_dual_eq`. -/
theorem geometric_hahn_banach_point_point [T1Space E] (hxy : x ≠ y) :
    ∃ f : StrongDual ℝ E, f x < f y := by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩

/-- A closed convex set is the intersection of the half-spaces containing it. -/
theorem iInter_halfSpaces_eq (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    ⋂ l : StrongDual ℝ E, { x | ∃ y ∈ s, l x ≤ l y } = s := by
  rw [Set.iInter_setOf]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra h
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).not_ge le_rfl
end

namespace RCLike

variable [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]

/-- Real linear extension of continuous extension of `LinearMap.extendTo𝕜'` -/
noncomputable def extendTo𝕜'ₗ [ContinuousConstSMul 𝕜 E] : StrongDual ℝ E →ₗ[ℝ] StrongDual 𝕜 E :=
  letI to𝕜 (fr : StrongDual ℝ E) : StrongDual 𝕜 E :=
    { toLinearMap := LinearMap.extendTo𝕜' fr
      cont := show Continuous fun x ↦ (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) by fun_prop }
  have h fr x : to𝕜 fr x = ((fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜)) := rfl
  { toFun := to𝕜
    map_add' := by intros; ext; simp [h]; ring
    map_smul' := by intros; ext; simp [h, real_smul_eq_coe_mul]; ring }

@[simp]
lemma re_extendTo𝕜'ₗ [ContinuousConstSMul 𝕜 E] (g : StrongDual ℝ E) (x : E) :
    re ((extendTo𝕜'ₗ g) x : 𝕜) = g x := by
  have h g (x : E) : extendTo𝕜'ₗ g x = ((g x : 𝕜) - (I : 𝕜) * (g ((I : 𝕜) • x) : 𝕜)) := rfl
  simp only [h, map_sub, ofReal_re, mul_re, I_re, zero_mul, ofReal_im, mul_zero,
    sub_self, sub_zero]

variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

theorem separate_convex_open_set {s : Set E}
    (hs₀ : (0 : E) ∈ s) (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) :
    ∃ f : StrongDual 𝕜 E, re (f x₀) = 1 ∧ ∀ x ∈ s, re (f x) < 1 := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨g, hg⟩ := _root_.separate_convex_open_set hs₀ hs₁ hs₂ hx₀
  use extendTo𝕜'ₗ g
  simp only [re_extendTo𝕜'ₗ]
  exact hg

/-- Following [Rudin, *Functional Analysis* (Theorem 3.4 (a))][rudin1991] -/
theorem geometric_hahn_banach_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht : Convex ℝ t)
    (disj : Disjoint s t) : ∃ (f : StrongDual 𝕜 E) (u : ℝ), (∀ a ∈ s, re (f a) < u) ∧
    ∀ b ∈ t, u ≤ re (f b) := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨f, u, h⟩ := _root_.geometric_hahn_banach_open hs₁ hs₂ ht disj
  use extendTo𝕜'ₗ f
  simp only [re_extendTo𝕜'ₗ]
  exact Exists.intro u h

theorem geometric_hahn_banach_open_point (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (disj : x ∉ s) :
    ∃ f : StrongDual 𝕜 E, ∀ a ∈ s, re (f a) < re (f x) := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨f, h⟩ := _root_.geometric_hahn_banach_open_point hs₁ hs₂ disj
  use extendTo𝕜'ₗ f
  simp only [re_extendTo𝕜'ₗ]
  exact fun a a_1 ↦ h a a_1

theorem geometric_hahn_banach_point_open (ht₁ : Convex ℝ t) (ht₂ : IsOpen t) (disj : x ∉ t) :
    ∃ f : StrongDual 𝕜 E, ∀ b ∈ t, re (f x) < re (f b) :=
  let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩

theorem geometric_hahn_banach_open_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s)
    (ht₁ : Convex ℝ t) (ht₃ : IsOpen t) (disj : Disjoint s t) :
    ∃ (f : StrongDual 𝕜 E) (u : ℝ), (∀ a ∈ s, re (f a) < u) ∧ ∀ b ∈ t, u < re (f b) := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨f, u, h⟩ := _root_.geometric_hahn_banach_open_open hs₁ hs₂ ht₁ ht₃ disj
  use extendTo𝕜'ₗ f
  simp only [re_extendTo𝕜'ₗ]
  exact Exists.intro u h

variable [LocallyConvexSpace ℝ E]

/-- Following [Rudin, *Functional Analysis* (Theorem 3.4 (b))][rudin1991] -/
theorem geometric_hahn_banach_compact_closed (hs₁ : Convex ℝ s) (hs₂ : IsCompact s)
    (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (disj : Disjoint s t) :
    ∃ (f : StrongDual 𝕜 E) (u v : ℝ), (∀ a ∈ s, re (f a) < u) ∧ u < v ∧ ∀ b ∈ t, v < re (f b) := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨g, u, v, h1⟩ := _root_.geometric_hahn_banach_compact_closed hs₁ hs₂ ht₁ ht₂ disj
  use extendTo𝕜'ₗ g
  simp only [re_extendTo𝕜'ₗ, exists_and_left]
  exact ⟨u, h1.1, v, h1.2⟩

theorem geometric_hahn_banach_closed_compact (hs₁ : Convex ℝ s) (hs₂ : IsClosed s)
    (ht₁ : Convex ℝ t) (ht₂ : IsCompact t) (disj : Disjoint s t) :
    ∃ (f : StrongDual 𝕜 E) (u v : ℝ), (∀ a ∈ s, re (f a) < u) ∧ u < v ∧ ∀ b ∈ t, v < re (f b) :=
  let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

theorem geometric_hahn_banach_point_closed (ht₁ : Convex ℝ t) (ht₂ : IsClosed t)
    (disj : x ∉ t) : ∃ (f : StrongDual 𝕜 E) (u : ℝ), re (f x) < u ∧ ∀ b ∈ t, u < re (f b) :=
  let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
  ⟨f, v, hst.trans' <| ha x <| mem_singleton _, hb⟩

theorem geometric_hahn_banach_closed_point (hs₁ : Convex ℝ s) (hs₂ : IsClosed s)
    (disj : x ∉ s) : ∃ (f : StrongDual 𝕜 E) (u : ℝ), (∀ a ∈ s, re (f a) < u) ∧ u < re (f x) :=
  let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
  ⟨f, s, ha, hst.trans <| hb x <| mem_singleton _⟩

theorem geometric_hahn_banach_point_point [T1Space E] (hxy : x ≠ y) :
    ∃ f : StrongDual 𝕜 E, re (f x) < re (f y) := by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (𝕜 := 𝕜) (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩

theorem iInter_halfSpaces_eq (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    ⋂ l : StrongDual 𝕜 E, { x | ∃ y ∈ s, re (l x) ≤ re (l y) } = s := by
  rw [Set.iInter_setOf]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra h
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point (𝕜 := 𝕜) hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).false

lemma mem_norm_le_of_balanced {𝕜 : Type*} [RCLike 𝕜] {K : Set 𝕜} (Balanced_K : Balanced 𝕜 K)
    {x : 𝕜} (hx : x ∈ K) (h0 : ‖x‖ > 0) : ∀ z : 𝕜, 0 ≤ ‖z‖ ∧ ‖z‖ ≤ ‖x‖ → z ∈ K :=
    fun z ⟨t1, t2⟩ ↦ by
  have : ‖z / x‖ ≤ 1 := by calc
    _ = ‖z‖ / ‖x‖ := by rw [norm_div]
    _ ≤ _ := (div_le_one₀ h0).mpr t2
  have ne : x ≠ 0 := fun nh ↦ by simp [nh] at h0
  simpa [ne] using balanced_iff_smul_mem.mp Balanced_K this hx

theorem closed_balanced_sep {𝕜 : Type*} [RCLike 𝕜] {r : ℝ} {K : Set 𝕜} (compact_K : IsCompact K)
    (zero_in : 0 ∈ K) (norm_lt_r : ∀ x ∈ K, ‖x‖ < r) :
    ∃ s, 0 < s ∧ s < r ∧ (∀ z ∈ K, ‖z‖ < s) := by
  set g : 𝕜 → ℝ := fun x ↦ ‖x‖ with hg
  obtain ⟨x, xin, eq⟩ : sSup (g '' K) ∈ g '' K :=
    IsCompact.sSup_mem (IsCompact.image compact_K continuous_norm) ⟨0, 0, zero_in, norm_zero⟩
  have g_le : ∀ z ∈ K, g z ≤ g x := fun z hz ↦ by
    rw [eq]
    refine le_csSup ?_ (Set.mem_image_of_mem g hz)
    exact ⟨r, fun y ⟨x, hx, _⟩ ↦ by linarith [norm_lt_r x hx]⟩
  obtain ⟨s, hs₁, hs₂⟩ : ∃ s, g x < s ∧ s < r := exists_between (by simp only [norm_lt_r x xin, g])
  exact ⟨s, by linarith [norm_nonneg x], hs₂, fun z hz ↦ by linarith [norm_lt_r x xin, g_le z hz]⟩

/-- Following [Rudin, *Functional Analysis* (Theorem 3.7)][rudin1991]
-/
theorem geometric_hahn_banach {B : Set E} (hs₁ : Convex ℝ B) (hs₂ : IsClosed B)
    (hs₃ : Balanced 𝕜 B) (hs₄ : B.Nonempty) {x₀ : E} (hx : x₀ ∉ B) :
    ∃ (f : StrongDual 𝕜 E) (s : ℝ), 0 < s ∧ s < ‖(f x₀)‖ ∧ ∀ b ∈ B, ‖f b‖ < s := by
  obtain ⟨f, u, v, h1, h2, h3⟩ : ∃ (f : StrongDual 𝕜 E) (u v : ℝ),
      (∀ a ∈ ({x₀} : Set E), re (f a) < u) ∧ u < v ∧ ∀ b ∈ B, v < re (f b) :=
    RCLike.geometric_hahn_banach_compact_closed (convex_singleton x₀) isCompact_singleton hs₁ hs₂
      (Set.disjoint_singleton_left.mpr hx)
  have h3 : ∀ z ∈ f '' B, v < re z := fun z ⟨y, ⟨hy, eq⟩⟩ ↦ by
    rw [← eq]
    exact h3 y hy
  set K := closure (⇑f '' B)
  have notin : f x₀ ∉ K := fun h ↦ by
    have : v ≤ re (f x₀) := le_on_closure_of_lt (by grind) continuous_re.continuousOn h
    linarith [h1 x₀ rfl]
  have Balanced_K : Balanced 𝕜 K := by
    refine Balanced.closure (fun a ha _ ⟨_, ⟨⟨t, ht, _⟩, _⟩⟩ ↦ ?_)
    exact ⟨a • t, Balanced.smul_mem hs₃ ha ht, by simp_all⟩
  have zero_in : 0 ∈ K := subset_closure ⟨0, by simpa using Balanced.zero_mem hs₃ hs₄⟩
  set r := ‖f x₀‖ with hr
  have r_pos : r > 0 := by simpa [hr] using fun nh ↦ by simp [nh, zero_in] at notin
  have norm_lt_r : ∀ x ∈ K, ‖x‖ < r := fun x hx ↦ by
    by_contra! nh
    have := mem_norm_le_of_balanced Balanced_K hx (by linarith) (f x₀) ⟨norm_nonneg (f x₀), nh⟩
    contradiction
  have compact_K : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
    refine (Metric.isBounded_iff_subset_ball 0 (s := K)).mpr ?_
    exact ⟨r, fun x hx ↦ mem_ball_zero_iff.mpr (norm_lt_r x hx)⟩
  obtain ⟨s, s_pos, s_lt, hs⟩ : ∃ s, 0 < s ∧ s < r ∧ (∀ z ∈ K, ‖z‖ < s) :=
    closed_balanced_sep compact_K zero_in norm_lt_r
  use f, s
  simpa [← hr, s_lt, s_pos] using fun b hb ↦ hs (f b) (subset_closure (mem_image_of_mem (⇑f) hb))

theorem geometric_hahn_banach' {B : Set E} (hs₁ : Convex ℝ B) (hs₂ : IsClosed B)
    (hs₃ : Balanced 𝕜 B) (hs₄ : B.Nonempty) (x₀ : E) (hx : x₀ ∉ B) :
    ∃ (f : StrongDual 𝕜 E), (‖(f x₀)‖ > 1) ∧ ∀ b ∈ B, ‖f b‖ < 1 := by
  obtain ⟨f, s, h1, h2, h3⟩ := geometric_hahn_banach hs₁ hs₂ hs₃ hs₄ hx
  use (‖f x₀‖ / (s * (f x₀))) • f
  have (x : E): ‖((‖f x₀‖ / (s * f x₀)) • f) x‖ = ‖f x‖ / s := by
    have : ‖f x₀‖ > 0 := by linarith
    simp [abs_of_pos h1, field]
  constructor
  · rw [this]
    exact (one_lt_div₀ h1).mpr h2
  · intro b hb
    rw [this, div_lt_one₀ h1]
    exact h3 b hb

end RCLike
