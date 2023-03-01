/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.algebra.order.left_right_lim
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Tactic.WLOG
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LeftRight

/-!
# Left and right limits

We define the (strict) left and right limits of a function.

* `leftLim f x` is the strict left limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its left).
* `rightLim f x` is the strict right limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its right).

We develop a comprehensive API for monotone functions. Notably,

* `Monotone.continuousAt_iff_leftLim_eq_rightLim` states that a monotone function is continuous
  at a point if and only if its left and right limits coincide.
* `Monotone.countable_not_continuousAt` asserts that a monotone function taking values in a
  second-countable space has at most countably many discontinuity points.

We also port the API to antitone functions.

## TODO

Prove corresponding stronger results for `StrictMono` and `StrictAnti` functions.
-/


open Set Filter

open Topology

section

variable {α β : Type _} [LinearOrder α] [TopologicalSpace β]

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the left of `f` at `a`, denoted with `leftLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left or the function has no left
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.leftLim (f : α → β) (a : α) : β := by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[<] a = ⊥ ∨ ¬∃ y, Tendsto f (𝓝[<] a) (𝓝 y) then f a else limUnder (𝓝[<] a) f
#align function.left_lim Function.leftLim

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the right of `f` at `a`, denoted with `rightLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its right or the function has no right
limit, , we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.rightLim (f : α → β) (a : α) : β :=
  @Function.leftLim αᵒᵈ β _ _ f a
#align function.right_lim Function.rightLim

open Function

theorem leftLim_eq_of_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology α] [T2Space β]
    {f : α → β} {a : α} {y : β} (h : 𝓝[<] a ≠ ⊥) (h' : Tendsto f (𝓝[<] a) (𝓝 y)) :
    leftLim f a = y := by
  have h'' : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y) := ⟨y, h'⟩
  rw [h'α.topology_eq_generate_intervals] at h h' h''
  simp only [leftLim, h, h'', not_true, or_self_iff, if_false]
  haveI := neBot_iff.2 h
  exact lim_eq h'
#align left_lim_eq_of_tendsto leftLim_eq_of_tendsto

theorem leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : 𝓝[<] a = ⊥) : leftLim f a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, ite_eq_left_iff, h]
#align left_lim_eq_of_eq_bot leftLim_eq_of_eq_bot

end

open Function

namespace Monotone

variable {α β : Type _} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Monotone f) {x y : α}

theorem leftLim_eq_supₛ [TopologicalSpace α] [OrderTopology α] (h : 𝓝[<] x ≠ ⊥) :
    leftLim f x = supₛ (f '' Iio x) :=
  leftLim_eq_of_tendsto h (hf.tendsto_nhdsWithin_Iio x)
#align monotone.left_lim_eq_Sup Monotone.leftLim_eq_supₛ

theorem leftLim_le (h : x ≤ y) : leftLim f x ≤ f y := by
  letI : TopologicalSpace α := Preorder.topology α
  haveI : OrderTopology α := ⟨rfl⟩
  rcases eq_or_ne (𝓝[<] x) ⊥ with (h' | h')
  · simpa [leftLim, h'] using hf h
  haveI A : NeBot (𝓝[<] x) := neBot_iff.2 h'
  rw [leftLim_eq_supₛ hf h']
  refine' csupₛ_le _ _
  · simp only [nonempty_image_iff]
    exact (forall_mem_nonempty_iff_neBot.2 A) _ self_mem_nhdsWithin
  · simp only [mem_image, mem_Iio, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro z hz
    exact hf (hz.le.trans h)
#align monotone.left_lim_le Monotone.leftLim_le

theorem le_leftLim (h : x < y) : f x ≤ leftLim f y := by
  letI : TopologicalSpace α := Preorder.topology α
  haveI : OrderTopology α := ⟨rfl⟩
  rcases eq_or_ne (𝓝[<] y) ⊥ with (h' | h')
  · rw [leftLim_eq_of_eq_bot _ h']
    exact hf h.le
  rw [leftLim_eq_supₛ hf h']
  refine' le_csupₛ ⟨f y, _⟩ (mem_image_of_mem _ h)
  simp only [upperBounds, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_setOf_eq]
  intro z hz
  exact hf hz.le
#align monotone.le_left_lim Monotone.le_leftLim

@[mono]
protected theorem leftLim : Monotone (leftLim f) := by
  intro x y h
  rcases eq_or_lt_of_le h with (rfl | hxy)
  · exact le_rfl
  · exact (hf.leftLim_le le_rfl).trans (hf.le_leftLim hxy)
#align monotone.left_lim Monotone.leftLim

theorem le_rightLim (h : x ≤ y) : f x ≤ rightLim f y :=
  hf.dual.leftLim_le h
#align monotone.le_right_lim Monotone.le_rightLim

theorem rightLim_le (h : x < y) : rightLim f x ≤ f y :=
  hf.dual.le_leftLim h
#align monotone.right_lim_le Monotone.rightLim_le

@[mono]
protected theorem rightLim : Monotone (rightLim f) := fun _ _ h => hf.dual.leftLim h
#align monotone.right_lim Monotone.rightLim

theorem leftLim_le_rightLim (h : x ≤ y) : leftLim f x ≤ rightLim f y :=
  (hf.leftLim_le le_rfl).trans (hf.le_rightLim h)
#align monotone.left_lim_le_right_lim Monotone.leftLim_le_rightLim

theorem rightLim_le_leftLim (h : x < y) : rightLim f x ≤ leftLim f y := by
  letI : TopologicalSpace α := Preorder.topology α
  haveI : OrderTopology α := ⟨rfl⟩
  rcases eq_or_ne (𝓝[<] y) ⊥ with (h' | h')
  · simp [leftLim, h']
    exact rightLim_le hf h
  obtain ⟨a, ⟨xa, ay⟩⟩ : (Ioo x y).Nonempty :=
    forall_mem_nonempty_iff_neBot.2 (neBot_iff.2 h') (Ioo x y)
      (Ioo_mem_nhdsWithin_Iio ⟨h, le_refl _⟩)
  calc
    rightLim f x ≤ f a := hf.rightLim_le xa
    _ ≤ leftLim f y := hf.le_leftLim ay

#align monotone.right_lim_le_left_lim Monotone.rightLim_le_leftLim

variable [TopologicalSpace α] [OrderTopology α]

theorem tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x)) := by
  rcases eq_or_ne (𝓝[<] x) ⊥ with (h' | h')
  · simp [h']
  rw [leftLim_eq_supₛ hf h']
  exact hf.tendsto_nhdsWithin_Iio x
#align monotone.tendsto_left_lim Monotone.tendsto_leftLim

theorem tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[≤] leftLim f x) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (hf.tendsto_leftLim x)
  filter_upwards [@self_mem_nhdsWithin _ _ x (Iio x)] with y hy using hf.le_leftLim hy
#align monotone.tendsto_left_lim_within Monotone.tendsto_leftLim_within

theorem tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x)) :=
  hf.dual.tendsto_leftLim x
#align monotone.tendsto_right_lim Monotone.tendsto_rightLim

theorem tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[≥] rightLim f x) :=
  hf.dual.tendsto_leftLim_within x
#align monotone.tendsto_right_lim_within Monotone.tendsto_rightLim_within

/-- A monotone function is continuous to the left at a point if and only if its left limit
coincides with the value of the function. -/
theorem continuousWithinAt_Iio_iff_leftLim_eq :
    ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x := by
  rcases eq_or_ne (𝓝[<] x) ⊥ with (h' | h')
  · simp [leftLim_eq_of_eq_bot f h', ContinuousWithinAt, h']
  haveI : (𝓝[Iio x] x).NeBot := neBot_iff.2 h'
  refine' ⟨fun h => tendsto_nhds_unique (hf.tendsto_leftLim x) h.tendsto, fun h => _⟩
  have := hf.tendsto_leftLim x
  rwa [h] at this
#align monotone.continuous_within_at_Iio_iff_left_lim_eq Monotone.continuousWithinAt_Iio_iff_leftLim_eq

/-- A monotone function is continuous to the right at a point if and only if its right limit
coincides with the value of the function. -/
theorem continuousWithinAt_Ioi_iff_rightLim_eq :
    ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x :=
  hf.dual.continuousWithinAt_Iio_iff_leftLim_eq
#align monotone.continuous_within_at_Ioi_iff_right_lim_eq Monotone.continuousWithinAt_Ioi_iff_rightLim_eq

/-- A monotone function is continuous at a point if and only if its left and right limits
coincide. -/
theorem continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x := by
  refine' ⟨fun h => _, fun h => _⟩
  · have A : leftLim f x = f x :=
      hf.continuousWithinAt_Iio_iff_leftLim_eq.1 h.continuousWithinAt
    have B : rightLim f x = f x :=
      hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 h.continuousWithinAt
    exact A.trans B.symm
  · have h' : leftLim f x = f x :=
      by
      apply le_antisymm (leftLim_le hf (le_refl _))
      rw [h]
      exact le_rightLim hf (le_refl _)
    refine' continuousAt_iff_continuous_left'_right'.2 ⟨_, _⟩
    · exact hf.continuousWithinAt_Iio_iff_leftLim_eq.2 h'
    · rw [h] at h'
      exact hf.continuousWithinAt_Ioi_iff_rightLim_eq.2 h'
#align monotone.continuous_at_iff_left_lim_eq_right_lim Monotone.continuousAt_iff_leftLim_eq_rightLim

/-- In a second countable space, the set of points where a monotone function is not right-continuous
is at most countable. Superseded by `countable_not_continuousAt` which gives the two-sided
version. -/
theorem countable_not_continuousWithinAt_Ioi [TopologicalSpace.SecondCountableTopology β] :
    Set.Countable { x | ¬ContinuousWithinAt f (Ioi x) x } := by
  /- If `f` is not continuous on the right at `x`, there is an interval `(f x, z x)` which is not
    reached by `f`. This gives a family of disjoint open intervals in `β`. Such a family can only
    be countable as `β` is second-countable. -/
  nontriviality α
  let s := { x | ¬ContinuousWithinAt f (Ioi x) x }
  have : ∀ x, x ∈ s → ∃ z, f x < z ∧ ∀ y, x < y → z ≤ f y :=
    by
    rintro x (hx : ¬ContinuousWithinAt f (Ioi x) x)
    contrapose! hx
    refine' tendsto_order.2 ⟨fun m hm => _, fun u hu => _⟩
    · filter_upwards [@self_mem_nhdsWithin _ _ x (Ioi x)] with y hy using hm.trans_le
        (hf (le_of_lt hy))
    rcases hx u hu with ⟨v, xv, fvu⟩
    have : Ioo x v ∈ 𝓝[>] x := Ioo_mem_nhdsWithin_Ioi ⟨le_refl _, xv⟩
    filter_upwards [this]with y hy
    apply (hf hy.2.le).trans_lt fvu
  -- choose `z x` such that `f` does not take the values in `(f x, z x)`.
  choose! z hz using this
  have I : InjOn f s := by
    apply StrictMonoOn.injOn
    intro x hx y _ hxy
    calc
      f x < z x := (hz x hx).1
      _ ≤ f y := (hz x hx).2 y hxy

  -- show that `f s` is countable by arguing that a disjoint family of disjoint open intervals
  -- (the intervals `(f x, z x)`) is at most countable.
  have fs_count : (f '' s).Countable :=
    by
    have A : (f '' s).PairwiseDisjoint fun x => Ioo x (z (invFunOn f s x)) := by
      rintro _ ⟨u, us, rfl⟩ _ ⟨v, vs, rfl⟩ huv
      wlog hle : u ≤ v generalizing u v
      · exact (this v vs u us huv.symm (le_of_not_le hle)).symm
      have hlt : u < v := hle.lt_of_ne (ne_of_apply_ne _ huv)
      apply disjoint_iff_forall_ne.2
      rintro a ha b hb rfl
      simp only [I.leftInvOn_invFunOn us, I.leftInvOn_invFunOn vs] at ha hb
      exact lt_irrefl _ ((ha.2.trans_le ((hz u us).2 v hlt)).trans hb.1)
    apply Set.PairwiseDisjoint.countable_of_Ioo A
    rintro _ ⟨y, ys, rfl⟩
    simpa only [I.leftInvOn_invFunOn ys] using (hz y ys).1
  exact MapsTo.countable_of_injOn (mapsTo_image f s) I fs_count
#align monotone.countable_not_continuous_within_at_Ioi Monotone.countable_not_continuousWithinAt_Ioi

/-- In a second countable space, the set of points where a monotone function is not left-continuous
is at most countable. Superseded by `countable_not_continuousAt` which gives the two-sided
version. -/
theorem countable_not_continuousWithinAt_Iio [TopologicalSpace.SecondCountableTopology β] :
    Set.Countable { x | ¬ContinuousWithinAt f (Iio x) x } :=
  hf.dual.countable_not_continuousWithinAt_Ioi
#align monotone.countable_not_continuous_within_at_Iio Monotone.countable_not_continuousWithinAt_Iio

/-- In a second countable space, the set of points where a monotone function is not continuous
is at most countable. -/
theorem countable_not_continuousAt [TopologicalSpace.SecondCountableTopology β] :
    Set.Countable { x | ¬ContinuousAt f x } := by
  apply
    (hf.countable_not_continuousWithinAt_Ioi.union hf.countable_not_continuousWithinAt_Iio).mono
      _
  refine' compl_subset_compl.1 _
  simp only [compl_union]
  rintro x ⟨hx, h'x⟩
  simp only [mem_setOf_eq, Classical.not_not, mem_compl_iff] at hx h'x⊢
  exact continuousAt_iff_continuous_left'_right'.2 ⟨h'x, hx⟩
#align monotone.countable_not_continuous_at Monotone.countable_not_continuousAt

end Monotone

namespace Antitone

variable {α β : Type _} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Antitone f) {x y : α}

theorem le_leftLim (h : x ≤ y) : f y ≤ leftLim f x :=
  hf.dual_right.leftLim_le h
#align antitone.le_left_lim Antitone.le_leftLim

theorem leftLim_le (h : x < y) : leftLim f y ≤ f x :=
  hf.dual_right.le_leftLim h
#align antitone.left_lim_le Antitone.leftLim_le

@[mono]
protected theorem leftLim : Antitone (leftLim f) :=
  hf.dual_right.leftLim
#align antitone.left_lim Antitone.leftLim

theorem rightLim_le (h : x ≤ y) : rightLim f y ≤ f x :=
  hf.dual_right.le_rightLim h
#align antitone.right_lim_le Antitone.rightLim_le

theorem le_rightLim (h : x < y) : f y ≤ rightLim f x :=
  hf.dual_right.rightLim_le h
#align antitone.le_right_lim Antitone.le_rightLim

@[mono]
protected theorem rightLim : Antitone (rightLim f) :=
  hf.dual_right.rightLim
#align antitone.right_lim Antitone.rightLim

theorem rightLim_le_leftLim (h : x ≤ y) : rightLim f y ≤ leftLim f x :=
  hf.dual_right.leftLim_le_rightLim h
#align antitone.right_lim_le_left_lim Antitone.rightLim_le_leftLim

theorem leftLim_le_rightLim (h : x < y) : leftLim f y ≤ rightLim f x :=
  hf.dual_right.rightLim_le_leftLim h
#align antitone.left_lim_le_right_lim Antitone.leftLim_le_rightLim

variable [TopologicalSpace α] [OrderTopology α]

theorem tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x)) :=
  hf.dual_right.tendsto_leftLim x
#align antitone.tendsto_left_lim Antitone.tendsto_leftLim

theorem tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[≥] leftLim f x) :=
  hf.dual_right.tendsto_leftLim_within x
#align antitone.tendsto_left_lim_within Antitone.tendsto_leftLim_within

theorem tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x)) :=
  hf.dual_right.tendsto_rightLim x
#align antitone.tendsto_right_lim Antitone.tendsto_rightLim

theorem tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[≤] rightLim f x) :=
  hf.dual_right.tendsto_rightLim_within x
#align antitone.tendsto_right_lim_within Antitone.tendsto_rightLim_within

/-- An antitone function is continuous to the left at a point if and only if its left limit
coincides with the value of the function. -/
theorem continuousWithinAt_Iio_iff_leftLim_eq :
    ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x :=
  hf.dual_right.continuousWithinAt_Iio_iff_leftLim_eq
#align antitone.continuous_within_at_Iio_iff_left_lim_eq Antitone.continuousWithinAt_Iio_iff_leftLim_eq

/-- An antitone function is continuous to the right at a point if and only if its right limit
coincides with the value of the function. -/
theorem continuousWithinAt_Ioi_iff_rightLim_eq :
    ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x :=
  hf.dual_right.continuousWithinAt_Ioi_iff_rightLim_eq
#align antitone.continuous_within_at_Ioi_iff_right_lim_eq Antitone.continuousWithinAt_Ioi_iff_rightLim_eq

/-- An antitone function is continuous at a point if and only if its left and right limits
coincide. -/
theorem continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x :=
  hf.dual_right.continuousAt_iff_leftLim_eq_rightLim
#align antitone.continuous_at_iff_left_lim_eq_right_lim Antitone.continuousAt_iff_leftLim_eq_rightLim

/-- In a second countable space, the set of points where an antitone function is not continuous
is at most countable. -/
theorem countable_not_continuousAt [TopologicalSpace.SecondCountableTopology β] :
    Set.Countable { x | ¬ContinuousAt f x } :=
  hf.dual_right.countable_not_continuousAt
#align antitone.countable_not_continuous_at Antitone.countable_not_continuousAt

end Antitone
