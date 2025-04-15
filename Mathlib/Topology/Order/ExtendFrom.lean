/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Lemmas about `extendFrom` in an order topology.
-/

open Filter Set Topology

variable {α β : Type*}

theorem continuousOn_Icc_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la lb : β}
    (hab : a ≠ b) (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la))
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) := by
  apply continuousOn_extendFrom
  · rw [closure_Ioo hab]
  · intro x x_in
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc x_in with (rfl | rfl | h)
    · exact ⟨la, ha.mono_left <| nhdsWithin_mono _ Ioo_subset_Ioi_self⟩
    · exact ⟨lb, hb.mono_left <| nhdsWithin_mono _ Ioo_subset_Iio_self⟩
    · exact ⟨f x, hf x h⟩

theorem eq_lim_at_left_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {la : β} (hab : a < b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 la)) : extendFrom (Ioo a b) f a = la := by
  apply extendFrom_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc]
  · simpa [hab]

theorem eq_lim_at_right_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {lb : β} (hab : a < b)
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : extendFrom (Ioo a b) f b = lb := by
  apply extendFrom_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc]
  · simpa [hab]

theorem continuousOn_Ico_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la : β}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ico a b) := by
  apply continuousOn_extendFrom
  · rw [closure_Ioo hab.ne]
    exact Ico_subset_Icc_self
  · intro x x_in
    rcases eq_left_or_mem_Ioo_of_mem_Ico x_in with (rfl | h)
    · use la
      simpa [hab]
    · exact ⟨f x, hf x h⟩

theorem continuousOn_Ioc_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {lb : β}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b) := by
  have := @continuousOn_Ico_extendFrom_Ioo αᵒᵈ _ _ _ _ _ _ _ f _ _ lb hab
  erw [Ico_toDual, Ioi_toDual, Ioo_toDual] at this
  exact this hf hb
