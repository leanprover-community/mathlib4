/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.ExtendFrom
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Lemmas about `extendFrom` in an order topology.
-/

public section

open Filter Set Topology

variable {α β : Type*} [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α] [OrderTopology α]
  [TopologicalSpace β] {f : α → β} {a b : α} {la lb : β}

section RegularSpace

variable [RegularSpace β]

theorem continuousOn_Icc_extendFrom_Ioo
    (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la))
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) := by
  by_cases! hab : a = b
  · simp [hab]
  apply continuousOn_extendFrom
  · rw [closure_Ioo hab]
  · intro x x_in
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc x_in with (rfl | rfl | h)
    · exact ⟨la, ha.mono_left <| nhdsWithin_mono _ Ioo_subset_Ioi_self⟩
    · exact ⟨lb, hb.mono_left <| nhdsWithin_mono _ Ioo_subset_Iio_self⟩
    · exact ⟨f x, hf x h⟩

theorem continuousOn_uIcc_extendFrom_uIoo
    (hf : ContinuousOn f (uIoo a b))
    (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 la)) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (uIoo a b) f) (uIcc a b) := by
  by_cases! hab : a = b
  · simp [hab]
  obtain hab' | hba' := hab.lt_or_gt
  · simp only [hab', uIoo_of_lt, nhdsWithin_Ioo_eq_nhdsGT, nhdsWithin_Ioo_eq_nhdsLT,
      uIcc_of_lt] at ha hb hf ⊢
    exact continuousOn_Icc_extendFrom_Ioo hf ha hb
  · simp only [hba', uIoo_of_gt, nhdsWithin_Ioo_eq_nhdsGT, nhdsWithin_Ioo_eq_nhdsLT,
      uIcc_of_gt] at ha hb hf ⊢
    exact continuousOn_Icc_extendFrom_Ioo hf hb ha

theorem continuousOn_Ico_extendFrom_Ioo
    (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ico a b) := by
  by_cases! hab : a ≥ b
  · simp [hab]
  apply continuousOn_extendFrom
  · rw [closure_Ioo hab.ne]
    exact Ico_subset_Icc_self
  · intro x x_in
    rcases eq_left_or_mem_Ioo_of_mem_Ico x_in with (rfl | h)
    · use la
      simpa [hab]
    · exact ⟨f x, hf x h⟩

theorem continuousOn_Ioc_extendFrom_Ioo
    (hf : ContinuousOn f (Ioo a b)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b) := by
  have := continuousOn_Ico_extendFrom_Ioo (f := f ∘ OrderDual.ofDual) (a := OrderDual.toDual b)
    (b := OrderDual.toDual a) (la := lb)
  rw [Ico_toDual, Ioi_toDual, Ioo_toDual] at this
  exact this hf hb

end RegularSpace

section T2Space

variable [T2Space β]

theorem eq_lim_at_left_extendFrom_Ioo (hab : a < b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 la)) : extendFrom (Ioo a b) f a = la := by
  apply extendFrom_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_lt hab, left_mem_Icc]
  · simpa [hab]

theorem eq_lim_at_right_extendFrom_Ioo (hab : a < b)
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : extendFrom (Ioo a b) f b = lb := by
  apply extendFrom_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_lt hab, right_mem_Icc]
  · simpa [hab]

theorem eq_lim_at_left_extendFrom_uIoo (hab : a ≠ b)
    (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 la)) : extendFrom (uIoo a b) f a = la :=
  extendFrom_eq (by simp [hab]) ha

theorem eq_lim_at_right_extendFrom_uIoo (hab : a ≠ b)
    (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 lb)) : extendFrom (uIoo a b) f b = lb :=
  extendFrom_eq (by simp [hab]) hb

end T2Space
