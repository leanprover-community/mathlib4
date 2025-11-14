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

variable {α β : Type*} [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α] [OrderTopology α]
  [TopologicalSpace β] {f : α → β} {a b : α} {la lb : β}

section RegularSpace

variable [RegularSpace β]

theorem continuousOn_Icc_extendFrom_Ioo
    (hab : a ≠ b) (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la))
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) := by
  apply continuousOn_extendFrom
  · rw [closure_Ioo hab]
  · intro x x_in
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc x_in with (rfl | rfl | h)
    · exact ⟨la, ha.mono_left <| nhdsWithin_mono _ Ioo_subset_Ioi_self⟩
    · exact ⟨lb, hb.mono_left <| nhdsWithin_mono _ Ioo_subset_Iio_self⟩
    · exact ⟨f x, hf x h⟩

theorem continuousOn_uIcc_extendFrom_uIoo
    (hab : a ≠ b) (hf : ContinuousOn f (uIoo a b)) (ha : Tendsto f (𝓝[≠] a) (𝓝 la))
    (hb : Tendsto f (𝓝[≠] b) (𝓝 lb)) : ContinuousOn (extendFrom (uIoo a b) f) (uIcc a b) := by
  obtain ⟨la, hla⟩ : ∃ la, Tendsto f (𝓝[>] min a b) (𝓝 la) :=
    min_rec' (fun i ↦ ∃ la, Tendsto f (𝓝[>] i) (𝓝 la))
      ⟨_, ha.mono_left (nhdsGT_le_nhdsNE _)⟩
      ⟨_, hb.mono_left (nhdsGT_le_nhdsNE _)⟩
  obtain ⟨lb, hlb⟩ : ∃ lb, Tendsto f (𝓝[<] max a b) (𝓝 lb) :=
    max_rec' (fun i ↦ ∃ lb, Tendsto f (𝓝[<] i) (𝓝 lb))
      ⟨_, ha.mono_left (nhdsLT_le_nhdsNE _)⟩
      ⟨_, hb.mono_left (nhdsLT_le_nhdsNE _)⟩
  exact continuousOn_Icc_extendFrom_Ioo (by simp [hab]) hf hla hlb

theorem continuousOn_Ico_extendFrom_Ioo
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

theorem continuousOn_Ioc_extendFrom_Ioo
    (hab : a < b) (hf : ContinuousOn f (Ioo a b)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b) := by
  have := continuousOn_Ico_extendFrom_Ioo (f := f ∘ OrderDual.ofDual) (la := lb) hab.dual
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
    (ha : Tendsto f (𝓝[≠] a) (𝓝 la)) : extendFrom (uIoo a b) f a = la :=
  extendFrom_eq (by simp [hab]) (ha.mono_left nhdsWithin_uIoo_left_le_nhdsNE)

theorem eq_lim_at_right_extendFrom_uIoo (hab : a ≠ b)
    (hb : Tendsto f (𝓝[≠] b) (𝓝 lb)) : extendFrom (uIoo a b) f b = lb :=
  extendFrom_eq (by simp [hab]) (hb.mono_left nhdsWithin_uIoo_right_le_nhdsNE)

end T2Space
