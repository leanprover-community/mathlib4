/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Topology.Path
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Primitive paths

A primitive path is either an injective path or a simple loop: it has no repeated values except
possibly at its two endpoints. No separation assumption on the ambient space is required.

## Main definitions

* `Path.IsPrimitive`: a path can identify distinct parameters only when they are `0` and `1`.
* `Path.IsSimpleLoop`: a loop is injective on `[0, 1)`.

## Main results

* `Path.isPrimitive_iff_injective` and `Path.isPrimitive_iff_isSimpleLoop` characterize primitive
  paths with distinct and equal endpoints, respectively.
* `Path.IsPrimitive.range_diff_endpoints` identifies the path interior with its range minus
  its endpoints. This set is nonempty and path-connected.
* `Path.IsPrimitive.symm` and `Path.IsPrimitive.map` preserve primitivity under reversal and
  continuous maps injective on the path range.

The general definition `Path.interior` is in `Mathlib.Topology.Path`.
The path interior is a parameter-image construction, not the topological interior of its range.
For a general path it can contain the endpoints; primitivity rules this out.
-/

@[expose] public section

open Set Function unitInterval

variable {X : Type*} [TopologicalSpace X] {x y : X} {γ : Path x y} {s t : I}

namespace Path

/-- A path is primitive if it is injectively parametrized, except that a loop may identify its
two endpoints. In particular, a constant path is not primitive. -/
def IsPrimitive (γ : Path x y) : Prop :=
  ∀ ⦃s t : I⦄, γ s = γ t → s = t ∨ ({s, t} : Set I) = {0, 1}

/-- A simple loop visits each point at most once before returning to its starting point. -/
def IsSimpleLoop (γ : Path x x) : Prop := InjOn γ (Ico 0 1)

lemma IsPrimitive.of_injective (h : Injective γ) : γ.IsPrimitive :=
  fun _ _ hst ↦ Or.inl (h hst)

/-- With distinct endpoints, primitivity is equivalent to injectivity on the whole interval. -/
lemma isPrimitive_iff_injective (hxy : x ≠ y) : γ.IsPrimitive ↔ Injective γ :=
  ⟨fun h _ _ hst ↦ (h hst).elim id fun hp ↦ (hxy (source_eq_target_of_eq_of_pair hst hp)).elim,
    fun h _ _ hst ↦ Or.inl (h hst)⟩
alias ⟨IsPrimitive.injective, _⟩ := isPrimitive_iff_injective

lemma IsSimpleLoop.isPrimitive {γ : Path x x} (h : γ.IsSimpleLoop) : γ.IsPrimitive := by
  intro s t hst
  by_cases hs1 : s = 1 <;> by_cases ht1 : t = 1
  · exact Or.inl (hs1.trans ht1.symm)
  · refine Or.inr ?_
    have htI : t ∈ Ico (0 : I) 1 := ⟨t.2.1, lt_of_le_of_ne t.2.2 ht1⟩
    have hγ : γ t = γ 0 :=
      (hst.symm.trans (congrArg γ hs1)).trans (γ.target.trans γ.source.symm)
    have ht0 : t = 0 := h htI (by simp) hγ
    rw [hs1, ht0, pair_comm]
  · refine Or.inr ?_
    have hsI : s ∈ Ico (0 : I) 1 := ⟨s.2.1, lt_of_le_of_ne s.2.2 hs1⟩
    have hγ : γ s = γ 0 :=
      (hst.trans (congrArg γ ht1)).trans (γ.target.trans γ.source.symm)
    have hs0 : s = 0 := h hsI (by simp) hγ
    rw [hs0, ht1]
  exact Or.inl <| h ⟨s.2.1, lt_of_le_of_ne s.2.2 hs1⟩ ⟨t.2.1, lt_of_le_of_ne t.2.2 ht1⟩ hst

lemma IsPrimitive.isSimpleLoop {γ : Path x x} (h : γ.IsPrimitive) : γ.IsSimpleLoop := by
  intro s hs t ht hst
  obtain rfl | hp := h hst
  · rfl
  have h1 : (1 : I) ∈ Ico (0 : I) 1 := by
    have : (1 : I) ∈ ({s, t} : Set I) := hp ▸ (by simp : (1 : I) ∈ ({0, 1} : Set I))
    exact this.elim (fun h1 ↦ h1 ▸ hs) (fun h1 ↦ h1 ▸ ht)
  exact (not_le_of_gt h1.2 le_rfl).elim

/-- For a loop, primitivity is equivalent to injectivity before the final parameter. -/
lemma isPrimitive_iff_isSimpleLoop {γ : Path x x} : γ.IsPrimitive ↔ γ.IsSimpleLoop :=
  ⟨IsPrimitive.isSimpleLoop, IsSimpleLoop.isPrimitive⟩

/-- A primitive path is injective, or is a simple loop after identifying its endpoints. -/
lemma isPrimitive_iff : γ.IsPrimitive ↔ Injective γ ∨ ∃ h : x = y, (γ.cast rfl h).IsSimpleLoop := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain rfl | hxy := eq_or_ne x y
    · exact Or.inr ⟨rfl, h.isSimpleLoop⟩
    exact Or.inl (h.injective hxy)
  rintro (hinj | ⟨rfl, hloop⟩)
  · exact IsPrimitive.of_injective hinj
  rw [cast_rfl_rfl] at hloop
  exact hloop.isPrimitive

@[simp]
lemma not_isPrimitive_refl : ¬ (Path.refl x).IsPrimitive := by
  obtain ⟨t, ht0, ht1⟩ := exists_between (zero_lt_one : (0 : I) < 1)
  intro h
  obtain h0t | hp := h (s := 0) (t := t) (by simp)
  · exact ht0.ne h0t
  obtain ⟨_, ht⟩ | ⟨h01, _⟩ := pair_eq_pair_iff.mp hp
  · exact ht1.ne ht
  exact zero_ne_one h01

/-- Reversing a primitive path preserves primitivity. -/
lemma IsPrimitive.symm (h : γ.IsPrimitive) : γ.symm.IsPrimitive := by
  intro s t hst
  rw [symm_apply, symm_apply] at hst
  refine (h hst).imp (fun hs ↦ symm_inj.mp hs) (fun hp ↦ ?_)
  rw [pair_eq_pair_iff] at hp ⊢
  simpa [symm_eq_zero, symm_eq_one, or_comm] using hp

lemma IsPrimitive.injOn_Ioo (h : γ.IsPrimitive) : InjOn γ (Ioo (0 : I) 1) := by
  intro s hs t _ hst
  obtain rfl | hp := h hst
  · rfl
  have hs01 : s ∈ ({0, 1} : Set I) := hp ▸ mem_insert s {t}
  have hsI := mem_Ioo_iff.mp hs
  exact hs01.elim (fun h0 ↦ (hsI.1 h0).elim) (fun h1 ↦ (hsI.2 (mem_singleton_iff.mp h1)).elim)

lemma IsPrimitive.source_notMem_interior (h : γ.IsPrimitive) : x ∉ γ.interior := by
  rintro ⟨t, ht, htx⟩
  obtain ht0 | hp := h (htx.trans γ.source.symm)
  · exact (mem_Ioo_iff.mp ht).1 ht0
  obtain ⟨rfl, h01⟩ | ⟨rfl, _⟩ := pair_eq_pair_iff.mp hp
  · exact zero_ne_one h01
  exact (mem_Ioo_iff.mp ht).2 rfl

lemma IsPrimitive.target_notMem_interior (h : γ.IsPrimitive) : y ∉ γ.interior := by
  rintro ⟨t, ht, hty⟩
  obtain ht1 | hp := h (hty.trans γ.target.symm)
  · exact (mem_Ioo_iff.mp ht).2 ht1
  obtain ⟨rfl, _⟩ | ⟨rfl, h10⟩ := pair_eq_pair_iff.mp hp
  · exact (mem_Ioo_iff.mp ht).1 rfl
  exact one_ne_zero h10

/-- Removing the endpoints from the range of a primitive path leaves exactly the image of
its open parameter interval. -/
lemma IsPrimitive.range_diff_endpoints (h : γ.IsPrimitive) : range γ \ {x, y} = γ.interior := by
  ext z
  refine ⟨?_, fun hz ↦ ⟨interior_subset_range γ hz, ?_⟩⟩
  · rintro ⟨⟨t, rfl⟩, hne⟩
    obtain ht0 | ht1 | ht := eq_zero_or_eq_one_or_mem_Ioo t
    · rw [ht0, Path.source] at hne
      exact (hne (mem_insert _ _)).elim
    · rw [ht1, Path.target] at hne
      exact (hne (by simp)).elim
    exact ⟨t, ht, rfl⟩
  rintro (rfl | rfl)
  · exact h.source_notMem_interior hz
  exact h.target_notMem_interior hz

lemma IsPrimitive.range_diff_endpoints_nonempty (h : γ.IsPrimitive) :
    (range γ \ {x, y}).Nonempty := by
  rw [h.range_diff_endpoints]
  exact (nonempty_Ioo.2 (zero_lt_one : (0 : I) < 1)).image _

/-- The range of a primitive path remains path-connected after removing its endpoints. -/
lemma IsPrimitive.isPathConnected_range_diff_endpoints (h : γ.IsPrimitive) :
    IsPathConnected (range γ \ {x, y}) := by
  rw [h.range_diff_endpoints]
  exact (isPathConnected_Ioo (zero_lt_one : (0 : I) < 1)).image γ.continuous

lemma IsPrimitive.isConnected_range_diff_endpoints (h : γ.IsPrimitive) :
    IsConnected (range γ \ {x, y}) :=
  h.isPathConnected_range_diff_endpoints.isConnected

/-- A continuous map that is injective on the path range preserves primitivity. -/
lemma IsPrimitive.map {Y : Type*} [TopologicalSpace Y] {f : X → Y} (h : γ.IsPrimitive)
    (hf : ContinuousOn f (range γ)) (hinj : InjOn f (range γ)) : (γ.map' hf).IsPrimitive := by
  intro s t hst
  exact h (hinj (mem_range_self s) (mem_range_self t) hst)

end Path
