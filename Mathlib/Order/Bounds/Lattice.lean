/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Set.Lattice

/-!
# Unions and intersections of bounds

## Implementation notes

`Mathlib.Data.Set.Lattice` is needed for `subset_iUnion_of_subset`.

-/

variable {γ : Type*} [Preorder γ]

open Set

theorem upperBounds_iUnion {ι : Sort*} {s : ι → Set γ} :
    upperBounds (⋃ i, s i) = ⋂ i, upperBounds (s i)  := Subset.antisymm
  (fun _ hb => mem_iInter.mpr
    (fun i => upperBounds_mono_set (subset_iUnion_of_subset i (by rfl)) hb))
  (fun _ _ _ _ => by aesop)

theorem lowerBounds_iUnion {ι : Sort*} {s : ι → Set γ} :
    lowerBounds (⋃ i, s i) = ⋂ i, lowerBounds (s i) := Subset.antisymm
  (fun _ hb => mem_iInter.mpr
    (fun i => lowerBounds_mono_set (subset_iUnion_of_subset i (by rfl)) hb))
  (fun _ _ _ _ => by aesop)

theorem IsLUB.iUnion {ι : Sort*} {u : ι → γ}  {s : ι → Set γ} (hs : ∀ (i : ι), IsLUB (s i) (u i))
    (c : γ) (hc : IsLUB (Set.range u ) c) : IsLUB (⋃ i, s i) c := by
  constructor
  · intro e he
    obtain ⟨i,hi⟩ := mem_iUnion.mp he
    obtain ⟨hc₁,hc₂⟩ := hc
    simp only [upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      mem_setOf_eq] at hc₁
    obtain ⟨hs₁,_⟩ := hs i
    exact Preorder.le_trans e (u i) c (hs₁ hi) (hc₁ i)
  · intro e he
    rw [upperBounds_iUnion] at he
    apply hc.2
    simp only [upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff, mem_setOf_eq]
    exact fun i => (hs i).2 (he _ (mem_range_self i))

theorem IsGLB.iUnion {ι : Sort*} {u : ι → γ}  {s : ι → Set γ} (hs : ∀ (i : ι), IsGLB (s i) (u i))
    (c : γ) (hc : IsGLB (Set.range u ) c) : IsGLB (⋃ i, s i) c := by
  constructor
  · intro e he
    obtain ⟨i,hi⟩ := mem_iUnion.mp he
    obtain ⟨hc₁,hc₂⟩ := hc
    simp only [lowerBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      mem_setOf_eq] at hc₁
    obtain ⟨hs₁,_⟩ := hs i
    exact Preorder.le_trans c (u i) e (hc₁ i) (hs₁ hi)
  · intro e he
    rw [lowerBounds_iUnion] at he
    apply hc.2
    simp only [lowerBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff, mem_setOf_eq]
    exact fun i => (hs i).2 (he _ (mem_range_self i))
