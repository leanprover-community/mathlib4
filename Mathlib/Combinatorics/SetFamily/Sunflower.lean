/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Slice
public import Mathlib.Tactic.Ring

/-!
# Sunflowers and the Erdős–Rado sunflower lemma

A *sunflower* (or *Δ-system*) with kernel `k` is a family of sets any two distinct members of
which intersect exactly in `k`. The Erdős–Rado sunflower lemma states that a family of more than
`(p - 1) ^ r * r !` sets of size at most `r` contains a sunflower with `p` petals.

## Main definitions

* `Set.IsSunflower`: Predicate for a family of elements of a meet-semilattice to be a sunflower
  with a given kernel.

## Main statements

* `Finset.exists_isSunflower_of_forall_card_le`: The Erdős–Rado sunflower lemma. A family of more
  than `(p - 1) ^ r * r !` sets of size at most `r` contains a sunflower with `p` petals.
* `Finset.exists_isSunflower_of_sized`: The Erdős–Rado sunflower lemma for `r`-uniform families.

## References

* [P. Erdős, R. Rado, *Intersection theorems for systems of sets*][erdosRado1960]

## Tags

sunflower, delta system, Erdős–Rado
-/

public section

open Finset Nat

namespace Set

section SemilatticeInf

variable {α β : Type*} [SemilatticeInf α] [SemilatticeInf β] {s t : Set α} {a k : α}

/-- A family `s` is a *sunflower* with kernel `k` if any two distinct members of `s` meet exactly
in `k`. Note that a family with fewer than two members is a sunflower with any kernel. -/
@[expose] def IsSunflower (s : Set α) (k : α) : Prop := s.Pairwise fun a b ↦ a ⊓ b = k

@[gcongr, mono]
theorem IsSunflower.mono (h : t ⊆ s) (hs : s.IsSunflower k) : t.IsSunflower k :=
  Set.Pairwise.mono h hs

@[simp] theorem isSunflower_empty : (∅ : Set α).IsSunflower k := pairwise_empty _

@[simp] theorem isSunflower_singleton : ({a} : Set α).IsSunflower k := pairwise_singleton _ _

protected theorem Subsingleton.isSunflower (hs : s.Subsingleton) (k : α) : s.IsSunflower k :=
  hs.pairwise _

/-- The image of a sunflower under a meet-homomorphism is a sunflower. -/
theorem IsSunflower.image (hs : s.IsSunflower k) (f : InfHom α β) :
    (f '' s).IsSunflower (f k) :=
  (hs.imp fun _ _ h ↦ by rw [Function.onFun, ← map_inf, h]).image

theorem isSunflower_bot_iff_pairwiseDisjoint [OrderBot α] :
    s.IsSunflower ⊥ ↔ s.PairwiseDisjoint id := by
  simp only [IsSunflower, PairwiseDisjoint, Set.Pairwise, Function.onFun, id, disjoint_iff]

end SemilatticeInf

end Set

namespace Finset

variable {α : Type*} [DecidableEq α] {𝒜 : Finset (Finset α)} {r p : ℕ}

/-- **Erdős–Rado sunflower lemma**: a family of more than `(p - 1) ^ r * r !` sets of size at
most `r` contains a sunflower with `p` petals.

The statement is trivial for `p ≤ 1` and vacuous for `r = 0`. -/
theorem exists_isSunflower_of_forall_card_le (h𝒜 : ∀ s ∈ 𝒜, #s ≤ r)
    (h : (p - 1) ^ r * r ! < #𝒜) :
    ∃ 𝒮 ⊆ 𝒜, #𝒮 = p ∧ ∃ k : Finset α, (𝒮 : Set (Finset α)).IsSunflower k := by
  classical
  obtain hp | hp := le_or_gt p 1
  · obtain ⟨𝒮, h𝒮𝒜, h𝒮⟩ := exists_subset_card_eq (hp.trans ((Nat.zero_le _).trans_lt h))
    exact ⟨𝒮, h𝒮𝒜, h𝒮, ∅, (card_le_one_iff_subsingleton.1 (h𝒮 ▸ hp)).isSunflower _⟩
  induction r generalizing α 𝒜 with
  | zero =>
    have h𝒜' : 𝒜 ⊆ {∅} := fun s hs ↦ mem_singleton.2 <| card_eq_zero.1 <| Nat.le_zero.1 (h𝒜 s hs)
    have := card_le_card h𝒜'
    simp only [pow_zero, factorial_zero, mul_one] at h
    simp only [card_singleton] at this
    omega
  | succ r ih =>
    -- Let `𝒟` be a pairwise disjoint subfamily of `𝒜` of maximum size.
    obtain ⟨𝒟, h𝒟, hmax⟩ := ({𝒟 ∈ 𝒜.powerset | (𝒟 : Set (Finset α)).PairwiseDisjoint id} :
      Finset (Finset (Finset α))).exists_max_image card ⟨∅, by simp⟩
    obtain ⟨h𝒟𝒜, h𝒟⟩ := mem_filter.1 h𝒟
    rw [mem_powerset] at h𝒟𝒜
    obtain hp𝒟 | hp𝒟 := le_or_gt p #𝒟
    -- If `𝒟` has at least `p` members, any `p` of them form a sunflower with empty kernel.
    · obtain ⟨𝒮, h𝒮𝒟, h𝒮⟩ := exists_subset_card_eq hp𝒟
      exact ⟨𝒮, h𝒮𝒟.trans h𝒟𝒜, h𝒮, ⊥,
        Set.isSunflower_bot_iff_pairwiseDisjoint.2 <| h𝒟.subset (coe_subset.2 h𝒮𝒟)⟩
    -- Otherwise, by maximality, every member of `𝒜` outside `𝒟` meets some member of `𝒟`.
    have hmeet : ∀ s ∈ 𝒜, s ∉ 𝒟 → ∃ t ∈ 𝒟, ¬ Disjoint s t := by
      intro s hs hs𝒟
      by_contra! hdisj
      have := hmax (insert s 𝒟) <| mem_filter.2 ⟨mem_powerset.2 (insert_subset hs h𝒟𝒜), by
        rw [coe_insert]
        exact h𝒟.insert_of_notMem (by simpa using hs𝒟) hdisj⟩
      rw [card_insert_of_notMem hs𝒟] at this
      omega
    have hempty : ∅ ∈ 𝒜 → ∅ ∈ 𝒟 := fun hempty ↦ by
      by_contra hempty𝒟
      obtain ⟨t, -, ht⟩ := hmeet ∅ hempty hempty𝒟
      exact ht (disjoint_empty_left t)
    -- Hence every nonempty member of `𝒜` meets `X := ⋃ (𝒟 \ {∅})`, a set of at most
    -- `#(𝒟.erase ∅) * (r + 1)` elements.
    set X := (𝒟.erase ∅).biUnion id
    have hXcard : #X ≤ #(𝒟.erase ∅) * (r + 1) :=
      card_biUnion_le_card_mul _ _ _ fun s hs ↦ h𝒜 s (h𝒟𝒜 (mem_of_mem_erase hs))
    have hmeetX : ∀ s ∈ 𝒜.erase ∅, ∃ x ∈ X, x ∈ s := by
      intro s hs
      rw [mem_erase] at hs
      by_cases hs𝒟 : s ∈ 𝒟
      · obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hs.1
        exact ⟨x, mem_biUnion.2 ⟨s, mem_erase.2 ⟨hs.1, hs𝒟⟩, hx⟩, hx⟩
      · obtain ⟨t, ht, hst⟩ := hmeet s hs.2 hs𝒟
        obtain ⟨x, hxs, hxt⟩ := not_disjoint_iff.1 hst
        exact ⟨x, mem_biUnion.2 ⟨t, mem_erase.2 ⟨ne_empty_of_mem hxt, ht⟩, hxt⟩, hxs⟩
    -- Counting shows that some `x ∈ X` lies in more than `(p - 1) ^ r * r !` members of `𝒜`.
    have h₂ : (p - 1) ^ (r + 1) * (r + 1)! = (p - 1) * ((r + 1) * ((p - 1) ^ r * r !)) := by
      rw [pow_succ, factorial_succ]; ring
    rw [h₂] at h
    set b := ((p - 1) ^ r * r !)
    have hb₁ : 1 ≤ b :=
      Nat.one_le_iff_ne_zero.2 <| mul_ne_zero (pow_ne_zero _ (by omega)) (factorial_ne_zero r)
    have hlt : #X * b < #(𝒜.erase ∅) := by
      have h₁ : #X * b ≤ #(𝒟.erase ∅) * ((r + 1) * b) :=
        (Nat.mul_le_mul_right b hXcard).trans_eq (mul_assoc _ _ _)
      by_cases hempty𝒟 : ∅ ∈ 𝒟
      · obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (card_ne_zero.2 ⟨∅, hempty𝒟⟩)
        rw [card_erase_of_mem hempty𝒟, hn, Nat.add_sub_cancel] at h₁
        rw [card_erase_of_mem (h𝒟𝒜 hempty𝒟)]
        have h₃ : (n + 1) * ((r + 1) * b) ≤ (p - 1) * ((r + 1) * b) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul] at h₃
        have h₄ : 1 ≤ (r + 1) * b :=
          Nat.one_le_iff_ne_zero.2 <| Nat.mul_ne_zero (by omega) (by omega)
        omega
      · rw [erase_eq_of_notMem hempty𝒟] at h₁
        rw [erase_eq_of_notMem fun h ↦ hempty𝒟 (hempty h)]
        have h₃ : #𝒟 * ((r + 1) * b) ≤ (p - 1) * ((r + 1) * b) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
    obtain ⟨x, hx, hxlt⟩ : ∃ x ∈ X, b < #{s ∈ 𝒜 | x ∈ s} := by
      refine exists_lt_of_sum_lt ?_
      rw [sum_const, smul_eq_mul]
      refine hlt.trans_le <| (card_le_card fun s hs ↦ ?_).trans card_biUnion_le
      obtain ⟨x, hx, hxs⟩ := hmeetX s hs
      exact mem_biUnion.2 ⟨x, hx, mem_filter.2 ⟨mem_of_mem_erase hs, hxs⟩⟩
    -- Remove `x` from the members containing it and apply the induction hypothesis.
    have hxℬ : ∀ s ∈ ({s ∈ 𝒜 | x ∈ s} : Finset _).image (·.erase x), x ∉ s := fun s hs ↦ by
      obtain ⟨t, -, rfl⟩ := mem_image.1 hs
      exact notMem_erase x t
    obtain ⟨𝒮, h𝒮ℬ, h𝒮, k, hk⟩ := ih (𝒜 := ({s ∈ 𝒜 | x ∈ s} : Finset _).image (·.erase x))
      (fun s hs ↦ by
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hs
        rw [mem_filter] at ht
        rw [card_erase_of_mem ht.2]
        exact Nat.sub_le_of_le_add (h𝒜 t ht.1))
      (by
        rw [card_image_of_injOn]
        · exact hxlt
        · exact Set.InjOn.mono (fun s hs ↦ (mem_filter.1 hs).2) (erase_injOn' x))
    refine ⟨𝒮.image (insert x), fun s hs ↦ ?_, ?_, insert x k, ?_⟩
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 hs
      obtain ⟨u, hu, rfl⟩ := mem_image.1 (h𝒮ℬ ht)
      rw [mem_filter] at hu
      rw [insert_erase hu.2]
      exact hu.1
    · rw [card_image_of_injOn fun s hs t ht hst ↦ ?_, h𝒮]
      rw [← erase_insert (hxℬ s (h𝒮ℬ hs)), ← erase_insert (hxℬ t (h𝒮ℬ ht))]
      exact congrArg (·.erase x) hst
    · rw [coe_image]
      exact hk.image ⟨insert x, fun s t ↦ insert_inter_distrib s t x⟩

/-- **Erdős–Rado sunflower lemma** for uniform families: an `r`-uniform family of more than
`(p - 1) ^ r * r !` sets contains a sunflower with `p` petals. -/
theorem exists_isSunflower_of_sized (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
    (h : (p - 1) ^ r * r ! < #𝒜) :
    ∃ 𝒮 ⊆ 𝒜, #𝒮 = p ∧ ∃ k : Finset α, (𝒮 : Set (Finset α)).IsSunflower k :=
  exists_isSunflower_of_forall_card_le (fun _ hs ↦ (h𝒜 hs).le) h

end Finset
