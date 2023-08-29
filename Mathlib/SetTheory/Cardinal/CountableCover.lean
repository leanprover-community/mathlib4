/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Order.Filter.Basic

/-!
# Cardinality of a set with a countable cover

Assume that a set `t` is eventually covered by a countable family of sets, all with
cardinality `≤ a`. Then `t` itself has cardinality at most `a`. This is proved in
`Cardinal.mk_subtype_le_of_countable_eventually_mem`.

Versions are also given when `t = univ`, and with `= a` instead of `≤ a`.
-/

set_option autoImplicit true

open Set Order Filter
open scoped Cardinal

namespace Cardinal

/-- If a set `t` is eventually covered by a countable family of sets, all with cardinality at
most `a`, then the cardinality of `t` is also bounded by `a`.
Supersed by `mk_le_of_countable_eventually_mem` which does not assume
that the indexing set lives in the same universe. -/
lemma mk_subtype_le_of_countable_eventually_mem_aux {α ι : Type u} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l]
    {t : Set α} (ht : ∀ x ∈ t, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #t ≤ a := by
  rcases lt_or_le a ℵ₀ with ha|ha
  -- ⊢ #↑t ≤ a
  /- case `a` finite. In this case, it suffices to show that any finite subset `s` of `t` has
  cardinality at most `a`. For this, we pick `i` such that `f i` contains all the points in `s`,
  and apply the assumption that the cardinality of `f i` is at most `a`.   -/
  · obtain ⟨n, rfl⟩ : ∃ (n : ℕ), a = n := lt_aleph0.1 ha
    -- ⊢ #↑t ≤ ↑n
    apply mk_le_iff_forall_finset_subset_card_le.2 (fun s hs ↦ ?_)
    -- ⊢ Finset.card s ≤ n
    have A : ∀ x ∈ s, ∀ᶠ i in l, x ∈ f i := fun x hx ↦ ht x (hs hx)
    -- ⊢ Finset.card s ≤ n
    have B : ∀ᶠ i in l, ∀ x ∈ s, x ∈ f i := (s.eventually_all).2 A
    -- ⊢ Finset.card s ≤ n
    rcases B.exists with ⟨i, hi⟩
    -- ⊢ Finset.card s ≤ n
    have : ∀ i, Fintype (f i) := fun i ↦ (lt_aleph0_iff_fintype.1 ((h'f i).trans_lt ha)).some
    -- ⊢ Finset.card s ≤ n
    let u : Finset α := (f i).toFinset
    -- ⊢ Finset.card s ≤ n
    have I1 : s.card ≤ u.card := by
      have : s ⊆ u := fun x hx ↦ by simpa only [Set.mem_toFinset] using hi x hx
      exact Finset.card_le_of_subset this
    have I2: (u.card : Cardinal) ≤ n := by
      convert h'f i; simp only [Set.toFinset_card, mk_fintype]
    exact I1.trans (Nat.cast_le.1 I2)
    -- 🎉 no goals
  -- case `a` infinite:
  · have : t ⊆ ⋃ i, f i := by
      intro x hx
      obtain ⟨i, hi⟩ : ∃ i, x ∈ f i := (ht x hx).exists
      exact mem_iUnion_of_mem i hi
    calc #t ≤ #(⋃ i, f i) := mk_le_mk_of_subset this
      _     ≤ sum (fun i ↦ #(f i)) := mk_iUnion_le_sum_mk
      _     ≤ sum (fun _ ↦ a) := sum_le_sum _ _ h'f
      _     = #ι * a := by simp
      _     ≤ ℵ₀ * a := mul_le_mul_right' mk_le_aleph0 a
      _     = a := aleph0_mul_eq ha

/-- If a set `t` is eventually covered by a countable family of sets, all with cardinality at
most `a`, then the cardinality of `t` is also bounded by `a`. -/
lemma mk_subtype_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l]
    {t : Set α} (ht : ∀ x ∈ t, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #t ≤ a := by
  let g : ULift.{u, v} ι → Set (ULift.{v, u} α) := (ULift.down ⁻¹' ·) ∘ f ∘ ULift.down
  -- ⊢ #↑t ≤ a
  suffices #(ULift.down.{v} ⁻¹' t) ≤ Cardinal.lift.{v, u} a by simpa
  -- ⊢ #↑(ULift.down ⁻¹' t) ≤ lift.{v, u} a
  let l' : Filter (ULift.{u} ι) := Filter.map ULift.up l
  -- ⊢ #↑(ULift.down ⁻¹' t) ≤ lift.{v, u} a
  have : NeBot l' := map_neBot
  -- ⊢ #↑(ULift.down ⁻¹' t) ≤ lift.{v, u} a
  apply mk_subtype_le_of_countable_eventually_mem_aux (ι := ULift.{u} ι) (l := l') (f := g)
  -- ⊢ ∀ (x : ULift α), x ∈ ULift.down ⁻¹' t → ∀ᶠ (i : ULift ι) in l', x ∈ g i
  · intro x hx
    -- ⊢ ∀ᶠ (i : ULift ι) in l', x ∈ g i
    simpa only [Function.comp_apply, mem_preimage, eventually_map] using ht _ hx
    -- 🎉 no goals
  · intro i
    -- ⊢ #↑(g i) ≤ lift.{v, u} a
    simpa using h'f i.down
    -- 🎉 no goals

/-- If a space is eventually covered by a countable family of sets, all with cardinality at
most `a`, then the cardinality of the space is also bounded by `a`. -/
lemma mk_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l] (ht : ∀ x, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #α ≤ a := by
  rw [← mk_univ]
  -- ⊢ #↑Set.univ ≤ a
  exact mk_subtype_le_of_countable_eventually_mem (l := l) (fun x _ ↦ ht x) h'f
  -- 🎉 no goals

/-- If a space is eventually covered by a countable family of sets, all with cardinality `a`,
then the cardinality of the space is also `a`. -/
lemma mk_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l] (ht : ∀ x, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) = a) : #α = a := by
  apply le_antisymm
  -- ⊢ #α ≤ a
  · apply mk_le_of_countable_eventually_mem ht (fun i ↦ (h'f i).le)
    -- 🎉 no goals
  · obtain ⟨i⟩ : Nonempty ι := nonempty_of_neBot l
    -- ⊢ a ≤ #α
    rw [← (h'f i)]
    -- ⊢ #↑(f i) ≤ #α
    exact mk_set_le (f i)
    -- 🎉 no goals

end Cardinal
