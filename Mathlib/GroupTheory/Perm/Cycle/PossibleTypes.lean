/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-! # Possible cycle types of permutations

* For `m : Multiset ℕ`, `Equiv.Perm.withCycleType_nonempty_iff m`
  proves that there are permutations with cycleType `m` if and only if
  its sum is at most `Fintype.card α` and its members are at least 2.

To prove this, we add some lemmas about lists which should probably be
put elsewhere

* `List.disjoint_map` and `List.disjoint_pmap` prove that
  the images of disjoint lists under an injective (partial) map
  are disjoint if that map is injective
* Given `l : List ℕ`, `List.ranges` construct a list of lists of integers
  whose zip is `[0,1,2,…]` and whose lengths are given by `l`.
  For example, `List.ranges [2,0,3] = [[0,1], [], [2,3,4]]`.
* `List.ranges_disjoint`, `List.ranges_nodup`, `List.ranges_lt`,
  `List.ranges_lengths` prove properties of that function
* Given `l : List ℕ` and a type `α` with more than `l.sum` elements,
  `List.exists_pw_disjoint_with_card α l` constructs a `List (List α)`
  with given lengths, pairwise disjoint members, each of them having no duplicates.
-/


/- section List

namespace List

variable {α β : Type _}

/-- The images of disjoint maps under a map are disjoint -/
theorem disjoint_map {f : α → β} {s t : List α} (hf : Function.Injective f)
    (h : Disjoint s t) : Disjoint (s.map f) (t.map f) := by
  simp only [Disjoint]
  intro b hbs hbt
  rw [mem_map] at hbs hbt
  obtain ⟨a, ha, rfl⟩ := hbs
  apply h ha
  obtain ⟨a', ha', ha''⟩ := hbt
  rw [hf ha''.symm]; exact ha'

/-- The images of disjoint lists under a partially defined map are disjoint -/
theorem disjoint_pmap {p : α → Prop} {f : ∀ a : α, p a → β} {s t : List α}
    (hs : ∀ a ∈ s, p a) (ht : ∀ a ∈ t, p a)
    (hf : ∀ (a a' : α) (ha : p a) (ha' : p a'), f a ha = f a' ha' → a = a')
    (h : Disjoint s t) :
    Disjoint (s.pmap f hs) (t.pmap f ht) := by
  simp only [Disjoint]
  intro b hbs hbt
  rw [mem_pmap] at hbs hbt
  obtain ⟨a, ha, rfl⟩ := hbs
  apply h ha
  obtain ⟨a', ha', ha''⟩ := hbt
  rw [hf a a' (hs a ha) (ht a' ha') ha''.symm]
  exact ha'

/-- From `l: List ℕ`, construct `ml: List (List ℕ)` such that
  `ml.map List.length = l` and `ml.join = range l.sum` -/
def ranges : List ℕ → List (List ℕ)
  | [] => nil
  | a::l => range a::(ranges l).map (map (Nat.add a))

/-- The members of `l.ranges` are pairwise disjoint -/
theorem ranges_disjoint (l : List ℕ) :
  Pairwise Disjoint (ranges l) := by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l hl =>
    simp only [ranges, pairwise_cons]
    constructor
    · intro s hs
      obtain ⟨s', _, rfl⟩ := mem_map.mp hs
      intro u hu
      rw [mem_map]
      rintro ⟨v, _, rfl⟩
      rw [mem_range] at hu
      exact lt_iff_not_le.mp hu le_self_add
    · rw [pairwise_map]
      apply Pairwise.imp _ hl
      intro u v
      apply disjoint_map
      exact fun u v => Nat.add_left_cancel
#align list.ranges_disjoint List.ranges_disjoint

/-- The members of `l.ranges` have no duplicate -/
theorem ranges_nodup (l : List ℕ) :
    ∀ s ∈ ranges l, s.Nodup := by
  induction l with
  | nil =>
    intro s hs
    simp only [ranges, not_mem_nil] at hs
  | cons a l hl =>
    intro s hs
    simp only [ranges, List.mem_cons] at hs
    cases hs with
    | inl hs => -- case s = a
      rw [hs]
      exact nodup_range a
    | inr hs => -- case s ∈ l
      obtain ⟨t, ht, rfl⟩ := mem_map.mp hs
      exact Nodup.map (fun u v => Nat.add_left_cancel) (hl t ht)

/-- The lengths of the members of `l.ranges` are those given by `l` -/
theorem ranges_length (l : List ℕ) :
    l.ranges.map length = l := by
  induction l with
  | nil => simp only [ranges, map_nil]
  | cons a l hl => -- (a :: l)
    simp only [map, length_range, map_map, cons.injEq, true_and]
    conv_rhs => rw [← hl]
    apply map_congr
    intro s _
    simp only [Function.comp_apply, length_map]

/-- Any entry of any member of `l.ranges` is strictly smaller than `l.sum` -/
theorem ranges_lt (l : List ℕ) {s : List ℕ} {n : ℕ}
    (hs : s ∈ List.ranges l) (hn : n ∈ s) :
    n < l.sum := by
  revert s n
  induction l with
  | nil =>
    intro s n hs _
    exfalso
    simp only [ranges] at hs
    exact not_mem_nil s hs
  | cons a l hl =>
    intro s n hs hn
    simp only [List.ranges, List.mem_cons] at hs
    cases hs with
    | inl hs =>
      rw [hs, mem_range] at hn
      apply lt_of_lt_of_le hn
      rw [sum_cons]
      exact le_self_add
    | inr hs =>
      obtain ⟨t, ht, rfl⟩ := mem_map.mp hs
      obtain ⟨m, hm, rfl⟩ := mem_map.mp hn
      simp only [List.sum_cons, Nat.add_def, add_lt_add_iff_left]
      exact hl ht hm

/-- For any `c : List ℕ` whose sum is at most `Fintype.card α`,
  we can find `o : List (List α)` whose members have no duplicate,
  whose lengths given by `c`, and which are pairwise disjoint -/
theorem exists_pw_disjoint_with_card {α : Type*} [Fintype α]
    {c : List ℕ} (hc : c.sum ≤ Fintype.card α) :
    ∃ o : List (List α),
      o.map length = c ∧ (∀ s ∈ o, s.Nodup) ∧ Pairwise List.Disjoint o := by
  let klift (n : ℕ) (hn : n < Fintype.card α) : Fin (Fintype.card α) :=
    (⟨n, hn⟩ : Fin (Fintype.card α))
  let klift' (l : List ℕ) (hl : ∀ a ∈ l, a < Fintype.card α) :
    List (Fin (Fintype.card α)) := List.pmap klift l hl
  have hc'_lt : ∀ l ∈ c.ranges, ∀ n ∈ l, n < Fintype.card α := by
    intro l hl n hn
    apply lt_of_lt_of_le _ hc
    apply ranges_lt c hl hn
  let l := (ranges c).pmap klift' hc'_lt
  have hl : ∀ (a : List ℕ) (ha : a ∈ c.ranges),
    (klift' a (hc'_lt a ha)).map Fin.valEmbedding = a := by
    intro a ha
    conv_rhs => rw [← List.map_id a]
    rw [List.map_pmap]
    simp only [Fin.valEmbedding_apply, Fin.val_mk, List.pmap_eq_map, List.map_id'', List.map_id]
  use l.map (List.map (Fintype.equivFin α).symm)
  constructor
  · -- length
    rw [← ranges_length c]
    simp only [map_map, map_pmap, Function.comp_apply, length_map, length_pmap, pmap_eq_map]
  constructor
  · -- nodup
    intro s
    rw [mem_map]
    rintro ⟨t, ht, rfl⟩
    apply Nodup.map (Equiv.injective _)
    obtain ⟨u, hu, rfl⟩ := mem_pmap.mp ht
    apply Nodup.of_map
    rw [hl u hu]
    apply ranges_nodup c u hu
  · -- pairwise disjoint
    refine Pairwise.map _ (fun s t ↦ disjoint_map (Equiv.injective _)) ?_
    · -- List.Pairwise List.disjoint l
      apply Pairwise.pmap (List.ranges_disjoint c)
      intro u hu v hv huv
      apply disjoint_pmap
      · intro a a' ha ha' h
        simpa only [Fin.mk_eq_mk] using h
      exact huv

end List
 -/

variable (α : Type _) [DecidableEq α] [Fintype α]

/-- There are permutations with cycleType `m` if and only if
  its sum is at most `Fintype.card α` and its members are at least 2. -/
theorem Equiv.Perm.with_cycleType_nonempty_iff {m : Multiset ℕ} :
    Set.Nonempty {g : Equiv.Perm α | g.cycleType = m} ↔
      (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) := by
  constructor
  · -- empty case
    intro h
    obtain ⟨g, hg⟩ := h
    simp only [Set.mem_setOf_eq] at hg
    constructor
    · rw [← hg, Equiv.Perm.sum_cycleType]
      exact (Equiv.Perm.support g).card_le_univ
    · intro a
      rw [← hg]
      exact Equiv.Perm.two_le_of_mem_cycleType
  · rintro ⟨hc, h2c⟩
    have hc' : m.toList.sum ≤ Fintype.card α
    · simp only [Multiset.sum_toList]
      exact hc
    obtain ⟨p, hp_length, hp_nodup, hp_disj⟩ := List.exists_pw_disjoint_with_card hc'
    use List.prod (List.map (fun l => List.formPerm l) p)
    simp only [Set.mem_setOf_eq]
    have hp2 : ∀ x ∈ p, 2 ≤ x.length := by
      intro x hx
      apply h2c x.length
      rw [← Multiset.mem_toList, ← hp_length, List.mem_map]
      exact ⟨x, hx, rfl⟩
    rw [Equiv.Perm.cycleType_eq _ rfl]
    · -- lengths
      rw [← Multiset.coe_toList m]
      apply congr_arg
      rw [List.map_map]; rw [← hp_length]
      apply List.map_congr
      intro x hx; simp only [Function.comp_apply]
      rw [List.support_formPerm_of_nodup x (hp_nodup x hx)]
      ·-- length
        rw [List.toFinset_card_of_nodup (hp_nodup x hx)]
      · -- length >= 1
        intro a h
        apply Nat.not_succ_le_self 1
        conv_rhs => rw [← List.length_singleton a]; rw [← h]
        exact hp2 x hx
    · -- cycles
      intro g
      rw [List.mem_map]
      rintro ⟨x, hx, rfl⟩
      have hx_nodup : x.Nodup := hp_nodup x hx
      rw [← Cycle.formPerm_coe x hx_nodup]
      apply Cycle.isCycle_formPerm
      rw [Cycle.nontrivial_coe_nodup_iff hx_nodup]
      exact hp2 x hx
    · -- disjoint
      rw [List.pairwise_map]
      apply List.Pairwise.imp_of_mem _ hp_disj
      intro a b ha hb hab
      rw [List.formPerm_disjoint_iff (hp_nodup a ha) (hp_nodup b hb) (hp2 a ha) (hp2 b hb)]
      exact hab
