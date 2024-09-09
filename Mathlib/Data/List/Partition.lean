/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.List.Join

/-!
# Partitions of a list

## Main definitions

* `List.sublistPartitions l`: the unordered partitions of `l` where the pieces are sublists of the
  original.
-/
variable {α}

namespace List

/-- Partitions of `l` into sublists.

For example,
```
#eval [1, 2, 3].sublistPartitions
```
gives
```
[[[1, 2, 3]],
 [[2, 3], [1]],
 [[1, 3], [2]],
 [[3], [1, 2]],
 [[3], [2], [1]]]
```
If `l.length = n`, then `l.sublistPartition.length` is the `n`th Bell number.
-/
@[simp]
def sublistPartitions (l : List α) : List (List (List α)) :=
  match l with
  | [] => [[]]
  | x :: xs => (sublistPartitions xs).bind fun p => next x p
where
  @[simp]
  next (x : α) (l : List (List α)) : List (List (List α)) :=
    match l with
    | [] => [[[x]]]
    | y :: ys => ((x :: y) :: ys) :: (next x ys).map (y :: ·)

/-- Every element of an element of a sublist partition of `l` is a sublist of `l` -/
theorem Sublist.of_mem_mem_sublistPartitions {pi : List α} {p : List (List α)} {l : List α}
    (hpi : pi ∈ p) (hp : p ∈ l.sublistPartitions) :
    pi <+ l := by
  induction l generalizing pi p with
  | nil => simp_all
  | cons x l ih =>
    rw [sublistPartitions, mem_bind] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    obtain ⟨qi, hqi, hpiqi⟩ | rfl := of_mem_next hpq hpi
    · exact hpiqi.trans (.cons₂ _ <| ih hqi hq)
    · exact (nil_sublist _).cons₂ _
where
  of_mem_next {x : α} {p : List (List α)} {q : List (List α)}
      (hp : p ∈ sublistPartitions.next x q) {pi : List α} (hpi : pi ∈ p) :
      (∃ qi ∈ q, pi <+ x :: qi) ∨ pi = [x] := by
    induction q generalizing p with
    | nil => simp_all [sublistPartitions.next]
    | cons q qs ih =>
      rw [sublistPartitions.next, mem_cons, mem_map] at hp
      simp_all only [mem_cons, exists_eq_or_imp]
      obtain rfl | ⟨a', ha', rfl⟩ := hp
      · left
        obtain rfl | hpi := List.mem_cons.1 hpi
        · exact .inl <| .refl _
        · exact .inr ⟨_, hpi, .cons _ <| .refl _⟩
      · obtain rfl | hpi := List.mem_cons.1 hpi
        · exact .inl <| .inl <| .cons _ <| .refl _
        · obtain ⟨qi, hqi, hhqi⟩ | rfl := ih ha' hpi
          · exact .inl <| .inr <| ⟨_, hqi, hhqi⟩
          · exact .inr rfl

-- TODO: is `p.join ~ l` really the best we can do here?
/--
The sublist partitions consist of nonempty sublists of `l` whose join is a permutation of `l`.
-/
theorem mem_sublistPartitions_iff {l : List α} {p : List (List α)} :
    p ∈ l.sublistPartitions ↔ (∀ pi ∈ p, pi ≠ [] ∧ pi <+ l) ∧ p.join ~ l := by
  induction l generalizing p with
  | nil =>
    simp only [sublistPartitions, mem_singleton, ne_eq, sublist_nil, not_and_self, imp_false,
      perm_nil, join_eq_nil, ← eq_nil_iff_forall_not_mem, iff_self_and]
    rintro rfl
    simp
  | cons x l ih =>
    simp only [sublistPartitions, mem_bind, ih]
    sorry
-- where
--   mem_next_iff {a : α} {p q : List (List α)} :
--     p ∈ sublistPartitions.next a q ↔ (∀ pi ∈ p, pi ≠ [] ∧ pi <+ l) ∧  p.join ~ x :: q.join

/-- If a list has no duplicates, then nor do any elements of its partitions. -/
theorem Nodup.of_mem_sublistPartitions {l : List α} (h : l.Nodup) {p : List (List α)}
    (hp : p ∈ l.sublistPartitions) {pi} (hpi : pi ∈ p) : pi.Nodup := by
  rw [mem_sublistPartitions_iff] at hp
  exact (hp.1 _ hpi).2.nodup h

/-- If a list has no duplicates, then its partitions have no duplicates -/
theorem nodup_iff_nodup_mem_sublistPartitions {l : List α} :
    l.Nodup ↔ ∀ p ∈ l.sublistPartitions, p.Nodup := by
  simp_rw [mem_sublistPartitions_iff]
  sorry

end List
