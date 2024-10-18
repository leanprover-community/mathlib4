/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.List.Join
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Sort

/-!
# Partitions of a list

## Main definitions

* `List.sublistPartitions l`: the unordered partitions of `l` where the pieces are sublists of the
  original.
-/
variable {α}

namespace List

/-- All possible ways to split a list at an element from `l` -/
@[simp]
def splits (l : List α) : List (List α × α × List α) :=
  match l with
  | [] => []
  | y :: ys => ([], y, ys) :: (splits ys).map (fun p => (y :: p.1, p.2.1, p.2.2))

theorem mem_splits_iff {p : List α × α × List α} {l : List α} :
    p ∈ l.splits ↔ p.1 ++ p.2.1 :: p.2.2 = l := by
  induction l generalizing p with
  | nil => simp
  | cons x xs ih =>
    simp only [splits, mem_cons, mem_map, ih]
    constructor
    · rintro (rfl | ⟨a, rfl, rfl⟩)
      · rfl
      · rfl
    · intro h
      obtain ⟨- | ⟨p1, p1s⟩, p2, p3⟩ := p <;> (dsimp at h; injections h; subst_vars)
      · exact .inl rfl
      · exact .inr ⟨(_, _, _), rfl, rfl⟩

/-- Apply `f` to each element of `α` in turn -/
@[simp, specialize]
def mapEach (f : α → α) : List α → List (List α)
  | [] => []
  | y :: ys => (f y :: ys) :: (mapEach f ys).map (y :: ·)

theorem mem_mapEach_iff {x : List α} {l : List α} {f : α → α} :
    x ∈ l.mapEach f ↔ ∃ hd a tl, hd ++ f a :: tl = x ∧ hd ++ a :: tl = l := by
  induction l generalizing x with
  | nil => simp
  | cons x xs ih =>
    simp only [mapEach, mem_cons, mem_map]
    simp_rw [ih]
    constructor
    · rintro (rfl | ⟨fa, ⟨hd, a, tl, rfl, rfl⟩, rfl⟩)
      · refine ⟨[], x, xs, ?_⟩
        simp
      · refine ⟨x :: hd, a, tl, ?_⟩
        simp
    · rintro ⟨hd, a, tl, rfl, h⟩
      obtain - | ⟨x, hd⟩ := hd <;> (dsimp at h; injections h; subst_vars)
      · exact .inl rfl
      · exact .inr ⟨_, ⟨hd, a, tl, rfl, rfl⟩, rfl⟩



-- theorem sublist_of_mem_removals {p : α × List α} {l : List α} (h : p ∈ removals l) :
--     p.2 <+ l := by
--   induction l generalizing p with
--   | nil => simp only [removals, not_mem_nil] at h
--   | cons x xs ih =>
--     rw [removals, List.mem_cons, List.mem_map] at h
--     obtain rfl | ⟨a, ha, rfl⟩ := h
--     · exact .cons _ (.refl _)
--     · exact .cons₂ _ (ih ha)

-- theorem cons_perm_of_mem_removals {p : α × List α} {l : List α} (h : p ∈ removals l) :
--     p.1 :: p.2 ~ l := by
--   induction l generalizing p with
--   | nil => simp only [removals, not_mem_nil] at h
--   | cons x xs ih =>
--     rw [removals, List.mem_cons, List.mem_map] at h
--     obtain rfl | ⟨a, ha, rfl⟩ := h
--     · exact .cons _ (.refl _)
--     · exact .trans (.swap _ _ _) (ih ha |>.cons x)


-- theorem mem_of_mem_removals {p : α × List α} {l : List α} (h : p ∈ removals l) :
--     p.1 ∈ l :=
--   (cons_perm_of_mem_removals h).subset (mem_cons_self _ _)


-- theorem mem_removals_iff {p : α × List α} {l : List α} :
--     p ∈ l.removals ↔ p.2 <+ l ∧ p.1 :: p.2 ~ l := by
--   refine ⟨fun h => ⟨sublist_of_mem_removals h, cons_perm_of_mem_removals h⟩, fun ⟨hs, hp⟩ => ?_⟩
--   induction l generalizing p with
--   | nil => simp_all
--   | cons x xs =>
--     simp_all


-- theorem mem_removals_iff {p : α × List α} {l : List α} :
--     p ∈ l.removals ↔ p.2 <+ l ∧ p.1 :: p.2 ~ l := by
--   refine ⟨fun h => ⟨sublist_of_mem_removals h, cons_perm_of_mem_removals h⟩, fun ⟨hs, hp⟩ => ?_⟩
--   induction l generalizing p with
--   | nil => simp_all
--   | cons x xs =>
--     simp_all


/-- Partitions of `l` into sublists.

For example,
```lean
#eval [1, 2, 3].sublistPartitions
```
gives
```lean
[[[1], [2], [3]],
 [[1, 2], [3]],
 [[2], [1, 3]],
 [[1], [2, 3]],
 [[1, 2, 3]]]
```
If `l.length = n`, then `l.sublistPartition.length` is the `n`th Bell number.
-/
@[simp]
def sublistPartitions (l : List α) : List (List (List α)) :=
  match l with
  | [] => [[]]
  | x :: xs => (sublistPartitions xs).bind fun p =>
    ([x] :: p) :: p.mapEach (x :: ·)

@[simp]
def sublistPartitions1 (l : List α) : List (List (List α)) :=
  match l with
  | [] => [[]]
  | x :: xs => (sublistPartitions1 xs).bind fun p =>
    ([x] :: p) :: (splits p).map fun p => p.1 ++ (x :: p.2.1) :: p.2.2

@[simp]
def sublistPartitions2 (l : List α) : List (List (List α)) :=
  match l with
  | [] => [[]]
  | x :: xs => (sublistPartitions2 xs).bind fun p => next x p
where
  @[simp]
  next (x : α) (l : List (List α)) : List (List (List α)) :=
    match l with
    | [] => [[[x]]]
    | y :: ys => ((x :: y) :: ys) :: (next x ys).map (y :: ·)

/-- Every element of an element of a sublist partition of `l` is a sublist of `l` -/
theorem Sublist.of_mem_mem_sublistPartitions2 {pi : List α} {p : List (List α)} {l : List α}
    (hpi : pi ∈ p) (hp : p ∈ l.sublistPartitions2) :
    pi <+ l := by
  induction l generalizing pi p with
  | nil => simp_all
  | cons x l ih =>
    rw [sublistPartitions2, mem_bind] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    obtain ⟨qi, hqi, hpiqi⟩ | rfl := of_mem_next hpq hpi
    · exact hpiqi.trans (.cons₂ _ <| ih hqi hq)
    · exact (nil_sublist _).cons₂ _
where
  of_mem_next {x : α} {p : List (List α)} {q : List (List α)}
      (hp : p ∈ sublistPartitions2.next x q) {pi : List α} (hpi : pi ∈ p) :
      (∃ qi ∈ q, pi <+ x :: qi) ∨ pi = [x] := by
    induction q generalizing p with
    | nil => simp_all [sublistPartitions2.next]
    | cons q qs ih =>
      rw [sublistPartitions2.next, mem_cons, mem_map] at hp
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


theorem perm_cons_iff (p : List α) (x : α) (l : List α):
    p ~ x :: l ↔ ∃ init tail, p = init ++ x :: tail ∧ init ++ tail ~ l := by
  constructor
  · intro h
    classical
    refine ⟨p.takeWhile (· ≠ x), (p.dropWhile (· ≠ x)).tail, ?_⟩
    have : (p.dropWhile (· ≠ x)) = x :: (p.dropWhile (· ≠ x)).tail := by
      replace h := h.symm.subset (mem_cons_self _ _)
      induction p with
      | nil => cases h
      | cons head tail ih =>
        obtain rfl | hx := eq_or_ne x head
        · simp
        · simp only [mem_cons] at h
          replace h := h.resolve_left hx
          rw [dropWhile_cons_of_pos]
          conv_lhs => rw [ih h]
          simp [hx.symm]
    rw [← this, takeWhile_append_dropWhile, ← perm_cons x]
    refine ⟨rfl, .trans (perm_middle.symm.trans ?_) h⟩
    rw [← this, takeWhile_append_dropWhile]
  · rintro ⟨init, tail, rfl, h⟩
    exact perm_middle.trans <| h.cons x


theorem join_perm_cons_iff (p : List (List α)) (x : α) (l : List α):
    p.join ~ x :: l ↔
      ∃ hd tl phd ptl, p = hd ++ (phd ++ x :: ptl) :: tl ∧ (hd ++ (phd ++ ptl) :: tl).join ~ l := by
  rw [perm_cons_iff]
  simp [List.join_eq_append]
  constructor
  · rintro ⟨init, tail, ⟨a, b, rfl, rfl, hb⟩ | ⟨as, bs, c, cs, ds, rfl, rfl, rfl, rfl⟩, hl⟩
    · rw [eq_comm, join_eq_cons] at hb
      obtain ⟨as, bs, cs, rfl, h, rfl⟩ := hb
      refine ⟨a ++ as, cs, [], bs, ?_, ?_⟩
      · simp
      · rw [join_append, join_eq_nil.mpr h]
        simpa
    · refine ⟨as, ds, bs, cs, rfl, ?_⟩
      simpa using hl
  · rintro ⟨hd, tl, phd, ptl, rfl, h⟩
    refine ⟨hd.join ++ phd, ptl ++ tl.join, .inr ⟨hd, phd, x, ptl, tl, rfl, rfl, rfl, rfl⟩, ?_⟩
    simpa using h


-- oops: not true

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
    simp only [sublistPartitions, mem_bind, mem_cons, mem_mapEach_iff, ih]
    clear ih
    constructor
    · rintro ⟨a, ⟨hpi, hjoin⟩, rfl | ⟨hd, a, tl, rfl, rfl⟩⟩
      · simp_rw [List.forall_mem_cons, and_assoc]
        refine ⟨cons_ne_nil _ _, ?_, fun x hx => ⟨(hpi _ hx).1, (hpi _ hx).2.cons _⟩, ?_⟩
        · simp
        · simpa using hjoin
      · simp_rw [List.forall_mem_append, List.forall_mem_cons] at hpi ⊢
        refine ⟨?_, ?_⟩
        · simp_all
        · replace hjoin := hjoin.cons x
          simp only [join_append, join_cons, cons_append _ a, ← cons_append _ hd.join] at hjoin ⊢
          refine .trans ?_ hjoin
          rw [append_cons]
          exact (perm_append_singleton x hd.join).append_right _
    · rintro ⟨h, hjoin⟩
      rw [join_perm_cons_iff] at hjoin
      obtain ⟨init, init', tail', tail, rfl, hjoin⟩ := hjoin

      /-
      Outline:
      * One element of `p` (`x :: a_1`) must start with `x`, due to `(h _ _).2` and `hjoin`
      * Use `a` as `p` with that `x` removed. -/
      -- simp_rw [and_or_left, exists_or, ← exists_and_left]
      -- simp [-exists_and_left]
      -- induction p generalizing x l with
      -- | nil => simp_all
      -- | cons p0 p ih =>
      --   simp_rw [forall_mem_cons] at h
      --   rw [join_cons] at hjoin
      --   obtain ⟨⟨hp0n, hpsub⟩, h⟩ := h
      --   simp only [ne_eq, cons.injEq]
      --   obtain - | ⟨p00, p0⟩ := p0
      --   · cases hp0n rfl
      --   clear hp0n
      --   simp at hjoin
      --   cases hpsub with
      --   | @cons₂ l0 l _ hl0 =>
      --     simp at hjoin
      --     sorry
      --     -- cases l
      --     -- · simp_all
      --     --   sorry
      --     -- refine ⟨?_, ?_⟩
      --   | cons hpsub =>
      --     sorry


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
