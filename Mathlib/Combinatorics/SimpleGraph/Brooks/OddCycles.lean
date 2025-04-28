/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

namespace SimpleGraph
open Walk
variable {α : Type*}{u v x: α} [DecidableEq α] {G : SimpleGraph α}

/-- Given a vertex `x` in a walk `w : G.Walk u v` form the walk that travels along `w` from `u`
to `x` and then back to `v` without revisiting `x` -/
def Walk.shortCut (w : G.Walk u v) (hx : x ∈ w.support) : G.Walk u v :=
  (w.takeUntil _ hx).append (w.reverse.takeUntil _ (w.mem_support_reverse.2 hx)).reverse


@[simp]
lemma Walk.shortCut_start (w : G.Walk u v) : w.shortCut w.start_mem_support =
    (w.reverse.takeUntil _ (w.mem_support_reverse.2 (by simp))).reverse:= by
  cases w <;> simp [shortCut];

@[simp]
lemma Walk.mem_support_shortCut (w : G.Walk u v) (hx : x ∈ w.support) :
    x ∈ (w.shortCut hx).support := by
  rw [shortCut]
  simp
/-- Given a vertex `x` in a walk `w` form the walk that travels along `w` from the first visit of
`x` to the last visit of `x` (which may be the same in which case this is `nil' x`) -/
def Walk.shortClosed (w : G.Walk u v) (hx : x ∈ w.support) : G.Walk x x :=
  (w.reverse.dropUntil _ (w.mem_support_reverse.2 hx)).reverse.dropUntil _ (by simp)

@[simp]
lemma Walk.shortClosed_start (w : G.Walk u v) : (w.shortClosed (w.start_mem_support)) =
    (w.reverse.dropUntil _ (by simp)).reverse := by
  cases w <;> simp [shortClosed]

@[simp]
lemma Walk.shortClosed_of_eq {y: α} (w : G.Walk u v) (hx : x ∈ w.support) (hy : y ∈ w.support)
    (h : y = x) : w.shortClosed hx = (w.shortClosed hy).copy h h := by
  subst h
  rfl

lemma Walk.shortCut_not_nil (w : G.Walk u v) (hx : x ∈ w.support) (hu : x ≠ u) :
    ¬(w.shortCut hx).Nil := by
  rw [shortCut]
  simp only [nil_append_iff, nil_takeUntil, nil_reverse, not_and]
  rintro rfl; contradiction

lemma Walk.dropUntil_reverse_takeUntil (w : G.Walk u v) (hx : x ∈ w.support) :
  (w.dropUntil _ hx).reverse.takeUntil _ (end_mem_support ..) =
  w.reverse.takeUntil _ (w.mem_support_reverse.2 hx) := by
  conv_rhs =>
    enter [1]
    rw [← take_spec w hx, reverse_append]
  rw [ takeUntil_append_of_mem_left _ _ (by simp)]

lemma Walk.takeUntil_spec (w : G.Walk u v) (hx : x ∈ w.support) :
  (w.reverse.dropUntil _ (w.mem_support_reverse.2 hx)).reverse.takeUntil _ (by simp) =
  w.takeUntil _ hx := by
  simp_rw [w.reverse.dropUntil_reverse_takeUntil (by simpa), reverse_reverse]

lemma Walk.dropUntil_reverse_comm (w : G.Walk u v) (hx : x ∈ w.support) (hu : x ≠ u) :
  ((w.dropUntil _ hx).reverse.dropUntil _ (by simp)).reverse =
  (((w.reverse.dropUntil _ (w.mem_support_reverse.2 hx)).reverse.dropUntil _ (by simp))):= by
  induction w with
  | nil => rw [mem_support_nil_iff] at hx; exact (hu hx).elim
  | @cons _ b _ _ p ih =>
    simp_rw [reverse_cons]
    rw [dropUntil_cons_ne_start hx hu]
    rw [support_cons, List.mem_cons] at hx
    cases hx with
  | inl hx => contradiction
  | inr hx =>
    simp_rw [dropUntil_append_of_mem_left _ _ ((p.mem_support_reverse.2 hx)),
          reverse_append]
    by_cases hb : x = b
    · subst b
      rw [dropUntil_start, dropUntil_append_of_mem_left _ _ (by simp)]
      simp_rw [reverse_cons, reverse_nil, nil_append]
      rw [dropUntil_cons_ne_start _ hu]
      simp
    · rw [dropUntil_append_of_mem_right _ _ (by simpa using ⟨hu, hb⟩) (by simp)]
      apply ih _ hb

lemma Walk.dropUntil_spec (w : G.Walk u v) (hx : x ∈ w.support) (hu : x ≠ u) :
    (w.shortClosed hx).append (w.reverse.takeUntil x (w.mem_support_reverse.2 hx)).reverse =
    w.dropUntil x hx := by
  have hc := congr_arg Walk.reverse <| take_spec (w.dropUntil _ hx).reverse (end_mem_support _)
  rw [Walk.reverse_reverse, ← hc, Walk.reverse_append] at *
  symm
  congr! 1
  · exact w.dropUntil_reverse_comm hx hu
  · congr! 1
    conv_rhs =>
      enter [1]
      rw [← take_spec w hx, Walk.reverse_append]
    rw [takeUntil_append_of_mem_left]

lemma Walk.not_mem_support_reverse_tail_takeUntil (w : G.Walk u v) (hx : x ∈ w.support) :
    x ∉ (w.takeUntil x hx).support.reverse.tail := by
  intro hx2
  rw [← List.count_pos_iff, List.count_tail (by simp)] at hx2
  simp at hx2

open List
/-- If `x` is a repeated vertex of the walk `w` and not the first vertex then `w.shortClosed hx` is
a non-nil closed walk. -/
lemma Walk.shortClosed_not_nil_of_one_lt_count (w : G.Walk u v) (hx : x ∈ w.support) (hu : x ≠ u)
    (h2 : 1 < w.support.count x) : ¬(w.shortClosed hx).Nil := by
  intro h
  have hs := dropUntil_spec w hx hu
  have : w.dropUntil x hx = (w.reverse.takeUntil x (w.mem_support_reverse.2 hx)).reverse := by
    rw [← hs, h.eq_nil]
    exact Walk.nil_append _
  have hw :=  congr_arg Walk.support <| take_spec w hx
  rw [this, support_append] at hw
  apply_fun List.count x at hw
  rw [List.count_append] at hw
  simp only [count_support_takeUntil_eq_one, support_reverse] at *
  have : 0 < count x (w.reverse.takeUntil x (w.mem_support_reverse.2 hx)).support.reverse.tail := by
    omega
  rw [List.count_pos_iff]at this
  exact (w.reverse.not_mem_support_reverse_tail_takeUntil _) this

/--
So the two walks `w.shortCut hx` and `w.shortClosed hx` are
-/
lemma Walk.length_shortCut_add_shortClosed (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortCut hx).length + (w.shortClosed hx).length = w.length := by
  rw [← Walk.length_takeUntil_add_dropUntil hx]
  by_cases hu : x ≠ u
  · rw [← w.dropUntil_spec hx hu, shortClosed, shortCut]
    simp only [length_append, length_reverse]
    omega
  · rw [not_not] at hu
    simp only [hu, shortCut_start, length_reverse, length_takeUntil_add_dropUntil]
    rw [w.shortClosed_of_eq  _ w.start_mem_support hu.symm, length_copy]
    simp

-- lemma Walk.count_support_rotate_new (w : G.Walk u u) (hx : x ∈ w.support) (hne : x ≠ u) :
--   (w.rotate hx).support.count x = w.support.count x + 1 := by
--   nth_rw 2 [← take_spec w hx]
--   simp_rw [rotate, Walk.support_append, List.count_append]
--   rw [List.count_tail (by simp), List.count_tail (by simp)]
--   simp [if_neg (Ne.symm hne)]

lemma Walk.count_support_rotate_old (w : G.Walk u u) (hx : x ∈ w.support) (hne : x ≠ u) :
  (w.rotate hx).support.count u = w.support.count u - 1 := by
  nth_rw 2 [← take_spec w hx]
  simp_rw [rotate, Walk.support_append, List.count_append]
  rw [List.count_tail (by simp), List.count_tail (by simp)]
  simp [head_support, beq_self_eq_true, ↓reduceIte,if_neg hne]
  rw [← Nat.add_sub_assoc (by simp), add_comm]

lemma Walk.count_support_rotate_other (w : G.Walk u u) (hx : x ∈ w.support)
  (hvx : x ≠ v) (hvu : u ≠ v) :
  (w.rotate hx).support.count v = w.support.count v := by
  nth_rw 2 [← take_spec w hx]
  simp_rw [rotate, Walk.support_append, List.count_append]
  rw [List.count_tail (by simp), List.count_tail (by simp)]
  simp [head_support, beq_iff_eq, if_neg hvu, if_neg hvx, add_comm]

def Walk.shorterOdd {u : α} (p : G.Walk u u) {x : α} (hx : x ∈ p.support) : G.Walk x x :=
  if ho : Odd (p.shortClosed hx).length then
    p.shortClosed hx
  else
    (p.shortCut hx).rotate (by simp)

lemma Walk.length_shorterOdd_le {u : α} (p : G.Walk u u) {x : α} (hx : x ∈ p.support) :
    (p.shorterOdd hx).length ≤ p.length := by
  by_cases ho : Odd (p.shortClosed hx).length
  · rw [shorterOdd, dif_pos ho]
    rw [← p.length_shortCut_add_shortClosed hx]
    omega
  · rw [shorterOdd, dif_neg ho]
    rw [← p.length_shortCut_add_shortClosed hx, length_rotate]
    omega

@[simp]
lemma Walk.shorterOdd_of_eq (p : G.Walk u u) {x y : α} (hx : x ∈ p.support) (hy : y ∈ p.support)
    (h : y = x) : (p.shorterOdd hy).copy h h = p.shorterOdd hx := by
  subst h
  rfl

lemma Walk.length_shorterOdd_lt_length {p : G.Walk u u} {x : α} (hx : x ∈ p.support) (hne : x ≠ u)
    (h2 : 1 < p.support.count x) : (p.shorterOdd hx).length < p.length := by
  rw [shorterOdd, ← p.length_shortCut_add_shortClosed hx]
  split_ifs with ho
  · rw [lt_add_iff_pos_left, ← not_nil_iff_lt_length]
    exact p.shortCut_not_nil hx hne
  · rw [Walk.length_rotate, lt_add_iff_pos_right, ← not_nil_iff_lt_length]
    exact p.shortClosed_not_nil_of_one_lt_count hx hne h2

lemma Walk.length_shorterOdd_odd {p : G.Walk u u} {x : α} (hx : x ∈ p.support)
    (ho : Odd p.length) : Odd (p.shorterOdd hx).length := by
  rw [← p.length_shortCut_add_shortClosed hx] at ho
  rw [shorterOdd]
  split_ifs with h1
  · exact h1
  · rw [Walk.length_rotate]
    exact (Nat.odd_add.1 ho).2 (Nat.not_odd_iff_even.1 h1)

/-- Return an almost minimal odd closed subwalk from an odd length closed walk
(if p.length is not odd then just returns some closed subwalk).
-/
def Walk.minOdd {u : α} (p : G.Walk u u) : Σ v, G.Walk v v := by
  if h : p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x) = []
    then exact ⟨_,p⟩
  else
    have hm := List.head_mem h
    rw [List.mem_filter, decide_eq_true_eq] at hm
    have := p.length_shorterOdd_lt_length hm.1 hm.2.1 hm.2.2
    exact (p.shorterOdd (head_filter_mem _ _ h)).minOdd
  termination_by p.length

lemma Walk.minOdd_nil {u : α} (p : G.Walk u u)
    (hx : ∀ v ∈ p.support, v ≠ u → p.support.count v ≤ 1) : p.minOdd = ⟨_, p⟩ := by
  have h : (p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x)) = [] := by
    simp_all
  rw [minOdd, dif_pos h]

lemma Walk.minOdd_ne_nil_aux {u v : α} (p : G.Walk u u)
  (hv : v ∈ p.support ∧ v ≠ u ∧ 1 < p.support.count v) :
  (p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x)) ≠ [] := by
  simpa using ⟨v, hv⟩

lemma Walk.minOdd_ne_nil {u v : α} (p : G.Walk u u)
    (hv : v ∈ p.support ∧ v ≠ u ∧ 1 < p.support.count v) :
    p.minOdd = (p.shorterOdd ((head_filter_mem _ _ (p.minOdd_ne_nil_aux hv)))).minOdd := by
  rw [minOdd, dif_neg (p.minOdd_ne_nil_aux hv)]

lemma Walk.minOdd_minOdd {u : α} (p : G.Walk u u) : p.minOdd.2.minOdd = p.minOdd := by
  induction hn : p.length using Nat.strong_induction_on generalizing p u with
  | h n ih =>
    by_cases hv : ∃ v ∈ p.support, v ≠ u ∧ 1 < p.support.count v
    · obtain ⟨v, hv⟩ := hv
      rw [p.minOdd_ne_nil hv]
      have hne_nil := (p.minOdd_ne_nil_aux hv)
      have hm := List.head_mem hne_nil
      rw [List.mem_filter, decide_eq_true_eq] at hm
      have hlt : (p.shorterOdd (head_filter_mem _ _ hne_nil)).length < n := by
        rw [← hn]
        apply p.length_shorterOdd_lt_length hm.1 hm.2.1 hm.2.2
      apply ih _ hlt _ rfl
    · push_neg at hv
      rw [minOdd_nil _ hv]
      dsimp
      rw [minOdd_nil _ hv]

lemma Walk.minOdd_length_le {u : α} (p : G.Walk u u) : p.minOdd.2.length ≤ p.length := by
  induction hn : p.length using Nat.strong_induction_on generalizing p u with
  | h n ih =>
    by_cases hv : ∃ v ∈ p.support, v ≠ u ∧ 1 < p.support.count v
    · obtain ⟨v, hv⟩ := hv
      rw [p.minOdd_ne_nil hv]
      have hne_nil := (p.minOdd_ne_nil_aux hv)
      have hm := List.head_mem hne_nil
      rw [List.mem_filter, decide_eq_true_eq] at hm
      have hlt : (p.shorterOdd (head_filter_mem _ _ hne_nil)).length < n := by
        rw [← hn]
        apply p.length_shorterOdd_lt_length hm.1 hm.2.1 hm.2.2
      apply (ih _ hlt _ rfl).trans hlt.le
    · push_neg at hv
      rw [minOdd_nil _ hv, hn]

structure Walk.IsAlmostCycle {u : α} (w : G.Walk u u) : Prop where
  count_le_one : ∀ x ∈ w.support, x ≠ u → count x w.support ≤ 1

lemma Walk.minOdd_almostCycle  {u : α} (p : G.Walk u u) : p.minOdd.2.IsAlmostCycle where
  count_le_one := by
    intro v hv
    by_contra! hc
    have := p.minOdd.2.minOdd_ne_nil ⟨hv, hc.1, hc.2⟩
    rw [minOdd_minOdd] at this
    have hne_nil := (p.minOdd.2.minOdd_ne_nil_aux ⟨hv, hc.1, hc.2⟩)
    have hm := List.head_mem hne_nil
    rw [List.mem_filter, decide_eq_true_eq] at hm
    have ht :=(p.minOdd.2.shorterOdd (head_filter_mem _ _ hne_nil)).minOdd_length_le
    rw [← this] at ht
    have := p.minOdd.2.length_shorterOdd_lt_length hm.1 hm.2.1 hm.2.2
    omega

lemma Walk.minOdd_odd {u : α} (p : G.Walk u u) (ho : Odd p.length) : Odd p.minOdd.2.length := by
  induction hn : p.length using Nat.strong_induction_on generalizing p u with
  | h n ih =>
    by_cases hv : ∃ v ∈ p.support, v ≠ u ∧ 1 < p.support.count v
    · obtain ⟨v, hv⟩ := hv
      rw [p.minOdd_ne_nil hv]
      have hne_nil := (p.minOdd_ne_nil_aux hv)
      have hm := List.head_mem hne_nil
      rw [List.mem_filter, decide_eq_true_eq] at hm
      have hlt : (p.shorterOdd (head_filter_mem _ _ hne_nil)).length < n := by
        rw [← hn]
        apply p.length_shorterOdd_lt_length hm.1 hm.2.1 hm.2.2
      have ho' := p.length_shorterOdd_odd hm.1  ho
      apply ih _ hlt _ ho' rfl
    · push_neg at hv
      rw [minOdd_nil _ hv, hn]
      exact hn ▸ ho


/--
A closed walk is cycle-like if it contains no repeated vertices except the first = last.
Any cycle-like walk is either a cycle, or `nil u` or `cons h (cons h.symm nil u)`
for `h = G.Adj u v`. In particular a cycle-like walk of length ≠ 0 , 2 is always a cycle.
-/
structure IsCycleLike {u : α} (w : G.Walk u u) : Prop extends IsAlmostCycle w where
  count_start_le : w.support.count u ≤ 2


/-
TODO : prove that if `w.IsCycleLike` then either `w` is `nil` or `cons h (con h.symm nil)` or
`w.IsCycle`. In particular `w.IsCycleLike ∧ Odd w.length → w.IsCycle`

Prove that if `w.IsAlmostCycle` then either `IsCycleLike` or `w = cons h p` where `h = G.Adj u x`
and `(w.rotate hx).shorterOdd hu` `IsCycleLike` (where `hu : u ∈ (w.rotate hx).support`).

Hence define `Walk.oddCycle` below to be either `p.minOdd` or
  `⟨_(p.minOdd.2.rotate hx).shorterOdd hu⟩`. To be an odd cycle in the odd closed walk `p`.
-/

def Walk.oddCycle {u : α} (p : G.Walk u u) : Σ v, G.Walk v v :=
  if 2 < p.minOdd.2.support.count (p.minOdd.1) then sorry else p.minOdd

lemma Walk.exists_odd_cycle_of_odd_closed_walk {v} (w : G.Walk v v) (ho : Odd w.length) :
    ∃ x, ∃ (c : G.Walk x x), c.IsCycle ∧ Odd c.length := by
  induction hn : w.length using Nat.strong_induction_on generalizing v w with
  | h n ih =>
  by_cases hs : ∃ x ∈ w.support , x ≠ v ∧ 1 < w.support.count x
  · obtain ⟨x, hx, hne, h2⟩ := hs
    exact ih _ (hn.symm ▸ (w.length_shorterOdd_lt_length hx hne h2)) (w.shorterOdd hx)
          (w.length_shorterOdd_odd hx ho) rfl
  · push_neg at hs
    by_cases hcv : w.support.count v ≤ 2
    · use v, w
      refine ⟨?_, ho⟩
      -- prove that if every vertex is counted once in the support
      -- except v that occurs twice then the walk is a cycle
      rw [isCycle_def ]
      refine ⟨?_,?_,?_⟩
      · -- take w = cons h w' then w' has no repeated vertices so no repeated edges
        -- need to check that h is not an edge of w' (if it is then the walk has length 2)
        cases w with
        | nil => simp [ho.pos]
        | @cons x y z h p =>
          rw [cons_isTrail_iff]
          refine ⟨?_,?_⟩
          · simp only [support_cons, count_cons_self, Nat.reduceLeDiff] at hcv
            refine ⟨edges_nodup_of_support_nodup ?_⟩
            apply List.nodup_iff_count_le_one.2
            intro a
            by_cases ha : a ∈ p.support
            · simp only [support_cons, List.mem_cons, ne_eq, forall_eq_or_imp, not_true_eq_false,
              count_cons_self, add_le_iff_nonpos_left, nonpos_iff_eq_zero, IsEmpty.forall_iff,
              true_and] at hs
              by_cases h : a = v
              · subst a; exact hcv
              · have := hs a ha h
                rwa [List.count_cons_of_ne (Ne.symm h)] at this
            · rw [List.count_eq_zero_of_not_mem ha]
              simp
          · cases p with
          | nil => simp
          | @cons a b c h1 p =>
            cases p with
            | nil =>
              simp only [length_cons, length_nil, zero_add, Nat.reduceAdd] at ho; contradiction
            | @cons d e f h2 p =>
              intro hf
              have hvy := h.ne
              have hyb := h1.ne
              have hbe := h2.ne
              simp_all only [length_cons, support_cons, List.mem_cons, ne_eq, forall_eq_or_imp,
                not_true_eq_false, count_cons_self, add_le_iff_nonpos_left, nonpos_iff_eq_zero,
                IsEmpty.forall_iff, not_false_eq_true, count_cons_of_ne, true_and, edges_cons,
                Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, and_self, Prod.swap_prod_mk, and_true,
                false_or, and_false, or_false]
              simp only [Nat.reduceLeDiff] at hcv
              have hvb : b ≠ v := by
                rintro rfl; rw [List.count_cons_of_ne (Ne.symm hvy), List.count_cons_self,
                  add_le_iff_nonpos_left, nonpos_iff_eq_zero, count_eq_zero] at hcv
                apply hcv p.end_mem_support
              obtain (rfl | ⟨rfl,rfl⟩ | hf) := hf
              · contradiction
              · rw [List.count_cons_of_ne (Ne.symm hbe), List.count_cons_self,
                  add_le_iff_nonpos_left, nonpos_iff_eq_zero, count_eq_zero] at hcv
                exact hcv p.end_mem_support
              · have := hs.1 (Ne.symm hvy)
                rw [List.count_cons_of_ne (Ne.symm hyb), count_eq_zero] at this
                apply this
                exact snd_mem_support_of_mem_edges p hf
      · rintro rfl
        simpa using ho.pos
      · rw [List.nodup_iff_count_le_one]
        intro a
        rw [List.count_tail (by simp)]
        by_cases ha : a ∈ w.support
        · simp only [head_support, beq_iff_eq, tsub_le_iff_right]
          split_ifs with hva
          · subst a; exact hcv
          · exact hs a ha (Ne.symm hva)
        · rw [List.count_eq_zero_of_not_mem ha]
          simp
    · push_neg at hcv
      -- get a vertex y ≠ v in the support of w and use (w.rotate hy)
      -- as in the first part
      cases w with
      | nil =>
        have := ho.pos
        simp at this
      | @cons v y _ h w  =>
        have hne := h.ne
        have hy : y ∈ (w.cons h).support := by simp
        let w' := (w.cons h).rotate hy
        have hv : v ∈ w'.support := by rw [mem_support_rotate_iff]; simp
        have h3 := (w'.length_shorterOdd_lt_length hv hne (by
            rw [(w.cons h).count_support_rotate_old hy (Ne.symm hne)]; omega))
        rw [length_rotate, hn] at h3
        exact ih _ h3 _ (w'.length_shorterOdd_odd hv (by rwa [length_rotate])) rfl

end SimpleGraph
