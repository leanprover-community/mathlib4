/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

/-!
We extend some of the walk decomposition API : we already have `Walk.takeUntil` and `Walk.dropUntil`
which satisfy `(w.takeUntil _ hx) ++ (w.dropUntil _ hx) = w`, where `w.takeUntil _ hx` is the part
of `w` from its start to the first occurence of `x` (given `hx : x ∈ w.support`).

We define two new walks `Walk.shortCut` and `Walk.shortClosed` where `w.shortCut hx` is the walk
that travels along `w` from `u` to `x` and then back to `v` without revisiting `x` and
`w.shortClosed hx` is the closed walk that travels along `w` from the first visit of `x` to the last
 visit.
-/

namespace SimpleGraph
open Walk List
variable {α : Type*}{u v x: α}  {G : SimpleGraph α}

lemma Walk.IsPath.length_one_of_end_start_mem_edges_of_path {u v : α} {w : G.Walk u v}
    (hp : w.IsPath) (h1 : s(v, u) ∈ w.edges) : w.length = 1 := by
  cases w with
  | nil => simp at h1
  | cons h p =>
    cases p with
    | nil => simp
    | cons h' p =>
      simp_all only [cons_isPath_iff, support_cons, mem_cons, not_or, edges_cons, Sym2.eq,
        Sym2.rel_iff', Prod.mk.injEq, and_false, Prod.swap_prod_mk, and_true, false_or, or_false,
        length_cons, Nat.add_eq_right, Nat.add_eq_zero, one_ne_zero]
      obtain ( rfl | ⟨rfl, rfl⟩ | hf) := h1
      · apply hp.1.2 p.end_mem_support
      · apply hp.2.2 p.start_mem_support
      · apply hp.2.2 (p.snd_mem_support_of_mem_edges hf)

/--
If `w : G.Walk u u` is a closed walk and `w.support.tail.Nodup` then it is almost a cycle, in
the sense that is either a cycle or nil or has length 2.
-/
lemma Walk.isCycle_or_nil_or_length_two_of_support_tail_nodup {u : α} (w : G.Walk u u)
    (hn : w.support.tail.Nodup) : w.IsCycle ∨ w.Nil ∨ w.length = 2 := by
  by_cases hnc : w.IsCycle
  · exact Or.inl hnc
  right
  contrapose! hnc
  rw [isCycle_def]
  refine ⟨?_, fun hf ↦ hnc.1 <| nil_iff_eq_nil.mpr hf, hn⟩
  apply IsTrail.mk
  cases w with
  | nil => simp
  | @cons _ b _ h w =>
    have : s(u, b) ∉ w.edges := by
      intro hf
      apply hnc.2
      simp only [support_cons, List.tail_cons] at hn
      simpa using (IsPath.mk' hn).length_one_of_end_start_mem_edges_of_path hf
    cases w with
    | nil => simp
    | cons h w =>
      rw [support_cons, List.tail_cons] at hn
      rw [edges_cons]
      apply nodup_cons.2 ⟨?_,edges_nodup_of_support_nodup hn⟩
      intro hf
      aesop

lemma Walk.isCycle_odd_support_tail_nodup {u : α} (w : G.Walk u u) (hn : w.support.tail.Nodup)
    (ho : Odd w.length) : w.IsCycle := by
  apply (w.isCycle_or_nil_or_length_two_of_support_tail_nodup hn).resolve_right
  rintro (hf | hf)
  · rw [nil_iff_length_eq.mp hf] at ho
    exact (Nat.not_odd_zero ho).elim
  · rw [hf] at ho
    exact (Nat.not_odd_iff_even.2 (by decide) ho).elim

variable [DecidableEq α]

lemma Walk.support_tail_nodup_iff_count_le {u : α} (w : G.Walk u u) : w.support.tail.Nodup ↔
    w.support.count u ≤ 2 ∧ ∀ x ∈ w.support, x ≠ u → count x w.support ≤ 1 := by
  rw [List.nodup_iff_count_le_one]
  constructor
  · intro h
    constructor
    · have := h u
      rw [List.count_tail (by simp)] at this
      simpa using this
    · intro x hx h'
      have := h x
      rw [List.count_tail (by simp)] at this
      simp only [head_support, beq_iff_eq, tsub_le_iff_right] at this
      rwa [if_neg (Ne.symm h'), add_zero] at this
  · intro ⟨h2, h1⟩
    intro a
    by_cases ha : a ∈ w.support
    · rw [count_tail (by simp)]
      have := h1 _ ha
      by_cases ha' : a = u
      · subst a
        simpa
      · have := this ha'
        omega
    · rw [count_eq_zero_of_not_mem (fun hf ↦ ha (mem_of_mem_tail hf))]
      omega


/-- Given a vertex `x` in a walk `w : G.Walk u v` form the walk that travels along `w` from `u`
to `x` and then back to `v` without revisiting `x` -/
abbrev Walk.shortCut (w : G.Walk u v) (hx : x ∈ w.support) : G.Walk u v :=
  (w.takeUntil _ hx).append (w.reverse.takeUntil _ (w.mem_support_reverse.2 hx)).reverse

/-- Given a vertex `x` in a walk `w` form the walk that travels along `w` from the first visit of
`x` to the last visit of `x` (which may be the same in which case this is `nil' x`) -/
abbrev Walk.shortClosed (w : G.Walk u v) (hx : x ∈ w.support) : G.Walk x x :=
  (w.reverse.dropUntil _ (w.mem_support_reverse.2 hx)).reverse.dropUntil _ (by simp)

@[simp]
lemma Walk.shortCut_start (w : G.Walk u v) : w.shortCut w.start_mem_support =
    (w.reverse.takeUntil _ (w.mem_support_reverse.2 (by simp))).reverse:= by
  cases w <;> simp [shortCut];

@[simp]
lemma Walk.mem_support_shortCut (w : G.Walk u v) (hx : x ∈ w.support) :
    x ∈ (w.shortCut hx).support := by
  simp [shortCut]

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

lemma Walk.reverse_dropUntil_reverse_takeUntil_eq_takeUntil (w : G.Walk u v) (hx : x ∈ w.support) :
  (w.reverse.dropUntil _ (w.mem_support_reverse.2 hx)).reverse.takeUntil _ (by simp) =
  w.takeUntil _ hx := by
  simp_rw [w.reverse.dropUntil_reverse_takeUntil (by simpa), reverse_reverse]

/--
w.drop.rev.drop.rev = w.rev.drop.rev.drop
-/
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
    simp_rw [dropUntil_append_of_mem_left _ _ ((p.mem_support_reverse.2 hx)), reverse_append]
    by_cases hb : x = b
    · subst b
      simp [hu]
    · simpa [hu, hb] using ih _ hb

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

/--
Given a closed walk `w : G.Walk u u` and a vertex `x ∈ w.support` we can form a new closed walk
`w.shorterOdd hx`. If `w.length` is odd then this walk is also odd. Morever if `x` occured more
than once in `w` then `w.shorterOdd hx` is strictly shorter than `w`.
-/
def Walk.shorterOdd {u : α} (p : G.Walk u u) {x : α} (hx : x ∈ p.support) : G.Walk x x :=
  if ho : Odd (p.shortClosed hx).length then
    p.shortClosed hx
  else
    (p.shortCut hx).rotate (by simp)



lemma Walk.length_shorterOdd_odd {p : G.Walk u u} {x : α} (hx : x ∈ p.support)
    (ho : Odd p.length) : Odd (p.shorterOdd hx).length := by
  rw [← p.length_shortCut_add_shortClosed hx] at ho
  rw [shorterOdd]
  split_ifs with h1
  · exact h1
  · rw [Walk.length_rotate]
    exact (Nat.odd_add.1 ho).2 (Nat.not_odd_iff_even.1 h1)

lemma Walk.length_shorterOdd_le {u : α} (p : G.Walk u u) {x : α} (hx : x ∈ p.support) :
    (p.shorterOdd hx).length ≤ p.length := by
  by_cases ho : Odd (p.shortClosed hx).length
  · rw [shorterOdd, dif_pos ho]
    rw [← p.length_shortCut_add_shortClosed hx]
    omega
  · rw [shorterOdd, dif_neg ho]
    rw [← p.length_shortCut_add_shortClosed hx, length_rotate]
    omega

-- @[simp]
-- lemma Walk.shorterOdd_of_eq (p : G.Walk u u) {x y : α} (hx : x ∈ p.support) (hy : y ∈ p.support)
--     (h : y = x) : (p.shorterOdd hy).copy h h = p.shorterOdd hx := by
--   subst h
--   rfl


lemma Walk.count_shorterOdd {p : G.Walk u u} {x : α} (hx : x ∈ p.support) (hne : x ≠ u) :
    (p.shorterOdd hx).support.count u ≤ 1 := by
  sorry

lemma Walk.length_shorterOdd_lt_length {p : G.Walk u u} {x : α} (hx : x ∈ p.support) (hne : x ≠ u)
    (h2 : 1 < p.support.count x) : (p.shorterOdd hx).length < p.length := by
  rw [shorterOdd, ← p.length_shortCut_add_shortClosed hx]
  split_ifs with ho
  · rw [lt_add_iff_pos_left, ← not_nil_iff_lt_length]
    exact p.shortCut_not_nil hx hne
  · rw [Walk.length_rotate, lt_add_iff_pos_right, ← not_nil_iff_lt_length]
    exact p.shortClosed_not_nil_of_one_lt_count hx hne h2

lemma Walk.length_shorterOdd_lt_length' {p : G.Walk u u}
    (h : p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x) ≠ []) :
    (p.shorterOdd (head_filter_mem _ _ h)).length < p.length := by
  have hm := List.head_mem h
  rw [List.mem_filter, decide_eq_true_eq] at hm
  exact p.length_shorterOdd_lt_length hm.1 hm.2.1 hm.2.2

/-- Return an almost minimal odd closed subwalk from an odd length closed walk
(if p.length is not odd then this just returns some closed subwalk).
-/
private def Walk.minOdd_aux {u : α} (p : G.Walk u u) : Σ v, G.Walk v v :=
  if h : p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x) = []
    then ⟨_,p⟩
  else
    have := p.length_shorterOdd_lt_length' h
    (p.shorterOdd (head_filter_mem _ _ h)).minOdd_aux
  termination_by p.length

lemma Walk.minOdd_aux_nil {u : α} (p : G.Walk u u)
    (hx : ∀ v ∈ p.support, v ≠ u → p.support.count v ≤ 1) : p.minOdd_aux = ⟨_, p⟩ := by
  have h : (p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x)) = [] := by
    simp_all
  rw [minOdd_aux, dif_pos h]

lemma Walk.minOdd_aux_filter_ne {u v : α} (p : G.Walk u u)
  (hv : v ∈ p.support ∧ v ≠ u ∧ 1 < p.support.count v) :
  (p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x)) ≠ [] := by
  simpa using ⟨v, hv⟩

lemma Walk.minOdd_aux_ne_nil {u v : α} (p : G.Walk u u)
    (hv : v ∈ p.support ∧ v ≠ u ∧ 1 < p.support.count v) : p.minOdd_aux =
    (p.shorterOdd ((head_filter_mem _ _ (p.minOdd_aux_filter_ne hv)))).minOdd_aux := by
  rw [minOdd_aux, dif_neg (p.minOdd_aux_filter_ne hv)]

lemma Walk.minOdd_aux_minOdd_aux {u : α} (p : G.Walk u u) :
    p.minOdd_aux.2.minOdd_aux = p.minOdd_aux := by
  induction hn : p.length using Nat.strong_induction_on generalizing p u with
  | h n ih =>
    by_cases hv : ∃ v ∈ p.support, v ≠ u ∧ 1 < p.support.count v
    · obtain ⟨v, hv⟩ := hv
      rw [p.minOdd_aux_ne_nil hv]
      exact ih _ (hn ▸ p.length_shorterOdd_lt_length' (p.minOdd_aux_filter_ne hv)) _ rfl
    · push_neg at hv
      rw [minOdd_aux_nil _ hv, minOdd_aux_nil _ hv]

lemma Walk.minOdd_aux_length_le {u : α} (p : G.Walk u u) : p.minOdd_aux.2.length ≤ p.length := by
  induction hn : p.length using Nat.strong_induction_on generalizing p u with
  | h n ih =>
    by_cases hv : ∃ v ∈ p.support, v ≠ u ∧ 1 < p.support.count v
    · obtain ⟨v, hv⟩ := hv
      rw [p.minOdd_aux_ne_nil hv]
      have hlt : (p.shorterOdd (head_filter_mem _ _ (p.minOdd_aux_filter_ne hv))).length < n :=
        hn ▸ p.length_shorterOdd_lt_length' (p.minOdd_aux_filter_ne hv)
      apply (ih _ hlt _ rfl).trans hlt.le
    · push_neg at hv
      rw [minOdd_aux_nil _ hv, hn]

lemma Walk.minOdd_aux_count_le_one_of_ne_start  {u v : α} (p : G.Walk u u)
    (hn : v ≠ p.minOdd_aux.1) : count v p.minOdd_aux.2.support ≤ 1 := by
  by_cases hv : v ∈ p.minOdd_aux.2.support
  · by_contra! hc
    have := p.minOdd_aux.2.minOdd_aux_ne_nil ⟨hv, hn, hc⟩
    rw [minOdd_aux_minOdd_aux] at this
    have hnil := p.minOdd_aux.2.minOdd_aux_filter_ne ⟨hv, hn, hc⟩
    have ht :=(p.minOdd_aux.2.shorterOdd (head_filter_mem _ _ hnil)).minOdd_aux_length_le
    rw [← this] at ht
    have := p.minOdd_aux.2.length_shorterOdd_lt_length' hnil
    omega
  · rw [count_eq_zero_of_not_mem hv]
    omega

lemma Walk.minOdd_aux_odd {u : α} (p : G.Walk u u) (ho : Odd p.length) :
    Odd p.minOdd_aux.2.length := by
  induction hn : p.length using Nat.strong_induction_on generalizing p u with
  | h n ih =>
    by_cases hv : ∃ v ∈ p.support, v ≠ u ∧ 1 < p.support.count v
    · obtain ⟨v, hv⟩ := hv
      rw [p.minOdd_aux_ne_nil hv]
      have hnil := (p.minOdd_aux_filter_ne hv)
      have hm := List.head_mem hnil
      rw [List.mem_filter, decide_eq_true_eq] at hm
      exact ih _ (hn ▸ p.length_shorterOdd_lt_length' hnil) _ (p.length_shorterOdd_odd hm.1 ho) rfl
    · push_neg at hv
      rw [minOdd_aux_nil _ hv, hn]
      exact hn ▸ ho

/-
Define `Walk.oddCycle` below to be either `p.minOdd_aux` or
  `⟨_(p.minOdd_aux.2.rotate hx).shorterOdd hu⟩`. To be an odd cycle in the odd closed walk `p`.
-/

@[simp]
lemma Walk.filter_ne_nil_of_one_lt_count {u : α} (p : G.Walk u u) (hp : 1 < p.support.count u) :
    p.support.filter (fun x ↦ x ≠ u) ≠ [] := by
  cases p with
  | nil => simp at hp
  | @cons _ x _ h p =>
    simpa using ⟨x,p.start_mem_support, h.ne'⟩


/-- Returns an odd cycle (given an odd closed walk) -/
def Walk.oddCycle {u : α} (p : G.Walk u u) : Σ v, G.Walk v v :=
  if h : p.minOdd_aux.2.support.count p.minOdd_aux.1 ≤ 2
  then
    p.minOdd_aux
  else
  -- we rotate to the first vertex ≠ p.minOdd_aux.1 and apply `shorterOdd hx` to the rotated walk
  have hx := head_filter_mem _ _ (p.minOdd_aux.2.filter_ne_nil_of_one_lt_count (by omega))
  ⟨_, (p.minOdd_aux.2.rotate hx).shorterOdd (by rwa [← mem_support_rotate_iff] at hx)⟩



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
    · exact ⟨_,_, w.isCycle_odd_support_tail_nodup
            (w.support_tail_nodup_iff_count_le.2 ⟨hcv, hs⟩) ho, ho⟩
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
