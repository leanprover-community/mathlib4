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

/-- w.shortCut1 ++ w.shortClosed ++ w.shortCut2 = w -/
lemma Walk.take_shortClosed_reverse_spec (w : G.Walk u v) (hx : x ∈ w.support) (hu : x ≠ u) :
    (w.takeUntil _ hx).append ((w.shortClosed hx).append
      (w.reverse.takeUntil _ (w.mem_support_reverse.2 hx)).reverse) = w := by
  conv_rhs =>
    rw [← take_spec w hx]
  rw [w.dropUntil_spec hx hu]

lemma Walk.count_reverse {y : α} (w : G.Walk u v) :
    w.reverse.support.count y = w.support.count y := by
  simp

lemma Walk.takeUntil_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.takeUntil _ hx).support.count y ≤ w.support.count y := by
  conv_rhs =>
    rw [← take_spec w hx]
  rw [support_append, count_append]
  omega

@[simp]
lemma Walk.dropUntil_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.dropUntil _ hx).support.count y ≤ w.support.count y := by
  conv_rhs =>
    rw [← take_spec w hx]
  rw [support_append, count_append, count_tail (by simp)]
  by_cases hy : x = y
  · simp only [head_support, hy, beq_self_eq_true, ↓reduceIte]
    subst y
    rw [w.count_support_takeUntil_eq_one hx]
    omega
  · simp [hy]

lemma Walk.shortClosed_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortClosed hx).support.count y ≤ w.support.count y := by
  by_cases hu : x = u
  · subst x; rw [shortClosed_start, support_reverse, ← w.count_reverse]
    rw [List.count_reverse]
    apply w.reverse.dropUntil_count_le
  · conv_rhs =>
      rw [← w.take_shortClosed_reverse_spec hx hu]
    simp_rw [support_append, count_append]
    by_cases hy : x = y
    · rw [List.count_tail (by simp)]
      subst y
      rw [w.count_support_takeUntil_eq_one hx]
      simp
      omega
    · rw [List.count_tail (by simp), add_comm]
      simp [hy, add_assoc]

/-- If `w.count u ≤ 2` and `x ≠ u` then `u ∉ w.shortClosed x` -/
lemma Walk.shortClosed_count_le_two {u x : α} (w : G.Walk u u) (hx : x ∈ w.support) (hne : x ≠ u)
  (h2 : w.support.count u ≤ 2) : u ∉ (w.shortClosed hx).support := by
  intro hf
  have := congr_arg Walk.support <| w.take_shortClosed_reverse_spec hx hne
  apply_fun List.count u at this
  rw [← this] at h2
  simp_rw [support_append, count_append] at h2
  simp at h2
  rw [List.count_tail (by simp)] at h2
  simp [hne] at h2
  rw [← List.reverse_reverse (w.reverse.takeUntil _ (by simp [hx])).support] at h2
  rw [List.dropLast_reverse, List.count_reverse] at h2
  rw [List.count_tail (by simp)] at h2
  simp [hne] at h2
  rw [← List.count_pos_iff] at hf
  have h1 : 0 < count u (w.takeUntil _ hx).support :=
    List.count_pos_iff.2 (start_mem_support ..)
  have h3 : 0 < count u (w.reverse.takeUntil x (by simp [hx])).support :=
    List.count_pos_iff.2 (start_mem_support ..)
  omega

lemma Walk.shortCut_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortCut hx).support.count y ≤ w.support.count y := by
  by_cases hu : x = u
  · subst x
    simp only [shortCut_start, support_reverse, List.count_reverse]
    rw [←w.count_reverse]
    apply w.reverse.takeUntil_count_le
  · rw [shortCut]
    conv_rhs =>
      rw [← w.take_shortClosed_reverse_spec hx hu]
    simp_rw [support_append, count_append]
    gcongr
    rw [List.count_tail (by simp), List.count_tail (by simp)]
    by_cases hy : x = y
    · subst y
      simp
    · simp only [support_reverse, List.count_reverse, head_reverse, getLast_support, beq_iff_eq,
      hy, ↓reduceIte, tsub_zero, tail_reverse, count_append, ne_eq, support_ne_nil,
      not_false_eq_true, head_append_of_ne_nil, head_support]
      rw [← List.reverse_reverse (w.reverse.takeUntil _ (by simp [hx])).support]
      rw [List.dropLast_reverse, List.reverse_reverse, List.count_reverse]
      rw [List.count_tail (by simp)]
      simp [hy]

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

lemma Walk.count_support_rotate_new (w : G.Walk u u) (hx : x ∈ w.support) (hne : x ≠ u) :
  (w.rotate hx).support.count x = w.support.count x + 1 := by
  nth_rw 2 [← take_spec w hx]
  simp_rw [rotate, Walk.support_append, List.count_append]
  rw [List.count_tail (by simp), List.count_tail (by simp)]
  simp [if_neg (Ne.symm hne)]

lemma Walk.count_support_rotate_old (w : G.Walk u u) (hx : x ∈ w.support) (hne : x ≠ u) :
  (w.rotate hx).support.count u = w.support.count u - 1 := by
  nth_rw 2 [← take_spec w hx]
  simp_rw [rotate, Walk.support_append, List.count_append]
  rw [List.count_tail (by simp), List.count_tail (by simp)]
  simp [head_support, beq_self_eq_true, ↓reduceIte,if_neg hne]
  rw [← Nat.add_sub_assoc (by simp), add_comm]

lemma Walk.count_support_rotate_other (w : G.Walk u u) (hx : x ∈ w.support) (hvx : x ≠ v)
  (hvu : u ≠ v) : (w.rotate hx).support.count v = w.support.count v := by
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

def Walk.shorterOdd2 {u : α} (p : G.Walk u u) : G.Walk u u  :=
  match p with
  | Walk.nil' u => nil' u
  | Walk.cons h p => by
    have hy : (p.cons h).snd ∈ (p.cons h).support := by simp
    have hu : u ∈ ((p.cons h).rotate hy).support := by
      exact (mem_support_rotate_iff hy).2 (p.cons h).start_mem_support
    exact ((p.cons h).rotate hy).shorterOdd hu

lemma Walk.length_shorterOdd2 {u : α} (p : G.Walk u u) (hp : 2 < p.support.count u):
    p.shorterOdd2.length < p.length := by
  cases p with
  | nil => simp at hp
  | cons h p =>
    have hy : (p.cons h).snd ∈ (p.cons h).support := by simp
    have hu : u ∈ ((p.cons h).rotate hy).support := by
      exact (mem_support_rotate_iff hy).2 (p.cons h).start_mem_support
    rw [shorterOdd2]
    have : ((p.cons h).rotate hy).length = (p.cons h).length := by simp
    rw [← this]
    have : u ≠ (p.cons h).snd := by simpa using h.ne
    apply length_shorterOdd_lt_length hu this
    rw [count_support_rotate_old _ hy (Ne.symm this)]
    omega

lemma Walk.count_le_shorterOdd2 {u x : α} (p : G.Walk u u) (hne : x ≠ u) (h2 : p.snd ≠ x):
    p.shorterOdd2.support.count x ≤ p.support.count x := by
  cases p with
  | nil => simp [shorterOdd2]
  | @cons _ y _ h p =>
    have hy : (p.cons h).snd ∈ (p.cons h).support := by simp
    have hu : u ∈ ((p.cons h).rotate hy).support := by
      exact (mem_support_rotate_iff hy).2 (p.cons h).start_mem_support
    by_cases ho : Odd (((p.cons h).rotate hy).shortClosed hu).length
    · simp only [shorterOdd2, shorterOdd, getVert_cons_succ, ho, ↓reduceDIte]
      apply le_trans
      · apply Walk.shortClosed_count_le
      · rw [Walk.count_support_rotate_other _  hy (by simpa using h2) (Ne.symm hne) ]
    · simp only [shorterOdd2, shorterOdd, getVert_cons_succ, ho, ↓reduceDIte]
      rw [Walk.count_support_rotate_other _ (by simp) (Ne.symm hne) (by simpa using h2)]
      apply le_trans
      · apply Walk.shortCut_count_le
      · rw [Walk.count_support_rotate_other _  hy (by simpa using h2) (Ne.symm hne) ]

lemma Walk.count_le_shorterOdd2_of_snd {u : α} (p : G.Walk u u) (hne : p.snd ≠ u)
    (h1 : p.support.count p.snd ≤ 1) : p.shorterOdd2.support.count p.snd ≤ 1 := by
  apply h1.trans'
  cases p with
  | nil => simp [shorterOdd2]
  | cons h p =>
    have hy : (p.cons h).snd ∈ (p.cons h).support := by simp
    have hu : u ∈ ((p.cons h).rotate hy).support := by
      exact (mem_support_rotate_iff hy).2 (p.cons h).start_mem_support
    by_cases ho : Odd (((p.cons h).rotate hy).shortClosed hu).length
    · simp only [shorterOdd2, shorterOdd, ho, ↓reduceDIte]
      have := shortClosed_count_le_two  ((p.cons h).rotate hy) hu (Ne.symm hne)
        (by rw [count_support_rotate_new _ (by simp) hne]; omega)
      have := List.count_eq_zero_of_not_mem  this
      omega
    · simp only [shorterOdd2, shorterOdd,ho, ↓reduceDIte]
      rw [count_support_rotate_old _ _ (Ne.symm hne)]
      simp only [tsub_le_iff_right, ge_iff_le]
      rw [← count_support_rotate_new _ (by simp) hne]
      apply shortCut_count_le

def Walk.cutvert {u : α} (w : G.Walk u u) : G.Walk u u  :=
  if h : w.support.count u ≤ 2 then w
  else
    have := w.length_shorterOdd2 (by rwa [not_le] at h)
    w.shorterOdd2.cutvert
  termination_by w.length

@[simp]
lemma Walk.cutvert_of_count_le_two {u : α} (w : G.Walk u u) (h : w.support.count u ≤ 2) :
    w.cutvert = w := by
  simp [cutvert,h]

@[simp]
lemma Walk.cutvert_of_two_lt_count {u : α} (w : G.Walk u u) (h : 2 < w.support.count u) :
    w.cutvert = w.shorterOdd2.cutvert := by
  rw [cutvert, dif_neg]
  omega

lemma Walk.cutvert_cutvert {u : α} (p : G.Walk u u) :
    p.cutvert.cutvert = p.cutvert := by
  induction hn : p.length using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases h : p.support.count u ≤ 2
    · simp [h]
    · push_neg at h
      rw [cutvert_of_two_lt_count _ h]
      apply ih _ (hn ▸ p.length_shorterOdd2 h) p.shorterOdd2 rfl

lemma Walk.cutvert_odd {u : α} (p : G.Walk u u) (ho : Odd p.length) : Odd p.cutvert.length := by
  induction hn : p.length using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases h : p.support.count u ≤ 2
    · simpa [h]
    · push_neg at h
      rw [cutvert_of_two_lt_count _ h]
      apply ih _ (hn ▸ p.length_shorterOdd2 h) p.shorterOdd2 _ rfl
      cases p with
      | nil => simp at ho
      | cons h p =>
        rw [shorterOdd2]
        apply length_shorterOdd_odd
        rwa [length_rotate]

lemma Walk.cutvert_count_start {u : α} (p : G.Walk u u) : p.cutvert.support.count u ≤ 2 := by
  induction hn : p.length using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases h : p.support.count u ≤ 2
    · rwa [cutvert_of_count_le_two _ h]
    · push_neg at h
      rw [cutvert_of_two_lt_count _ h]
      exact ih _ (hn ▸ p.length_shorterOdd2 h) p.shorterOdd2 rfl

lemma Walk.cutvert_count_ne_start {u x : α} (p : G.Walk u u) (hx : x ≠ u)
    (h1 : p.support.count x ≤ 1) : p.cutvert.support.count x ≤ 1 := by
  induction hn : p.length using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases h : p.support.count u ≤ 2
    · rwa [cutvert_of_count_le_two _ h]
    · push_neg at h
      rw [cutvert_of_two_lt_count _ h]
      apply ih _ (hn ▸ p.length_shorterOdd2 h) p.shorterOdd2 _ rfl
      by_cases h' : p.snd = x
      · subst x
        exact p.count_le_shorterOdd2_of_snd  hx h1
      · exact (p.count_le_shorterOdd2 hx h').trans h1

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

/-- Returns an odd cycle (given an odd closed walk) -/
def Walk.oddCycle {u : α} (p : G.Walk u u) : Σ v, G.Walk v v := ⟨_, p.minOdd_aux.2.cutvert⟩

lemma Walk.oddCycle_is_odd {u : α} (p : G.Walk u u) (ho : Odd p.length) :
    Odd p.oddCycle.2.length := cutvert_odd _ <| p.minOdd_aux_odd ho

lemma Walk.oddCycle_isCycle {u : α} (p : G.Walk u u) (ho : Odd p.length) :
    p.oddCycle.2.IsCycle := by
  apply isCycle_odd_support_tail_nodup  _ _ <| p.oddCycle_is_odd ho
  apply (support_tail_nodup_iff_count_le _).2
      ⟨cutvert_count_start _,
      fun _ _ h ↦ cutvert_count_ne_start _ h <| minOdd_aux_count_le_one_of_ne_start p h⟩

lemma Walk.oddCycle_spec {u : α} (p : G.Walk u u) (ho : Odd p.length) :
    Odd p.oddCycle.2.length ∧ p.oddCycle.2.IsCycle := ⟨p.oddCycle_is_odd ho, p.oddCycle_isCycle ho⟩

lemma Walk.exists_odd_cycle_of_odd_closed_walk {v} (p : G.Walk v v) (ho : Odd p.length) :
    ∃ x, ∃ (c : G.Walk x x), Odd c.length ∧ c.IsCycle :=
  ⟨_, _, p.oddCycle_spec ho⟩

end SimpleGraph
