import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
set_option linter.style.header false
namespace SimpleGraph
namespace Walk
open Finset List

variable  {α : Type*} {G : SimpleGraph α} {u v w x y a b : α} {p q : G.Walk u v} {n : ℕ}
section LFDEq
variable [DecidableEq α]
/-- If a path `q : G.Walk u v` is contained in a Finset `s` then we can extend it to a path `p ++ q`
contained in `s` such that `p : G.Walk x u` and `x` has no neighbors in `s` but not in `p ++ q`. -/
lemma exists_maximal_path_subset (s : Finset α) (hq : q.IsPath) (hs : ∀ y , y ∈ q.support → y ∈ s) :
    ∃ x, ∃ p : G.Walk x u, (p.append q).IsPath ∧ (∀ y, y ∈ (p.append q).support → y ∈ s) ∧
    ∀ y, G.Adj x y → y ∈ s → y ∈ (p.append q).support := by
  by_contra! hf
  have : ∀ n, ∃ x, ∃ p : G.Walk x u, (p.append q).IsPath ∧ (∀ x, x ∈ (p.append q).support → x ∈ s) ∧
    n ≤ (p.append q).length := by
    intro n
    induction n with
    | zero => exact ⟨u, .nil, by simpa using ⟨hq, hs⟩⟩
    | succ n ih =>
      obtain ⟨x, p, hp, hs, hc⟩ := ih
      obtain ⟨y, hy⟩ := hf x p hp hs
      exact ⟨y, p.cons hy.1.symm, by aesop⟩
  obtain ⟨_, _, hp, hc1, hc2⟩ := this #s
  simp_rw [← mem_toFinset] at hc1
  have := length_support _ ▸ ((toFinset_card_of_nodup hp.2) ▸ (card_le_card hc1))
  exact hc2.not_lt this


lemma IsPath.support_takeUntil_disjoint_dropUntil_tail (hp : p.IsPath) (hx : x ∈ p.support) :
    Disjoint (p.takeUntil x hx).support (p.dropUntil x hx).support.tail := by
  rw [← p.take_spec hx, append_isPath_iff] at hp
  exact hp.2.2

end LFDEq

lemma IsPath.eq_snd_of_start_mem_edge (hp : p.IsPath) (hs : s(x, u) ∈ p.edges) : x = p.snd := by
  cases p with
  | nil => simp at hs
  | cons h p =>
    rw [snd_cons, edges_cons, List.mem_cons, cons_isPath_iff] at *
    cases hs with
    | inl h => rwa [Sym2.eq_swap, Sym2.congr_right] at h
    | inr h => exact (hp.2 <| snd_mem_support_of_mem_edges p h).elim

lemma IsPath.eq_penultimate_of_end_mem_edge (hp : p.IsPath) (hs : s(x, v) ∈ p.edges) :
     x = p.penultimate :=
  p.snd_reverse.symm ▸
    hp.reverse.eq_snd_of_start_mem_edge (p.edges_reverse ▸ (List.mem_reverse.mpr hs))

/-- Given a walk that ends in a set S, there is a first vertex of the walk in the set. -/
lemma getVert_find_first {S : Set α} [DecidablePred (· ∈ S)] (w : G.Walk u v) (h : v ∈ S) :
    ∃ n ≤ w.length, w.getVert n ∈ S ∧ ∀ m < n, w.getVert m ∉ S :=
  have h := w.getVert_length.symm ▸ h
  ⟨_, Nat.find_min' _ h, Nat.find_spec ⟨_, h⟩, fun _ h' ↦ Nat.find_min _ h'⟩

section withDecEq
variable [DecidableEq α]
lemma takeUntil_append_of_mem_left (p : G.Walk u v) (q : G.Walk v w) (hx : x ∈ p.support) :
    (p.append q).takeUntil x (subset_support_append_left _ _ hx) = p.takeUntil _ hx  := by
  induction p with
  | nil =>
    simp only [support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx; subst_vars; simp
  | @cons u _ _ _ p ih =>
    rw [support_cons] at hx
    by_cases hxu : u = x
    · subst_vars; simp
    · have := List.mem_of_ne_of_mem (fun hf ↦ hxu hf.symm) hx
      simp_rw [takeUntil_cons this hxu, cons_append]
      rw [takeUntil_cons (subset_support_append_left _ _ this) hxu]
      simpa using ih _ this

lemma takeUntil_append_of_mem_right (p : G.Walk u v) (q : G.Walk v w) (hxn : x ∉ p.support)
    (hx : x ∈ q.support) :
    (p.append q).takeUntil x (subset_support_append_right _ _ hx) =
    p.append (q.takeUntil _ hx) := by
  induction p with
  | nil => simp
  | @cons u _ _ _ p ih =>
    simp_rw [cons_append]
    rw [support_cons] at hxn
    rw [takeUntil_cons (subset_support_append_right _ _ hx) (List.ne_of_not_mem_cons hxn).symm]
    simpa using ih _ (List.not_mem_of_not_mem_cons hxn) hx

lemma takeUntil_takeUntil' (p : G.Walk u v) (hw : w ∈ p.support)
    (hx : x ∈ (p.takeUntil w hw).support) :
    (p.takeUntil w hw).takeUntil x hx = p.takeUntil x (p.support_takeUntil_subset hw hx) := by
  rw [← takeUntil_append_of_mem_left _ (p.dropUntil w hw) hx]
  simp_rw [take_spec]

lemma takeUntil_of_take (hx : x ∈ (p.take n).support) :
    (p.take n).takeUntil _ hx = (p.takeUntil x ((support_take_subset _ _) hx)) := by
  rw [← takeUntil_append_of_mem_left _ (p.drop n) hx]
  simp_rw [take_append_drop]

lemma length_takeUntil_le_of_mem_take (hx : x ∈ (p.take n).support) :
    (p.takeUntil x ((support_take_subset _ _) hx)).length ≤ n := by
  have := length_takeUntil_le _ hx
  rw [takeUntil_of_take hx] at this
  exact this.trans (length_take_le _ _)

lemma dropUntil_append_of_mem_left (p : G.Walk u v) (q : G.Walk v w) (hx : x ∈ p.support) :
    (p.append q).dropUntil x (subset_support_append_left _ _ hx) = (p.dropUntil x hx).append q := by
  induction p with
  | nil =>
    simp only [support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx; subst_vars; simp
  | @cons u _ _ _ p ih =>
    rw [support_cons] at hx
    simp_rw [cons_append, dropUntil]
    by_cases hxu : u = x
    · subst_vars; simp
    · simp_rw [dif_neg hxu]
      simpa using ih _ (List.mem_of_ne_of_mem (fun hf ↦ hxu hf.symm) hx)

lemma dropUntil_append_of_mem_right  (p : G.Walk u v) (q : G.Walk v w) (hxn : x ∉ p.support)
    (hx : x ∈ q.support) :
    (p.append q).dropUntil x (subset_support_append_right _ _ hx) = q.dropUntil _ hx := by
  induction p with
  | nil => simp
  | @cons u _ _ _ p ih =>
    simp_rw [cons_append]
    rw [support_cons] at hxn
    rw [dropUntil, dif_neg (List.ne_of_not_mem_cons hxn).symm]
    simpa using ih _ (List.not_mem_of_not_mem_cons hxn) hx

lemma dropUntil_dropUntil (p : G.Walk u v) (hw : w ∈ p.support)
    (hx : x ∈ (p.dropUntil w hw).support) (hxn : x ∉ (p.takeUntil w hw).support) :
    (p.dropUntil w hw).dropUntil x hx = p.dropUntil x (p.support_dropUntil_subset hw hx) := by
  rw [← dropUntil_append_of_mem_right _ _ hxn hx]
  simp_rw [take_spec]

lemma dropUntil_of_drop (hx : x ∈ (p.drop n).support) (hxn : x ∉ (p.take n).support) :
    (p.drop n).dropUntil _ hx = (p.dropUntil x ((support_drop_subset _ _) hx)) := by
  rw [← dropUntil_append_of_mem_right (p.take n) _ hxn hx]
  simp_rw [take_append_drop]

end withDecEq

lemma mem_support_take {m n : ℕ} (p : G.Walk u v) (h : m ≤ n) :
    p.getVert m ∈ (p.take n).support := by
  have := getVert_take p n m
  cases h.lt_or_eq with
  | inl h =>
    rw [if_neg h.not_le] at this
    rw [← this]
    exact getVert_mem_support ..
  | inr h =>
    rw [if_pos h.symm.le] at this
    simp_rw [h, ← this]
    exact getVert_mem_support ..

lemma mem_support_take_iff (p : G.Walk u v) (n : ℕ) :
    x ∈ (p.take n).support ↔ ∃ m ≤ n, p.getVert m = x := by
  classical
  constructor <;> intro h
  · exact ⟨_, length_takeUntil_le_of_mem_take h,
      getVert_length_takeUntil_eq_self p (support_take_subset p n h)⟩
  · obtain ⟨m, hm , hx⟩ := h
    exact hx.symm ▸ mem_support_take  _ hm

lemma mem_support_drop {m n : ℕ} (p : G.Walk u v) (hn : m ≤ n) :
    p.getVert n ∈ (p.drop m).support := by
  have : (p.drop m).getVert (n - m) = p.getVert n := by
    rw [getVert_drop, Nat.add_sub_of_le hn]
  exact this.symm ▸ getVert_mem_support ..

lemma mem_support_drop_iff (p : G.Walk u v) (n : ℕ) :
    x ∈ (p.drop n).support ↔ ∃ m, n ≤ m ∧ p.getVert m = x := by
  classical
  constructor <;> intro h
  · rw [← getVert_length_takeUntil_eq_self _ h, getVert_drop]
    exact ⟨_, Nat.le_add_right .., rfl⟩
  · obtain ⟨m, hm , hx⟩ := h
    exact hx.symm ▸ mem_support_drop  _ hm

variable {S : Set α}
/-- Given a walk that contains the set S, there is a first vertex of the walk in the
 set. -/
lemma exists_getVert_first (p : G.Walk u v) (hy : y ∈ S ) (h : ∀ x, x ∈ S → x ∈ p.support) :
    ∃ n, p.getVert n ∈ S ∧ ∀ x, x ∈ S → x ∈ (p.drop n).support := by
  classical
  obtain ⟨n, hn1, hn2, hn3⟩ := getVert_find_first (p.takeUntil _ (h y hy)) hy
  simp_rw [getVert_takeUntil (h y hy) hn1] at *
  use n, hn2
  conv at hn3 =>
    enter [2]; intro h'
    rw [getVert_takeUntil (h y hy) (h'.le.trans hn1)]
  intro x hx
  have := h x hx
  rw [← take_append_drop p n, mem_support_append_iff] at this
  cases this with
  | inl h =>
    obtain ⟨m, h, h1⟩ := (mem_support_take_iff p n).1 h
    cases h.lt_or_eq with
    | inl h => exact ((h1 ▸ hn3 _ h) hx).elim
    | inr h => exact (h ▸ h1).symm ▸ (start_mem_support (p.drop n))
  | inr h => exact h

lemma IsPath.cons_drop_isCycle {n : ℕ} (hp : p.IsPath) (ha : G.Adj v (p.getVert n))
    (hs : p.getVert n ≠ p.penultimate) : ((p.drop n).cons ha).IsCycle :=
  cons_isCycle_iff _ ha|>.2 ⟨hp.drop _, fun hf ↦ (fun hf ↦ hs
    <| hp.eq_penultimate_of_end_mem_edge hf) <| (edges_drop_subset ..) (Sym2.eq_swap ▸ hf)⟩

variable [DecidableEq α]
lemma IsPath.cons_takeUntil_isCycle  (hp : p.IsPath) (ha : G.Adj x u) (hx : x ∈ p.support)
    (hs : x ≠ p.snd) : ((p.takeUntil x hx).cons ha).IsCycle :=
  cons_isCycle_iff _ ha|>.2 ⟨hp.takeUntil _, fun hf ↦
    (fun hf ↦ hs <| hp.eq_snd_of_start_mem_edge hf) <| (edges_takeUntil_subset ..) hf⟩

lemma IsPath.cons_dropUntil_isCycle (hp : p.IsPath) (ha : G.Adj v x) (hx : x ∈ p.support)
    (hs : x ≠ p.penultimate) : ((p.dropUntil x hx).cons ha).IsCycle :=
  cons_isCycle_iff _ ha|>.2 ⟨hp.dropUntil _, fun hf ↦ (fun hf ↦ hs
    <| hp.eq_penultimate_of_end_mem_edge hf) <| (edges_dropUntil_subset ..) (Sym2.eq_swap ▸ hf)⟩

end Walk
end SimpleGraph
