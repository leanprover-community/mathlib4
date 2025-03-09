import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}
--import Mathlib.Combinatorics.SimpleGraph.Greedy

section Walks
namespace Walk

-- @[simp]
-- lemma IsPath.start_ne_end {u v : α} {p : G.Walk u v} (hp : p.IsPath) (h0 : ¬ p.Nil) :
--   u ≠ v := by
--   cases p with
--   | nil => simp at h0
--   | cons h p => intro; subst_vars; simp at hp

lemma IsPath.eq_snd_of_start_mem_edge {u v x : α} {p : G.Walk u v} (hp : p.IsPath)
    (hs : s(x, u) ∈ p.edges) : x = p.snd := by
  cases p with
  | nil => simp at hs
  | cons h p =>
    rw [snd_cons, edges_cons, List.mem_cons, cons_isPath_iff] at *
    cases hs with
    | inl h => aesop
    | inr h => exact False.elim <| hp.2 <| snd_mem_support_of_mem_edges p h


lemma IsPath.eq_penultimate_of_end_mem_edge {u v x : α} {p : G.Walk u v} (hp : p.IsPath)
    (hs : s(x, v) ∈ p.edges) : x = p.penultimate :=
  p.snd_reverse.symm ▸
    hp.reverse.eq_snd_of_start_mem_edge (p.edges_reverse ▸ (List.mem_reverse.mpr hs))


-- /-- If p is a path of length > 1 from u to v then uv is not an edge of p -/
-- @[simp]
-- lemma IsPath.not_edge_end_start {u v : α} {p : G.Walk u v} (hp : p.IsPath) (h1 : 1 < p.length) :
--     s(v, u) ∉ p.edges := by
--   cases p with
--   | nil => simp at h1
--   | cons h p =>
--     intro hf;
--     have := hp.eq_snd_of_start_mem_edge hf
--     aesop

/-- The first vertex in a walk that satisfies a given predicate or
its  end vertex if no such vertex exists. -/
abbrev find {u v : α} (p : G.Walk u v) (P : α → Prop) [DecidablePred P] : α :=
  match p with
  | nil => u
  | cons _ p => if (P u) then u else (p.find P)

@[simp]
lemma find_nil {u : α} {P : α → Prop} [DecidablePred P] :(@nil _ G u).find P = u := rfl

@[simp]
lemma find_cons {u v w : α} {P : α → Prop} [DecidablePred P] {h : G.Adj u v} {p : G.Walk v w} :
     (cons h p).find P = if (P u) then u else (p.find P) := rfl

@[simp]
lemma find_cons_pos {u v w : α} {P : α → Prop} [DecidablePred P] (h : G.Adj u v) (p : G.Walk v w)
(hu : P u) : (cons h p).find P = u := by
  rw [find_cons, if_pos hu]

@[simp]
lemma find_cons_neg {u v w : α} {P : α → Prop} [DecidablePred P] (h : G.Adj u v) (p : G.Walk v w)
(hu : ¬ P u) : (cons h p).find P = (p.find P) := by
  rw [find_cons, if_neg hu]

lemma find_spec_some {u v a : α}  (p : G.Walk u v) (P : α → Prop) [DecidablePred P]
(hp : a ∈ p.support.filter P) : P (p.find P) := by
  induction p with
  | nil => aesop
  | cons h p ih =>
    rw [find]
    split_ifs with h1
    · exact h1
    · aesop

lemma not_of_not_find {u v a : α} {P : α → Prop} [DecidablePred P] {p : G.Walk u v}
    (hp : ¬ P (p.find P)) (ha : a ∈ p.support) : ¬ P a :=
  fun ha' ↦ hp <| find_spec_some _ _ <| List.mem_filter.2 ⟨ha, decide_eq_true ha'⟩

lemma find_spec_none {u v : α} (p : G.Walk u v) (P : α → Prop) [DecidablePred P]
(hp : ∀ a, a ∈ p.support → ¬ P a) : p.find P = v := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp_rw [support_cons] at hp
    have : ¬ P u := hp u <| List.mem_cons_self _ _
    rw [find_cons_neg _ _ this]
    apply ih
    intro a ha
    exact hp a (by simp [ha])

@[simp]
lemma find_mem_support {u v : α} {P : α → Prop} [DecidablePred P] {p : G.Walk u v} :
    p.find P ∈ p.support := by
  induction p with
  | nil => aesop
  | cons h p ih =>
    rw [find]
    split_ifs <;> aesop

variable [DecidableEq α]

lemma find_spec_not {u v b : α} {P : α → Prop} [DecidablePred P] {p : G.Walk u v}
(hp : b ∈ (p.takeUntil (p.find P) find_mem_support).support) (hb : P b) : b = p.find P := by
  induction p with
  | nil => simp_all
  | @cons u v w h p ih =>
    by_cases hu : P u
    · have hf := find_cons_pos h p hu
      rw [ ← (cons h p).takeUntil_eq _ (cons h p).start_mem_support hf.symm] at *
      simp only [takeUntil_start, support_copy, support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      exact hf.symm ▸ hp
    · have hf := find_cons_neg h p hu
      have hnu : u ≠ p.find P := by
        intro h; apply hu; rw [h, ← hf]
        apply find_spec_some _ _
          <| List.mem_filter.2 ⟨support_takeUntil_subset _ _ hp, decide_eq_true hb⟩
      rw [ ← (cons h p).takeUntil_eq _ (hf ▸ find_mem_support) hf.symm, support_copy,
         takeUntil_cons find_mem_support hnu, support_cons] at hp
      rw [hf]
      cases hp with
      | head as => contradiction
      | tail b h' => exact ih h'
      
/-- If there `x` is in the walk `p` and `P x` holds then `x` is also in the walk
`p.reverse.dropUntil (p.reverse.find P)` -/
lemma find_spec_reverse {u v x : α} {P : α → Prop} [DecidablePred P] {p : G.Walk u v}
    (hx : x ∈ p.support.filter P) :
    x ∈ (p.reverse.dropUntil (p.reverse.find P) find_mem_support).support := by
  have := p.reverse.take_spec (u := p.reverse.find P) find_mem_support
  apply_fun support at this
  simp_rw [support_append, p.support_reverse] at this
  rw [List.mem_filter, ← List.mem_reverse] at hx
  cases List.mem_append.1 (this ▸ hx.1) with
  | inl h =>
    rw [find_spec_not h (by simpa using hx.2)]
    simp
  | inr h => exact List.mem_of_mem_tail h

open Finset

lemma IsPath.isCycle_of_mem_ne_snd_adj_start {u v x : α} {p : G.Walk u v} (hp : p.IsPath)
    (ha : G.Adj x u) (hx : x ∈ p.support) (hs : x ≠ p.snd) : ((p.takeUntil x hx).cons ha).IsCycle :=
  cons_isCycle_iff _ ha|>.2 ⟨hp.takeUntil _, fun hf ↦
    (fun hf ↦ hs <| hp.eq_snd_of_start_mem_edge hf) <| (edges_takeUntil_subset ..) hf⟩

lemma IsPath.isCycle_of_end_adj_mem_ne_penultimate {u v x : α} {p : G.Walk u v} (hp : p.IsPath)
    (ha : G.Adj v x) (hx : x ∈ p.support) (hs : x ≠ p.penultimate) :
    ((p.dropUntil x hx).cons ha).IsCycle :=
  cons_isCycle_iff _ ha|>.2 ⟨hp.dropUntil _, fun hf ↦ (fun hf ↦ hs
    <| hp.eq_penultimate_of_end_mem_edge hf) <| (edges_dropUntil_subset ..) (Sym2.eq_swap ▸ hf)⟩

variable [LocallyFinite G]
--variable [DecidableEq α]

lemma exists_closing_adj {u v : α} {p : G.Walk u v} (hp : p.IsPath)
  (hmax : G.neighborFinset u ⊆ p.support.toFinset) (h1 : 1 < G.degree u) :
    ∃ x, x ∈ p.support ∧ x ≠ p.snd ∧ G.Adj u x := by
  obtain ⟨x, _, hxy⟩ := (G.one_lt_degree_iff u).1 h1
  wlog hax : x ≠ p.snd
  · rw [ne_eq, not_not] at hax
    subst_vars
    exact this hp hmax h1 _ p.snd ⟨hxy.2.1, hxy.1, hxy.2.2.symm⟩ hxy.2.2.symm
  exact ⟨_, List.mem_toFinset.1 <| hmax <| (mem_neighborFinset ..).2 hxy.1, hax, hxy.1⟩


lemma exists_cycle_of_max_path {u v : α} {p : G.Walk u v} (hp : p.IsPath)
  (hmax : G.neighborFinset u ⊆ p.support.toFinset) (h1 : 1 < G.degree u) :
    ∃ x, ∃ (ha : G.Adj x u), ∃ (hx : x ∈ p.support), ((p.takeUntil x hx).cons ha).IsCycle :=
    let ⟨x, hx, hne, ha⟩ := exists_closing_adj hp hmax h1
    ⟨x, ha.symm, hx, hp.isCycle_of_mem_ne_snd_adj_start ha.symm hx hne ⟩





end Walk

end Walks

end SimpleGraph
