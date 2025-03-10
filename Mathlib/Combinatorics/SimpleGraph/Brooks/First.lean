import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}
--import Mathlib.Combinatorics.SimpleGraph.Greedy

section Walks
namespace Walk

variable {u v w x a b : α} {p : G.Walk u v}
lemma IsPath.eq_snd_of_start_mem_edge (hp : p.IsPath) (hs : s(x, u) ∈ p.edges) : x = p.snd := by
  cases p with
  | nil => simp at hs
  | cons h p =>
    rw [snd_cons, edges_cons, List.mem_cons, cons_isPath_iff] at *
    cases hs with
    | inl h => aesop
    | inr h => exact False.elim <| hp.2 <| snd_mem_support_of_mem_edges p h

lemma IsPath.eq_penultimate_of_end_mem_edge (hp : p.IsPath) (hs : s(x, v) ∈ p.edges) :
     x = p.penultimate :=
  p.snd_reverse.symm ▸
    hp.reverse.eq_snd_of_start_mem_edge (p.edges_reverse ▸ (List.mem_reverse.mpr hs))

/-- The first vertex in a walk that satisfies a given predicate or
its  end vertex if no such vertex exists. -/
def find {u v : α} (p : G.Walk u v) (P : α → Prop) [DecidablePred P] : α :=
  match p with
  | nil => u
  | cons _ p => if (P u) then u else (p.find P)

variable {P : α → Prop} [DecidablePred P]
@[simp]
lemma find_nil :(@nil _ G u).find P = u := rfl

@[simp]
lemma find_cons (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).find P = if (P u) then u else (p.find P) := rfl

@[simp]
lemma find_cons_pos (h : G.Adj u v) (p : G.Walk v w)  (hu : P u) : (cons h p).find P = u := by
  rw [find_cons, if_pos hu]

@[simp]
lemma find_cons_neg (h : G.Adj u v) (p : G.Walk v w) (hu : ¬ P u) :
    (cons h p).find P = (p.find P) := by rw [find_cons, if_neg hu]

lemma find_spec_some  (p : G.Walk u v) (P : α → Prop) [DecidablePred P]
    (hp : a ∈ p.support.filter P) : P (p.find P) := by
  induction p with
  | nil => aesop
  | cons h p ih =>
    rw [find]
    split_ifs with h1
    · exact h1
    · aesop

lemma not_of_not_find (hp : ¬ P (p.find P)) (ha : a ∈ p.support) : ¬ P a :=
  fun ha' ↦ hp <| find_spec_some _ _ <| List.mem_filter.2 ⟨ha, decide_eq_true ha'⟩

lemma find_spec_none_eq_end (hp : ∀ a, a ∈ p.support → ¬ P a) : p.find P = v := by
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
lemma find_mem_support : p.find P ∈ p.support := by
  induction p with
  | nil => aesop
  | cons h p ih =>
    rw [find]
    split_ifs <;> aesop

variable [DecidableEq α]
/-- The only element of `p.takeUntil (p.find P)` for which `P` holds is `p.find P`. -/
lemma eq_of_mem_takeUntil_find (hp : b ∈ (p.takeUntil (p.find P) find_mem_support).support)
    (hb : P b) : b = p.find P := by
  induction p with
  | nil => simp_all
  | @cons u v w h p ih =>
    by_cases hu : P u
    · have hf := find_cons_pos h p hu
      rw [ ← (cons h p).takeUntil_eq _ (cons h p).start_mem_support hf.symm] at *
      aesop
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

/-- If `x ∈ p.support` and `P x` holds then `x` is also in the walk `p.dropUntil (p.find P)`. -/
lemma mem_dropUntil_find_of_mem_filter (hx : x ∈ p.support.filter P) :
    x ∈ (p.dropUntil (p.find P) find_mem_support).support := by
  have := p.take_spec (u := p.find P) find_mem_support
  apply_fun support at this
  simp_rw [support_append] at this
  rw [List.mem_filter] at hx
  cases List.mem_append.1 (this ▸ hx.1) with
  | inl h =>
    rw [eq_of_mem_takeUntil_find h (decide_eq_true_eq (p:= P x) ▸ hx.2)]
    exact start_mem_support _
  | inr h => exact List.mem_of_mem_tail h

open Finset

lemma IsPath.cons_takeUntil_isCycle  (hp : p.IsPath) (ha : G.Adj x u) (hx : x ∈ p.support)
    (hs : x ≠ p.snd) : ((p.takeUntil x hx).cons ha).IsCycle :=
  cons_isCycle_iff _ ha|>.2 ⟨hp.takeUntil _, fun hf ↦
    (fun hf ↦ hs <| hp.eq_snd_of_start_mem_edge hf) <| (edges_takeUntil_subset ..) hf⟩

lemma IsPath.cons_dropUntil_isCycle (hp : p.IsPath) (ha : G.Adj v x) (hx : x ∈ p.support)
    (hs : x ≠ p.penultimate) : ((p.dropUntil x hx).cons ha).IsCycle :=
  cons_isCycle_iff _ ha|>.2 ⟨hp.dropUntil _, fun hf ↦ (fun hf ↦ hs
    <| hp.eq_penultimate_of_end_mem_edge hf) <| (edges_dropUntil_subset ..) (Sym2.eq_swap ▸ hf)⟩

variable [LocallyFinite G]

lemma exists_closing_adj (hp : p.IsPath) (hmax : G.neighborFinset v ⊆ p.support.toFinset)
    (h1 : 1 < G.degree v) : ∃ x, x ∈ p.support ∧ G.Adj v x ∧ x ≠ p.penultimate  := by
  obtain ⟨x, _, hxy⟩ := (G.one_lt_degree_iff v).1 h1
  wlog hax : x ≠ p.penultimate
  · rw [ne_eq, not_not] at hax
    subst_vars
    exact this hp hmax h1 _ p.penultimate ⟨hxy.2.1, hxy.1, hxy.2.2.symm⟩ hxy.2.2.symm
  exact ⟨_, List.mem_toFinset.1 <| hmax <| (mem_neighborFinset ..).2 hxy.1, hxy.1, hax⟩

lemma exists_cycle_of_max_path (hp : p.IsPath) (hmax : G.neighborFinset v ⊆ p.support.toFinset)
    (h1 : 1 < G.degree v) : ∃ x, ∃ (hx : x ∈ p.support), ∃ (ha : G.Adj v x),
    ((p.dropUntil x hx).cons ha).IsCycle :=
  let ⟨x, hx, ha, hne⟩ := exists_closing_adj hp hmax h1
  ⟨x, hx, ha, hp.cons_dropUntil_isCycle ha hx hne⟩

variable [DecidableRel G.Adj]
lemma maximal_cycle_of_maximal_path (hp : p.IsPath) (hmax : G.neighborFinset v ⊆ p.support.toFinset)
    (h1 : 1 < G.degree v) : ∃ x, ∃ (hx : x ∈ p.support), ∃ (ha : G.Adj v x),
    ((p.dropUntil x hx).cons ha).IsCycle ∧
    G.neighborFinset v ⊆ ((p.dropUntil x hx).cons ha).support.toFinset := by
  let P : α → Prop := fun x => G.Adj v x ∧ x ≠ p.penultimate
  let ⟨x, hx, ha, hne⟩ := exists_closing_adj hp hmax h1
  have hP : P x := ⟨ha, hne⟩
  use (p.find P), find_mem_support
  have := p.find_spec_some _ <| List.mem_filter.2 ⟨hx, decide_eq_true hP⟩
  use this.1, hp.cons_dropUntil_isCycle this.1 find_mem_support this.2
  intro y hy
  rw [List.mem_toFinset, support_cons] at *
  right
  by_cases hpen : y = p.penultimate
  · rw [hpen]
    have h2 := (p.dropUntil (p.find P) find_mem_support).penultimate_mem_support
    rwa [penultimate_dropUntil (fun hv ↦ G.loopless _ (hv ▸ this.1))] at h2
  · apply mem_dropUntil_find_of_mem_filter <| List.mem_filter.2 ⟨List.mem_toFinset.1 (hmax hy), _⟩
    rw [decide_eq_true]
    rw [mem_neighborFinset] at hy
    exact ⟨hy, hpen⟩





end Walk

end Walks

end SimpleGraph
