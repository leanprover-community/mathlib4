import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}
--import Mathlib.Combinatorics.SimpleGraph.Greedy

section Walks
namespace Walk
open Finset
variable {u v x : α}
/-- the ith dart of w is (wᵢ, wᵢ₊₁) -/
@[simp]
lemma get_dart_eq {w : G.Walk u v} {i : ℕ} (hi : i < w.length) :
    w.darts.get ⟨i, w.length_darts.symm ▸ hi⟩ =
    ⟨(w.getVert i, w.getVert (i + 1)), w.adj_getVert_succ hi⟩ := by
  induction w generalizing i with
  | nil => simp at hi
  | cons h p ih =>
    cases i with
    | zero => simp
    | succ i => aesop





lemma getVert_induct {w : G.Walk u v} (P : α → Prop) (hstart : P u)
   (hsucc : ∀ n, P (w.getVert n) → P (w.getVert (n + 1))) (hx : x ∈ w.support) : P x := by
  induction w with
  | nil => exact (mem_support_nil_iff.1 hx) ▸ hstart
  | cons h p ih =>
    have := getVert_zero .. ▸  (getVert_cons_succ ..) ▸ hsucc 0 hstart
    rw [support_cons] at hx
    cases hx with
    | head as => exact hstart
    | tail b hb =>
      apply ih this
      · intro n hn
        have := hsucc (n + 1)
        simp_rw [getVert_cons_succ] at this
        exact this hn
      · exact hb

lemma exists_getVert_change (w : G.Walk u v) (P : α → Prop) {x : α} (hu : P u) (hx : x ∈ w.support)
    (hxP : ¬ P x) : ∃ n, P (w.getVert n) ∧ ¬ P (w.getVert (n + 1)) ∧ n + 1 ≤ w.length := by
  have ⟨n, h1, h2⟩ : ∃ n, P (w.getVert n) ∧ ¬ P (w.getVert (n + 1)) := by
    by_contra! hc
    exact  hxP <| getVert_induct P hu hc hx
  use n, h1, h2
  by_contra! hf
  apply h2
  rw [getVert_of_length_le _ (Nat.le_of_succ_le_succ hf)] at h1
  rwa [getVert_of_length_le _ hf.le]

/-- support.get is injective on a path -/
lemma get_path_injective {p : G.Walk u v} (hp : p.IsPath): Function.Injective p.support.get :=
  List.nodup_iff_injective_get.1 hp.2


lemma exists_cycle [DecidableEq α] {c : G.Walk u u} (hc : c.IsCycle) (P : Set α) {x y : α}
    (hx : x ∈ c.support) (hxP : x ∈ P) (hy : y ∈ c.support) (hyP : y ∉ P) : ∃ (a : α),
    ∃ (c' : G.Walk a a), P a ∧ ¬ P c'.snd ∧ c'.IsCycle ∧
    c'.support.toFinset = c.support.toFinset := by
  obtain ⟨d, h1, h2, hlt⟩ := exists_getVert_change (c.rotate hx) P hxP
    ((mem_support_rotate_iff _).2 hy) hyP
  rw [length_rotate] at hlt
  have ha : (c.rotate hx).getVert d ∈ c.support := (mem_support_rotate_iff _).1 <|
    getVert_mem_support ..
  use (c.rotate hx).getVert d
  use c.rotate ha
  use h1
  refine ⟨?_,hc.rotate ha, ?_ ⟩
  · rw [snd]
    rw [getVert_rotate]
    · split_ifs with h2
      · sorry
      · sorry
    · sorry

  · ext x ; simp [mem_support_rotate_iff]

section LFDEq

lemma exists_maximal_path_subset [DecidableEq α] {u v : α} [LocallyFinite G] (s : Finset α)
    {q : G.Walk u v} (hq : q.IsPath) (hs : ∀ y , y ∈ q.support → y ∈ s) : ∃ x, ∃ p : G.Walk x u,
    (p.append q).IsPath ∧ (∀ y, y ∈ (p.append q).support → y ∈ s) ∧
    ∀ y, y ∈ G.neighborFinset x ∩ s → y ∈ (p.append q).support := by
  by_contra! hf
  have : ∀ n, ∃ x, ∃ p : G.Walk x u, (p.append q).IsPath ∧ (∀ x, x ∈ (p.append q).support → x ∈ s) ∧
    n ≤ (p.append q).length := by
    intro n
    induction n with
    | zero =>
      use u, Walk.nil; simpa using ⟨hq, hs⟩
    | succ n ih =>
      obtain ⟨x, p, hp, hs, hc⟩ := ih
      obtain ⟨y, hy⟩ := hf x p hp hs
      rw [mem_inter, mem_neighborFinset] at hy
      use y, p.cons hy.1.1.symm
      aesop
  obtain ⟨_, _, hp, hc⟩ := this #s
  simp_rw [← List.mem_toFinset] at hc
  have := length_support _ ▸ ((List.toFinset_card_of_nodup hp.2) ▸ (card_le_card hc.1))
  exact Nat.not_succ_le_self _ (this.trans hc.2)

open List
lemma IsPath.support_takeUntil_disjoint_dropUntil_tail [DecidableEq α] {u v x : α} {p : G.Walk u v}
   (hp : p.IsPath) (hx : x ∈ p.support) : Disjoint (p.takeUntil x hx).support
   (p.dropUntil x hx).support.tail := by
  rw [← p.take_spec hx, append_isPath_iff] at hp
  exact hp.2.2

end LFDEq

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


/-- The first vertex in a walk `p` that satisfies a predicate `P` or its end vertex if no such
 vertex exists. -/
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

lemma find_spec_some  {p : G.Walk u v} {P : α → Prop} [DecidablePred P]
    (hp : a ∈ p.support ∧ P a) : P (p.find P) := by
  induction p with
  | nil => aesop
  | cons h p ih =>
    rw [find]
    split_ifs with h1
    · exact h1
    · aesop

lemma not_of_not_find (hp : ¬ P (p.find P)) (ha : a ∈ p.support) : ¬ P a :=
  fun ha' ↦ hp <| find_spec_some ⟨ha, ha'⟩

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
      rw [ ← (cons h p).takeUntil_of_eq _ (cons h p).start_mem_support hf.symm] at *
      aesop
    · have hf := find_cons_neg h p hu
      have hnu : u ≠ p.find P := by
        intro h; apply hu; rw [h, ← hf]
        exact find_spec_some ⟨support_takeUntil_subset _ _ hp, hb⟩
      rw [ ← (cons h p).takeUntil_of_eq _ (hf ▸ find_mem_support) hf.symm, support_copy,
         takeUntil_cons find_mem_support hnu, support_cons] at hp
      rw [hf]
      cases hp with
      | head as => contradiction
      | tail b h' => exact ih h'

/-- If `x ∈ p.support` and `P x` holds then `x` is also in the walk `p.dropUntil (p.find P)`. -/
lemma mem_dropUntil_find_of_mem_prop (hx : x ∈ p.support ∧ P x) :
    x ∈ (p.dropUntil (p.find P) find_mem_support).support := by
  have := p.take_spec (u := p.find P) find_mem_support
  apply_fun support at this
  simp_rw [support_append] at this
  cases List.mem_append.1 (this ▸ hx.1) with
  | inl h =>
    rw [eq_of_mem_takeUntil_find h hx.2]
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

@[mk_iff IsMaximal.iff]
structure IsMaximal {u v : α} (p : G.Walk u v) : Prop where
  max : ∀ y, G.Adj v y → y ∈ p.support

/-- A walk `IsMaxPath` if it is a path containing all neighbors of its end-vertex. -/
structure IsMaxPath {u v : α} (p : G.Walk u v) [Fintype (G.neighborSet v)] : Prop extends
  IsPath p, IsMaximal p

/-- A walk `IsClosableMaxPath` if it is a path containing all neighbors of its end-vertex of which
there is more than one -/
structure IsCloseableMaxPath {u v : α} (p : G.Walk u v) [Fintype (G.neighborSet v)] : Prop extends
  IsMaxPath p where
/-- The end vertex has at least one other neighbor -/
  one_lt_degree : 1 < G.degree v

omit [DecidableEq α] in
lemma IsCloseableMaxPath.mk' {u v : α} [Fintype (G.neighborSet v)] {p : G.Walk u v}
    (hp : p.IsPath) (hmax : ∀ y, G.Adj v y → y ∈ p.support)
    (h1 : 1 < G.degree v) : IsCloseableMaxPath p := ⟨⟨hp, by rwa [IsMaximal.iff]⟩, h1⟩


/-- A walk `IsMaxCycle` if it contains all neighbors of its end-vertex. -/
structure IsMaxCycle {v : α} (p : G.Walk v v) : Prop extends IsCycle p, IsMaximal p

/-- A walk `p` in a graph `G` `IsClosable` if there is an edge in `G` from its end-vertex to a
vertex other than the penultimate vertex of `p`. -/
abbrev IsClosable (p : G.Walk u v) : Prop := ∃ x, x ∈ p.support ∧ G.Adj v x ∧ x ≠ p.penultimate

variable [DecidableRel G.Adj]
/-- The first vertex in the walk `p` that is adjacent to its end-vertex and not equal to its
penultimate vertex. -/
abbrev close (p : G.Walk u v) : α := p.find (fun x ↦ G.Adj v x ∧ x ≠ p.penultimate)

lemma IsClosable.adj (hp : p.IsClosable) : G.Adj v p.close :=
  let ⟨_, ha, hp⟩ := hp
  (find_spec_some (P := (fun x ↦ G.Adj v x ∧ x ≠ p.penultimate)) ⟨ha, hp⟩).1

lemma IsClosable.ne (hp : p.IsClosable) : p.close ≠ p.penultimate :=
  let ⟨_, ha, hp⟩ := hp
  (find_spec_some (P := (fun x ↦ G.Adj v x ∧ x ≠ p.penultimate)) ⟨ha, hp⟩).2

variable [Fintype (G.neighborSet v)]
lemma IsMaximal.isClosable (hm : p.IsMaximal) (h1 : 1 < G.degree v) :
    p.IsClosable := by
  obtain ⟨x, _, hxy⟩ := (G.one_lt_degree_iff v).1 h1
  wlog hax : x ≠ p.penultimate
  · rw [ne_eq, not_not] at hax
    subst_vars
    exact this hm h1 _ p.penultimate ⟨hxy.2.1, hxy.1, hxy.2.2.symm⟩ hxy.2.2.symm
  exact ⟨_, hm.max _ hxy.1, hxy.1, hax⟩

lemma IsCloseableMaxPath.isClosable (hp : p.IsCloseableMaxPath) : p.IsClosable :=
  hp.toIsMaximal.isClosable hp.one_lt_degree

/--
If `p : G.Walk u v` is a a closable maximal path (i.e. all neighbors of `v` lie in `p` and `v` has
 more than one neighbor) then we can close `p` into a maximal cycle, where a cycle `c : G.Walk w w`
 is maximal means that all neighbors of `w` lie in `c`. -/
lemma IsMaxCycle.dropUntil_of_isClosableMaxPath (hp : p.IsCloseableMaxPath) :
    ((p.dropUntil p.close find_mem_support).cons hp.isClosable.adj).IsMaxCycle := by
  use hp.cons_dropUntil_isCycle hp.isClosable.adj find_mem_support hp.isClosable.ne
  apply IsMaximal.mk
  intro y hy
  rw [support_cons] at *
  right
  by_cases hpen : y = p.penultimate
  · rw [hpen]
    have h2 := (p.dropUntil p.close find_mem_support).penultimate_mem_support
    rwa [penultimate_dropUntil (fun hv ↦ G.loopless _ (hv ▸ hp.isClosable.adj))] at h2
  · apply (mem_dropUntil_find_of_mem_prop ⟨(hp.max _ hy), _⟩)
    exact ⟨hy, hpen⟩




end Walk
end Walks
end SimpleGraph
