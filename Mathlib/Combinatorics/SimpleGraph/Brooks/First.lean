import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
set_option linter.style.header false
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}
--import Mathlib.Combinatorics.SimpleGraph.Greedy

section Walks
namespace Walk
open Finset
section LFDEq

lemma exists_maximal_path_subset [DecidableEq α] {u v : α} [LocallyFinite G] (s : Finset α)
    {q : G.Walk u v} (hq : q.IsPath) (hs : ∀ y , y ∈ q.support → y ∈ s) : ∃ x, ∃ p : G.Walk x u,
    (p.append q).IsPath ∧ (∀ y, y ∈ (p.append q).support → y ∈ s) ∧
    ∀ y, G.Adj x y → y ∈ s → y ∈ (p.append q).support := by
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
      use y, p.cons hy.1.symm
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

/-- Given a walk that ends in a set S, there is a first vertex of the walk in the set. -/
lemma getVert_find_spec {u v : α} {S : Set α} [DecidablePred (· ∈ S)] (w : G.Walk u v)
    (h : v ∈ S) : ∃ n ≤ w.length, w.getVert n ∈ S ∧ ∀ m < n, w.getVert m ∉ S :=
  have h := w.getVert_length.symm ▸ h
  ⟨_, Nat.find_min' _ h, Nat.find_spec ⟨_, h⟩, fun _ h' ↦ Nat.find_min _ h'⟩

lemma takeUntil_append_of_mem_left  [DecidableEq α] {u v w x : α} (p : G.Walk u v) (q : G.Walk v w)
    (hx : x ∈ p.support) :
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

lemma takeUntil_append_of_mem_right [DecidableEq α] {u v w x : α} (p : G.Walk u v) (q : G.Walk v w)
    (hxn : x ∉ p.support) (hx : x ∈ q.support):
    (p.append q).takeUntil x (subset_support_append_right _ _ hx) =
    p.append (q.takeUntil _ hx) := by
  induction p with
  | nil => simp
  | @cons u _ _ _ p ih =>
    simp_rw [cons_append]
    rw [support_cons] at hxn
    rw [takeUntil_cons (subset_support_append_right _ _ hx) (List.ne_of_not_mem_cons hxn).symm]
    simpa using ih _ (List.not_mem_of_not_mem_cons hxn) hx

lemma takeUntil_takeUntil' {w x : α} [DecidableEq α] (p : G.Walk u v) (hw : w ∈ p.support)
    (hx : x ∈ (p.takeUntil w hw).support) :
    (p.takeUntil w hw).takeUntil x hx = p.takeUntil x (p.support_takeUntil_subset hw hx) := by
  rw [← takeUntil_append_of_mem_left _ (p.dropUntil w hw) hx]
  simp_rw [take_spec]

lemma takeUntil_of_take {u v x : α} {w : G.Walk u v} {n : ℕ}
    [DecidableEq α] (hx : x ∈ (w.take n).support) :
    (w.take n).takeUntil _ hx = (w.takeUntil x ((support_take_subset _ _) hx)) := by
  rw [← takeUntil_append_of_mem_left _ (w.drop n) hx]
  simp_rw [take_append_drop]

lemma length_takeUntil_le_of_mem_take {u v x : α} {w : G.Walk u v} {n : ℕ}
    [DecidableEq α] (hx : x ∈ (w.take n).support) :
    (w.takeUntil x ((support_take_subset _ _) hx)).length ≤ n := by
  have := length_takeUntil_le _ hx
  rw [takeUntil_of_take hx] at this
  exact this.trans (length_take_le w n)

lemma dropUntil_append_of_mem_left  [DecidableEq α] {u v w x : α} (p : G.Walk u v) (q : G.Walk v w)
    (hx : x ∈ p.support) :
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

lemma dropUntil_append_of_mem_right  [DecidableEq α] {u v w x : α} (p : G.Walk u v) (q : G.Walk v w)
    (hxn : x ∉ p.support) (hx : x ∈ q.support) :
    (p.append q).dropUntil x (subset_support_append_right _ _ hx) = q.dropUntil _ hx := by
  induction p with
  | nil => simp
  | @cons u _ _ _ p ih =>
    simp_rw [cons_append]
    rw [support_cons] at hxn
    rw [dropUntil, dif_neg (List.ne_of_not_mem_cons hxn).symm]
    simpa using ih _ (List.not_mem_of_not_mem_cons hxn) hx

lemma dropUntil_dropUntil {w x : α} [DecidableEq α] (p : G.Walk u v) (hw : w ∈ p.support)
    (hx : x ∈ (p.dropUntil w hw).support) (hxn : x ∉ (p.takeUntil w hw).support) :
    (p.dropUntil w hw).dropUntil x hx = p.dropUntil x (p.support_dropUntil_subset hw hx) := by
  rw [← dropUntil_append_of_mem_right _ _ hxn hx]
  simp_rw [take_spec]

lemma dropUntil_of_drop {u v x : α} {w : G.Walk u v} {n : ℕ}
    [DecidableEq α] (hx : x ∈ (w.drop n).support) (hxn : x ∉ (w.take n).support):
    (w.drop n).dropUntil _ hx = (w.dropUntil x ((support_drop_subset _ _) hx)) := by
  rw [← dropUntil_append_of_mem_right (w.take n) _ hxn hx]
  simp_rw [take_append_drop]

-- We apply this to p : G.Walk v₁ vᵣ with S = {x | G.Adj vᵣ x ∧ x ≠ p.penultimate}
-- then cons (w.getVert n) (w.drop n) is a cycle containing vᵣ  and all its neighbors.
/-- Given a walk that contains the set S, there is a first vertex of the walk in the
 set. -/
lemma exists_getVert_first {u v y : α} {S : Set α} [DecidableEq α] (w : G.Walk u v) (hy : y ∈ S )
    (h : ∀ x, x ∈ S → x ∈ w.support) :
    ∃ n, w.getVert n ∈ S ∧ ∀ x, x ∈ S → x ∈ (w.drop n).support := by
  classical
  obtain ⟨n, hn1, hn2, hn3⟩ := getVert_find_spec (w.takeUntil _ (h y hy)) hy
  simp_rw [getVert_takeUntil (h y hy) hn1] at *
  use n, hn2
  contrapose! hn3
  obtain ⟨x, hx1, hx2⟩ := hn3
  have hx' : x ∈ (w.take n).support ∧ x ≠ w.getVert n := by
    simp_rw [← take_append_drop w n, support_append, List.mem_append] at h
    cases h x hx1 with
    | inl h =>
      refine ⟨h, ?_⟩
      rintro rfl; apply hx2 <| start_mem_support (w.drop n)
    | inr h => exact (hx2 <| List.mem_of_mem_tail h).elim
  have := w.getVert_length_takeUntil_eq_self (h x hx1)
  use (w.takeUntil _ (h x hx1)).length
  have hl :(w.takeUntil x (h x hx1)).length < n := by
    cases (length_takeUntil_le_of_mem_take hx'.1).lt_or_eq with
    | inl h => exact h
    | inr h =>
      exfalso
      apply hx'.2.symm
      rwa [← h]
  constructor
  · exact hl
  · rw [getVert_takeUntil _ (hl.le.trans hn1)]
    rwa [← this] at hx1




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
#check List.find?
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


lemma mem_support_drop_le {m n : ℕ} (hn : m ≤ n) :
    p.getVert n ∈ (p.drop m).support := by
  have : (p.drop m).getVert (n - m) = p.getVert n := by
    rw [getVert_drop]
    congr!; omega
  rw [← this]
  exact getVert_mem_support _ _


lemma penultimate_mem_support_drop_lt_length {n : ℕ} (hn : n < p.length) :
    p.penultimate ∈ (p.drop n).support := mem_support_drop_le (by omega)


lemma IsPath.cons_drop_isCycle {n : ℕ} (hp : p.IsPath) (ha : G.Adj v (p.getVert n))
    (hs : p.getVert n ≠ p.penultimate) : ((p.drop n).cons ha).IsCycle :=
  cons_isCycle_iff _ ha|>.2 ⟨hp.drop _, fun hf ↦ (fun hf ↦ hs
    <| hp.eq_penultimate_of_end_mem_edge hf) <| (edges_drop_subset ..) (Sym2.eq_swap ▸ hf)⟩


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
