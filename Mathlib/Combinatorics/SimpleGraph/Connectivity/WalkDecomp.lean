/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/

import Mathlib.Combinatorics.SimpleGraph.Walk

/-!
# Decomposing walks
## Main definitions
- `takeUntil`: The path obtained by taking edges of an existing path until a given vertex.
- `dropUntil`: The path obtained by dropping edges of an existing path until a given vertex.
- `rotate`: Rotate a loop walk such that it is centered at the given vertex.
-/

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {v w u : V}

/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
def takeUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk v u
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then
      hx ▸ Walk.nil
    else
      cons r (takeUntil p u <| by
        cases h
        · exact (hx rfl).elim
        · assumption)

@[simp] theorem takeUntil_nil {u : V} {h} : takeUntil (nil : G.Walk u u) u h = nil := rfl

lemma takeUntil_cons {v' : V} {p : G.Walk v' v} (hwp : w ∈ p.support) (h : u ≠ w)
    (hadj : G.Adj u v') :
    (p.cons hadj).takeUntil w (List.mem_of_mem_tail hwp) = (p.takeUntil w hwp).cons hadj := by
  simp [Walk.takeUntil, h]

@[simp]
lemma takeUntil_start (p : G.Walk u v) :
    p.takeUntil u p.start_mem_support = .nil := by cases p <;> simp [Walk.takeUntil]

@[simp]
lemma nil_takeUntil (p : G.Walk u v) (hwp : w ∈ p.support) :
    (p.takeUntil w hwp).Nil ↔ u = w := by
  refine ⟨?_, fun h => by subst h; simp⟩
  intro hnil
  cases p with
  | nil => exact hnil.eq
  | cons h q =>
    simp only [support_cons, List.mem_cons, false_or] at hwp
    obtain hl | hr := hwp
    · exact hl.symm
    · by_contra! hc
      simp [takeUntil_cons hr hc] at hnil

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def dropUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk u w
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
    else dropUntil p u <| by
      cases h
      · exact (hx rfl).elim
      · assumption

@[simp] theorem dropUntil_nil {u : V} {h} : dropUntil (nil : G.Walk u u) u h = nil := rfl

@[simp]
lemma dropUntil_start (p : G.Walk u v) :
    p.dropUntil u p.start_mem_support = p := by cases p <;> simp [Walk.dropUntil]

@[simp]
lemma not_nil_dropUntil (p : G.Walk u v) (hwp : w ∈ p.support) (hne : w ≠ v) :
    ¬ (p.dropUntil w hwp).Nil := by
  contrapose! hne
  induction p with
  | nil => exact hne.eq
  | @cons u v x h p ih =>
    rw [dropUntil] at hne
    rw [support_cons, List.mem_cons] at hwp
    by_cases h: u = w
    · rw [dif_pos h] at hne
      exact hne.eq
    · rw [dif_neg h] at hne
      obtain hw1 | hw2 := hwp
      · exact absurd hw1.symm h
      · exact ih hw2 hne

/-- The `takeUntil` and `dropUntil` functions split a walk into two pieces.
The lemma `SimpleGraph.Walk.count_support_takeUntil_eq_one` specifies where this split occurs. -/
@[simp]
theorem take_spec {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).append (p.dropUntil u h) = p := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    rfl
  · cases h
    · simp!
    · simp! only
      split_ifs with h' <;> subst_vars <;> simp [*]

theorem mem_support_iff_exists_append {V : Type u} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} : w ∈ p.support ↔ ∃ (q : G.Walk u w) (r : G.Walk w v), p = q.append r := by
  classical
  constructor
  · exact fun h => ⟨_, _, (p.take_spec h).symm⟩
  · rintro ⟨q, r, rfl⟩
    simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self_iff]

@[simp]
theorem count_support_takeUntil_eq_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support.count u = 1 := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    simp!
  · cases h
    · simp!
    · simp! only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp! [*, List.count_cons]

theorem count_edges_takeUntil_le_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) (x : V) :
    (p.takeUntil u h).edges.count s(u, x) ≤ 1 := by
  induction p with
  | nil =>
    rw [mem_support_nil_iff] at h
    subst u
    simp!
  | cons ha p' ih =>
    cases h
    · simp!
    · simp! only
      split_ifs with h'
      · subst h'
        simp
      · rw [edges_cons, List.count_cons]
        split_ifs with h''
        · simp only [beq_iff_eq, Sym2.eq, Sym2.rel_iff'] at h''
          obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h''
          · exact (h' rfl).elim
          · cases p' <;> simp!
        · apply ih

@[simp]
theorem takeUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).takeUntil u h = (p.takeUntil u (by subst_vars; exact h)).copy hv rfl := by
  subst_vars
  rfl

@[simp]
theorem dropUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).dropUntil u h = (p.dropUntil u (by subst_vars; exact h)).copy rfl hw := by
  subst_vars
  rfl

theorem support_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support ⊆ p.support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inl hx

theorem support_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).support ⊆ p.support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inr hx

theorem darts_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).darts ⊆ p.darts := fun x hx => by
  rw [← take_spec p h, darts_append, List.mem_append]
  exact Or.inl hx

theorem darts_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).darts ⊆ p.darts := fun x hx => by
  rw [← take_spec p h, darts_append, List.mem_append]
  exact Or.inr hx

theorem edges_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).edges ⊆ p.edges :=
  List.map_subset _ (p.darts_takeUntil_subset h)

theorem edges_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).edges ⊆ p.edges :=
  List.map_subset _ (p.darts_dropUntil_subset h)

theorem length_takeUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).length ≤ p.length := by
  have := congr_arg Walk.length (p.take_spec h)
  rw [length_append] at this
  exact Nat.le.intro this

theorem length_dropUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).length ≤ p.length := by
  have := congr_arg Walk.length (p.take_spec h)
  rw [length_append, add_comm] at this
  exact Nat.le.intro this

lemma getVert_dropUntil {u v : V} {p : G.Walk u v} (n : ℕ) (hw : w ∈ p.support) :
    (p.dropUntil w hw).getVert n = p.getVert (n + (p.takeUntil w hw).length) := by
  nth_rw 2 [← take_spec p hw]
  have ha := getVert_append (p.takeUntil w hw) (p.dropUntil w hw) (n + (p.takeUntil w hw).length)
  rwa [if_neg <| not_lt.2 <| Nat.le_add_left _ _, Nat.add_sub_cancel, Eq.comm] at ha

@[simp]
lemma getVert_length_takeUntil_eq_self {u v x} (p : G.Walk u v) (h : x ∈ p.support) :
    p.getVert (p.takeUntil _ h).length = x := by
  have := congr_arg₂ (y := (p.takeUntil _ h).length) getVert (take_spec p h) rfl
  rwa [getVert_append, if_neg <| lt_irrefl _, Nat.sub_self, getVert_zero, Eq.comm] at this

lemma getVert_takeUntil {u v : V} {n : ℕ} {p : G.Walk u v} (hw : w ∈ p.support)
    (hn : n ≤ (p.takeUntil w hw).length) : (p.takeUntil w hw).getVert n = p.getVert n := by
  cases hn.lt_or_eq with
  | inl h =>
    nth_rw 2 [← take_spec p hw]
    rw [getVert_append, if_pos h]
  | inr h => simp [h]

lemma snd_takeUntil (p : G.Walk u v) (h : w ∈ p.support) (hn : w ≠ u):
    (p.takeUntil w h).snd = p.snd := by
  apply p.getVert_takeUntil h
  by_contra! hc
  simp only [Nat.lt_one_iff, ← nil_iff_length_eq, nil_takeUntil] at hc
  exact hn hc.symm

@[simp]
lemma length_takeUntil_add_dropUntil {p : G.Walk u v} (h : w ∈ p.support) :
    (p.takeUntil w h).length + (p.dropUntil w h).length = p.length := by
  rw [← length_append, take_spec]

lemma penultimate_dropUntil (p : G.Walk u v) (hw : w ∈ p.support) (hn : w ≠ v) :
    (p.dropUntil w hw).penultimate = p.penultimate := by
  rw [penultimate, getVert_dropUntil]
  congr
  rw [← length_takeUntil_add_dropUntil hw, add_comm, Nat.add_sub_assoc]
  exact not_nil_iff_lt_length.1 <| p.not_nil_dropUntil hw hn

lemma length_takeUntil_lt {u v w : V} {p : G.Walk v w} (h : u ∈ p.support) (huw : u ≠ w) :
    (p.takeUntil u h).length < p.length := by
  rw [(p.length_takeUntil_le h).lt_iff_ne]
  exact fun hl ↦ huw (by simpa using (hl ▸ getVert_takeUntil h (by rfl) :
    (p.takeUntil u h).getVert (p.takeUntil u h).length = p.getVert p.length))

variable {x : V}
lemma takeUntil_append_of_mem_left (p : G.Walk u v) (q : G.Walk v w) (hx : x ∈ p.support) :
    (p.append q).takeUntil x (subset_support_append_left _ _ hx) = p.takeUntil _ hx  := by
  induction p with
  | nil =>
    simp_rw [support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst_vars
    simp
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

lemma takeUntil_takeUntil (p : G.Walk u v) (hw : w ∈ p.support)
    (hx : x ∈ (p.takeUntil w hw).support) :
    (p.takeUntil w hw).takeUntil x hx = p.takeUntil x (p.support_takeUntil_subset hw hx) := by
  rw [← takeUntil_append_of_mem_left _ (p.dropUntil w hw) hx]
  simp_rw [take_spec]

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

lemma not_mem_support_takeUntil_takeUntil {p : G.Walk u v} {w x : V} (h : x ≠ w)
    (hw : w ∈ p.support) (hx : x ∈ (p.takeUntil w hw).support) :
    w ∉ ((p.takeUntil w hw).takeUntil x hx).support := by
  intro hw'
  have h1 : (((p.takeUntil w hw).takeUntil x hx).takeUntil w hw').length
      < ((p.takeUntil w hw).takeUntil x hx).length := by
    exact length_takeUntil_lt _ h.symm
  have h2 : ((p.takeUntil w hw).takeUntil x hx).length < (p.takeUntil w hw).length := by
    exact length_takeUntil_lt _ h
  simp only [takeUntil_takeUntil] at h1 h2
  omega

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)

@[simp]
theorem rotate_copy {u v v'} (p : G.Walk v v) (hv : v = v') (h : u ∈ (p.copy hv hv).support) :
    (p.copy hv hv).rotate h = (p.rotate (by simpa using h)) := by
  subst_vars
  rfl

@[simp]
theorem rotate_start {v} (p : G.Walk v v)  : p.rotate (start_mem_support ..) = p := by
  cases p <;> simp [rotate]

@[simp]
theorem rotate_not_nil {u v} {p : G.Walk v v} (hn : ¬ p.Nil) (h : u ∈ p.support) :
    ¬ (p.rotate h).Nil := by
  rw [rotate, nil_append_iff]
  intro hf
  exact hn <| (p.take_spec h) ▸ nil_append_iff.2 hf.symm

@[simp]
theorem support_rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).support.tail ~r c.support.tail := by
  simp only [rotate, tail_support_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← tail_support_append, take_spec]

theorem rotate_darts {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).darts ~r c.darts := by
  simp only [rotate, darts_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← darts_append, take_spec]

theorem rotate_edges {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).edges ~r c.edges :=
  (rotate_darts c h).map _

@[simp]
lemma length_rotate {v : V} {c : G.Walk u u} (h : v ∈ c.support) :
    (c.rotate h).length = c.length := by
  rw [rotate, length_append, add_comm, length_takeUntil_add_dropUntil]

lemma getVert_rotate {n : ℕ} {c : G.Walk v v} (h : w ∈ c.support) (hn : n ≤ c.length) :
    (c.rotate h).getVert n = if (n < (c.dropUntil _ h).length) then
      c.getVert ((n + (c.takeUntil _ h).length)) else c.getVert (n - (c.dropUntil _ h).length) := by
  rw [rotate, getVert_append, getVert_dropUntil, getVert_takeUntil]
  simpa

end WalkDecomp

/-- Given a walk `w` and a node in the support, there exists a natural `n`, such that given node
is the `n`-th node (zero-indexed) in the walk. In addition, `n` is at most the length of the path.
Due to the definition of `getVert` it would otherwise be legal to return a larger `n` for the last
node. -/
theorem mem_support_iff_exists_getVert {u v w : V} {p : G.Walk v w} :
    u ∈ p.support ↔ ∃ n, p.getVert n = u ∧ n ≤ p.length := by
  classical
  constructor
  · intro h
    exact ⟨_, p.getVert_length_takeUntil_eq_self h, p.length_takeUntil_le h⟩
  · intro ⟨_, h⟩
    exact h.1 ▸ (getVert_mem_support _ _)

variable {x : V} {p : G.Walk u v} {n : ℕ}

section withDecEq

variable [DecidableEq V]

lemma takeUntil_of_take (hx : x ∈ (p.take n).support) :
    (p.take n).takeUntil _ hx = (p.takeUntil x ((support_take_subset _ _) hx)) := by
  rw [← takeUntil_append_of_mem_left _ (p.drop n) hx]
  simp_rw [take_append_drop]

lemma length_takeUntil_le_of_mem_take (hx : x ∈ (p.take n).support) :
    (p.takeUntil x ((support_take_subset _ _) hx)).length ≤ n := by
  have := length_takeUntil_le _ hx
  rw [takeUntil_of_take hx] at this
  exact this.trans (length_take_le _ _)

lemma dropUntil_of_drop (hx : x ∈ (p.drop n).support) (hxn : x ∉ (p.take n).support) :
    (p.drop n).dropUntil _ hx = (p.dropUntil x ((support_drop_subset _ _) hx)) := by
  rw [← dropUntil_append_of_mem_right (p.take n) _ hxn hx]
  simp_rw [take_append_drop]

lemma mem_support_rotate_iff  {u v x} {c : G.Walk u u} (h : v ∈ c.support) :
    x ∈ (c.rotate h).support ↔ x ∈ c.support := by
  constructor <;> intro h' <;> rw [support_eq_cons] at h'
  · cases h' with
    | head _ => exact h
    | tail _ hb => exact List.mem_of_mem_tail <| (support_rotate c h).mem_iff.1 hb
  · cases h' with
    | head _ =>
      rw [rotate, support_append]
      exact List.mem_append_left _ <| end_mem_support ..
    | tail _ hb => exact List.mem_of_mem_tail <| (support_rotate c h).mem_iff.2 hb

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

/-- Given a walk that ends in a set S, there is a first vertex of the walk in the set. -/
lemma getVert_find_first {S : Set V} [DecidablePred (· ∈ S)] (w : G.Walk u v) (h : v ∈ S) :
    ∃ n ≤ w.length, w.getVert n ∈ S ∧ ∀ m < n, w.getVert m ∉ S :=
  have h := w.getVert_length.symm ▸ h
  ⟨_, Nat.find_min' _ h, Nat.find_spec ⟨_, h⟩, fun _ h' ↦ Nat.find_min _ h'⟩


/-- Given a walk that contains the nonempty set S, there is a walk containing the set that starts
from a vertex in the set. -/
lemma exists_getVert_first {S : Set V} (p : G.Walk u v) (hw : w ∈ S )
    (h : ∀ x, x ∈ S → x ∈ p.support) :
    ∃ n, p.getVert n ∈ S ∧ ∀ x, x ∈ S → x ∈ (p.drop n).support := by
  classical
  obtain ⟨n, hn1, hn2, hn3⟩ := getVert_find_first (p.takeUntil _ (h w hw)) hw
  simp_rw [getVert_takeUntil (h w hw) hn1] at *
  use n, hn2
  conv at hn3 =>
    enter [2]; intro h'
    rw [getVert_takeUntil (h w hw) (h'.le.trans hn1)]
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

end SimpleGraph.Walk
