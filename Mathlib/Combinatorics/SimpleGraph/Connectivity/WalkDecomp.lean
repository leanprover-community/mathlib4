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
lemma takeUntil_first (p : G.Walk u v) :
    p.takeUntil u p.start_mem_support = .nil := by cases p <;> simp [Walk.takeUntil]

@[simp]
lemma nil_takeUntil (p : G.Walk u v) (hwp : w ∈ p.support) :
    (p.takeUntil w hwp).Nil ↔ u = w := by
  refine ⟨?_, fun h => by subst h; simp⟩
  intro hnil
  cases p with
  | nil => simp only [takeUntil, eq_mpr_eq_cast] at hnil; exact hnil.eq
  | cons h q =>
    simp only [support_cons, List.mem_cons] at hwp
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
    simp
  · cases h
    · simp
    · simp! only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp! [*, List.count_cons]

theorem count_edges_takeUntil_le_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) (x : V) :
    (p.takeUntil u h).edges.count s(u, x) ≤ 1 := by
  induction p with
  | nil =>
    rw [mem_support_nil_iff] at h
    subst u
    simp
  | cons ha p' ih =>
    cases h
    · simp
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

lemma getVert_takeUntil {u v : V} {n : ℕ} {p : G.Walk u v} (hw : w ∈ p.support)
    (hn : n ≤ (p.takeUntil w hw).length) : (p.takeUntil w hw).getVert n = p.getVert n := by
  cases p with
  | nil => simp only [support_nil, List.mem_singleton] at hw; aesop
  | cons h q =>
    by_cases huw : w = u
    · subst huw
      simp_all
    simp only [support_cons, List.mem_cons, huw, false_or] at hw
    by_cases hn0 : n = 0
    · aesop
    simp only [takeUntil_cons hw ((Ne.eq_def _ _).mpr huw).symm, length_cons,
      getVert_cons _ _ hn0] at hn ⊢
    apply q.getVert_takeUntil hw
    omega

lemma snd_takeUntil (hsu : w ≠ u) (p : G.Walk u v) (h : w ∈ p.support) :
    (p.takeUntil w h).snd = p.snd := by
  apply p.getVert_takeUntil h
  by_contra! hc
  simp only [Nat.lt_one_iff, ← nil_iff_length_eq, nil_takeUntil] at hc
  exact hsu hc.symm

lemma length_takeUntil_lt {u v w : V} {p : G.Walk v w} (h : u ∈ p.support) (huw : u ≠ w) :
    (p.takeUntil u h).length < p.length := by
  rw [(p.length_takeUntil_le h).lt_iff_ne]
  exact fun hl ↦ huw (by simpa using (hl ▸ getVert_takeUntil h (by rfl) :
    (p.takeUntil u h).getVert (p.takeUntil u h).length = p.getVert p.length))

lemma takeUntil_takeUntil {w x : V} (p : G.Walk u v) (hw : w ∈ p.support)
    (hx : x ∈ (p.takeUntil w hw).support) :
    (p.takeUntil w hw).takeUntil x hx = p.takeUntil x (p.support_takeUntil_subset hw hx) := by
  induction p, w, hw using takeUntil.induct with
  | case1 u v h =>
    #adaptation_note
    /-- Prior to `nightly-2025-02-24` this was just `aesop`. -/
    simp at h
    subst h
    simp
  | case2 _ _ q _ hadj hu' =>
    simp only [takeUntil_first, support_nil, List.mem_singleton] at hx
    subst hx
    simp
  | case3 a w' v' hadj q u' hu' hau' ih =>
    rw [← Ne.eq_def] at hau'
    simp only [support_cons, List.mem_cons, hau'.symm, false_or] at hu'
    simp only [takeUntil_cons hu' hau' hadj, support_cons, List.mem_cons] at hx
    by_cases hx' : x = a
    · aesop
    · replace hx : x ∈ (q.takeUntil u' hu').support := by simpa [hx'] using hx
      push_neg at hx'
      conv_lhs =>
        enter [1]
        rw [takeUntil_cons hu' hau' hadj]
      rw [takeUntil_cons hx hx'.symm hadj, ih _, takeUntil_cons _ hx'.symm]

lemma notMem_support_takeUntil_support_takeUntil_subset {p : G.Walk u v} {w x : V} (h : x ≠ w)
    (hw : w ∈ p.support) (hx : x ∈ (p.takeUntil w hw).support) :
    w ∉ (p.takeUntil x (p.support_takeUntil_subset hw hx)).support := by
  rw [← takeUntil_takeUntil p hw hx]
  intro hw'
  have h1 : (((p.takeUntil w hw).takeUntil x hx).takeUntil w hw').length
      < ((p.takeUntil w hw).takeUntil x hx).length := by
    exact length_takeUntil_lt _ h.symm
  have h2 : ((p.takeUntil w hw).takeUntil x hx).length < (p.takeUntil w hw).length := by
    exact length_takeUntil_lt _ h
  simp only [takeUntil_takeUntil] at h1 h2
  omega

@[deprecated (since := "2025-05-23")]
alias not_mem_support_takeUntil_support_takeUntil_subset :=
  notMem_support_takeUntil_support_takeUntil_subset

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)

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
    obtain ⟨q, r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp h
    use q.length
    rw [hqr, Walk.getVert_append]
    simp only [lt_self_iff_false, ↓reduceIte, Nat.sub_self, getVert_zero, length_append,
      Nat.le_add_right, and_self]
  · rintro ⟨n, hn⟩
    rw [mem_support_iff]
    cases n with
    | zero => aesop
    | succ n =>
      right
      have hnp : ¬ p.Nil := by
        rw [nil_iff_length_eq]
        omega
      rw [← support_tail_of_not_nil _ hnp, mem_support_iff_exists_getVert]
      use n
      rwa [getVert_tail, ← Nat.add_one_le_add_one_iff, length_tail_add_one hnp]
termination_by p.length
decreasing_by
· simp_wf
  rw [Nat.lt_iff_add_one_le, length_tail_add_one hnp]

end SimpleGraph.Walk
