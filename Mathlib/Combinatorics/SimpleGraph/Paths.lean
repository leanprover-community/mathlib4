/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
public import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walks.Subwalks
public import Mathlib.Order.Preorder.Finite

/-!

# Trail, Path, and Cycle

In a simple graph,

* A *trail* is a walk whose edges each appear no more than once.

* A *circuit* is a nonempty trail whose first and last vertices are the
  same.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk.IsTrail`, `SimpleGraph.Walk.IsPath`, and `SimpleGraph.Walk.IsCycle`.

* `SimpleGraph.Path`

* `SimpleGraph.Path.map` for the induced map on paths,
  given an (injective) graph homomorphism.

## Tags
trails, paths, circuits, cycles
-/

@[expose] public section

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v}
variable (G : SimpleGraph V) (G' : SimpleGraph V')

namespace Walk

variable {G} {u u' v w : V}

/-! ### Trails, paths, circuits, cycles -/

/-- A *trail* is a walk with no repeating edges. -/
@[mk_iff isTrail_def]
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup

/-- A *path* is a walk with no repeating vertices.
Use `SimpleGraph.Walk.IsPath.mk'` for a simpler constructor. -/
structure IsPath {u v : V} (p : G.Walk u v) : Prop extends isTrail : IsTrail p where
  support_nodup : p.support.Nodup

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
@[mk_iff isCircuit_def]
structure IsCircuit {u : V} (p : G.Walk u u) : Prop extends isTrail : IsTrail p where
  ne_nil : p ≠ nil

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) : Prop extends isCircuit : IsCircuit p where
  support_nodup : p.support.tail.Nodup

@[deprecated (since := "2025-08-26")] protected alias IsPath.toIsTrail := IsPath.isTrail
@[deprecated (since := "2025-08-26")] protected alias IsCircuit.toIsTrail := IsCircuit.isTrail
@[deprecated (since := "2025-08-26")] protected alias IsCycle.toIsCircuit := IsCycle.isCircuit

@[simp]
theorem isTrail_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsTrail ↔ p.IsTrail := by
  subst_vars
  rfl

theorem IsPath.mk' {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : p.IsPath :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

theorem isPath_def {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup :=
  ⟨IsPath.support_nodup, IsPath.mk'⟩

theorem isPath_iff_injective_get_support {u v : V} (p : G.Walk u v) :
    p.IsPath ↔ (p.support.get ·).Injective :=
  p.isPath_def.trans List.nodup_iff_injective_get

@[simp]
theorem isPath_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsPath ↔ p.IsPath := by
  subst_vars
  rfl

@[simp]
theorem isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCircuit ↔ p.IsCircuit := by
  subst_vars
  rfl

lemma IsCircuit.not_nil {p : G.Walk v v} (hp : IsCircuit p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

theorem isCycle_def {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p ≠ nil ∧ p.support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[simp]
theorem isCycle_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCycle ↔ p.IsCycle := by
  subst_vars
  rfl

lemma IsCycle.not_nil {p : G.Walk v v} (hp : IsCycle p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

@[simp]
theorem IsTrail.nil {u : V} : (nil : G.Walk u u).IsTrail :=
  ⟨by simp [edges]⟩

theorem IsTrail.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsTrail → p.IsTrail := by simp [isTrail_def]

@[simp]
theorem isTrail_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsTrail ↔ p.IsTrail ∧ s(u, v) ∉ p.edges := by simp [isTrail_def, and_comm]

@[deprecated (since := "2025-11-03")] alias cons_isTrail_iff := isTrail_cons

protected lemma IsTrail.cons {w : G.Walk u' v} (hw : w.IsTrail) (hu : G.Adj u u')
    (hu' : s(u, u') ∉ w.edges) : (w.cons hu).IsTrail := by simp [*]

theorem IsTrail.reverse {u v : V} (p : G.Walk u v) (h : p.IsTrail) : p.reverse.IsTrail := by
  simpa [isTrail_def] using h

@[simp]
theorem reverse_isTrail_iff {u v : V} (p : G.Walk u v) : p.reverse.IsTrail ↔ p.IsTrail := by
  constructor <;>
    · intro h
      convert h.reverse _
      try rw [reverse_reverse]

theorem IsTrail.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : p.IsTrail := by
  rw [isTrail_def, edges_append, List.nodup_append] at h
  exact ⟨h.1⟩

theorem IsTrail.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : q.IsTrail := by
  rw [isTrail_def, edges_append, List.nodup_append] at h
  exact ⟨h.2.1⟩

theorem append_isTrail_iff_edges_disjoint {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsTrail) (hq : q.IsTrail) :
    (p.append q).IsTrail ↔ p.edges.Disjoint q.edges:= by
  rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append]
  exact ⟨fun h _ x y ↦ h.2.2 _ x _ y rfl,
    fun h ↦ ⟨hp.edges_nodup, hq.edges_nodup, fun _ x _ y ↦ ne_of_mem_of_not_mem x (h.symm y)⟩⟩

theorem IsTrail.count_edges_le_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (e : Sym2 V) : p.edges.count e ≤ 1 :=
  List.nodup_iff_count_le_one.mp h.edges_nodup e

theorem IsTrail.count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    {e : Sym2 V} (he : e ∈ p.edges) : p.edges.count e = 1 :=
  List.count_eq_one_of_mem h.edges_nodup he

theorem IsTrail.length_le_card_edgeFinset [Fintype G.edgeSet] {u v : V}
    {w : G.Walk u v} (h : w.IsTrail) : w.length ≤ G.edgeFinset.card := by
  classical
  let edges := w.edges.toFinset
  have : edges.card = w.length := length_edges _ ▸ List.toFinset_card_of_nodup h.edges_nodup
  rw [← this]
  have : edges ⊆ G.edgeFinset := by
    intro e h
    refine mem_edgeFinset.mpr ?_
    apply w.edges_subset_edgeSet
    simpa [edges] using h
  exact Finset.card_le_card this

theorem IsPath.nil {u : V} : (nil : G.Walk u u).IsPath := by constructor <;> simp

theorem IsPath.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsPath → p.IsPath := by simp [isPath_def]

@[simp]
theorem cons_isPath_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support := by
  constructor <;> simp +contextual [isPath_def]

protected lemma IsPath.cons {p : Walk G v w} (hp : p.IsPath) (hu : u ∉ p.support) {h : G.Adj u v} :
    (cons h p).IsPath :=
  (cons_isPath_iff _ _).2 ⟨hp, hu⟩

@[simp]
theorem isPath_iff_eq_nil {u : V} (p : G.Walk u u) : p.IsPath ↔ p = nil := by
  cases p <;> simp [IsPath.nil]

theorem IsPath.reverse {u v : V} {p : G.Walk u v} (h : p.IsPath) : p.reverse.IsPath := by
  simpa [isPath_def] using h

@[simp]
theorem isPath_reverse_iff {u v : V} (p : G.Walk u v) : p.reverse.IsPath ↔ p.IsPath := by
  constructor <;> intro h <;> convert h.reverse; simp

theorem IsPath.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).IsPath → p.IsPath := by
  simp only [isPath_def, support_append]
  exact List.Nodup.of_append_left

theorem IsPath.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsPath) : q.IsPath := by
  rw [← isPath_reverse_iff] at h ⊢
  rw [reverse_append] at h
  apply h.of_append_left

theorem isTrail_of_isSubwalk {v w v' w'} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'}
    (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsTrail) : p₁.IsTrail := by
  obtain ⟨_, _, h⟩ := h
  rw [h] at h₂
  exact h₂.of_append_left.of_append_right

theorem isPath_of_isSubwalk {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'}
    (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsPath) : p₁.IsPath := by
  obtain ⟨_, _, h⟩ := h
  rw [h] at h₂
  exact h₂.of_append_left.of_append_right

lemma IsPath.of_adj {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : h.toWalk.IsPath := by
  aesop

theorem concat_isPath_iff {p : G.Walk u v} (h : G.Adj v w) :
    (p.concat h).IsPath ↔ p.IsPath ∧ w ∉ p.support := by
  rw [← (p.concat h).isPath_reverse_iff, ← p.isPath_reverse_iff, reverse_concat, ← List.mem_reverse,
    ← support_reverse]
  exact cons_isPath_iff h.symm p.reverse

theorem IsPath.concat {p : G.Walk u v} (hp : p.IsPath) (hw : w ∉ p.support)
    (h : G.Adj v w) : (p.concat h).IsPath :=
  (concat_isPath_iff h).mpr ⟨hp, hw⟩

lemma take_isPath_of_take {u v n k} {p : G.Walk u v} (h : (p.take k).IsPath) (hle : n ≤ k) :
    (p.take n).IsPath := by
  rw [Walk.isPath_def] at h ⊢
  exact (isSubwalk_iff_support_isInfix.mp (p.take_isSubwalk_take hle)).nodup h

lemma drop_isPath_of_drop {u v n k} {p : G.Walk u v} (h : (p.drop k).IsPath) (hle : k ≤ n) :
    (p.drop n).IsPath := by
  rw [Walk.isPath_def] at h ⊢
  exact (isSubwalk_iff_support_isInfix.mp (p.drop_isSubwalk_drop hle)).nodup h

lemma IsPath.take_isPath {u v} {p : G.Walk u v} (h : p.IsPath) (n : ℕ) :
    (p.take n).IsPath := by
  cases le_or_gt n p.length with
  | inl hp => exact take_isPath_of_take (by simpa [take_of_length_le rfl.le]) hp
  | inr hp => simpa [take_of_length_le hp.le]

lemma IsPath.drop_isPath {u v} {p : G.Walk u v} (h : p.IsPath) (n : ℕ) :
    (p.drop n).IsPath :=
  drop_isPath_of_drop (by rwa [Walk.drop_zero, isPath_copy]) n.zero_le

lemma IsPath.mem_support_iff_exists_append {p : G.Walk u v} (hp : p.IsPath) :
    w ∈ p.support ↔ ∃ (q : G.Walk u w) (r : G.Walk w v), q.IsPath ∧ r.IsPath ∧ p = q.append r := by
  refine ⟨fun hw ↦ ?_, fun ⟨q, r, hq, hr, hqr⟩ ↦ p.mem_support_iff_exists_append.mpr ⟨q, r, hqr⟩⟩
  obtain ⟨q, r, hqr⟩ := p.mem_support_iff_exists_append.mp hw
  have : (q.append r).IsPath := hqr ▸ hp
  exact ⟨q, r, this.of_append_left, this.of_append_right, hqr⟩

lemma IsPath.disjoint_support_of_append {p : G.Walk u v} {q : G.Walk v w}
    (hpq : (p.append q).IsPath) (hq : ¬q.Nil) : p.support.Disjoint q.tail.support := by
  have hpq' := hpq.support_nodup
  rw [support_append] at hpq'
  rw [support_tail_of_not_nil q hq]
  exact List.disjoint_of_nodup_append hpq'

lemma IsPath.ne_of_mem_support_of_append {p : G.Walk u v} {q : G.Walk v w}
    (hpq : (p.append q).IsPath) {x y : V} (hyv : y ≠ v) (hx : x ∈ p.support) (hy : y ∈ q.support) :
    x ≠ y := by
  rintro rfl
  have hq : ¬q.Nil := by
    intro hq
    simp [nil_iff_support_eq.mp hq, hyv] at hy
  have hx' : x ∈ q.tail.support := by
    rw [support_tail_of_not_nil q hq]
    rw [mem_support_iff] at hy
    exact hy.resolve_left hyv
  exact IsPath.disjoint_support_of_append hpq hq hx hx'

@[simp]
theorem IsCycle.not_of_nil {u : V} : ¬(nil : G.Walk u u).IsCycle := fun h => h.ne_nil rfl

lemma IsCycle.ne_bot : ∀ {p : G.Walk u u}, p.IsCycle → G ≠ ⊥
  | nil, hp => by cases hp.ne_nil rfl
  | cons h _, hp => by rintro rfl; exact h

lemma IsCycle.three_le_length {v : V} {p : G.Walk v v} (hp : p.IsCycle) : 3 ≤ p.length := by
  have ⟨⟨hp, hp'⟩, _⟩ := hp
  match p with
  | .nil => simp at hp'
  | .cons h .nil => simp at h
  | .cons _ (.cons _ .nil) => simp at hp
  | .cons _ (.cons _ (.cons _ _)) => simp_rw [SimpleGraph.Walk.length_cons]; lia

lemma not_nil_of_isCycle_cons {p : G.Walk u v} {h : G.Adj v u} (hc : (Walk.cons h p).IsCycle) :
    ¬ p.Nil := by
  have := Walk.length_cons _ _ ▸ Walk.IsCycle.three_le_length hc
  rw [Walk.not_nil_iff_lt_length]
  lia

theorem cons_isCycle_iff {u v : V} (p : G.Walk v u) (h : G.Adj u v) :
    (Walk.cons h p).IsCycle ↔ p.IsPath ∧ s(u, v) ∉ p.edges := by
  simp only [Walk.isCycle_def, Walk.isPath_def, Walk.isTrail_def, edges_cons, List.nodup_cons,
    support_cons, List.tail_cons]
  have : p.support.Nodup → p.edges.Nodup := edges_nodup_of_support_nodup
  tauto

protected lemma IsCycle.reverse {p : G.Walk u u} (h : p.IsCycle) : p.reverse.IsCycle := by
  simp only [Walk.isCycle_def, nodup_tail_support_reverse] at h ⊢
  exact ⟨h.1.reverse, fun h' ↦ h.2.1 (by simp_all [← Walk.length_eq_zero_iff]), h.2.2⟩

@[simp]
lemma isCycle_reverse {p : G.Walk u u} : p.reverse.IsCycle ↔ p.IsCycle where
  mp h := by simpa using h.reverse
  mpr := .reverse

lemma IsCycle.isPath_of_append_right {p : G.Walk u v} {q : G.Walk v u} (h : ¬ p.Nil)
    (hcyc : (p.append q).IsCycle) : q.IsPath := by
  have := hcyc.2
  rw [tail_support_append, List.nodup_append'] at this
  rw [isPath_def, support_eq_cons, List.nodup_cons]
  exact ⟨this.2.2 (p.end_mem_tail_support h), this.2.1⟩

lemma IsCycle.isPath_of_append_left {p : G.Walk u v} {q : G.Walk v u} (h : ¬ q.Nil)
    (hcyc : (p.append q).IsCycle) : p.IsPath :=
  p.isPath_reverse_iff.mp ((reverse_append _ _ ▸ hcyc.reverse).isPath_of_append_right (by simpa))

lemma IsPath.tail {p : G.Walk u v} (hp : p.IsPath) : p.tail.IsPath := by
  cases p with
  | nil => simp
  | cons hadj p =>
    simp_all [Walk.isPath_def]

/-- There exists a trail of maximal length in a non-empty graph on finite edges. -/
lemma exists_isTrail_forall_isTrail_length_le_length (G : SimpleGraph V) [N : Nonempty V]
    [Finite G.edgeSet] :
    ∃ (u v : V) (p : G.Walk u v) (_ : p.IsTrail),
      ∀ (u' v' : V) (p' : G.Walk u' v') (_ : p'.IsTrail), p'.length ≤ p.length := by
  have := Fintype.ofFinite G.edgeSet
  let s := {n | ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = n}
  have : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ ↦ hn ▸ hp.length_le_card_edgeFinset
  obtain ⟨x⟩ := N
  obtain ⟨_, ⟨⟨u, v, p, hp, _⟩, hn⟩⟩ := this.exists_maximal ⟨0, ⟨x, x, Walk.nil, by simp⟩⟩
  refine ⟨u, v, p, hp, fun u' v' p' hp' ↦ ?_⟩
  have := hn ⟨u', v', p', hp', Eq.refl p'.length⟩
  lia

/-- There exists a path of maximal length in a non-empty graph on finite edges. -/
lemma exists_isPath_forall_isPath_length_le_length (G : SimpleGraph V) [N : Nonempty V]
    [Finite G.edgeSet] :
    ∃ (u v : V) (p : G.Walk u v) (_ : p.IsPath),
      ∀ (u' v' : V) (p' : G.Walk u' v') (_ : p'.IsPath), p'.length ≤ p.length := by
  have := Fintype.ofFinite G.edgeSet
  let s := {n | ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = n}
  have : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ ↦ hn ▸ hp.isTrail.length_le_card_edgeFinset
  obtain ⟨x⟩ := N
  obtain ⟨_, ⟨⟨u, v, p, hp, _⟩, hn⟩⟩ := this.exists_maximal ⟨0, ⟨x, x, Walk.nil, by simp⟩⟩
  refine ⟨u, v, p, hp, fun u' v' p' hp' ↦ ?_⟩
  have := hn ⟨u', v', p', hp', Eq.refl p'.length⟩
  lia

/-! ### About paths -/

instance [DecidableEq V] {u v : V} (p : G.Walk u v) : Decidable p.IsPath := by
  rw [isPath_def]
  infer_instance

theorem IsPath.length_lt [Fintype V] {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.length < Fintype.card V := by
  rw [Nat.lt_iff_add_one_le, ← length_support]
  exact hp.support_nodup.length_le_card

lemma IsPath.getVert_injOn {p : G.Walk u v} (hp : p.IsPath) :
    Set.InjOn p.getVert {i | i ≤ p.length} := by
  intro n hn m hm hnm
  induction p generalizing n m with
  | nil => simp_all
  | @cons v w u h p ihp =>
    simp only [length_cons, Set.mem_setOf_eq] at hn hm hnm
    by_cases hn0 : n = 0 <;> by_cases hm0 : m = 0
    · lia
    · simp only [hn0, getVert_zero, Walk.getVert_cons p h hm0] at hnm
      have hvp : v ∉ p.support := by aesop
      exact (hvp (Walk.mem_support_iff_exists_getVert.mpr ⟨(m - 1), ⟨hnm.symm, by lia⟩⟩)).elim
    · simp only [hm0, Walk.getVert_cons p h hn0] at hnm
      have hvp : v ∉ p.support := by simp_all
      exact (hvp (Walk.mem_support_iff_exists_getVert.mpr ⟨(n - 1), ⟨hnm, by lia⟩⟩)).elim
    · simp only [Walk.getVert_cons _ _ hn0, Walk.getVert_cons _ _ hm0] at hnm
      have := ihp hp.of_cons (by lia : (n - 1) ≤ p.length)
        (by lia : (m - 1) ≤ p.length) hnm
      lia

lemma IsPath.getVert_eq_start_iff {i : ℕ} {p : G.Walk u w} (hp : p.IsPath) (hi : i ≤ p.length) :
    p.getVert i = u ↔ i = 0 := by
  refine ⟨?_, by simp_all⟩
  intro h
  by_cases hi : i = 0
  · exact hi
  · apply hp.getVert_injOn (by rw [Set.mem_setOf]; lia) (by rw [Set.mem_setOf]; lia)
    simp [h]

lemma IsPath.getVert_eq_end_iff {i : ℕ} {p : G.Walk u w} (hp : p.IsPath) (hi : i ≤ p.length) :
    p.getVert i = w ↔ i = p.length := by
  have := hp.reverse.getVert_eq_start_iff (by lia : p.reverse.length - i ≤ p.reverse.length)
  simp only [length_reverse, getVert_reverse, show p.length - (p.length - i) = i by lia] at this
  rw [this]
  lia

lemma IsPath.getVert_injOn_iff (p : G.Walk u v) : Set.InjOn p.getVert {i | i ≤ p.length} ↔
    p.IsPath := by
  refine ⟨?_, fun a => a.getVert_injOn⟩
  induction p with
  | nil => simp
  | cons h q ih =>
    intro hinj
    rw [cons_isPath_iff]
    refine ⟨ih (by
      intro n hn m hm hnm
      simp only [Set.mem_setOf_eq] at hn hm
      have := hinj
        (by rw [length_cons]; lia : n + 1 ≤ (q.cons h).length)
        (by rw [length_cons]; lia : m + 1 ≤ (q.cons h).length)
        (by simpa [getVert_cons] using hnm)
      lia), fun h' => ?_⟩
    obtain ⟨n, ⟨hn, hnl⟩⟩ := mem_support_iff_exists_getVert.mp h'
    have := hinj
      (by rw [length_cons]; lia : (n + 1) ≤ (q.cons h).length)
      (by lia : 0 ≤ (q.cons h).length)
      (by rwa [getVert_cons _ _ n.add_one_ne_zero, getVert_zero])
    lia

theorem IsPath.eq_snd_of_mem_edges {p : G.Walk u v} (hp : p.IsPath) (hmem : s(u, w) ∈ p.edges) :
    w = p.snd := by
  have hnil := edges_eq_nil.not.mp <| List.ne_nil_of_mem hmem
  rw [← cons_tail_eq _ hnil, edges_cons, List.mem_cons, Sym2.eq, Sym2.rel_iff'] at hmem
  have : u ∉ p.tail.support := by induction p <;> simp_all
  grind [fst_mem_support_of_mem_edges]

theorem IsPath.eq_penultimate_of_mem_edges {p : G.Walk u v} (hp : p.IsPath)
    (hmem : s(v, w) ∈ p.edges) : w = p.penultimate := by
  simpa [hmem] using isPath_reverse_iff p |>.mpr hp |>.eq_snd_of_mem_edges (w := w)

/-! ### About cycles -/

-- TODO: These results could possibly be less laborious with a periodic function getCycleVert
lemma IsCycle.getVert_injOn {p : G.Walk u u} (hpc : p.IsCycle) :
    Set.InjOn p.getVert {i | 1 ≤ i ∧ i ≤ p.length} := by
  rw [← p.cons_tail_eq hpc.not_nil] at hpc
  intro n hn m hm hnm
  rw [← SimpleGraph.Walk.length_tail_add_one
    (p.not_nil_of_tail_not_nil (not_nil_of_isCycle_cons hpc)), Set.mem_setOf] at hn hm
  have := ((Walk.cons_isCycle_iff _ _).mp hpc).1.getVert_injOn
    (by lia : n - 1 ≤ p.tail.length) (by lia : m - 1 ≤ p.tail.length)
    (by simp_all [SimpleGraph.Walk.getVert_tail, Nat.sub_add_cancel hn.1, Nat.sub_add_cancel hm.1])
  lia

lemma IsCycle.getVert_injOn' {p : G.Walk u u} (hpc : p.IsCycle) :
    Set.InjOn p.getVert {i |  i ≤ p.length - 1} := by
  intro n hn m hm hnm
  simp only [Set.mem_setOf_eq] at *
  have := hpc.three_le_length
  have : p.length - n = p.length - m := Walk.length_reverse _ ▸ hpc.reverse.getVert_injOn
    (by simp only [Walk.length_reverse, Set.mem_setOf_eq]; lia)
    (by simp only [Walk.length_reverse, Set.mem_setOf_eq]; lia)
    (by simp [Walk.getVert_reverse, show p.length - (p.length - n) = n by lia, hnm,
      show p.length - (p.length - m) = m by lia])
  lia

lemma IsCycle.snd_ne_penultimate {p : G.Walk u u} (hp : p.IsCycle) : p.snd ≠ p.penultimate := by
  intro h
  have := hp.three_le_length
  apply hp.getVert_injOn (by simp; lia) (by simp; lia) at h
  lia

lemma IsCycle.getVert_endpoint_iff {i : ℕ} {p : G.Walk u u} (hpc : p.IsCycle) (hl : i ≤ p.length) :
    p.getVert i = u ↔ i = 0 ∨ i = p.length := by
  refine ⟨?_, by aesop⟩
  rw [or_iff_not_imp_left]
  intro h hi
  exact hpc.getVert_injOn (by simp only [Set.mem_setOf_eq]; lia)
    (by simp only [Set.mem_setOf_eq]; lia) (h.symm ▸ (Walk.getVert_length p).symm)

lemma IsCycle.getVert_sub_one_ne_getVert_add_one {i : ℕ} {p : G.Walk u u} (hpc : p.IsCycle)
    (h : i ≤ p.length) : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
  intro h'
  have hl := hpc.three_le_length
  by_cases hi' : i ≥ p.length - 1
  · rw [p.getVert_of_length_le (by lia : p.length ≤ i + 1),
      hpc.getVert_endpoint_iff (by lia)] at h'
    lia
  have := hpc.getVert_injOn' (by simp only [Set.mem_setOf_eq, Nat.sub_le_iff_le_add]; lia)
    (by simp only [Set.mem_setOf_eq]; lia) h'
  lia

/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

protected theorem IsTrail.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.takeUntil u h).IsTrail :=
  IsTrail.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)

protected theorem IsTrail.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.dropUntil u h).IsTrail :=
  IsTrail.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)

protected theorem IsPath.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.takeUntil u h).IsPath :=
  IsPath.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)

protected theorem IsPath.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.dropUntil u h).IsPath :=
  IsPath.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)

lemma IsTrail.disjoint_edges_takeUntil_dropUntil {x : V} {w : G.Walk u v} (hw : w.IsTrail)
    (hx : x ∈ w.support) : (w.takeUntil x hx).edges.Disjoint (w.dropUntil x hx).edges :=
  List.disjoint_of_nodup_append <| by simpa [← edges_append] using hw.edges_nodup

protected theorem IsTrail.rotate {u v : V} {c : G.Walk v v} (hc : c.IsTrail) (h : u ∈ c.support) :
    (c.rotate h).IsTrail := by
  rw [isTrail_def, (c.rotate_edges h).perm.nodup_iff]
  exact hc.edges_nodup

protected theorem IsCircuit.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCircuit)
    (h : u ∈ c.support) : (c.rotate h).IsCircuit := by
  refine ⟨hc.isTrail.rotate _, ?_⟩
  cases c
  · exact (hc.ne_nil rfl).elim
  · intro hn
    have hn' := congr_arg length hn
    rw [rotate, length_append, add_comm, ← length_append, take_spec] at hn'
    simp at hn'

protected theorem IsCycle.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCycle) (h : u ∈ c.support) :
    (c.rotate h).IsCycle := by
  refine ⟨hc.isCircuit.rotate _, ?_⟩
  rw [List.IsRotated.nodup_iff (support_rotate _ _)]
  exact hc.support_nodup

lemma IsCycle.isPath_takeUntil {c : G.Walk v v} (hc : c.IsCycle) (h : w ∈ c.support) :
    (c.takeUntil w h).IsPath := by
  by_cases hvw : v = w
  · subst hvw
    simp
  rw [← isCycle_reverse, ← take_spec c h, reverse_append] at hc
  exact (c.takeUntil w h).isPath_reverse_iff.mp (hc.isPath_of_append_right (not_nil_of_ne hvw))

theorem IsCycle.count_support {c : G.Walk v v} (hc : c.IsCycle) : c.support.count v = 2 := by
  have := List.count_eq_one_of_mem hc.support_nodup <| c.end_mem_tail_support hc.not_nil
  have := c.head_support ▸ List.head?_eq_some_head c.support_ne_nil
  grind

theorem IsCycle.count_support_of_mem {c : G.Walk v v} (hc : c.IsCycle) (hu : u ∈ c.support)
    (hv : u ≠ v) : c.support.count u = 1 := by
  have := List.eq_or_mem_of_mem_cons <| List.cons_head_tail c.support_ne_nil ▸ hu
  have := List.count_eq_one_of_mem hc.support_nodup <| this.resolve_left <| head_support _ ▸ hv
  have := c.head_support ▸ List.head?_eq_some_head c.support_ne_nil
  grind

/-- Taking a strict initial segment of a path removes the end vertex from the support. -/
lemma endpoint_notMem_support_takeUntil {p : G.Walk u v} (hp : p.IsPath) (hw : w ∈ p.support)
    (h : v ≠ w) : v ∉ (p.takeUntil w hw).support := by
  intro hv
  rw [Walk.mem_support_iff_exists_getVert] at hv
  obtain ⟨n, ⟨hn, hnl⟩⟩ := hv
  rw [getVert_takeUntil hw hnl] at hn
  have := p.length_takeUntil_lt hw h.symm
  have : n = p.length := hp.getVert_injOn (by rw [Set.mem_setOf]; lia) (by simp)
    (hn.symm ▸ p.getVert_length.symm)
  lia

@[deprecated (since := "2025-05-23")]
alias endpoint_not_mem_support_takeUntil := endpoint_notMem_support_takeUntil

end WalkDecomp

end Walk

/-! ### Type of paths -/

/-- The type for paths between two vertices. -/
abbrev Path (u v : V) := { p : G.Walk u v // p.IsPath }

namespace Path

variable {G G'}

@[simp]
protected theorem isPath {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsPath := p.property

@[simp]
protected theorem isTrail {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsTrail :=
  p.property.isTrail

/-- The length-0 path at a vertex. -/
@[refl, simps]
protected def nil {u : V} : G.Path u u :=
  ⟨Walk.nil, Walk.IsPath.nil⟩

/-- The length-1 path between a pair of adjacent vertices. -/
@[simps]
def singleton {u v : V} (h : G.Adj u v) : G.Path u v :=
  ⟨Walk.cons h Walk.nil, by simp [h.ne]⟩

theorem mk'_mem_edges_singleton {u v : V} (h : G.Adj u v) :
    s(u, v) ∈ (singleton h : G.Walk u v).edges := by simp [singleton]

/-- The reverse of a path is another path.  See also `SimpleGraph.Walk.reverse`. -/
@[symm, simps]
def reverse {u v : V} (p : G.Path u v) : G.Path v u :=
  ⟨Walk.reverse p, p.property.reverse⟩

theorem count_support_eq_one [DecidableEq V] {u v w : V} {p : G.Path u v}
    (hw : w ∈ (p : G.Walk u v).support) : (p : G.Walk u v).support.count w = 1 :=
  List.count_eq_one_of_mem p.property.support_nodup hw

theorem count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Path u v} (e : Sym2 V)
    (hw : e ∈ (p : G.Walk u v).edges) : (p : G.Walk u v).edges.count e = 1 :=
  List.count_eq_one_of_mem p.property.isTrail.edges_nodup hw

@[simp]
theorem nodup_support {u v : V} (p : G.Path u v) : (p : G.Walk u v).support.Nodup :=
  (Walk.isPath_def _).mp p.property

theorem loop_eq {v : V} (p : G.Path v v) : p = Path.nil := by
  obtain ⟨_ | _, h⟩ := p
  · rfl
  · simp at h

theorem notMem_edges_of_loop {v : V} {e : Sym2 V} {p : G.Path v v} :
    e ∉ (p : G.Walk v v).edges := by simp [p.loop_eq]

@[deprecated (since := "2025-05-23")] alias not_mem_edges_of_loop := notMem_edges_of_loop

theorem cons_isCycle {u v : V} (p : G.Path v u) (h : G.Adj u v)
    (he : s(u, v) ∉ (p : G.Walk v u).edges) : (Walk.cons h ↑p).IsCycle := by
  simp [Walk.isCycle_def, Walk.isTrail_cons, he]

end Path


/-! ### Walks to paths -/

namespace Walk

variable {G} {u v : V}

lemma IsPath.exists_of_edges {u v a b : V} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath)
    (hep : s(a, b) ∈ p.edges) (heq : s(a, b) ∈ q.edges) (hl : 1 < p.length) :
    ∃ z, z ∈ p.support.tail ∧ z ∈ q.support.tail := by
  apply Walk.getVert_of_edge at hep
  apply Walk.getVert_of_edge at heq
  obtain ⟨k₁, hl₁, h₁⟩ := hep
  obtain ⟨k₂, hl₂, h₂⟩ := heq
  cases h₁ with
  | inl h₁ => cases h₂ with
    | inl h₂ =>
      use b
      nth_rw 1 [h₁.2, h₂.2, p.getVert_eq_support_getElem hl₁, q.getVert_eq_support_getElem hl₂]
      exact ⟨List.mem_tail _ (Nat.zero_lt_succ k₁) _, List.mem_tail _ (Nat.zero_lt_succ k₂) _⟩
    | inr h₂ =>
      cases k₁
      · use b
        apply And.intro <| h₁.2 ▸ p.getVert_eq_support_getElem hl₁ ▸ List.mem_tail _ Nat.one_pos _
        cases k₂
        · have h : v = p.getVert p.length := (getVert_length p).symm
          rw [getVert_zero] at h₂
          nth_rw 1 [← h₂.1, h₁.2] at h
          rw [← hp.getVert_injOn hl.le (by simp) h] at hl
          contradiction
        · simp [List.mem_tail, h₂.1, q.getVert_eq_support_getElem hl₂.le]
      · use a
        nth_rw 1 [h₁.1, h₂.2, p.getVert_eq_support_getElem hl₁.le, q.getVert_eq_support_getElem hl₂]
        simp [List.mem_tail]
  | inr h₁ => cases h₂ with
    | inl h₂ =>
      cases k₁
      · use a
        apply And.intro <| h₁.2 ▸ p.getVert_eq_support_getElem hl₁ ▸ List.mem_tail _ Nat.one_pos _
        cases k₂
        · obtain ⟨_, h₁⟩ := h₁
          nth_rw 1 [h₂.1, getVert_zero, ← p.getVert_length] at h₁
          rw [hp.getVert_injOn (by simp) hl.le h₁] at hl
          contradiction
        · simp [List.mem_tail,h₂.1, q.getVert_eq_support_getElem hl₂.le]
      use b
      nth_rw 1 [h₁.1, h₂.2]
      apply And.intro <;>
      simp [List.mem_tail, p.getVert_eq_support_getElem hl₁.le, q.getVert_eq_support_getElem hl₂]
    | inr h₂ =>
      use a
      nth_rw 1 [h₁.2, h₂.2, p.getVert_eq_support_getElem hl₁, q.getVert_eq_support_getElem hl₂]
      simp [List.mem_tail]

lemma isPath_append_isCycle' {u v} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
    (h : p.support.tail.Disjoint q.support.tail) (hn : 1 < p.length) :
    (p.append q).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [append_isTrail_iff_edges_disjoint hp.isTrail hq.isTrail]
    intro x h₁ h₂
    have : ∃ a b, x = s(a, b) := ⟨x.out.1, x.out.2, Prod.mk.eta ▸ (Quot.out_eq x).symm⟩
    obtain ⟨_, _, hx⟩ := this
    subst hx
    obtain ⟨z, hz₁, hz₂⟩ := Walk.IsPath.exists_of_edges hp h₁ h₂ hn
    exact h hz₁ hz₂
  · rw [ne_eq, ← Walk.nil_iff_eq_nil, Walk.not_nil_iff_lt_length, Walk.length_append]
    omega
  · rw [Walk.tail_support_append, List.nodup_append]
    exact ⟨p.support.tail_sublist.nodup (p.isPath_def.mp hp), q.support.tail_sublist.nodup
      (q.isPath_def.mp hq), fun _ x _ y ↦ ne_of_mem_of_not_mem x (h.symm y)⟩

lemma isPath_append_isCycle {u v} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
    (h : p.support.tail.Disjoint q.support.tail) (hn : 1 < p.length ⊔ q.length) :
    (p.append q).IsCycle := by
  cases lt_sup_iff.mp hn with
  | inl hn => exact isPath_append_isCycle' hp hq h hn
  | inr hn =>
    have := isPath_append_isCycle' hq hp (List.disjoint_left.mpr h.symm) hn
    rw [isCycle_def] at this ⊢
    obtain ⟨h₁, h₂, h₃⟩ := this
    refine ⟨?_, ?_, ?_⟩
    · rw [isTrail_def, edges_append] at h₁ ⊢
      exact List.nodup_append_comm.mp h₁
    · rw [ne_eq, ← length_eq_zero_iff.not, length_append] at h₂ ⊢
      rwa [add_comm]
    · simp only [support_append, ne_eq, support_ne_nil, not_false_eq_true,
        List.tail_append_of_ne_nil] at h₃ ⊢
      exact List.nodup_append_comm.mp h₃

theorem cycle_from_two_paths {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (h : p ≠ q) :
    ∃ w, w ∈ p.support ++ q.support ∧
    ∃ c : G.Walk w w, c.IsCycle ∧ c.length ≤ p.length + q.length := by
  induction hs : p.length + q.length using Nat.strong_induction_on generalizing u v with | h s ih =>
  by_cases! hw : ∃ w ∈ p.support, w ∈ q.support ∧ w ≠ u ∧ w ≠ v
  · classical
    obtain ⟨w, hwp, hwq, hwu, hwv⟩ := hw
    by_cases! htake : p.takeUntil w hwp ≠ q.takeUntil w hwq
    · obtain ⟨x, hx, c, hc⟩ := ih ((p.takeUntil w hwp).length + (q.takeUntil w hwq).length)
        (hs ▸ Nat.add_lt_add (length_takeUntil_lt hwp hwv) (length_takeUntil_lt hwq hwv))
        (hp.takeUntil hwp) (hq.takeUntil hwq) htake rfl
      use x
      apply And.intro
      · cases List.mem_append.mp hx
        · exact List.mem_append.mpr <| Or.inl <| p.support_takeUntil_subset _ ‹_›
        · exact List.mem_append.mpr <| Or.inr <| q.support_takeUntil_subset _ ‹_›
      · use c, hc.1, hc.2.trans
        <| hs ▸ Nat.add_le_add (p.length_takeUntil_le hwp) (q.length_takeUntil_le hwq)
    · have hdrop : p.dropUntil w hwp ≠ q.dropUntil w hwq := by
        contrapose! h
        rw [← p.take_spec hwp, ← q.take_spec hwq, htake, h]
      obtain ⟨x, hx, c, hc⟩ := ih ((p.dropUntil w hwp).length + (q.dropUntil w hwq).length)
        (hs ▸ Nat.add_lt_add (length_dropUntil_lt hwp hwu) (length_dropUntil_lt hwq hwu))
        (hp.dropUntil hwp) (hq.dropUntil hwq) hdrop rfl
      use x
      apply And.intro
      · cases List.mem_append.mp hx
        · exact List.mem_append.mpr <| Or.inl <| p.support_dropUntil_subset _ ‹_›
        · exact List.mem_append.mpr <| Or.inr <| q.support_dropUntil_subset _ ‹_›
      · use c, hc.1, hc.2.trans
        <| hs ▸ Nat.add_le_add (p.length_dropUntil_le hwp) (q.length_dropUntil_le hwq)
  · use u, by simp, p.append q.reverse
    refine ⟨isPath_append_isCycle hp ((isPath_reverse_iff q).mpr hq) ?_ ?_, by simpa using hs.le⟩
    · intro a hap haq
      specialize hw a (List.mem_of_mem_tail hap) <| by
        rw [support_reverse, List.tail_reverse, List.mem_reverse] at haq
        exact List.mem_of_mem_dropLast haq
      have : u ∉ p.support.tail := (List.nodup_cons.mp (p.support_eq_cons ▸ hp.support_nodup)).1
      have : a ≠ u := by
        contrapose! this
        rwa [this] at hap
      rw [hw this, support_reverse, List.tail_reverse, List.mem_reverse] at haq
      have := (List.nodup_concat _ _).mp <| q.support_eq_concat ▸ hq.support_nodup
      tauto
    · rw [length_reverse, lt_sup_iff]
      by_contra! hpq
      obtain ⟨hpl, hql⟩ := hpq
      rw [Nat.le_one_iff_eq_zero_or_eq_one] at hpl hql
      rcases hpl with hpl | hpl <;> rcases hql with hql | hql
      · have := (nil_iff_length_eq.mpr hpl).eq
        subst this
        simp [length_eq_zero_iff.mp hpl, length_eq_zero_iff.mp hql] at h
      · exact (adj_of_length_eq_one hql).ne (nil_iff_length_eq.mpr hpl).eq
      · exact (adj_of_length_eq_one hpl).ne (nil_iff_length_eq.mpr hql).eq
      · contrapose! h
        apply ext_getVert_le_length (by rw [hpl, hql]) (fun k hk ↦ ?_)
        cases Nat.le_one_iff_eq_zero_or_eq_one.mp (hpl ▸ hk)
        · simp [‹_›]
        · subst ‹_›
          nth_rw 1 [← hpl, ← hql, getVert_length, getVert_length]

variable [DecidableEq V] {u' v' : V}

/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `SimpleGraph.Walk.bypass_isPath`.
This is packaged up in `SimpleGraph.Walk.toPath`. -/
def bypass {u v : V} : G.Walk u v → G.Walk u v
  | nil => nil
  | cons ha p =>
    let p' := p.bypass
    if hs : u ∈ p'.support then
      p'.dropUntil u hs
    else
      cons ha p'

@[simp]
theorem bypass_copy (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).bypass = p.bypass.copy hu hv := by
  subst_vars
  rfl

theorem bypass_isPath (p : G.Walk u v) : p.bypass.IsPath := by
  induction p with
  | nil => simp!
  | cons _ p' ih =>
    simp only [bypass]
    split_ifs with hs
    · exact ih.dropUntil hs
    · simp [*, cons_isPath_iff]

theorem length_bypass_le (p : G.Walk u v) : p.bypass.length ≤ p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    simp only [bypass]
    split_ifs
    · trans
      · apply length_dropUntil_le
      rw [length_cons]
      lia
    · rw [length_cons, length_cons]
      exact Nat.add_le_add_right ih 1

lemma bypass_eq_self_of_length_le (p : G.Walk u v) (h : p.length ≤ p.bypass.length) :
    p.bypass = p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [Walk.bypass]
    split_ifs with hb
    · exfalso
      simp only [hb, Walk.bypass, Walk.length_cons, dif_pos] at h
      apply Nat.not_succ_le_self p.length
      calc p.length + 1
        _ ≤ (p.bypass.dropUntil _ _).length := h
        _ ≤ p.bypass.length := Walk.length_dropUntil_le p.bypass hb
        _ ≤ p.length := Walk.length_bypass_le _
    · simp only [hb, Walk.bypass, Walk.length_cons, not_false_iff, dif_neg,
        Nat.add_le_add_iff_right] at h
      rw [ih h]

/-- Given a walk, produces a path with the same endpoints using `SimpleGraph.Walk.bypass`. -/
def toPath (p : G.Walk u v) : G.Path u v :=
  ⟨p.bypass, p.bypass_isPath⟩

theorem support_bypass_subset (p : G.Walk u v) : p.bypass.support ⊆ p.support := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    simp! only
    split_ifs
    · apply List.Subset.trans (support_dropUntil_subset _ _)
      apply List.subset_cons_of_subset
      assumption
    · rw [support_cons]
      apply List.cons_subset_cons
      assumption

theorem support_toPath_subset (p : G.Walk u v) :
    (p.toPath : G.Walk u v).support ⊆ p.support :=
  support_bypass_subset _

theorem darts_bypass_subset (p : G.Walk u v) : p.bypass.darts ⊆ p.darts := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    simp! only
    split_ifs
    · apply List.Subset.trans (darts_dropUntil_subset _ _)
      apply List.subset_cons_of_subset _ ih
    · rw [darts_cons]
      exact List.cons_subset_cons _ ih

theorem edges_bypass_subset (p : G.Walk u v) : p.bypass.edges ⊆ p.edges :=
  List.map_subset _ p.darts_bypass_subset

theorem darts_toPath_subset (p : G.Walk u v) : (p.toPath : G.Walk u v).darts ⊆ p.darts :=
  darts_bypass_subset _

theorem edges_toPath_subset (p : G.Walk u v) : (p.toPath : G.Walk u v).edges ⊆ p.edges :=
  edges_bypass_subset _

/-- Bypass repeated vertices like `Walk.bypass`, except the starting vertex.

This is intended to be used for closed walks, for which `Walk.bypass` unhelpfully returns the empty
walk. -/
def cycleBypass : G.Walk v v → G.Walk v v
  | .nil => .nil
  | .cons hvv' w => .cons hvv' w.bypass

@[simp] lemma cycleBypass_nil : (.nil : G.Walk v v).cycleBypass = .nil := rfl

lemma edges_cycleBypass_subset : ∀ {w : G.Walk v v}, w.cycleBypass.edges ⊆ w.edges
  | .nil => by simp
  | .cons (v := v') hvv' w => by
    classical
    dsimp only [cycleBypass, edges_cons]
    gcongr
    exact edges_bypass_subset _

lemma IsTrail.isCycle_cycleBypass : ∀ {w : G.Walk v v}, w ≠ .nil → w.IsTrail → w.cycleBypass.IsCycle
  | .cons (v := v') hvv' w, _, hw => by
    dsimp [cycleBypass]
    refine ⟨⟨(bypass_isPath _).isTrail.cons _ fun hvv' ↦ ?_, by simp⟩, ?_⟩
    · simp only [isTrail_cons] at hw
      exact hw.2 <| edges_bypass_subset _ hvv'
    · simpa using (bypass_isPath _).support_nodup

end Walk

/-! ### Mapping paths -/

namespace Walk

variable {G G'}
variable (f : G →g G') {u v : V} (p : G.Walk u v)
variable {p f}

theorem map_isPath_of_injective (hinj : Function.Injective f) (hp : p.IsPath) :
    (p.map f).IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [Walk.cons_isPath_iff] at hp
    simp only [map_cons, cons_isPath_iff, ih hp.1, support_map, List.mem_map, not_exists, not_and,
      true_and]
    intro x hx hf
    cases hinj hf
    exact hp.2 hx

protected theorem IsPath.of_map {f : G →g G'} (hp : (p.map f).IsPath) : p.IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih => grind [map_cons, Walk.cons_isPath_iff, support_map]

theorem map_isPath_iff_of_injective (hinj : Function.Injective f) : (p.map f).IsPath ↔ p.IsPath :=
  ⟨IsPath.of_map, map_isPath_of_injective hinj⟩

theorem map_isTrail_iff_of_injective (hinj : Function.Injective f) :
    (p.map f).IsTrail ↔ p.IsTrail := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [map_cons, isTrail_cons, ih, isTrail_cons]
    apply and_congr_right'
    rw [← Sym2.map_pair_eq, edges_map, ← List.mem_map_of_injective (Sym2.map.injective hinj)]

alias ⟨_, map_isTrail_of_injective⟩ := map_isTrail_iff_of_injective

theorem map_isCycle_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
    (p.map f).IsCycle ↔ p.IsCycle := by
  rw [isCycle_def, isCycle_def, map_isTrail_iff_of_injective hinj, Ne, map_eq_nil_iff,
    support_map, ← List.map_tail, List.nodup_map_iff hinj]

alias ⟨_, IsCycle.map⟩ := map_isCycle_iff_of_injective

@[simp]
theorem mapLe_isTrail {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsTrail ↔ p.IsTrail :=
  map_isTrail_iff_of_injective Function.injective_id

alias ⟨IsTrail.of_mapLe, IsTrail.mapLe⟩ := mapLe_isTrail

@[simp]
theorem mapLe_isPath {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsPath ↔ p.IsPath :=
  map_isPath_iff_of_injective Function.injective_id

alias ⟨IsPath.of_mapLe, IsPath.mapLe⟩ := mapLe_isPath

@[simp]
theorem mapLe_isCycle {G G' : SimpleGraph V} (h : G ≤ G') {u : V} {p : G.Walk u u} :
    (p.mapLe h).IsCycle ↔ p.IsCycle :=
  map_isCycle_iff_of_injective Function.injective_id

alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩ := mapLe_isCycle

end Walk

namespace Path

variable {G G'}

/-- Given an injective graph homomorphism, map paths to paths. -/
@[simps]
protected def map (f : G →g G') (hinj : Function.Injective f) {u v : V} (p : G.Path u v) :
    G'.Path (f u) (f v) :=
  ⟨Walk.map f p, Walk.map_isPath_of_injective hinj p.2⟩

theorem map_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Path.map f hinj : G.Path u v → G'.Path (f u) (f v)) := by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  simp only [Path.map, Subtype.mk.injEq] at h
  simp [Walk.map_injective_of_injective hinj u v h]

/-- Given a graph embedding, map paths to paths. -/
@[simps!]
protected def mapEmbedding (f : G ↪g G') {u v : V} (p : G.Path u v) : G'.Path (f u) (f v) :=
  Path.map f.toHom f.injective p

theorem mapEmbedding_injective (f : G ↪g G') (u v : V) :
    Function.Injective (Path.mapEmbedding f : G.Path u v → G'.Path (f u) (f v)) :=
  map_injective f.injective u v

end Path

/-! ### Transferring between graphs -/

namespace Walk

variable {G} {u v : V} {H : SimpleGraph V}
variable {p : G.Walk u v}

protected theorem IsPath.transfer (hp) (pp : p.IsPath) :
    (p.transfer H hp).IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.transfer, cons_isPath_iff, support_transfer _] at pp ⊢
    exact ⟨ih _ pp.1, pp.2⟩

protected theorem IsCycle.transfer {q : G.Walk u u} (qc : q.IsCycle) (hq) :
    (q.transfer H hq).IsCycle := by
  cases q with
  | nil => simp at qc
  | cons _ q =>
    simp only [edges_cons, List.mem_cons, forall_eq_or_imp] at hq
    simp only [Walk.transfer, cons_isCycle_iff, edges_transfer q hq.2] at qc ⊢
    exact ⟨qc.1.transfer hq.2, qc.2⟩

end Walk

/-! ## Deleting edges -/

namespace Walk

variable {v w : V}

protected theorem IsPath.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v w} (h : p.IsPath) (hp) : (p.toDeleteEdges s hp).IsPath :=
  h.transfer _

protected theorem IsCycle.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v v} (h : p.IsCycle) (hp) : (p.toDeleteEdges s hp).IsCycle :=
  h.transfer _

@[simp]
theorem toDeleteEdges_copy {v u u' v' : V} (s : Set (Sym2 V))
    (p : G.Walk u v) (hu : u = u') (hv : v = v') (h) :
    (p.copy hu hv).toDeleteEdges s h =
      (p.toDeleteEdges s (by subst_vars; exact h)).copy hu hv := by
  subst_vars
  rfl

end Walk

end SimpleGraph
