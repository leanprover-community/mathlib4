/-
Copyright (c) 2025 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walks.Operations
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Subwalks

We define a relation on walks stating that one walk is the subwalk of another.

## Main definitions

* `SimpleGraph.Walk.IsSubwalk`: A relation on walks stating that the first walk is a contiguous
  subwalk of the second walk.

## Tags
walks, subwalks
-/

@[expose] public section

namespace SimpleGraph

namespace Walk

variable {V : Type*} {G G' : SimpleGraph V} {u v u' v' : V}

/-- `p.IsSubwalk q` means that the walk `p` is a contiguous subwalk of the walk `q`. -/
def IsSubwalk {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop :=
  ∃ (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv

@[refl, simp]
lemma isSubwalk_rfl {u v} (p : G.Walk u v) : p.IsSubwalk p :=
  ⟨nil, nil, by simp⟩

@[simp]
lemma nil_isSubwalk {u v} (q : G.Walk u v) : (Walk.nil : G.Walk u u).IsSubwalk q :=
  ⟨nil, q, by simp⟩

protected lemma IsSubwalk.cons {u v u' v' w} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) (h : G.Adj w u') : p.IsSubwalk (q.cons h) := by
  obtain ⟨r1, r2, rfl⟩ := hpq
  use r1.cons h, r2
  simp

@[simp]
lemma isSubwalk_cons {u v w} (p : G.Walk u v) (h : G.Adj w u) : p.IsSubwalk (p.cons h) :=
  (isSubwalk_rfl p).cons h

protected lemma IsSubwalk.concat {u v u' v' w} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) (h : G.Adj v' w) : p.IsSubwalk (q.concat h) := by
  obtain ⟨r₁, r₂, rfl⟩ := hpq
  exact ⟨r₁, r₂.concat h, by rw [append_concat]⟩

@[simp]
lemma isSubwalk_concat {u v w} (p : G.Walk u v) (h : G.Adj v w) : p.IsSubwalk (p.concat h) :=
  (isSubwalk_rfl p).concat h

lemma IsSubwalk.trans {u₁ v₁ u₂ v₂ u₃ v₃} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}
    {p₃ : G.Walk u₃ v₃} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₃) :
    p₁.IsSubwalk p₃ := by
  obtain ⟨q₁, r₁, rfl⟩ := h₁
  obtain ⟨q₂, r₂, rfl⟩ := h₂
  use q₂.append q₁, r₁.append r₂
  simp [append_assoc]

lemma isSubwalk_nil_iff {u v u'} (p : G.Walk u v) :
    p.IsSubwalk (nil : G.Walk u' u') ↔ ∃ (hu : u' = u) (hv : u' = v), p = nil.copy hu hv := by
  cases p with
  | nil =>
    constructor
    · rintro ⟨_ | _, _, ⟨⟩⟩
      simp
    · rintro ⟨rfl, _, _⟩
      simp
  | cons h p =>
    constructor
    · rintro ⟨_ | _, _, h⟩ <;> simp at h
    · rintro ⟨rfl, rfl, ⟨⟩⟩

lemma nil_isSubwalk_iff_exists {u' u v} (q : G.Walk u v) :
    (Walk.nil : G.Walk u' u').IsSubwalk q ↔
      ∃ (ru : G.Walk u u') (rv : G.Walk u' v), q = ru.append rv := by
  simp [IsSubwalk]

lemma length_le_of_isSubwalk {u₁ v₁ u₂ v₂} {q : G.Walk u₁ v₁} {p : G.Walk u₂ v₂}
    (h : p.IsSubwalk q) : p.length ≤ q.length := by
  grind [IsSubwalk, length_append]

lemma isSubwalk_of_append_left {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u}
    (h : p₃ = p₁.append p₂) : p₁.IsSubwalk p₃ :=
  ⟨nil, p₂, h⟩

lemma isSubwalk_of_append_right {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u}
    (h : p₃ = p₁.append p₂) : p₂.IsSubwalk p₃ :=
  ⟨p₁, nil, append_nil _ ▸ h⟩

theorem isSubwalk_take {u v : V} (p : G.Walk u v) (n : ℕ) : (p.take n).IsSubwalk p :=
  ⟨nil, p.drop n, by simp⟩

theorem isSubwalk_drop {u v : V} (p : G.Walk u v) (n : ℕ) : (p.drop n).IsSubwalk p :=
  ⟨p.take n, nil, by simp⟩

theorem isSubwalk_iff_support_isInfix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} :
    p₁.IsSubwalk p₂ ↔ p₁.support <:+: p₂.support := by
  refine ⟨fun ⟨ru, rv, h⟩ ↦ ?_, fun ⟨s, t, h⟩ ↦ ?_⟩
  · grind [support_append, support_append_eq_support_dropLast_append]
  · have : (s.length + p₁.length) ≤ p₂.length := by grind [_=_ length_support]
    refine ⟨p₂.take s.length |>.copy rfl ?_, p₂.drop (s.length + p₁.length) |>.copy ?_ rfl, ?_⟩
    · simp [p₂.getVert_eq_support_getElem (by lia : s.length ≤ p₂.length), ← h,
        List.getElem_zero]
    · simp [p₂.getVert_eq_support_getElem (by omega), ← h, ← p₁.getVert_eq_support_getElem le_rfl]
    apply ext_support
    simp only [← h, support_append, support_copy, take_support_eq_support_take_succ,
      List.take_append, drop_support_eq_support_drop_min, List.tail_drop]
    rw [Nat.min_eq_left (by grind), List.drop_append, List.drop_append,
      List.drop_eq_nil_of_le (by lia), List.drop_eq_nil_of_le (by grind),
      p₁.support_eq_cons]
    simp +arith

theorem isSubwalk_iff_darts_isInfix {p₁ : G.Walk u v} {p₂ : G.Walk u' v'} (hnil : ¬p₁.Nil) :
    p₁.IsSubwalk p₂ ↔ p₁.darts <:+: p₂.darts := by
  rw [isSubwalk_iff_support_isInfix, List.infix_iff_getElem?, List.infix_iff_getElem?]
  refine ⟨fun ⟨k, hk, h⟩ ↦ ⟨k, by grind, fun i hi ↦ ?_⟩,
    fun ⟨k, hk, h⟩ ↦ ⟨k, by grind, fun i hi ↦ ?_⟩⟩
  · rw [getElem?_pos _ _ <| by grind, Option.some_inj]
    ext <;> grind [fst_darts_getElem, snd_darts_getElem]
  · rw [getElem?_pos _ _ <| by grind, Option.some_inj]
    by_cases hi' : i = p₁.length
    · have := h <| i - 1
      grind [not_nil_iff_lt_length, snd_darts_getElem]
    have := h i
    grind [fst_darts_getElem]

@[simp]
theorem isSubwalk_nil_iff_mem_support (p : G.Walk u v) :
    (nil : G.Walk v' v').IsSubwalk p ↔ v' ∈ p.support :=
  isSubwalk_iff_support_isInfix.trans <| p.support.singleton_infix_iff _

theorem isSubwalk_toWalk_iff_mem_darts (p : G.Walk u v) (h : G.Adj u' v') :
    h.toWalk.IsSubwalk p ↔ ⟨⟨u', v'⟩, h⟩ ∈ p.darts := by
  simp [isSubwalk_iff_darts_isInfix, List.singleton_infix_iff]

theorem isSubwalk_toWalk_adj_iff_mem_darts {d : G.Dart} (p : G.Walk u v) :
    d.adj.toWalk.IsSubwalk p ↔ d ∈ p.darts :=
  isSubwalk_toWalk_iff_mem_darts ..

theorem isSubwalk_toWalk_iff_mem_edges {p : G.Walk u v} (h : G.Adj u' v') :
    h.toWalk.IsSubwalk p ∨ h.symm.toWalk.IsSubwalk p ↔ s(u', v') ∈ p.edges := by
  rw [isSubwalk_toWalk_iff_mem_darts, isSubwalk_toWalk_iff_mem_darts, edges, List.mem_map]
  refine ⟨fun h ↦ by grind [Dart.edge], fun h ↦ ?_⟩
  have ⟨d, hd, h⟩ := h
  rw [Dart.edge, Sym2.eq, Sym2.rel_iff'] at h
  refine h.elim (fun h ↦ .inl ?_) (fun h ↦ .inr ?_)
    <;> convert hd using 2
    <;> exact h.symm

theorem infix_support_iff_mem_edges {p : G.Walk u v} :
    [u', v'] <:+: p.support ∨ [v', u'] <:+: p.support ↔ s(u', v') ∈ p.edges := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h.elim adj_of_infix_support (adj_of_infix_support · |>.symm)
    simpa [← isSubwalk_toWalk_iff_mem_edges this, isSubwalk_iff_support_isInfix]
  · have := (isSubwalk_toWalk_iff_mem_edges <| p.adj_of_mem_edges h).mpr h
    simpa [isSubwalk_iff_support_isInfix]

lemma isSubwalk_antisymm {u v} {p₁ p₂ : G.Walk u v} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₁) :
    p₁ = p₂ := by
  rw [isSubwalk_iff_support_isInfix] at h₁ h₂
  exact ext_support <| List.infix_antisymm h₁ h₂

@[simp]
theorem IsSubwalk.support_subset {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) : p₂.support ⊆ p₁.support :=
  (isSubwalk_iff_support_isInfix.mp h).subset

theorem IsSubwalk.edges_isInfix {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₁.IsSubwalk p₂) : p₁.edges <:+: p₂.edges := by
  grind [edges_append, IsSubwalk]

@[simp]
theorem IsSubwalk.edges_subset {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) : p₂.edges ⊆ p₁.edges :=
  h.edges_isInfix.subset

theorem IsSubwalk.darts_isInfix {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₁.IsSubwalk p₂) : p₁.darts <:+: p₂.darts := by
  grind [darts_append, IsSubwalk]

@[simp]
theorem IsSubwalk.darts_subset {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) : p₂.darts ⊆ p₁.darts :=
  h.darts_isInfix.subset

protected lemma IsSubwalk.map {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) (f : G →g G') : (p₂.map f).IsSubwalk (p₁.map f) := by
  simp [isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp h, List.IsInfix.map]

protected lemma IsSubwalk.dropLast {u v u' v'} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) : p.dropLast.IsSubwalk q :=
  (isSubwalk_take _ _).trans hpq

protected lemma IsSubwalk.tail {u v u' v'} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) : p.tail.IsSubwalk q :=
  (isSubwalk_drop _ _).trans hpq

end Walk

end SimpleGraph
