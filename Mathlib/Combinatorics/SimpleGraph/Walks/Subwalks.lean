/-
Copyright (c) 2025 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walks.Operations

/-!
# Subwalks

We define a relation on walks stating that one walk is the subwalk of another.

## Main definitions

* `SimpleGraph.Walk.IsSubwalk`:
  A relation on walks stating that the first walk is a contiguous subwalk of the second walk

## Tags
walks
-/

@[expose] public section

namespace SimpleGraph

namespace Walk

variable {V : Type*} {G : SimpleGraph V}

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

lemma IsSubwalk.trans {u₁ v₁ u₂ v₂ u₃ v₃} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}
    {p₃ : G.Walk u₃ v₃} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₃) :
    p₁.IsSubwalk p₃ := by
  obtain ⟨q₁, r₁, rfl⟩ := h₁
  obtain ⟨q₂, r₂, rfl⟩ := h₂
  use q₂.append q₁, r₁.append r₂
  simp only [append_assoc]

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

theorem isSubwalk_iff_support_isInfix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} :
    p₁.IsSubwalk p₂ ↔ p₁.support <:+: p₂.support := by
  refine ⟨fun ⟨ru, rv, h⟩ ↦ ?_, fun ⟨s, t, h⟩ ↦ ?_⟩
  · grind [support_append, support_append_eq_support_dropLast_append]
  · have : (s.length + p₁.length) ≤ p₂.length := by grind [_=_ length_support]
    refine ⟨p₂.take s.length |>.copy rfl ?_, p₂.drop (s.length + p₁.length) |>.copy ?_ rfl, ?_⟩
    · simp [p₂.getVert_eq_support_getElem (by cutsat : s.length ≤ p₂.length), ← h,
        List.getElem_zero]
    · simp [p₂.getVert_eq_support_getElem (by omega), ← h, ← p₁.getVert_eq_support_getElem le_rfl]
    apply ext_support
    simp only [← h, support_append, support_copy, take_support_eq_support_take_succ,
      List.take_append, drop_support_eq_support_drop_min, List.tail_drop]
    rw [Nat.min_eq_left (by grind [length_support]), List.drop_append, List.drop_append,
      List.drop_eq_nil_of_le (by cutsat), List.drop_eq_nil_of_le (by grind [length_support]),
      p₁.support_eq_cons]
    simp +arith

lemma isSubwalk_antisymm {u v} {p₁ p₂ : G.Walk u v} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₁) :
    p₁ = p₂ := by
  rw [isSubwalk_iff_support_isInfix] at h₁ h₂
  exact ext_support <| List.infix_antisymm h₁ h₂

end Walk

end SimpleGraph
