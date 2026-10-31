/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Yury Kudryashov, Oliver Nash
-/
module

public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Collapsing a subset to a point.

Given a subset `A ⊆ X`, a common operation is to collapse `A` to a point. This file contains basic
API to support this operation.

-/

variable {α : Type*}

namespace Setoid

open Relation

/-- Given a family of subsets, this is the setoid that collapses each member of the family to a
point. -/
public def fromSets (S : Set (Set α)) : Setoid α where
  r := ReflTransGen fun a b ↦ ∃ s ∈ S, a ∈ s ∧ b ∈ s
  iseqv :=
    { refl _ := ReflTransGen.refl
      trans := ReflTransGen.trans
      symm h := by
        have : Std.Symm fun a b ↦ ∃ s ∈ S, a ∈ s ∧ b ∈ s := ⟨by tauto⟩
        exact ReflTransGen.stdSymm.symm _ _ h }

public theorem fromSets_r_iff (S : Set (Set α)) (h : S.PairwiseDisjoint id) (a b : α) :
    (Setoid.fromSets S).r a b ↔ a = b ∨ ∃ s ∈ S, a ∈ s ∧ b ∈ s := by
  constructor
  · intro hr
    induction hr with
    | refl => exact .inl rfl
    | tail _ hs ih =>
      rcases ih with rfl | ht
      · exact .inr hs
      · right
        obtain ⟨s, hs, hbs, hcs⟩ := hs
        obtain ⟨t, ht, hat, hbt⟩ := ht
        have : s = t := h.elim_set hs ht _ hbs hbt
        exact ⟨s, hs, this ▸ hat, hcs⟩
  · rintro (rfl | hr)
    · exact .refl
    · exact .single hr

end Setoid

namespace Set

/-- Given a subset, this is the setoid that collapses it to a point.

In the case that the set is empty, it produces the minimal (equality) setoid. -/
public def toSetoid (s : Set α) : Setoid α := Setoid.fromSets {s}

@[simp] public lemma toSetoid_r_iff {s : Set α} {a b : α} :
    s.toSetoid.r a b ↔ a = b ∨ (a ∈ s ∧ b ∈ s) := by
  rw [Set.toSetoid]
  simp [Setoid.fromSets_r_iff]

variable {β : Type*}

/-- A function is constant on a subset if any two inputs give the same result. -/
public def IsConstOn (f : α → β) (s : Set α) : Prop :=
  ∀ᵉ (a ∈ s) (b ∈ s), f a = f b

@[simp] public lemma isConstOn_iff {f : α → β} {s : Set α} :
    s.IsConstOn f ↔ ∀ᵉ (a ∈ s) (b ∈ s), f a = f b :=
  Iff.rfl

namespace IsConstOn

public protected lemma empty {f : α → β} : IsConstOn f ∅ := by simp

/-- Functions which are constant on a subset are the same as functions from the quotient in which
the set is collapsed to a point. -/
public protected def equiv (s : Set α) :
    {f : α → β // s.IsConstOn f} ≃ (Quotient s.toSetoid → β) where
  toFun f q := Quotient.recOn q f <| fun a b hab ↦ by
    have : a = b ∨ a ∈ s ∧ b ∈ s := by simpa using hab
    aesop
  invFun f := ⟨f ∘ .mk _, by
    intro a ha b hb
    have : Quotient.mk (s.toSetoid) a = Quotient.mk (s.toSetoid) b := by
      apply Quotient.sound
      aesop
    aesop⟩
  left_inv f := by ext; simp
  right_inv f := by
    ext q
    induction q using Quotient.ind
    rfl

public lemma iff_exists_eqOn_const_or {f : α → β} {s : Set α} :
    s.IsConstOn f ↔ (∃ a, s.EqOn f (Function.const α a)) ∨ s = ∅ := by
  rcases s.eq_empty_or_nonempty with rfl | hs; · simp
  have := Set.nonempty_iff_ne_empty.mp hs
  have := hs.some_mem
  aesop (add simp Set.EqOn)

end IsConstOn

end Set
