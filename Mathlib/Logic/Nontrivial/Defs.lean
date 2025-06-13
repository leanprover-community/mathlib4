/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.TypeStar

/-!
# Nontrivial types

A type is *nontrivial* if it contains at least two elements. This is useful in particular for rings
(where it is equivalent to the fact that zero is different from one) and for vector spaces
(where it is equivalent to the fact that the dimension is positive).

We introduce a typeclass `Nontrivial` formalizing this property.

Basic results about nontrivial types are in `Mathlib/Logic/Nontrivial/Basic.lean`.
-/

variable {α : Type*} {β : Type*}

/-- Predicate typeclass for expressing that a type is not reduced to a single element. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. -/
class Nontrivial (α : Type*) : Prop where
  /-- In a nontrivial type, there exists a pair of distinct terms. -/
  exists_pair_ne : ∃ x y : α, x ≠ y

theorem nontrivial_iff : Nontrivial α ↔ ∃ x y : α, x ≠ y :=
  ⟨fun h ↦ h.exists_pair_ne, fun h ↦ ⟨h⟩⟩

theorem exists_pair_ne (α : Type*) [Nontrivial α] : ∃ x y : α, x ≠ y :=
  Nontrivial.exists_pair_ne

-- See Note [decidable namespace]
protected theorem Decidable.exists_ne [Nontrivial α] [DecidableEq α] (x : α) : ∃ y, y ≠ x := by
  rcases exists_pair_ne α with ⟨y, y', h⟩
  by_cases hx : x = y
  · rw [← hx] at h
    exact ⟨y', h.symm⟩
  · exact ⟨y, Ne.symm hx⟩

open Classical in
theorem exists_ne [Nontrivial α] (x : α) : ∃ y, y ≠ x := Decidable.exists_ne x

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.
theorem nontrivial_of_ne (x y : α) (h : x ≠ y) : Nontrivial α :=
  ⟨⟨x, y, h⟩⟩

theorem nontrivial_iff_exists_ne (x : α) : Nontrivial α ↔ ∃ y, y ≠ x :=
  ⟨fun h ↦ @exists_ne α h x, fun ⟨_, hy⟩ ↦ nontrivial_of_ne _ _ hy⟩

instance : Nontrivial Prop :=
  ⟨⟨True, False, true_ne_false⟩⟩

/-- See Note [lower instance priority]

Note that since this and `instNonemptyOfInhabited` are the most "obvious" way to find a nonempty
instance if no direct instance can be found, we give this a higher priority than the usual `100`.
-/
instance (priority := 500) Nontrivial.to_nonempty [Nontrivial α] : Nonempty α :=
  let ⟨x, _⟩ := _root_.exists_pair_ne α
  ⟨x⟩

theorem subsingleton_iff : Subsingleton α ↔ ∀ x y : α, x = y :=
  ⟨by
    intro h
    exact Subsingleton.elim, fun h ↦ ⟨h⟩⟩

theorem not_nontrivial_iff_subsingleton : ¬Nontrivial α ↔ Subsingleton α := by
  simp only [nontrivial_iff, subsingleton_iff, not_exists, Classical.not_not]

theorem not_nontrivial (α) [Subsingleton α] : ¬Nontrivial α :=
  fun ⟨⟨x, y, h⟩⟩ ↦ h <| Subsingleton.elim x y

theorem not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α :=
  fun _ => not_nontrivial _ ‹_›

lemma not_subsingleton_iff_nontrivial : ¬ Subsingleton α ↔ Nontrivial α := by
  rw [← not_nontrivial_iff_subsingleton, Classical.not_not]

/-- A type is either a subsingleton or nontrivial. -/
theorem subsingleton_or_nontrivial (α : Type*) : Subsingleton α ∨ Nontrivial α := by
  rw [← not_nontrivial_iff_subsingleton, or_comm]
  exact Classical.em _

theorem false_of_nontrivial_of_subsingleton (α : Type*) [Nontrivial α] [Subsingleton α] : False :=
  not_nontrivial _ ‹_›

/-- Pullback a `Nontrivial` instance along a surjective function. -/
protected theorem Function.Surjective.nontrivial [Nontrivial β] {f : α → β}
    (hf : Function.Surjective f) : Nontrivial α := by
  rcases exists_pair_ne β with ⟨x, y, h⟩
  rcases hf x with ⟨x', hx'⟩
  rcases hf y with ⟨y', hy'⟩
  have : x' ≠ y' := by
    refine fun H ↦ h ?_
    rw [← hx', ← hy', H]
  exact ⟨⟨x', y', this⟩⟩

namespace Bool

instance : Nontrivial Bool :=
  ⟨⟨true, false, nofun⟩⟩

end Bool
