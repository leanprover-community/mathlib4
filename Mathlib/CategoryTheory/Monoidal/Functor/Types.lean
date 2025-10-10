/-
Copyright (c) 2025 Vilim Lendvaj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vilim Lendvaj
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Tactic.Simps.Basic

/-!

# Convert from `Applicative` to `CategoryTheory.Functor.LaxMonoidal`

This allows us to use Lean's `Type`-based applicative functors in category theory.

-/

namespace CategoryTheory

section

universe u v

variable (F : Type u → Type v) [Applicative F] [LawfulApplicative F]

/-- A lawful `Applicative` gives a category theory `LaxMonoidal` functor
between categories of types. -/
@[simps!]
instance : (ofTypeFunctor F).LaxMonoidal where
  ε := by
    intro
    simp only [ofTypeFunctor_obj]
    apply pure PUnit.unit
  μ := by
    intro _ _ ⟨x, y⟩
    simp only [ofTypeFunctor_obj]
    exact Prod.mk <$> x <*> y
  μ_natural_left := by
    repeat intro
    funext x
    cases x
    simp [map_seq]
    rfl
  μ_natural_right := by
    repeat intro
    funext x
    cases x
    simp [map_seq, seq_map_assoc]
    rfl
  associativity := by
    repeat intro
    funext x
    rcases x with ⟨⟨_, _⟩, _⟩
    simp [map_seq, seq_map_assoc, LawfulApplicative.seq_assoc]
    rfl
  left_unitality := by
    repeat intro
    funext x
    cases x
    simp [LawfulApplicative.pure_seq]
  right_unitality := by
    repeat intro
    funext x
    cases x
    simp

end

end CategoryTheory
