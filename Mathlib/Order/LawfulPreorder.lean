/-
Copyright (c) 2017 Pierre Quinton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Quinton
-/
import Mathlib.Order.SetNotation
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Defs.PartialOrder

/-!
# Lawful Suprema and Infima

This file introduces type classes that enforce correctness properties for suprema and infima
operations on preorders, ensuring they return actual least upper bounds and greatest lower bounds
whenever they exist.

## Main declarations

- `LawfulSupPreorder`: Typeclass ensuring that whenever a set `s` has a least upper bound, `sSup s`
  returns a least upper bound.
- `LawfulInfPreorder`: Typeclass ensuring that whenever a set `s` has a greatest lower bound,
  `sInf s` returns a greatest lower bound.
- `LawfulPreorder`: Typeclass combining both lawful suprema and infima properties.

## Main statements

- `Preorder.toLawfulSupPreorder`: Any preorder can be made into a lawful sup preorder by defining
  `sSup s` to be any LUB of `s` when one exists.
- `Preorder.toLawfulInfPreorder`: Any preorder can be made into a lawful inf preorder by defining
  `sInf s` to be any GLB of `s` when one exists.
- `Preorder.toLawfulPreorder`: Any preorder can therefore be made into a lawful preorder.
-/

variable {α : Type*}

/--
A preorder with lawful suprema: whenever a set has a least upper bound, `sSup` returns a least upper
bound for that set.

This ensures that the supremum operation `sSup` behaves correctly by returning actual least upper
bounds rather than arbitrary elements when a least upper bound exists.
-/
class LawfulSupPreorder (α) extends Preorder α, SupSet α where
  isLUB_sSup_of_exists_isLUB (s : Set α) : (∃ x, IsLUB s x) → IsLUB s (sSup s)

/-- Defines `sSup` so as to return an arbitrary LUB when it exists, and a default element otherwise. -/
open Classical in
noncomputable def Preorder.toLawfulSupPreorder [Preorder α] [Inhabited α] :
    LawfulSupPreorder α where
  sSup s := if hs : ∃ x, IsLUB s x then Classical.choose hs else default
  isLUB_sSup_of_exists_isLUB s := by
    intro ⟨x, hs⟩
    rw [dif_pos]
    exact Classical.choose_spec ⟨x, hs⟩

/--
A preorder with lawful infima: whenever a set has a greatest lower bound, `sInf` returns a greastest
lower bound for that set.

This ensures that the infimum operation `sInf` behaves correctly by returning actual greatest lower
bounds rather than arbitrary elements when a greatest lower bounds exists.
-/
class LawfulInfPreorder (α) extends Preorder α, InfSet α where
  isGLB_sInf_of_exists_isGLB (s : Set α) : (∃ x, IsGLB s x) → IsGLB s (sInf s)

open Classical in
noncomputable instance Preorder.toLawfulInfPreorder [Preorder α] [Inhabited α] :
    LawfulInfPreorder α where
  sInf s := if hs : ∃ x, IsGLB s x then Classical.choose hs else default
  isGLB_sInf_of_exists_isGLB s := by
    intro ⟨x, hs⟩
    rw [dif_pos]
    exact Classical.choose_spec ⟨x, hs⟩

/--
A preorder with both lawful suprema and lawful infima.
-/
class LawfulPreorder (α) extends LawfulSupPreorder α, LawfulInfPreorder α

open Classical in
noncomputable instance Preorder.toLawfulPreorder [Preorder α] [Inhabited α] :
    LawfulPreorder α where
