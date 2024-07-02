/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Mathport.Notation
import Mathlib.Lean.Expr.ExtraRecognizers

/-!
# Set Notation

This file defines two pieces of scoped notation related to sets and subtypes.

The first is a coercion; for each `α : Type*` and `s : Set α`, `(↑) : Set s → Set α`
is the function coercing `t : Set s` into a set in the ambient type; i.e. `↑t = Subtype.val '' t`.

The second, for `s t : Set α`, is the notation `s ↓∩ t`, which denotes the intersection
of `s` and `t` as a set in `Set s`.

These notations are developed further in `Data.Set.Functor` and `Data.Set.Subset` respectively.
They are defined here separately so that this file can be added as an exception to the shake linter
and can thus be imported without a linting false positive when only the notation is desired.
-/

namespace Set.Notation
/--
Given two sets `A` and `B`, `A ↓∩ B` denotes the intersection of `A` and `B` as a set in `Set A`.

The notation is short for `((↑) ⁻¹' B : Set A)`, while giving hints to the elaborator
that both `A` and `B` are terms of `Set α` for the same `α`.
This set is the same as `{x : ↑A | ↑x ∈ B}`.
-/
scoped notation3 A:67 " ↓∩ " B:67 => (Subtype.val ⁻¹' (B : type_of% A) : Set (A : Set _))

/-- Coercion using `(Subtype.val '' ·)` -/
instance {α : Type*} {s : Set α} : CoeHead (Set s) (Set α) := ⟨fun t => (Subtype.val '' t)⟩

open Lean PrettyPrinter Delaborator SubExpr in
/--
If the `Set.Notation` namespace is open, sets of a subtype coerced to the ambient type are
represented with `↑`.
-/
@[scoped delab app.Set.image]
def delab_set_image_subtype : Delab := whenPPOption getPPCoercions do
  let #[α, _, f, _] := (← getExpr).getAppArgs | failure
  guard <| f.isAppOfArity ``Subtype.val 2
  let some _ := α.coeTypeSet? | failure
  let e ← withAppArg delab
  `(↑$e)

end Set.Notation
