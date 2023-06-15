/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module examples.prop_encodable
! leanprover-community/mathlib commit 328375597f2c0dd00522d9c2e5a33b6a6128feeb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.W.Basic

/-!
# W types

The file `data/W.lean` shows that if `α` is an an encodable fintype and for every `a : α`,
`β a` is encodable, then `W β` is encodable.

As an example of how this can be used, we show that the type of propositional formulas with
variables labeled from an encodable type is encodable.

The strategy is to define a type of labels corresponding to the constructors.
From the definition (using `sum`, `unit`, and an encodable type), Lean can infer
that it is encodable. We then define a map from propositional formulas to the
corresponding `Wfin` type, and show that map has a left inverse.

We mark the auxiliary constructions `private`, since their only purpose is to
show encodability.
-/


namespace PropEncodable

/-- Propositional formulas with labels from `α`. -/
inductive PropForm (α : Type _)
  | var : α → prop_form
  | Not : prop_form → prop_form
  | And : prop_form → prop_form → prop_form
  | Or : prop_form → prop_form → prop_form
#align prop_encodable.prop_form PropEncodable.PropForm

/-!
The next three functions make it easier to construct functions from a small
`fin`.
-/


section

variable {α : Type _}

/-- the trivial function out of `fin 0`. -/
def mkFn0 : Fin 0 → α
  | ⟨_, h⟩ => absurd h (by decide)
#align prop_encodable.mk_fn0 PropEncodable.mkFn0

/-- defines a function out of `fin 1` -/
def mkFn1 (t : α) : Fin 1 → α
  | ⟨0, _⟩ => t
  | ⟨n + 1, h⟩ => absurd h (by decide)
#align prop_encodable.mk_fn1 PropEncodable.mkFn1

/-- defines a function out of `fin 2` -/
def mkFn2 (s t : α) : Fin 2 → α
  | ⟨0, _⟩ => s
  | ⟨1, _⟩ => t
  | ⟨n + 2, h⟩ => absurd h (by decide)
#align prop_encodable.mk_fn2 PropEncodable.mkFn2

attribute [simp] mk_fn0 mk_fn1 mk_fn2

end

namespace PropForm

private def constructors (α : Type _) :=
  Sum α (Sum Unit (Sum Unit Unit))

local notation "cvar " a => Sum.inl a

local notation "cnot" => Sum.inr (Sum.inl Unit.unit)

local notation "cand" => Sum.inr (Sum.inr (Sum.inr Unit.unit))

local notation "cor" => Sum.inr (Sum.inr (Sum.inl Unit.unit))

@[simp]
private def arity (α : Type _) : Constructors α → Nat
  | cvar a => 0
  | cnot => 1
  | cand => 2
  | cor => 2

variable {α : Type _}

private def f : PropForm α → WType fun i => Fin (arity α i)
  | var a => ⟨cvar a, mkFn0⟩
  | Not p => ⟨cnot, mkFn1 (f p)⟩
  | And p q => ⟨cand, mkFn2 (f p) (f q)⟩
  | Or p q => ⟨cor, mkFn2 (f p) (f q)⟩

private def finv : (WType fun i => Fin (arity α i)) → PropForm α
  | ⟨cvar a, fn⟩ => var a
  | ⟨cnot, fn⟩ => not (finv (fn ⟨0, by decide⟩))
  | ⟨cand, fn⟩ => and (finv (fn ⟨0, by decide⟩)) (finv (fn ⟨1, by decide⟩))
  | ⟨cor, fn⟩ => or (finv (fn ⟨0, by decide⟩)) (finv (fn ⟨1, by decide⟩))

instance [Encodable α] : Encodable (PropForm α) :=
  haveI : Encodable (constructors α) := by unfold constructors; infer_instance
  Encodable.ofLeftInverse f finv (by intro p; induction p <;> simp [f, finv, *])

end PropForm

end PropEncodable

