/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.W.Basic
import Mathlib.Data.Fin.VecNotation

#align_import examples.prop_encodable from "leanprover-community/mathlib"@"328375597f2c0dd00522d9c2e5a33b6a6128feeb"

/-!
# W types

The file `Mathlib/Data/W/Basic.lean` shows that if `α` is an encodable fintype and for every
`a : α`, `β a` is encodable, then `W β` is encodable.

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
inductive PropForm (α : Type*)
  | var : α → PropForm α
  | not : PropForm α → PropForm α
  | and : PropForm α → PropForm α → PropForm α
  | or : PropForm α → PropForm α → PropForm α
#align prop_encodable.prop_form PropEncodable.PropForm

/-!
The next three functions make it easier to construct functions from a small
`Fin`.
-/

-- Porting note: using `![_, _]` notation instead
#noalign prop_encodable.mk_fn0
#noalign prop_encodable.mk_fn1
#noalign prop_encodable.mk_fn2

namespace PropForm

private def Constructors (α : Type*) :=
  α ⊕ (Unit ⊕ (Unit ⊕ Unit))

local notation "cvar " a => Sum.inl a

local notation "cnot" => Sum.inr (Sum.inl Unit.unit)

local notation "cand" => Sum.inr (Sum.inr (Sum.inr Unit.unit))

local notation "cor" => Sum.inr (Sum.inr (Sum.inl Unit.unit))

@[simp]
private def arity (α : Type*) : Constructors α → Nat
  | cvar _ => 0
  | cnot => 1
  | cand => 2
  | cor => 2

variable {α : Type*}

instance : ∀ c : Unit ⊕ (Unit ⊕ Unit), NeZero (arity α (.inr c))
  | .inl () => ⟨one_ne_zero⟩
  | .inr (.inl ()) => ⟨two_ne_zero⟩
  | .inr (.inr ()) => ⟨two_ne_zero⟩

private def f : PropForm α → WType fun i => Fin (arity α i)
  | var a => ⟨cvar a, ![]⟩
  | not p => ⟨cnot, ![f p]⟩
  | and p q => ⟨cand, ![f p, f q]⟩
  | or p q => ⟨cor, ![f p, f q]⟩

private def finv : (WType fun i => Fin (arity α i)) → PropForm α
  | ⟨cvar a, _⟩ => var a
  | ⟨cnot, fn⟩ => not (finv (fn 0))
  | ⟨cand, fn⟩ => and (finv (fn 0)) (finv (fn 1))
  | ⟨cor, fn⟩ => or (finv (fn 0)) (finv (fn 1))

instance [Encodable α] : Encodable (PropForm α) :=
  haveI : Encodable (Constructors α) := by unfold Constructors; infer_instance
  Encodable.ofLeftInverse f finv (by intro p; induction p <;> simp [f, finv, *])

end PropForm

end PropEncodable
