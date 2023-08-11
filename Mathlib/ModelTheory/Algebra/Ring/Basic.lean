/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

namespace FirstOrder

namespace Language

inductive RingFunc : ℕ → Type
  | add : RingFunc 2
  | mul : RingFunc 2
  | neg : RingFunc 1
  | zero : RingFunc 0
  | one : RingFunc 0

def ring : Language :=
  { Functions := RingFunc
    Relations := fun _ => Empty }

namespace ring

open RingFunc

abbrev zeroFunc : Language.ring.Functions 0 := zero

abbrev oneFunc : Language.ring.Functions 0 := one

abbrev addFunc : Language.ring.Functions 2 := add

abbrev mulFunc : Language.ring.Functions 2 := mul

abbrev negFunc : Language.ring.Functions 1 := neg

instance (α : Type*) : Zero (Language.ring.Term α) :=
{ zero := Constants.term zeroFunc }

theorem zero_def (α : Type*) : (0 : Language.ring.Term α) = Constants.term zeroFunc := rfl

instance (α : Type*) : One (Language.ring.Term α) :=
{ one := Constants.term oneFunc }

theorem one_def (α : Type*) : (1 : Language.ring.Term α) = Constants.term oneFunc := rfl

instance (α : Type*) : Add (Language.ring.Term α) :=
{ add := addFunc.apply₂ }

theorem add_def (α : Type*) (t₁ t₂ : Language.ring.Term α) :
    t₁ + t₂ = addFunc.apply₂ t₁ t₂ := rfl

instance (α : Type*) : Mul (Language.ring.Term α) :=
{ mul := mulFunc.apply₂ }

theorem mul_def (α : Type*) (t₁ t₂ : Language.ring.Term α) :
    t₁ * t₂ = mulFunc.apply₂ t₁ t₂ := rfl

instance (α : Type*) : Neg (Language.ring.Term α) :=
{ neg := negFunc.apply₁ }

theorem neg_def (α : Type*) (t : Language.ring.Term α) :
    -t = negFunc.apply₁ t := rfl

end ring

end Language

end FirstOrder
