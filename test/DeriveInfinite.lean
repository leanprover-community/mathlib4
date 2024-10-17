/-
Copyright (c) 2023 Tiancheng "Timothy" Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Gu
-/
import Mathlib.Tactic.DeriveInfinite

namespace tests

-- for debugging, uncomment this:
-- set_option trace.Elab.Deriving.infinite true

-- We assume Nat is Infinite in a few places.
example : Infinite Nat := inferInstance

section existing_infinite

structure S where
  a : Nat
  b : Unit
  deriving Infinite

inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'
  deriving Inhabited, Infinite

inductive Simple
  | mk₁ : Simple
  | mk₂ : Unit → Unit → Nat → Simple
  deriving Infinite

inductive Param (α : Type _) : Type _
  | mk₁ : α → Param α
  | mk₂ : Nat → Param α
  deriving Infinite

example : Infinite (Param Empty) := inferInstance

inductive ParamOnly (α : Type _) : Type _
  | mk : α → ParamOnly α
  -- deriving Infinite -- doesn't work w/o additional hypotheses

example [Infinite α] : Infinite (ParamOnly α) := derive_infinite% _
example [Infinite α] (h : Finite (ParamOnly α)) : False :=
  let inf := derive_infinite% (ParamOnly α)
  absurd h inf.not_finite
example [Infinite α] (h : Finite (ParamOnly α)) : False :=
  Infinite.not_finite (self := derive_infinite% _) h

inductive ParamWithInfinite (α : Type _) [Infinite α] : Type _
  | mk : α → ParamWithInfinite α
  deriving Infinite

inductive ParamOnly₂ (α β : Type _) : Type _
  | mk : α → β → ParamOnly₂ α β
  -- deriving Infinite -- doesn't work w/o additional hypotheses

example [Infinite α] [Nonempty β] : Infinite (ParamOnly₂ α β) := derive_infinite% _
example [Nonempty α] [Infinite β] : Infinite (ParamOnly₂ α β) := derive_infinite% _
example [Infinite α] [Infinite β] : Infinite (ParamOnly₂ α β) := derive_infinite% _

inductive ParamAndNat (α : Type _) : Type _
  | mk : α → Nat → ParamAndNat α
  -- deriving Infinite -- doesn't work w/o additional hypotheses

example [Nonempty α] : Infinite (ParamAndNat α) := derive_infinite% _

inductive ParamAndNatWithNonempty (α : Type _) [Nonempty α] : Type _
  | mk : α → Nat → ParamAndNatWithNonempty α
  deriving Infinite

example : Infinite (ParamAndNatWithNonempty Unit) := inferInstance

inductive SelfAndNat (α : Type _) : Type _
  | mk₀ : SelfAndNat α
  | mk₁ : SelfAndNat α → {_ : Nat} → SelfAndNat α
  deriving Nonempty, Infinite

example : Infinite (SelfAndNat Empty) := inferInstance

def T (_ : Nat) : Type := Nat
instance : Infinite (T n) := inferInstanceAs (Infinite Nat)

inductive Dependent (α : Type _) : Type _
  | mk₁ : ∀ {n : Nat}, List (T n) → Dependent α
  deriving Nonempty, Infinite

example : Infinite (Dependent Empty) := inferInstance

local instance : Nonempty (a = a) := ⟨rfl⟩
structure HasProof where
  n : Nat
  h : 0 = 0
  deriving Infinite

attribute [-instance] instInfiniteOption in
example [Infinite α] : Infinite (Option α) := derive_infinite% _

end existing_infinite

section recursive

inductive Self : Type u
  | mk₀ : Self
  | mk₁ : Self → Self
  deriving Inhabited, Infinite

example : Infinite Self := inferInstance

inductive SelfIrreducible : Type u
  | mk₀ : SelfIrreducible
  | mk₁ : SelfIrreducible → SelfIrreducible

@[irreducible] instance : Inhabited SelfIrreducible := ⟨.mk₀⟩
-- deriving instance Infinite for SelfIrreducible -- doesn't work

inductive SelfWithComplexDefault : Type u
  | mk₀ : SelfWithComplexDefault
  | mk₁ : SelfWithComplexDefault → SelfWithComplexDefault

instance : Inhabited SelfWithComplexDefault := ⟨.mk₁ .mk₀⟩
-- deriving instance Infinite for SelfWithComplexDefault -- doesn't work

inductive SelfComplicated : Type u
  | mk₀ : Empty → SelfComplicated
  | mk₁ : SelfComplicated → Unit → SelfComplicated
  | mk₂ : PUnit.{u} → SelfComplicated
  deriving Inhabited, Infinite

example : Infinite SelfComplicated := inferInstance

inductive List' (α : Type u) where
  | nil : List' α
  | cons (head : α) (tail : List' α) : List' α
  deriving Inhabited

instance [Nonempty α] : Infinite (List' α) := derive_infinite% _

inductive Indexed : Nat → Type u
  | mk₀ : Indexed n → Indexed (n + 1)
  | mk₁ : Indexed 2 → Indexed 2
  | mk₂ : Indexed n
  | mk₃ : Nat → Indexed 0
  -- deriving Inhabited -- doesn't work
  -- deriving Infinite  -- doesn't work either

example : Infinite (Indexed 0) := derive_infinite% _
example : Infinite (Indexed 1) :=
  let _ : Infinite (Indexed 0) := derive_infinite% _
  derive_infinite% _
example : Infinite (Indexed 2) :=
  let _ : Inhabited (Indexed 2) := ⟨.mk₂⟩
  derive_infinite% _

inductive Vector' (α : Type u) : Nat → Type u where
  | nil : Vector' α 0
  | cons (head : α) (tail : Vector' α n) : Vector' α (n + 1)
instance Vector'.instInhabited [Inhabited α] : ∀ n, Inhabited (Vector' α n)
  | 0 => ⟨.nil⟩
  | n + 1 => ⟨.cons default (Vector'.instInhabited n).1⟩
instance [Inhabited α] [Infinite α] : Infinite (Vector' α (n + 1)) := derive_infinite% _

end recursive

end tests
