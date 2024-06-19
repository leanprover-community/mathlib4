/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
import Mathlib.Tactic.ToAdditive
import Mathlib.Mathport.Rename

/-! ## Classes for `Zero` and `One` -/

set_option autoImplicit true

class Zero.{u} (α : Type u) where
  zero : α
#align has_zero Zero

instance (priority := 300) Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

instance (priority := 200) Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where
  zero := 0


@[to_additive]
class One (α : Type u) where
  one : α
#align has_one One

@[to_additive existing Zero.toOfNat0]
instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1
@[to_additive existing Zero.ofOfNat0, to_additive_change_numeral 2]
instance (priority := 200) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

@[deprecated, match_pattern] def bit0 {α : Type u} [Add α] (a : α) : α := a + a

set_option linter.deprecated false in
@[deprecated, match_pattern] def bit1 {α : Type u} [One α] [Add α] (a : α) : α := bit0 a + 1

attribute [to_additive_change_numeral 2] OfNat OfNat.ofNat

/- These attributes need to be in a low-level file where `@[to_additive]` exists. -/
attribute [to_additive Empty] Empty
attribute [to_additive PEmpty] PEmpty
attribute [to_additive PUnit] PUnit
attribute [to_additive existing Unit] Unit
