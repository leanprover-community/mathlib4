/-
Copyright (c) 2024 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Mathlib.Tactic.ToAdditive.Frontend

/-!
## `@[to_additive]` attributes for basic types
-/

attribute [to_additive Empty] Empty
attribute [to_additive PEmpty] PEmpty
attribute [to_additive PUnit] PUnit
attribute [to_additive existing Unit] Unit

attribute [to_additive_change_numeral 2] OfNat OfNat.ofNat

attribute [to_additive] One
attribute [to_additive existing Zero.toOfNat0] One.toOfNat1
attribute [to_additive existing Zero.ofOfNat0] One.ofOfNat1
