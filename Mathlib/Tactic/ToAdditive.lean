/-
Copyright (c) 2024 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public meta import Mathlib.Tactic.Translate.ToAdditive

/-!
## `@[to_additive]` attributes for basic types
-/

public meta section

attribute [to_additive self] Empty PEmpty Unit PUnit

attribute [translate_change_numeral 2] OfNat OfNat.ofNat

attribute [to_additive] One
attribute [to_additive existing Zero.toOfNat0] One.toOfNat1
attribute [to_additive existing Zero.ofOfNat0] One.ofOfNat1
