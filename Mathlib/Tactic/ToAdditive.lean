/-
Copyright (c) 2024 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Mathlib.Tactic.ToAdditive.Frontend

/-!
## `@[to_additive]` attributes for basic types
-/

attribute [to_additive self] Empty PEmpty Unit PUnit
-- the heuristic that checks if instances have changed or not does the wrong thing when it sees
-- a function whose output type is polymorphic. So, for now we need to tag them here to fix it.
attribute [to_additive self] inferInstance inferInstanceAs Subtype.val PSigma.fst id

attribute [to_additive_change_numeral 2] OfNat OfNat.ofNat
attribute [to_additive_instance_arg 3] OfNat.ofNat

attribute [to_additive] One
attribute [to_additive existing Zero.toOfNat0] One.toOfNat1
attribute [to_additive existing Zero.ofOfNat0] One.ofOfNat1
