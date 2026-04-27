/-
Copyright (c) 2024 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Tactic.Translate.ToAdditive

/-!
## `@[to_additive]` attributes for basic types
-/

public meta section

set_option linter.privateModule false

attribute [to_additive_do_translate] Empty PEmpty Unit PUnit
attribute [to_additive_ignore_args 2] Subtype

attribute [to_additive] One
attribute [to_additive existing Zero.toOfNat0] One.toOfNat1
attribute [to_additive existing Zero.ofOfNat0] One.ofOfNat1

attribute [to_additive existing] Inv Mul HMul instHMul Div HDiv instHDiv

attribute [to_additive (reorder := α β) SMul] Pow
attribute [to_additive existing (reorder := α β, 4 5) smul] Pow.pow
attribute [to_additive existing (reorder := α β, pow (1 2))] Pow.mk
attribute [to_additive (reorder := α β)] HPow
attribute [to_additive existing (reorder := α β, 5 6)] HPow.hPow
attribute [to_additive existing (reorder := α β, hPow (1 2))] HPow.mk
attribute [to_additive existing] instHPow
