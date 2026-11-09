/-
Copyright (c) 2026 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

import Mathlib.Init

/-!
# `bdsimp` tactic

`bdsimp` is a backward compatibility macro for `dsimp` that allows dependent rewrites inside
depended-on positions.
-/

public meta section

open Lean.Parser.Tactic

/-- `bdsimp` definitionally simplifies the goal. This is a backward compatibility macro for `dsimp`.
Like `dsimp`, it applies only theorems that hold by reflexivity, and the result is guaranteed to be
definitionally equal to the input. The difference is that `bdsimp` allows any theorem whose proof is
reflexivity, while `dsimp` requires the proof to hold at `.instances` transparency level.

This tactic is a temporary workaround.
`bdsimp` also rewrites in depended-on positions, which means the result can fail to typecheck at
the expected `.instances` transparency level. For example:
```lean
@[expose] def two := 2
@[defeq] lemma two_eq : two = 2 := by rfl
instance : NeZero two := inferInstanceAs (NeZero 2)

example (x : Fin two) : x * 0 = 0 := by
  bdsimp only [two_eq]
  fail_if_success rw [Fin.mul_zero] -- Fails: `x : Fin two` but `· * · : Fin 2 → Fin 2 → Fin 2`
```

This tactic supports all options supported by `dsimp`.
-/
syntax (name := bdsimp) "bdsimp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

macro_rules
| `(tactic|bdsimp $cfg $[$disch]? $[only%$only]? $[[$lemmas]]? $[$loc]?) =>
    `(tactic|set_option backward.defeqAttrib.useBackward true in
      dsimp $cfg $[$disch]? $[only%$only]? $[[$lemmas]]? $[$loc]?)
