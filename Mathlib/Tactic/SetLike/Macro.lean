/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Tactic.SetLike.Init

/-!
# SetLike

We define the `set_like` tactic using `aesop`. -/

/-- The `set_like` attribute used to tag statements concerning `SetLike` objects for the `set_like`
tactic. -/
macro "set_like" : attr =>
  `(attr|aesop safe apply (rule_sets [$(Lean.mkIdent `SetLike):ident]))

/-- The tactic `set_like` solves goals of the form `expr ∈ S`, where `expr` is some mathematical
expressona and `S` is a subobject in some `SetLike` class, by applying lemmas tagged with the
`set_like` user attribute. -/
macro "set_like" : tactic =>
  `(tactic| aesop (options := { terminal := true }) (rule_sets [$(Lean.mkIdent `SetLike):ident]))

/-- The tactic `set_like` solves goals of the form `expr ∈ S`, where `expr` is some mathematical
expressona and `S` is a subobject in some `SetLike` class, by applying lemmas tagged with the
`set_like` user attribute. -/
macro "set_like?" : tactic =>
  `(tactic| aesop? (options := { terminal := true })
    (rule_sets [$(Lean.mkIdent `SetLike):ident]))
