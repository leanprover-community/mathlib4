/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers, Floris van Doorn
-/

import Lean.Data.Name

/-!
Fixups corresponding to lean4/src/Lean/Data/Name.lean.
-/

namespace Lean.Name

open Lean

/-- Lean 4 makes declarations which are technically not internal
(that is, head string does not start with `_`) but which sometimes should
be treated as such. For example, the `to_additive` attribute needs to
transform `proof_1` constants generated by `Lean.Meta.mkAuxDefinitionFor`.
This might be better fixed in core (perhaps via a change such as
https://github.com/leanprover/lean4/pull/2112), but until then, this method can act
as a polyfill.

Note: this declaration also occurs as `shouldIgnore` in the Lean 4 file `test/lean/run/printDecls`.
Another similar function is Std.Tactic.Lint.isAutoDecl.
-/
def isInternal' (declName : Name) : Bool :=
  declName.isInternal ||
  match declName with
  | .str _ s => "match_".isPrefixOf s || "proof_".isPrefixOf s || "eq_".isPrefixOf s
  | _        => true
