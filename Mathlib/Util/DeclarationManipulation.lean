/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Init
import Mathlib.Lean.Syntax
import Mathlib.Lean.Elab.InfoTree
import Mathlib.Tactic.Lemma

/-!
# Declaration manipulation tools for metaprogramming

This module defines a suite of tools for working with user-written declarations in metaprogramming,
which often involves interactions betweeen the infotrees, source syntax, and the environment.

This is a work-in-progress, and only in its early stages.
-/

namespace Lean.Elab.InfoTree

section declToInfoAndSyntax

/-! Given a declaration, these tools help us access `Info` associated with those declarations and
let us extract components of the command syntax corresponding to different parts of the
declaration. -/

/--
Given a constant name, find the first `TermInfo` whose expression is exactly that constant. Expects
`decl` to be a fully resolved name.
-/
def getConstTermInfo? (t : InfoTree) (decl : Name) : Option TermInfo :=
  t.findSome? fun
    | _, .ofTermInfo ti, _ => if ti.expr.isConstOf decl then some ti else none
    | _, _, _ => none

/--
Get the syntax of the `TermInfo` corresponding to the first appearance of `decl` as an
`Expr.const ..`.

Usually, this is the syntax of the identifier occurring after a token like `def` or `theorem`,
*excluding*  universe syntax (i.e., `id` in `$id$[.{$_,*}]?`). In the case of `instance` with no
identifier, the `instance` token is used.

Note that the behavior described here is undocumented, and subject to change.
-/
def getConstRef? (t : InfoTree) (decl : Name) : Option Syntax :=
  t.getConstTermInfo? decl |>.map (·.stx)

/- TODO: refactor through more general "declaration syntax view", like a more fine-grained version
of `mkDefView` and without the unneeded (for our purposes) elaboration state. -/
-- TODO: generalize to `def`s, etc.
open Parser.Command in
/--
Attempts find the type signature part of the originating syntax for `decl` appearing within the
syntax `cmd` by matching the position info of the syntax of the identifier occurring after a token
like `def` or `theorem`, *excluding*  universe syntax (i.e., `id` in `$id$[.{$_,*}]?`). (In the
case of `instance` with no identifier, the `instance` token is used.)

This `idRef : Syntax`, with the properties described here, can be extracted from the infotrees with
`InfoTree.getConstRef?`.

Only handles declarations originating from `theorem`, `lemma`, and `instance` (including
when nested in `mutual` blocks or buried somewhere in `cmd`). Does not handle `let rec`/
`where`-style `let rec` declarations.
-/
def _root_.Lean.Syntax.getThmSigRefOfId? (cmd idRef : Syntax) : Option (TSyntax ``declSig) :=
  cmd.findSome? fun
    | `(Parser.Command.theorem| theorem $id$[.{$_,*}]? $sig:declSig $_:declVal)
    | `(«lemma»| lemma $id$[.{$_,*}]? $sig:declSig $_:declVal)
    | `(Parser.Command.instance| $_:attrKind instance $[$_:namedPrio]?
        $id$[.{$_,*}]? $sig:declSig $_:declVal) =>
      if id.raw.rangeEq idRef then sig else none
    -- When no `declId` is present, Lean uses the position information for the `instance` token.
    | `(Parser.Command.instance| $_:attrKind instance%$tk $[$_:namedPrio]?
        $sig:declSig $_:declVal) => if tk.rangeEq idRef then sig else none
    -- TODO: handle `let rec` decls (after `where`), handle defs etc.
    | _ => none

-- TODO: generalize to `def`s, etc.
/--
Attempts to run `x : m α` with the monad's ref set to the syntax for the type signature of the
originating syntax of `decl` appearing within the syntax `cmd`, according to the link between the
`decl` and its syntax carried by the infotree `t`.

If the type signature's position info cannot be found, uses the position info of the syntax for
`decl` found in `t`. If that can't be found either, uses `cmd` as the ref.

Only handles declarations originating from `theorem`, `lemma`, and `instance` (including
when nested in `mutual` blocks or buried somewhere in `cmd`). Does not handle `let rec`/
`where`-style `let rec` declarations.
-/
def withThmSigRef {m : Type → Type} [Monad m] [MonadRef m] {α}
    (t : InfoTree) (cmd : Syntax) (decl : Name) (x : m α) : m α := withRef cmd do
  let some idRef := t.getConstRef? decl | x
  let sigRef? := cmd.getThmSigRefOfId? idRef
  -- Fall back to `idRef` if `sigRef` is not found or has no position info.
  withRef idRef <| withRef? sigRef? x

end declToInfoAndSyntax

end Lean.Elab.InfoTree
