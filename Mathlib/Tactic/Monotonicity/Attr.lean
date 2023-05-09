/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Thomas Murrills
-/
import Lean
import Std.Lean.Meta.DiscrTree
import Qq.MetaM
import Mathlib.Order.Monotone.Basic

/-! # The @[mono] attribute -/

open Lean Meta Elab Term Qq

initialize registerTraceClass `Tactic.mono

namespace Mathlib.Tactic.Monotonicity

/-- A token indicating the side of the mono extension. -/
syntax mono.side := &"left" <|> &"right" <|> &"both"

/-- The side for a mono extension. -/
inductive Side where | left | right | both
deriving Inhabited

namespace Attr

/-- A lemma stating the monotonicity of some function, with respect to appropriate relations on its
domain and range, and possibly with side conditions. -/
syntax (name := mono) "mono" (ppSpace mono.side)? : attr

/--
An extension for `mono`.
-/
structure MonoExt where
  /-- The side this expression applies to. -/
  side : Side := .both
  /-- The name of the `mono` extension. -/
  name : Name
deriving Inhabited

/-- Checks for left `mono`s (i.e., `mono`s with `side` equal to `.left` or `.both`) -/
def isLeft : MonoExt → Bool
| ⟨.right, _⟩ => false
| ⟨_,      _⟩ => true

/-- Checks for right `mono`s (i.e., `mono`s with `side` equal to `.right` or `.both`) -/
def isRight : MonoExt → Bool
| ⟨.left, _⟩ => false
| ⟨_,     _⟩ => true

/-- Parse optional `mono.side` syntax, returning `Side.both` by default. -/
def parseSide [Monad m] [MonadError m] (s : Option (TSyntax ``mono.side)) : m Side :=
  match s with
  | some s => match s with
    | `(mono.side|left)  => pure .left
    | `(mono.side|right) => pure .right
    | `(mono.side|both)  => pure .both
    | _        => throwErrorAt s "{s} is expected to be 'left', 'right', or 'both'"
  | none   => pure .both

/-- Read a `mono` extension from an (imported) extension declaration. `MonoExt`s are only provided
as declarations by imports, so this is only used to read off those imported declarations. -/
def mkMonoExt (n : Name) : ImportM MonoExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck MonoExt opts ``MonoExt n

/-- Each `mono` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev Entry := Array (DiscrTree.Key true) × MonoExt --!! Need side?

/-- The state of the `mono` extension environment -/
structure Monos where
  /-- The tree of `mono` extensions. -/
  tree   : DiscrTree MonoExt true := {}
  /-- Erased `mono`s. -/
  erased : PHashSet Name := {}
deriving Inhabited

/-- Environment extensions for `mono` declarations -/
initialize monoExt : ScopedEnvExtension Entry Entry Monos ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq MonoExt := ⟨fun _ _ ↦ false⟩
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ e ↦ return e
    toOLeanEntry := id
    addEntry := fun { tree, erased } (ks, ext) ↦
      { tree := tree.insertCore ks ext, erased := erased.erase ext.name }
  }

/-- Erases a name marked `mono` by adding it to the state's `erased` field and
  removing it from the state's list of `Entry`s. -/
def Monos.eraseCore (d : Monos) (declName : Name) : Monos :=
 { d with erased := d.erased.insert declName }

/--
  Erase a name's `mono` attribute.

  Check that it does in fact have the `mono` attribute by making sure it names a `MonoExt`
found somewhere in the state's tree, and is not already erased.
-/
def Monos.erase [Monad m] [MonadError m] (d : Monos) (declName : Name) : m Monos := do
  unless d.tree.values.any (·.name == declName) && ! d.erased.contains declName do
    throwError "'{declName}' does not have the [mono] attribute"
  return d.eraseCore declName


initialize registerBuiltinAttribute {
  name := `mono
  descr := "adds a mono extension"
  applicationTime := .afterCompilation
  add := fun name stx kind ↦ match stx with
    | `(attr| mono $[$s:mono.side]?) => do
      let side ← parseSide s
      let env ← getEnv
      unless (env.find? name).isNone do
        let s := monoExt.getState env
        if s.tree.values.any (·.name == name) then
          throwError "declaration '{name}' is already tagged mono"
      if (IR.getSorryDep env name).isSome then return -- ignore in progress definitions
      let ext := { name, side }
      let cinfo ← getConstInfo name
      let val := Expr.const name (cinfo.levelParams.map mkLevelParam)
      let keys ← MetaM.run' <| withReducible do
        let type ← inferType val
        let type ← instantiateMVars type
        unless (← isProp type) do
          throwError "invalid 'mono', proposition expected{indentExpr type}"
        let type ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
          let (_, _, type) ←
            forallMetaTelescopeReducing (← mkForallFVars (← getLCtx).getFVars type true)
          whnfR type
        trace[Tactic.mono] "adding DiscrTree.mkPath {type} to the DiscrTree"
        DiscrTree.mkPath type
      monoExt.add (keys, ext) kind
    | _ => throwUnsupportedSyntax
  erase := fun name => do
    let s := monoExt.getState (← getEnv)
    let s ← s.erase name
    modifyEnv fun env => monoExt.modifyState env fun _ => s
}
