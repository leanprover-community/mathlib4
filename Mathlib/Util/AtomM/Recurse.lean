/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Util.AtomM

/-!
# Running `AtomM` metaprograms recursively

Tactics such as `ring` and `abel` are implemented using the `AtomM` monad, which tracks "atoms" --
expressions which cannot be further parsed according to the arithmetic operations they handle --
to allow for consistent normalization relative to these atoms.

This file provides methods to allow for such normalization to run recursively: the atoms themselves
will have the normalization run on any of their subterms for which this makes sense. For example,
given an implementation of ring-normalization, the methods in this file implement the bottom-to-top
recursive ring-normalization in which `sin (x + y) + sin (y + x)` is normalized first to
`sin (x + y) + sin (x + y)` and then to `2 * sin (x + y)`.

## Main declarations

* `Mathlib.Tactic.AtomM.RecurseM.run`: run a metaprogram (in `AtomM` or its slight extension
  `AtomM.RecurseM`), with atoms normalized according to a provided normalization operation (in
  `AtomM`), run recursively.

* `Mathlib.Tactic.AtomM.recurse`: run a normalization operation (in `AtomM`) recursively on an
  expression.

-/

namespace Mathlib.Tactic.AtomM
open Lean Meta

/-- Configuration for `AtomM.Recurse`. -/
structure Recurse.Config where
  /-- the reducibility setting to use when comparing atoms for defeq -/
  red := TransparencyMode.reducible
  /-- if true, local let variables can be unfolded -/
  zetaDelta := false
deriving Inhabited, BEq, Repr

/-- The read-only state of the `AtomM.Recurse` monad. -/
structure Recurse.Context where
  /-- A basically empty simp context, passed to the `simp` traversal in `AtomM.onSubexpressions`.
  -/
  ctx : Simp.Context
  /-- A cleanup routine, which simplifies evaluation results to a more human-friendly format. -/
  simp : Simp.Result → MetaM Simp.Result

/-- The monad for `AtomM.Recurse` contains, in addition to the `AtomM` state,
a simp context for the main traversal and a cleanup function to simplify evaluation results. -/
abbrev RecurseM := ReaderT Recurse.Context AtomM

/--
A tactic in the `AtomM.RecurseM` monad which will simplify expression `parent` to a normal form, by
running a core operation `eval` (in the `AtomM` monad) on the maximal subexpression(s) on which
`eval` does not fail.

There is also a subsequent clean-up operation, governed by the context from the `AtomM.RecurseM`
monad.

* `root`: true if this is a direct call to the function.
  `AtomM.RecurseM.run` sets this to `false` in recursive mode.
-/
def onSubexpressions (eval : Expr → AtomM Simp.Result) (parent : Expr) (root := true) :
    RecurseM Simp.Result :=
  fun nctx rctx s ↦ do
    let pre : Simp.Simproc := fun e =>
      try
        guard <| root || parent != e -- recursion guard
        let r' ← eval e rctx s
        let r ← nctx.simp r'
        if ← withReducible <| isDefEq r.expr e then return .done { expr := r.expr }
        pure (.done r)
      catch _ => pure <| .continue
    let post := Simp.postDefault #[]
    (·.1) <$> Simp.main parent nctx.ctx (methods := { pre, post })

/--
Runs a tactic in the `AtomM.RecurseM` monad, given initial data:

* `s`: a reference to the mutable `AtomM` state, for persisting across calls.
  This ensures that atom ordering is used consistently.
* `cfg`: the configuration options
* `eval`: a normalization operation which will be run recursively, potentially dependent on a known
  atom ordering
* `simp`: a cleanup operation which will be used to post-process expressions
* `x`: the tactic to run
-/
partial def RecurseM.run
    {α : Type} (s : IO.Ref State) (cfg : Recurse.Config) (eval : Expr → AtomM Simp.Result)
    (simp : Simp.Result → MetaM Simp.Result) (x : RecurseM α) :
    MetaM α := do
  let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta, singlePass := true }
    (simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}])
    (congrTheorems := ← getSimpCongrTheorems)
  let nctx := { ctx, simp }
  let rec
    /-- The recursive context. -/
    rctx := { red := cfg.red, evalAtom },
    /-- The atom evaluator calls `AtomM.onSubexpressions` recursively. -/
    evalAtom e := onSubexpressions eval e false nctx rctx s
  withConfig ({ · with zetaDelta := cfg.zetaDelta }) <| x nctx rctx s

/--
Normalizes an expression, given initial data:

* `s`: a reference to the mutable `AtomM` state, for persisting across calls.
  This ensures that atom ordering is used consistently.
* `cfg`: the configuration options
* `eval`: a normalization operation which will be run recursively, potentially dependent on a known
  atom ordering
* `simp`: a cleanup operation which will be used to post-process expressions
* `tgt`: the expression to normalize
-/
def recurse (s : IO.Ref State) (cfg : Recurse.Config)
    (eval : Expr → AtomM Simp.Result)
    (simp : Simp.Result → MetaM Simp.Result) (tgt : Expr) :
    MetaM Simp.Result := do
  RecurseM.run s cfg eval simp <| onSubexpressions eval tgt

end Mathlib.Tactic.AtomM
