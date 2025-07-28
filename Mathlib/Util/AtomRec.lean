/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
import Mathlib.Util.AtomM

/-!
# `ring_nf` tactic

A tactic which uses `ring` to rewrite expressions. This can be used non-terminally to normalize
ring expressions in the goal such as `⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to
prove some equations that `ring` cannot because they involve ring reasoning inside a subterm,
such as `sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

-/

namespace Mathlib.Tactic
open Lean
open Qq Meta


namespace AtomRec

/-- Configuration for `ring_nf`. -/
structure Config where
  /-- the reducibility setting to use when comparing atoms for defeq -/
  red := TransparencyMode.reducible
  /-- if true, local let variables can be unfolded -/
  zetaDelta := false
  /-- if true, atoms inside ring expressions will be reduced recursively -/
  recursive := true
  /-- if true, then fail if no progress is made -/
  failIfUnchanged := true
  deriving Inhabited, BEq, Repr

/-- The read-only state of the `AtomRec` monad. -/
structure Context where
  /-- A basically empty simp context, passed to the `simp` traversal in `AtomRec.rewrite`. -/
  ctx : Simp.Context
  /-- A cleanup routine, which simplifies normalized polynomials to a more human-friendly
  format. -/
  simp : Simp.Result → MetaM Simp.Result

/-- The monad for `AtomRec` contains, in addition to the `AtomM` state,
a simp context for the main traversal and a simp function (which has another simp context)
to simplify normalized polynomials. -/
abbrev M := ReaderT Context AtomM

/--
A tactic in the `AtomRec.M` monad which will simplify expression `parent` to a normal form.
* `root`: true if this is a direct call to the function.
  `AtomRec.M.run` sets this to `false` in recursive mode.
-/
def rewrite
    (bar : ∀ (rctx : AtomM.Context) (s : IO.Ref AtomM.State) (e : Expr), MetaM Simp.Result)
    (parent : Expr) (root := true) :
    M Simp.Result :=
  fun nctx rctx s ↦ do
    let pre : Simp.Simproc := fun e =>
      try
        guard <| root || parent != e -- recursion guard
        let r' ← bar rctx s e
        let r ← nctx.simp r'
        if ← withReducible <| isDefEq r.expr e then return .done { expr := r.expr }
        pure (.done r)
      catch _ => pure <| .continue
    let post := Simp.postDefault #[]
    (·.1) <$> Simp.main parent nctx.ctx (methods := { pre, post })

/--
Runs a tactic in the `AtomRec.M` monad, given initial data:

* `s`: a reference to the mutable state of `ring`, for persisting across calls.
  This ensures that atom ordering is used consistently.
* `cfg`: the configuration options
* `x`: the tactic to run
-/
partial def M.run
    {α : Type} (s : IO.Ref AtomM.State) (cfg : AtomRec.Config) (nctx : AtomRec.Context)
    (bar : ∀ (rctx : AtomM.Context) (s : IO.Ref AtomM.State) (e : Expr), MetaM Simp.Result)
    (x : M α) :
    MetaM α := do
  let rec
    /-- The recursive context. -/
    rctx := { red := cfg.red, evalAtom },
    /-- The atom evaluator calls either `AtomRec.rewrite` recursively,
    or nothing depending on `cfg.recursive`. -/
    evalAtom e := if cfg.recursive
      then rewrite bar e false nctx rctx s
      else pure { expr := e }
  withConfig ({ · with zetaDelta := cfg.zetaDelta }) <| x nctx rctx s

def foo (s : IO.Ref AtomM.State) (cfg : Config) (nctx : AtomRec.Context)
    (bar : ∀ (rctx : AtomM.Context) (s : IO.Ref AtomM.State) (e : Expr), MetaM Simp.Result)
    (tgt : Expr) :
    MetaM Simp.Result := do
  M.run s cfg nctx bar <| rewrite bar tgt

end AtomRec

end Mathlib.Tactic
