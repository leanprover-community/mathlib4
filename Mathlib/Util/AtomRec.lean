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
abbrev M := ReaderT AtomRec.Context AtomM

/--
A tactic in the `AtomRec.M` monad which will simplify expression `parent` to a normal form.
* `root`: true if this is a direct call to the function.
  `AtomRec.M.run` sets this to `false` in recursive mode.
-/
def rewrite (eval : Expr → AtomM Simp.Result) (parent : Expr) (root := true) :
    M Simp.Result :=
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
Runs a tactic in the `AtomRec.M` monad, given initial data:

* `s`: a reference to the mutable `AtomM` state, for persisting across calls.
  This ensures that atom ordering is used consistently.
* `cfg`: the configuration options
* `x`: the tactic to run
-/
partial def M.run
    {α : Type} (s : IO.Ref AtomM.State) (cfg : AtomRec.Config)
    (simp : Simp.Result → MetaM Simp.Result)
    (eval : Expr → AtomM Simp.Result) (x : M α) :
    MetaM α := do
  let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta, singlePass := true }
    (simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}])
    (congrTheorems := ← getSimpCongrTheorems)
  let nctx := { ctx, simp }
  let rec
    /-- The recursive context. -/
    rctx := { red := cfg.red, evalAtom },
    /-- The atom evaluator calls `AtomRec.rewrite` recursively. -/
    evalAtom e := rewrite eval e false nctx rctx s
  withConfig ({ · with zetaDelta := cfg.zetaDelta }) <| x nctx rctx s

def foo (s : IO.Ref AtomM.State) (cfg : AtomRec.Config)
    (simp : Simp.Result → MetaM Simp.Result)
    (eval : Expr → AtomM Simp.Result) (tgt : Expr) :
    MetaM Simp.Result := do
  M.run s cfg simp eval <| rewrite eval tgt

end AtomRec

end Mathlib.Tactic
