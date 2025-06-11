import Lean

open Lean

namespace Mathlib.Tactic.Widget.Rewrite

inductive Path where
  | node : Path
  | app (arg : Nat) (explicit : Bool) (next : Path) : Path
  | proj (next : Path) : Path
  | fun (next : Path) : Path
  | type (next : Path) : Path
  | body (next : Path) : Path
  | value (next : Path) : Path

def pathToSubExpr (expr : Expr) (path : Path) : MetaM SubExpr.Pos :=
  go expr path .root
where
  go (expr : Expr) (path : Path) (acc : SubExpr.Pos) : MetaM SubExpr.Pos :=
    match path with
    | .node => pure acc
    | .type next =>
      match expr.consumeMData with
      | .letE _ t _ _ _ => go t next acc.pushLetVarType
      | .lam _ t _ _
      | .forallE _ t _ _ => go t next acc.pushBindingDomain
      | _ => throwError m!"invalid binding domain access on{indentExpr expr}"
    | .body next =>
      match expr.consumeMData with
      | .letE _ _ _ b _ => go b next acc.pushLetBody
      | .lam _ _ b _
      | .forallE _ _ b _ => go b next acc.pushBindingBody
      | _ => throwError m!"invalid binding body access on{indentExpr expr}"
    | .value next =>
      match expr.consumeMData with
      | .letE _ _ v _  _ => go v next acc.pushLetValue
      | _ => throwError m!"invalid let value access on{indentExpr expr}"
    | .proj next =>
      match expr.consumeMData with
      | .proj _ _ e => go e next acc.pushProj
      | _ => throwError m!"invalid proj access on{indentExpr expr}"
    | .fun next =>
      match expr.consumeMData with
      | .app f _ => go f next acc.pushAppFn
      | _ => throwError m!"invalid fun access on{indentExpr expr}"
    | .app 0 true next => go expr.getAppFn' next (acc.pushNaryFn expr.getAppNumArgs')
    | .app (n + 1) true next => do
      let c ← getIdxExplicit expr (expr.getAppNumArgs' - n - 1)
      go c next (acc.pushNaryArg expr.getAppNumArgs' n)
    | _ => failure
  getIdxExplicit (e : Expr) (n : Nat) : MetaM Expr :=
    match e.consumeMData, n with
    | .app _ a, 0 => pure a
    | .app f _, n + 1 => getIdxExplicit f n
    | _, _ => failure

end Mathlib.Tactic.Widget.Rewrite
