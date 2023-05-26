/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean

/-!

# Additions to Lean.SubExpr

This file introduces utilities for folding over the (raw) `SubExpr` children of a given expression,
along with basic functionality for finding positions and extracting `Expr`s at positions.

TODO: `foldrChildren`/`foldlb`/`foldrt`/`foldrb`/`foldlApp` (etc.), if ever needed; `foldlMeta*` to
handle loose bvars appropriately.

-/

open Lean SubExpr Meta

namespace Lean.Expr

/-! # Folds -/

/-- Fold over all subexpressions in a given expression, from `l`eft-to-right and `t`op-to-bottom—
i.e., each node is visited by `f` before its children. `.mdata` is ignored, as it does not receive
a unique `Pos`.

This is analogous to `Expr.traverseChildrenWithPos`, but with two main differences:

* does not reconstruct the original expression, instead passing arbitrary data in fold style
* does not instantiate loose bvars with fvars. As such, loose bvars may be encountered.
-/
def foldltWithPosM {α : Type u} {m : Type u → Type u} [Monad m] (e : Expr)
    (f : α → Pos → Expr → m α) (init : α) : m α :=
  go Pos.root e init
where
  go (p : Pos) (e : Expr) (a : α) : m α := match e with
  | .app f' x => f a p e >>= go p.pushAppFn f' >>= go p.pushAppArg x
  | .lam _ d b _ | .forallE _ d b _ => f a p e
      >>= go p.pushBindingDomain d
      >>= go p.pushBindingBody b
  | .mdata _ e => go p e a
  | .proj _ _ b => f a p e >>= go p.pushProj b
  | .letE _ t v b _ => f a p e
      >>= go p.pushLetVarType t
      >>= go p.pushLetValue v
      >>= go p.pushLetBody b
  | e => f a p e

@[inherit_doc foldltWithPosM]
def foldltWithPos {α : Type u} (e : Expr) (f : α → Pos → Expr → α) (init : α) : α :=
  Id.run <| e.foldltWithPosM f init

/-- Folds over the `SubExpr`-terminal expressions in a given expression. Namely, `.app`, `.lam`,
`.forallE`, `.mdata`, `.proj`, and `.letE` subexpressions are transparent to this fold, and will
not be used directly as inputs to `f`.

This is analogous to `Expr.traverseChildrenWithPos`, but with two main differences:

* does not reconstruct the original expression, instead passing arbitrary data in fold style
* does not instantiate loose bvars with fvars. As such, loose bvars may be encountered.
-/
def foldlChildrenWithPosM {α : Type u} {m : Type u → Type u} [Monad m] (e : Expr)
    (f : α → Pos → Expr → m α) (init : α) : m α :=
  go Pos.root e init
where
  go (p : Pos) (e : Expr) (a : α) : m α := match e with
  | .app f x => go p.pushAppFn f a >>= go p.pushAppArg x
  | .lam _ d b _ | .forallE _ d b _ => go p.pushBindingDomain d a >>= go p.pushBindingBody b
  | .mdata _ e => go p e a
  | .proj _ _ b => go p.pushProj b a
  | .letE _ t v b _ => go p.pushLetVarType t a >>= go p.pushLetValue v >>= go p.pushLetBody b
  | e => f a p e

@[inherit_doc foldlChildrenWithPosM]
def foldlChildrenWithPos {α : Type u} (e : Expr) (f : α → Pos → Expr → α) (init : α) : α :=
  Id.run <| e.foldlChildrenWithPosM f init

/-- Collect all the subexpressions in a given expression. Metadata is ignored. -/
def collectSubExprs (e : Expr) : Array SubExpr :=
  e.foldltWithPos (init := #[]) fun acc p e => acc.push ⟨e,p⟩

/-- Collect all the terminal subexpressions in a given expression. Namely, `.app`, `.lam`,
`.forallE`, `.mdata`, `.proj`, and `.letE` subexpressions are non-terminal. -/
def collectSubExprChildren (e : Expr) : Array SubExpr :=
  e.foldlChildrenWithPos (init := #[]) fun acc p e => acc.push ⟨e,p⟩

/-- Collect the positions of all subexpressions which satisfy a predicate. -/
def collectPositions (e : Expr) (pred : Pos → Expr → Bool) : Array Pos :=
  e.foldltWithPos (init := #[]) fun ps p e => if pred p e then ps.push p else ps

/-- Collect the positions of all terminal subexpressions which satisfy a predicate. -/
def collectChildrenPositions (e : Expr) (pred : Pos → Expr → Bool) : Array Pos :=
  e.foldlChildrenWithPos (init := #[]) fun ps p e => if pred p e then ps.push p else ps

/-! # Indexing into an `Expr` -/

/-- Given an array of positions `ps`, get the subexpressions of `e` found at each position (if such
a position can be found in `e`.) -/
def getExprsAt? (e : Expr) (ps : Array Pos) : Array (Option Expr) :=
  e.foldltWithPos (init := mkArray ps.size none) fun es? p e =>
    match ps.findIdx? (p == ·) with
    | some i => es?.set! i (some e)
    | none => es?

/-- Given an array of positions `ps`, get the subexpressions of `e` found at each position. If any
position in `ps` does not exist in `e`, this returns `none`. -/
def getAllExprsAt? (e : Expr) (ps : Array Pos) : Option (Array Expr) :=
  getExprsAt? e ps |>.mapM id

/-- Like `getExprsAt?`, but only search terminal subexpressions. -/
def getChildrenExprsAt? (e : Expr) (ps : Array Pos) : Array (Option Expr) :=
  e.foldlChildrenWithPos (init := mkArray ps.size none) fun es? p e =>
    match ps.findIdx? (p == ·) with
    | some i => es?.set! i (some e)
    | none => es?

/-- Like `getAllExprsAt?`, but only search terminal subexpressions. -/
def getAllChildrenExprsAt? (e : Expr) (ps : Array Pos) : Option (Array Expr) :=
  getChildrenExprsAt? e ps |>.mapM id

/-! # Finding positions -/

/-- Get the first positions of each element of `mvars` in `e`, if they can be found. -/
def getMVarsFirstPositions? (e : Expr) (mvars : Array MVarId) : Array (Option Pos) :=
  e.foldlChildrenWithPos (init := mkArray mvars.size none) fun
    | ps?, p, .mvar mvarId =>
      match mvars.findIdx? (mvarId == ·) with
      | some i => ps?.modifyOp i fun | none => some p | b? => b?
      | none => ps?
    | ps?, _, _ => ps?

/-- Get the first positions of each element of `mvars` in `e`. If any element can't be found,
return `none`. -/
def getAllMVarsFirstPositions? (e : Expr) (mvars : Array MVarId) : Option (Array Pos) :=
  getMVarsFirstPositions? e mvars |>.mapM id

/-- Get the array of positions of each element of `mvars` in `e`. -/
def getMVarsPositions (e : Expr) (mvars : Array MVarId) : Array (Array Pos) :=
  e.foldlChildrenWithPos (init := mkArray mvars.size #[]) fun
    | pss, p, .mvar mvarId =>
      match mvars.findIdx? (mvarId == ·) with
      | some i => pss.modifyOp i (·.push p)
      | none => pss
    | pss, _, _ => pss
