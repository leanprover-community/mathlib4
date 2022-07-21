/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Patrick Massot
-/

import Lean

open Lean Parser Elab Tactic

def Lean.Expr.renameBVar (e : Expr) (old new : Name) : Expr :=
  match e with
  | app fn arg => app (fn.renameBVar old new) (arg.renameBVar old new)
  | lam n ty bd bi =>
    lam (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | forallE n ty bd bi =>
    forallE (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | e => e

def renameBVarAt (old new : Name) (hyp? : Option Name) : TacticM Unit := sorry

#check Location

elab "rename_var " old:ident " → " new:ident loc:(ppSpace location)? : tactic =>
  match loc with
  | some loc =>
    withLocation (expandOptLocation loc) sorry sorry sorry
  | none =>
    pure ()
