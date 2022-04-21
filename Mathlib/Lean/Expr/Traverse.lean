/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/

import Lean
import Mathlib.Lean.Expr.Basic

/-!
# Traversal functions for expressions.
-/

namespace Lean.Expr

/-- Maps `f` on each immediate child of the given expression. -/
def traverseChildren [Applicative M] (f : Expr → M Expr) : Expr → M Expr
  | e@(forallE _ d b _) => pure e.updateForallE! <*> f d <*> f b
  | e@(lam _ d b _)     => pure e.updateLambdaE! <*> f d <*> f b
  | e@(mdata _ b _)     => e.updateMData! <$> f b
  | e@(letE _ t v b _)  => pure e.updateLet! <*> f t <*> f v <*> f b
  | e@(app l r _)       => pure e.updateApp! <*> f l <*> f r
  | e@(proj _ _ b _)    => e.updateProj! <$> f b
  | e                   => pure e

def traverseApp {M} [Monad M]
  (f : Expr → M Expr) (e : Expr) : M Expr :=
  e.withApp fun fn args => (pure mkAppN) <*> (f fn) <*> (args.mapM f)


end Lean.Expr

namespace Lean.Meta

variable {M} [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M]

def traverseLambda
  (f : Expr → M Expr) (fvars : Array Expr) (e : Expr) : M Expr :=
  match e with
  | (Expr.lam n d b c) => do withLocalDecl n c.binderInfo (← f (d.instantiateRev fvars)) fun x => traverseLambda f (fvars.push x) b
  | e   => do mkLambdaFVars (usedLetOnly := false) fvars (← f (e.instantiateRev fvars))

def traverseForall
  (f : Expr → M Expr) (fvars : Array Expr) (e : Expr) : M Expr :=
  match e with
  | (Expr.forallE n d b c) => do withLocalDecl n c.binderInfo (← f (d.instantiateRev fvars)) fun x => traverseForall f (fvars.push x) b
  | e   => do mkForallFVars (usedLetOnly := false) fvars (← f (e.instantiateRev fvars))

def traverseLet
  (f : Expr → M Expr) (fvars : Array Expr) (e : Expr) : M Expr := do
  match e with
  | Expr.letE n t v b _ =>
    withLetDecl n (← f (t.instantiateRev fvars)) (← f (v.instantiateRev fvars)) fun x =>
      traverseLet f (fvars.push x) b
  | e => mkLetFVars (usedLetOnly := false) fvars (← f (e.instantiateRev fvars))

/-- A version of traverseChildren that automatically makes free variables etc. -/
def traverseChildren (f : Expr → M Expr) (e : Expr) : M Expr :=
  match e with
  | Expr.forallE .. => traverseForall f #[] e
  | Expr.lam .. => traverseLambda f #[] e
  | Expr.letE .. => traverseLet f #[] e
  | Expr.app .. => Lean.Expr.traverseApp f e
  | _ => Lean.Expr.traverseChildren f e

end Lean.Meta
