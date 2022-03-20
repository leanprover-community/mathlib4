/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/

import Lean
import Mathlib.Util.MemoFix

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

/-- Returns a list of the immediate child expressions of the given expression. -/
def getChildren : Expr → List Expr
| e@(forallE _ d b _) => [d,b]
| e@(lam _ d b _)     => [d,b]
| e@(mdata _ b _)     => [b]
| e@(letE _ t v b _)  => [t,v,b]
| e@(app l r _)       => [l,r]
| e@(proj _ _ b _)    => [b]
| e                   => []

/-- Folds `f` over each subexpression in a depth-first, left to right manner. -/
def foldM {M} [Monad M] {α} (f : α → Expr → M α) : (init : α) → Expr → M α :=
flip $ memoFix $ fun r e a => f a e >>= e.getChildren.foldlM (flip r)

def fold {α} : (f : α → Expr → α) → (init : α)  → Expr → α := foldM (M := Id)

end Lean.Expr
