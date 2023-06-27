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
  | e@(mdata _ b)       => e.updateMData! <$> f b
  | e@(letE _ t v b _)  => pure e.updateLet! <*> f t <*> f v <*> f b
  | e@(app l r)         => pure e.updateApp! <*> f l <*> f r
  | e@(proj _ _ b)      => e.updateProj! <$> f b
  | e                   => pure e

/-- `e.foldlM f a` folds the monadic function `f` over the direct subterms of the expression `e`,
with initial value `a`. -/
def foldlM {α : Type} {m} [Monad m] (f : α → Expr → m α) (init : α) (e : Expr) : m α :=
  Prod.snd <$> (StateT.run (e.traverseChildren $ fun e' =>
      Functor.mapConst e' (get >>= monadLift ∘ flip f e' >>= set)) init : m _)

/-- Implementation of `traverse`. -/
partial def traverseImpl [Inhabited α] [Monad m] (f : α → Expr → m α) (init : α) (e : Expr) : m α :=
  e.foldlM (init := init) fun a e => do
    e.traverseImpl f (← f a e)

/-- Visit all subexpressions of an expression, depth-first. -/
def traverse [Monad m] (f : α → Expr → m α) (init : α) (e : Expr) : m α :=
  have : Inhabited α := ⟨init⟩
  traverseImpl f init e

end Lean.Expr
