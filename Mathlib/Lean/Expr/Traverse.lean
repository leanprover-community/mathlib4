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

set_option autoImplicit true

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

/-- `e.foldlM f a` folds the monadic function `f` over the subterms of the expression `e`,
with initial value `a`. -/
def foldlM {α : Type} {m} [Monad m] (f : α → Expr → m α) (x : α) (e : Expr) : m α :=
  Prod.snd <$> (StateT.run (e.traverseChildren fun e' =>
      Functor.mapConst e' (get >>= monadLift ∘ flip f e' >>= set)) x : m _)

end Lean.Expr
