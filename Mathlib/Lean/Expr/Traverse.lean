/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/

import Lean
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Expr.SubExpr

/-!
# Traversal functions for expressions.
-/

namespace Lean.Expr

/-- Maps `f` on each immediate child of the given expression.

Note that bound variablesremain abstracted, so you can't
use `MetaM` methods in the traversing function `f`.
To do this, you need to use `Lean.Meta.traverseChildren` instead. -/
def traverseChildren [Applicative M] (f : Expr → M Expr) : Expr → M Expr
  | e@(forallE _ d b _) => pure e.updateForallE! <*> f d <*> f b
  | e@(lam _ d b _)     => pure e.updateLambdaE! <*> f d <*> f b
  | e@(mdata _ b _)     => e.updateMData! <$> f b
  | e@(letE _ t v b _)  => pure e.updateLet! <*> f t <*> f v <*> f b
  | e@(app l r _)       => pure e.updateApp! <*> f l <*> f r
  | e@(proj _ _ b _)    => e.updateProj! <$> f b
  | e                   => pure e

/-- Given `e = fn a₁ ... aₙ`, runs `f` on `fn` and each of the arguments `aᵢ` and
makes a new function application with the results. -/
def traverseApp {M} [Monad M]
  (f : Expr → M Expr) (e : Expr) : M Expr :=
  e.withApp fun fn args => (pure mkAppN) <*> (f fn) <*> (args.mapM f)

end Lean.Expr

namespace Lean.Meta

variable {M} [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M]

/-- Given an expression `fun (x₁ : α₁) ... (xₙ : αₙ) => b`, will run
`f` on each of the variable types `αᵢ` and `b` with the correct MetaM context,
replacing each expression with the output of `f` and creating a new lambda.
(that is, correctly instantiating bound variables and repackaging them after)  -/
def traverseLambda
  (f : Expr → M Expr) (fvars : Array Expr := #[]) (e : Expr) : M Expr :=
  match e with
  | (Expr.lam n d b c) => do withLocalDecl n c.binderInfo (← f (d.instantiateRev fvars)) fun x => traverseLambda f (fvars.push x) b
  | e   => do mkLambdaFVars (usedLetOnly := false) fvars (← f (e.instantiateRev fvars))

/-- Given an expression ` (x₁ : α₁) → ... → (xₙ : αₙ) → b`, will run
`f` on each of the variable types `αᵢ` and `b` with the correct MetaM context,
replacing the expression with the output of `f` and creating a new forall expression.
(that is, correctly instantiating bound variables and repackaging them after)  -/
def traverseForall
  (f : Expr → M Expr) (fvars : Array Expr := #[]) (e : Expr) : M Expr :=
  match e with
  | (Expr.forallE n d b c) => do withLocalDecl n c.binderInfo (← f (d.instantiateRev fvars)) fun x => traverseForall f (fvars.push x) b
  | e   => do mkForallFVars (usedLetOnly := false) fvars (← f (e.instantiateRev fvars))

/-- Similar to traverseLambda and traverseForall but with let binders.  -/
def traverseLet
  (f : Expr → M Expr) (fvars : Array Expr := #[]) (e : Expr) : M Expr := do
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

/-! # SubExpr optics -/

namespace SubExpr

variable {M} [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M] [MonadError M]

open Lean.PrettyPrinter.Delaborator SubExpr

/-- Given a constructor index for Expr, runs `g` on the value of that subexpression and replaces it.
If the subexpression is under a binder it will instantiate and abstract the binder body correctly.
Mdata is ignored. An index of 3 is interpreted as the type of the expression. An index of 3 will throw. -/
private def lensPos (g : Expr → M Expr) : Nat → Expr → M Expr
  | 0, e@(Expr.app f a _)       => return e.updateApp! (← g f) a
  | 1, e@(Expr.app f a _)       => return e.updateApp! f (← g a)
  | 0, e@(Expr.lam n y b _)     => return e.updateLambdaE! (← g y) b
  | 1, e@(Expr.lam n y b c)     => return e.updateLambdaE! y <|← withLocalDecl n c.binderInfo y fun x => do mkLambdaFVars #[x] (← g (b.instantiateRev #[x]))
  | 0, e@(Expr.forallE n y b _) => return e.updateForallE! (← g y) b
  | 1, e@(Expr.forallE n y b c) => return e.updateForallE! y <|← withLocalDecl n c.binderInfo y fun x => do mkForallFVars #[x] (← g (b.instantiateRev #[x]))
  | 0, e@(Expr.letE n y a b c)  => return e.updateLet! (← g y) a b
  | 1, e@(Expr.letE n y a b c)  => return e.updateLet! y (← g a) b
  | 2, e@(Expr.letE n y a b c)  => return e.updateLet! y a (← withLetDecl n y a fun x => do mkLetFVars #[x] (← g (b.instantiateRev #[x])))
  | 0, e@(Expr.proj _ _ b _)    => pure e.updateProj! <*> g b
  | n, e@(Expr.mdata _ a _)     => pure e.updateMData! <*> lensPos g n a
  | 3, e                        => throwError "Lensing on types is not supported"
  | c, e                        => throwError "Invalid coordinate {c} for {e}"

private def lensAux (g : Expr → M Expr) : List Nat → Expr → M Expr
  | [], e => g e
  | head::tail, e => lensPos (lensAux g tail) head e

/-- Run the given `g` function to replace the expression at the subexpression position. If the subexpression is below a binder
the bound variables will be appropriately instantiated with free variables and reabstracted after the replacement.
If the subexpression is invalid or points to a type then this will throw. -/
def lens (g : Expr → M Expr) : SubExpr → M SubExpr
  | ⟨e, p⟩ => do
    let e₂ ← lensAux g (Pos.decode p |> Array.toList) e
    return ⟨e₂, p⟩

/-- Runs `k` on the given coordinate, including handling binders properly.
The subexpression value passed to `k` is not instantiated with respected to the
array of free variables. -/
private def viewPosAux (k : Array Expr → Expr → M α) (fvars: Array Expr) : Nat → Expr → M α
  | 3, e                        => throwError "Internal: Types should be handled by viewAux"
  | 0, e@(Expr.app f a _)       => k fvars f
  | 1, e@(Expr.app f a _)       => k fvars a
  | 0, e@(Expr.lam n y b _)     => k fvars y
  | 1, e@(Expr.lam n y b c)     => withLocalDecl n c.binderInfo (y.instantiateRev fvars) fun x => k (fvars.push x) b
  | 0, e@(Expr.forallE n y b _) => k fvars <| y.instantiateRev fvars
  | 1, e@(Expr.forallE n y b c) => withLocalDecl n c.binderInfo (y.instantiateRev fvars) fun x => k (fvars.push x) b
  | 0, e@(Expr.letE n y a b c)  => k fvars y
  | 1, e@(Expr.letE n y a b c)  => k fvars a
  | 2, e@(Expr.letE n y a b c)  => withLetDecl n (y.instantiateRev fvars) (a.instantiateRev fvars) fun x => k (fvars.push x) b
  | 0, e@(Expr.proj _ _ b _)    => k fvars b
  | n, e@(Expr.mdata _ a _)     => viewPosAux k fvars n a
  | c, e                        => throwError "Invalid coordinate {c} for {e}"

private def viewAux (k : Array Expr → Expr → M α) (fvars : Array Expr) : List Nat → Expr → M α
  | [],         e => k fvars <| e.instantiateRev fvars
  | 3::tail,    e => do
    let y ← inferType <| e.instantiateRev fvars
    viewAux (fun otherFvars => k (fvars ++ otherFvars)) #[] tail y
  | head::tail, e => viewPosAux (fun fvars => viewAux k fvars tail) fvars head e

/-- Runs `k fvars s` where `s` is the expression pointed to by the given SubExpr
and fvars are the free variables for the binders that `s` is under.
`s` is already instantiated with respect to these.
The behaviour is analogous to `Lean.Meta.forallTelescope`. -/
def view (k : Array Expr → Expr → M α) : SubExpr → M α
  | ⟨e, p⟩ => viewAux k #[] (Pos.decode p |> Array.toList) e

end SubExpr

end Lean.Meta
