import Lean

namespace Lean.PrettyPrinter.Delaborator

private abbrev N : Nat := SubExpr.maxChildren

/-- Creates a subexpression `Pos` from an array of 'coordinates'.
Each coordinate is a number {0,1,2} expressing which child subexpression should be explored.
The first coordinate in the array corresponds to the root of the expression tree.  -/
def Pos.encode (ps : Array Nat) : Pos := Id.run do
  let mut r := 1
  for p in ps do
    r ← r * N + p
  return r

/-- Decodes a subexpression `Pos` as a sequence of coordinates. See `Pos.encode` for details.-/
def Pos.decode (p : Pos) : Array Nat := Id.run do
    let mut x := p
    let mut a := #[]
    while x >= N do
      let head := x % N
      x ← (x - head) / N
      a ← a.push head
    return a.reverse

namespace SubExpr

variable {M} [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M] [MonadError M]

open Lean.PrettyPrinter.Delaborator SubExpr Lean.Meta

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
  | 0, e@(Expr.forallE n y b _) => k fvars y
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

end Lean.PrettyPrinter.Delaborator
