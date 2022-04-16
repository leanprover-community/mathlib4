import Lean

namespace Lean.Expr


def modifyAppArgM [Functor M] [Pure M] (modifier : Expr → M Expr) : Expr → M Expr
  | e@(app f a _) => e.updateApp! f <$> modifier a
  | e => pure e

def modifyAppArg (modifier : Expr → Expr) : Expr → Expr := modifyAppArgM (M := Id) modifier

def modifyRevArg (modifier : Expr → Expr): Nat → Expr  → Expr
  | 0 => modifyAppArg modifier
  | (i+1) => modifyAppArg (modifyRevArg modifier i)

/-- Given `f a₀ a₁ ... aₙ₋₁`, runs `modifier` on the `i`th argument or returns the original expression if out of bounds. -/
def modifyArg (modifier : Expr → Expr) (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Expr :=
  modifyRevArg modifier (n - i - 1) e

def getRevArg? : Expr → Nat → Option Expr
  | app f a _, 0   => a
  | app f _ _, i+1 => getRevArg! f i
  | _,         _   => none

/-- Given `f a₀ a₁ ... aₙ₋₁`, returns the `i`th argument or none if out of bounds. -/
def getArg? (e : Expr) (i : Nat) (n := e.getAppNumArgs): Option Expr :=
  getRevArg? e (n - i - 1)

def modifyArgM [Monad M] (modifier : Expr → M Expr) (e : Expr) (i : Nat) (n := e.getAppNumArgs) : M Expr := do
  let some a := getArg? e i | return e
  let a ← modifier a
  return modifyArg (fun _ => a) e i n

end Lean.Expr
