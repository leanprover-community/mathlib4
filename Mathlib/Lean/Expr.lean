/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis, Floris van Doorn
-/
import Lean
/-!
# Additional operations on Expr and related types

This file defines basic operations on the types expr, name, declaration, level, environment.

This file is mostly for non-tactics.
-/

open Lean Meta

namespace Lean

namespace BinderInfo

/-! ### Declarations about `BinderInfo` -/

/-- The brackets corresponding to a given `BinderInfo`. -/
def brackets : BinderInfo → String × String
| BinderInfo.implicit => ("{", "}")
| BinderInfo.strictImplicit => ("{{", "}}")
| BinderInfo.instImplicit => ("[", "]")
| _ => ("(", ")")

end BinderInfo

namespace Name

/-! ### Declarations about `name` -/

/-- Find the largest prefix `n` of a `Name` such that `f n != none`, then replace this prefix
with the value of `f n`. -/
def mapPrefix (f : Name → Option Name) : Name → Name
| anonymous => anonymous
| str n' s _ => (f (mkStr n' s)).getD (mkStr (mapPrefix f n') s)
| num n' nr _ => (f (mkNum n' nr)).getD (mkNum (mapPrefix f n') nr)

end Name

namespace Expr
private def getAppFnArgsAux : Expr → Array Expr → Nat → Name × Array Expr
  | app f a _,   as, i => getAppFnArgsAux f (as.set! i a) (i-1)
  | const n _ _, as, i => (n, as)
  | _,           as, _ => (Name.anonymous, as)

def getAppFnArgs (e : Expr) : Name × Array Expr :=
  let nargs := e.getAppNumArgs
  getAppFnArgsAux e (mkArray nargs arbitrary) (nargs-1)

def natLit! : Expr → Nat
  | lit (Literal.natVal v) _ => v
  | _                        => panic! "nat literal expected"

end Expr

end Lean
