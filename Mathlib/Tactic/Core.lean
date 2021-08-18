/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue
-/

import Lean.Expr

namespace Lean.Expr

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
