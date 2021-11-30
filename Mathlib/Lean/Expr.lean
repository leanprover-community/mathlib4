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


instance : Inhabited BinderInfo :=
  ⟨BinderInfo.default⟩

/-- The brackets corresponding to a given `BinderInfo`. -/
def brackets : BinderInfo → String × String
| BinderInfo.implicit => ("{", "}")
| BinderInfo.strictImplicit => ("{{", "}}")
| BinderInfo.instImplicit => ("[", "]")
| _ => ("(", ")")

end BinderInfo

/-- The type of binders containing a name, the binder info and the binding type -/
structure Binder :=
  (name : Name)
  (info : BinderInfo)
  (type : Expr)
deriving Inhabited

namespace Binder

/-- Turn a binder into a string. Uses expr.to_string for the type. -/
protected def toString (b : Binder) : String :=
  let (l, r) := b.info.brackets
  l ++ toString b.name ++ " : " ++ toString b.type ++ r

instance : ToString Binder :=
⟨Binder.toString⟩

-- instance : ToFormat Binder :=
-- ⟨λ b => b.toString⟩

-- instance : hasToTacticFormat Binder :=
--   ⟨fun b =>
--       let (l, r) := b.info.brackets
--       (fun e => l ++ b.name.to_string ++ " : " ++ e ++ r) <$> pp b.type⟩

end Binder

namespace Name

/-! ### Declarations about `name` -/

/-- Find the largest prefix `n` of a `Name` such that `f n != none`, then replace this prefix
with the value of `f n`. -/
def mapPrefix (f : Name → Option Name) : Name → Name
| anonymous => anonymous
| str n' s d => (f (mkStr n' s)).getD (mkStr (mapPrefix f n') s)
| num n' nr d => (f (mkNum n' nr)).getD (mkNum (mapPrefix f n') nr)

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

/-!
Some declarations work with open expressions, i.e. an expr that has free variables.
Terms will free variables are not well-typed, and one should not use them in tactics like
`infer_type` or `unify`. You can still do syntactic analysis/manipulation on them.
The reason for working with open types is for performance: instantiating variables requires
iterating through the expression. In one performance test `pi_binders` was more than 6x
quicker than `mk_local_pis` (when applied to the type of all imported declarations 100x).
-/
-- library_note "open expressions"

/-- Get the codomain/target of a pi-type.
  This definition doesn't instantiate bound variables, and therefore produces a term that is open.
  See note [open expressions]. -/
def piCodomain : Expr → Expr
| forallE n t b d => piCodomain b
| e => e

/-- Get the binders and codomain of a pi-type.
  This definition doesn't instantiate bound variables, and therefore produces a term that is open.
  See note [open expressions]. -/
def piBinders : Expr → List Binder × Expr
| forallE n t b d => let (l, e) := piBinders b; (⟨n, d.binderInfo, t⟩ :: l, e)
| e => ([], e)

end Expr

end Lean
