/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis,
Floris van Doorn, E.W.Ayers, Arthur Paulino
-/
import Lean

/-!
# Additional operations on Expr and related types

This file defines basic operations on the types expr, name, declaration, level, environment.

This file is mostly for non-tactics.
-/

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
def mapPrefix (f : Name → Option Name) (n : Name) : Name := Id.run do
  if let some n' := f n then return n'
  match n with
  | anonymous => anonymous
  | str n' s => mkStr (mapPrefix f n') s
  | num n' i => mkNum (mapPrefix f n') i

end Name


namespace ConstantInfo

def isDef : ConstantInfo → Bool
  | defnInfo _ => true
  | _          => false

def isThm : ConstantInfo → Bool
  | thmInfo _ => true
  | _          => false

def updateName : ConstantInfo → Name → ConstantInfo
  | defnInfo   info, n => defnInfo   {info with name := n}
  | axiomInfo  info, n => axiomInfo  {info with name := n}
  | thmInfo    info, n => thmInfo    {info with name := n}
  | opaqueInfo info, n => opaqueInfo {info with name := n}
  | quotInfo   info, n => quotInfo   {info with name := n}
  | inductInfo info, n => inductInfo {info with name := n}
  | ctorInfo   info, n => ctorInfo   {info with name := n}
  | recInfo    info, n => recInfo    {info with name := n}

def updateType : ConstantInfo → Expr → ConstantInfo
  | defnInfo   info, y => defnInfo   {info with type := y}
  | axiomInfo  info, y => axiomInfo  {info with type := y}
  | thmInfo    info, y => thmInfo    {info with type := y}
  | opaqueInfo info, y => opaqueInfo {info with type := y}
  | quotInfo   info, y => quotInfo   {info with type := y}
  | inductInfo info, y => inductInfo {info with type := y}
  | ctorInfo   info, y => ctorInfo   {info with type := y}
  | recInfo    info, y => recInfo    {info with type := y}

def updateValue : ConstantInfo → Expr → ConstantInfo
  | defnInfo   info, v => defnInfo   {info with value := v}
  | thmInfo    info, v => thmInfo    {info with value := v}
  | opaqueInfo info, v => opaqueInfo {info with value := v}
  | d, _ => d

def toDeclaration! : ConstantInfo → Declaration
  | defnInfo   info => Declaration.defnDecl info
  | thmInfo    info => Declaration.thmDecl     info
  | axiomInfo  info => Declaration.axiomDecl   info
  | opaqueInfo info => Declaration.opaqueDecl  info
  | quotInfo   _ => panic! "toDeclaration for quotInfo not implemented"
  | inductInfo _ => panic! "toDeclaration for inductInfo not implemented"
  | ctorInfo   _ => panic! "toDeclaration for ctorInfo not implemented"
  | recInfo    _ => panic! "toDeclaration for recInfo not implemented"

end ConstantInfo

namespace Expr

/-! ### Declarations about `Expr` -/

/-- If the expression is a constant, return that name. Otherwise return `Name.anonymous`. -/
def constName (e : Expr) : Name :=
  e.constName?.getD Name.anonymous

def bvarIdx? : Expr → Option Nat
  | bvar idx => some idx
  | _        => none

/-- Return the function (name) and arguments of an application. -/
def getAppFnArgs (e : Expr) : Name × Array Expr :=
  withApp e λ e a => (e.constName, a)

/-- Turn an expression that is a natural number literal into a natural number. -/
def natLit! : Expr → Nat
  | lit (Literal.natVal v) => v
  | _                      => panic! "nat literal expected"

/-- Returns a `NameSet` of all constants in an expression starting with a certain prefix. -/
def listNamesWithPrefix (pre : Name) (e : Expr) : NameSet :=
  e.foldConsts ∅ fun n l => if n.getPrefix == pre then l.insert n else l

def modifyAppArgM [Functor M] [Pure M] (modifier : Expr → M Expr) : Expr → M Expr
  | app f a => mkApp f <$> modifier a
  | e => pure e

def modifyAppArg (modifier : Expr → Expr) : Expr → Expr :=
  modifyAppArgM (M := Id) modifier

def modifyRevArg (modifier : Expr → Expr): Nat → Expr  → Expr
  | 0 => modifyAppArg modifier
  | (i+1) => modifyAppArg (modifyRevArg modifier i)

/-- Given `f a₀ a₁ ... aₙ₋₁`, runs `modifier` on the `i`th argument or returns the original expression if out of bounds. -/
def modifyArg (modifier : Expr → Expr) (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Expr :=
  modifyRevArg modifier (n - i - 1) e

def getRevArg? : Expr → Nat → Option Expr
  | app _ a, 0   => a
  | app f _, i+1 => getRevArg! f i
  | _,       _   => none

/-- Given `f a₀ a₁ ... aₙ₋₁`, returns the `i`th argument or none if out of bounds. -/
def getArg? (e : Expr) (i : Nat) (n := e.getAppNumArgs): Option Expr :=
  getRevArg? e (n - i - 1)

/-- Given `f a₀ a₁ ... aₙ₋₁`, runs `modifier` on the `i`th argument.
An argument `n` may be provided which says how many arguments we are expecting `e` to have. -/
def modifyArgM [Monad M] (modifier : Expr → M Expr) (e : Expr) (i : Nat) (n := e.getAppNumArgs) : M Expr := do
  let some a := getArg? e i | return e
  let a ← modifier a
  return modifyArg (fun _ => a) e i n

/-- Traverses an expression `e` and renames bound variables named `old` to `new`. -/
def renameBVar (e : Expr) (old new : Name) : Expr :=
  match e with
  | app fn arg => app (fn.renameBVar old new) (arg.renameBVar old new)
  | lam n ty bd bi =>
    lam (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | forallE n ty bd bi =>
    forallE (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | e => e

end Expr

end Lean
