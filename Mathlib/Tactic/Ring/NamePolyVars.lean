/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Kenny Lau
-/
import Lean

/-!
The command `name_poly_vars` names variables in any combination of `Polynomial`, `MvPolynomial`,
`RatFunc`, `PowerSeries`, `MvPowerSeries`, and `LaurentSeries`, where the `Mv` is restricted to
`Fin n`.

The notation introduced by `name_poly_vars` is local.

Usage:

```lean
variable (R : Type) [CommRing R]

name_poly_vars R[[X,Y]][t]⸨a⸩(u)

#check X -- X : R[[X,Y]][t]⸨a⸩(u)
#check t -- t : R[[X,Y]][t]⸨a⸩(u)
```

For the edge case of `MvPolynomial (Fin 1) R`, use the syntax `R[u,]` with a trailing comma.

To register new polynomial-like functors, use the command `register_poly_vars`:

```lean
register_poly_vars "[" X "]" Polynomial Polynomial.C Polynomial.X
register_poly_vars "[" X, ... "]" MvPolynomial MvPolynomial.C MvPolynomial.X
```

The registration is global and should only be done once for each functor.
-/

open Lean Elab Command

initialize registerTraceClass `name_poly_vars

namespace Mathlib.Tactic.NamePolyVars

open Mathlib.Tactic.NamePolyVars

/-- The signature of a polynomial-like notation, consisting of the opening and closing brackets,
and a `Bool` to declare if it is multivariate. -/
structure NotationSignature where
  /-- The opening bracket. -/
  opening : String
  /-- The closing bracket. -/
  closing : String
  /-- Whether the notation is multivariate. -/
  mv? : Bool
deriving Inhabited, DecidableEq, Hashable, Repr

/-- A polynomial-like notation, consisting of the opening and closing brackets, a `Bool` to declare
if it is multivariate, the `type` (e.g. `Polynomial`), the constant term `c` (e.g. `Polynomial.C`),
and the formal variable(s) `x` (e.g. `Polynomial.X`). -/
structure Notation where
  /-- The opening bracket. -/
  opening : String
  /-- The closing bracket. -/
  closing : String
  /-- Whether the notation is multivariate. -/
  mv? : Bool
  /-- The polynomial-like type of the notation. -/
  type : Term
  /-- The constant term of the notation. -/
  c : Term
  /-- The formal variable(s) of the notation. -/
  x : Term
deriving Inhabited, Repr

/-- Get the signature of a polynomial-like notation. -/
def Notation.signature (n : Notation) : NotationSignature where
  opening := n.opening
  closing := n.closing
  mv? := n.mv?

/-- The category that in the future will contain things like:
`syntax "[" vars "]" : polyesque_notation` -/
declare_syntax_cat polyesque_notation

/-- A polynomial-like notation. -/
abbrev PolyesqueNotation : Type := TSyntax `polyesque_notation

/-- A syntax for variables in a polynomial-like notation. The special case of one-variable
multivariate notation is `X,` with a trailing comma. -/
syntax vars := sepBy(ident,",",",",allowTrailingSep)

/-- Parse variables in a polynomial-like notation. One-variable goes to `Sum.inl`, and multivariate
goes to `Sum.inr`. -/
def parseVars : TSyntax ``vars → Option (Ident ⊕ Array Ident)
  | `(vars| $var:ident) => pure (Sum.inl var)
  | `(vars| $var:ident,) => pure (Sum.inr #[var])
  | `(vars| $vars:ident,*) => pure (Sum.inr vars.getElems)
  | _ => .none

/-- A syntax to declare whether the polynomial notation is for one-variable or multivariate. -/
syntax var_decl := &"X" ("," "...")?

/-- The syntax for variable declarations in a polynomial-like notation. -/
abbrev VarDecl : Type := TSyntax ``var_decl

/-- The parser for whether the polynomial notation is for one-variable or multivariate. -/
def Lean.TSyntax.varDeclToBool : VarDecl → Bool
  | `(var_decl| X) => false
  | `(var_decl| X, ...) => true
  | _ => false

/-- Convert a `Bool` to a variable declaration. -/
def Bool.toVarDecl : Bool → String
  | false => "X"
  | true => "X, ..."

/-- An unambiguous term declaration, which is `_`, an identifier, or a term enclosed in brackets -/
syntax term_decl := hole <|> ident <|> ("(" term ")")

/-- A type synonym for a term declaration, used to avoid ambiguity in the syntax. -/
abbrev TermDecl : Type := TSyntax ``term_decl

/-- Convert a `TermDecl` to a term. -/
def Lean.TSyntax.term : TermDecl → Term
  | `(term_decl| $u:hole) => ⟨u.raw⟩
  | `(term_decl| $k:ident) => ⟨k.raw⟩
  | `(term_decl| ($u:term)) => u
  | _ => default

/-- Convert a `TermDecl` to a string. -/
def Lean.TSyntax.rawTermDecl : TermDecl → String
  | `(term_decl| $_:hole) => "_"
  | `(term_decl| $k:ident) => s!"{k.getId}"
  | `(term_decl| ($u:term)) => s!"({u.raw.prettyPrint.pretty'})"
  | _ => ""

/-- The table for storing registered polynomial-like notations. We use the signature for lookup. -/
abbrev NotationTable := Std.HashMap NotationSignature Notation

/-- The environmental extension for registered polynomial-like notations. -/
abbrev NotationTableExt := SimpleScopedEnvExtension Notation NotationTable

/-- Initialize the notation table extension. -/
initialize notationTableExt : NotationTableExt ← registerSimpleScopedEnvExtension <|
  { addEntry old new := insert (new.signature, new) old
    initial := {} }

/-- Usage:

```lean
register_poly_vars "[[" X "]]" PowerSeries (PowerSeries.C _) PowerSeries.X
register_poly_vars "[[" X, ... "]]" MvPowerSeries (MvPowerSeries.C _ _) MvPowerSeries.X
```
-/
syntax (name := register)
  "register_poly_vars " str var_decl str term_decl term_decl term_decl : command

/-- Elaborate the `register_poly_vars` command. -/
@[command_elab register]
def registerElab : CommandElab := fun stx ↦ do
  let `(command|register_poly_vars $opening:str $mv?:var_decl $closing:str
      $type:term_decl $c:term_decl $x:term_decl) := stx
    | throwError m!"Unrecognised syntax: {stx}"
  have opening := opening.getString
  have closing := closing.getString
  have declared := notationTableExt.getState (← getEnv)
  if declared.keys.all fun s ↦ (s.opening, s.closing) ≠ (opening, closing) then
    -- Extend the polyesque_notation to include the new notation
    -- e.g. for polynomial, `syntax "[" vars "]" : polyesque_notation`
    elabCommand <| ← `(command|/-- Register a polynomial-like notation. -/
      syntax $(quote opening):str vars $(quote closing):str : polyesque_notation)
  -- register the new syntax to the global table
  trace[name_poly_vars] m!"Registering new syntax: {opening} {mv?} {closing}"
  notationTableExt.add
    { opening := opening
      closing := closing
      mv? := mv?.varDeclToBool
      type := type.term
      c := c.term
      x := x.term }
    .global
  trace[name_poly_vars] m!"New table size: {(notationTableExt.getState (← getEnv)).size}"

/-- A parsed body for one polynomial-like notation, consisting of the type of the notation
(e.g. `MvPolynomial`) and the array of variable identifiers (or one identifier). -/
abbrev Body : Type := Notation × (Ident ⊕ Array Ident)

/-- Get the `Body` from a polynomial-like notation. -/
def Lean.TSyntax.polyesqueNotation (p : PolyesqueNotation) : CoreM Body := do
  let .node _ _ #[.atom _ opening, v, .atom _ closing] := p.raw
    | throwError m!"Unrecognised polynomial-like notation: {p}"
  let `(vars|$v) := v
  let .some v := parseVars v
    | throwError m!"Unrecognised variable notation: {v}"
  have mv? : Bool := v.isRight
  let .some n := (notationTableExt.getState (← getEnv)).get? ⟨opening, closing, mv?⟩
    | throwError s!"Unrecognised polynomial-like syntax: {opening} {mv?.toVarDecl} {closing}"
  return (n, v)

/-- Create the functor for a polynomial-like notation, e.g. `[a,b]` gives `MvPolynomial (Fin 2)`. -/
def Body.mkFunctor (b : Body) : CoreM Term :=
  match b.snd with
  | Sum.inl _ => `($b.fst.type)
  | Sum.inr ns => `($b.fst.type (Fin $(quote ns.size)))

/-- Create the constant term for a polynomial-like notation. -/
def Body.mkC (b : Body) (term : Term) : CoreM Term :=
  `($b.fst.c $term)

/-- Create the formal variable term(s) for a polynomial-like notation. -/
def Body.mkX (b : Body) : CoreM (Array (Ident × Term)) :=
  match b.snd with
  | Sum.inl n => return #[(n, b.fst.x)]
  | Sum.inr ns => ns.zipIdx.mapM fun n ↦ return (n.fst, ← `($b.fst.x $(quote n.snd)))

/-- Convert the notation to a raw string. -/
def Body.raw (b : Body) : String :=
  b.fst.opening ++
  (match b.snd with
    | Sum.inl n => s!"{n.getId}"
    | Sum.inr ns => ",".intercalate (ns.map fun n ↦ s!"{n.getId}").toList) ++
  b.fst.closing

/-- The syntax for polynomial-like notations, which is an unambiguous term declaration followed by
one or more polynomial-like notations, e.g. `(Fin 37)[x,y,z][[t]]`. -/
syntax polyesque := term_decl noWs polyesque_notation+

/-- The type of polynomial-like syntaxes. -/
abbrev Polyesque : Type := TSyntax ``polyesque

/-- A syntax category for declared polynomial-like notations, stored as raw strings literals.
For example, after `(Fin 37)[x,y,z]` is declared, this will store the string literal `"[x,y,z]"`.
This is used to retrieve the declared notation, e.g. `(Fin 37)[x,y,z]` as a term will now be parsed
as the term declaration `(Fin 37)` followed by the atom `"[x,y,z]"`. -/
declare_syntax_cat polyesque_declared

/-- The syntax category for retrieving declared notations, which is an umambiguous term declaration
followed by a declared polynomial-like notation, e.g. `(Fin 37)` followed by `"[x,y,z][[t]]"`. -/
syntax (name := polyesqueTerm) term_decl noWs polyesque_declared : term

/-- Parse a declared polynomial-like notation. -/
def parseDeclared (stx : TSyntax `polyesque_declared) : String :=
  match stx.raw with
  | .node _ _ #[.atom _ str] => str
  | _ => ""

/-- Declare a local polynomial-like notation. Usage:
```lean
name_poly_vars (Fin 37)[x,y,z][[t]]
#check x
#check t
#check (Fin 37)[x,y,z][[t]]
```

Use `_` to declare it for all base rings. Usage:
```lean
name_poly_vars _[a,b,c,d]
#check R[a,b,c,d]
#check S[a,b,c,d]
```
-/
syntax (name := declare) "name_poly_vars " polyesque : command

/-- The table to store local polynomial-like notations, indexed by the raw string representation.
If the head is a hole `_`, then the array of functors will be stored. Otherwise, we store the
one resulting term.

E.g. for `_[a,b][c]`, we store the array ``#[`(MvPolynomial (Fin 2)), `(Polynomial)]``;

for `R[a,b][c]`, we store the one term `Polynomial (MvPolynomial (Fin 2) R))` -/
abbrev Declared := Std.HashMap String (Term ⊕ Array Term)

/-- The environmental extension to locally store polynomial-like notations. -/
abbrev DeclaredExt := SimpleScopedEnvExtension (String × (Term ⊕ Array Term)) Declared

/-- A local instance to help prove that `DeclaredExt` is inhabited. -/
@[local instance] def inhabitedSum {α β : Type _} [Inhabited α] : Inhabited (α ⊕ β) :=
  ⟨.inl default⟩

/-- Initialise the environmental extension to locally store polynomial-like notations. -/
initialize declaredExt : DeclaredExt ← registerSimpleScopedEnvExtension <|
  { addEntry old new := insert new old
    initial := {} }

/-- Given a declaration of polynomial-like notation (e.g. `(Fin 37)[x,y,z][[t]]`), parse it fully to
return the head (e.g. `(Fin 37)`), the raw body (e.g. `"[x,y,z][[t]]`"), the total type generated
(e.g. `PowerSeries (MvPolynomial (Fin 3) (Fin 37))`), and the terms corresponding to each declared
identifier (e.g. `x := PowerSeries.C (MvPolynomial.X 0)`).

The head and body are returned as strings here so that they can be stored in a table in the
environment. -/
def Lean.TSyntax.parsePolyesqueFull (p : Polyesque) :
    CoreM (String × String × Bool × Term × Array Term × Array (Ident × Term)) := do
  let `(polyesque| $head:term_decl$body:polyesque_notation*) := p
    | throwError m!"Unrecognised syntax: {p}"
  have isHole : Bool := match head with
    | `(term_decl| $_:hole) => true
    | _ => false
  let mut type : Term := head.term
  let mut funcs : Array Term := #[]
  let mut terms : Array (Ident × Term) := #[]
  let mut bodyStr : String := ""
  for p in body do
    let b ← p.polyesqueNotation
    let func ← b.mkFunctor
    type ← `($func $type)
    funcs := funcs ++ #[func]
    terms := (← terms.mapM fun it ↦ return (it.fst, ← b.mkC it.snd)) ++ (← b.mkX)
    bodyStr := bodyStr ++ b.raw
  return (head.rawTermDecl, bodyStr, isHole, type, funcs, terms)

/-- Elaborate the command `name_poly_vars`. -/
@[command_elab declare]
def elabDeclarePolyVars : CommandElab := fun stx => do
  let `(command|name_poly_vars $p:polyesque) := stx
    | throwError m!"Wrong command syntax: {stx}"
  let (headStr, bodyStr, isHole, type, funcs, terms) ← liftCoreM p.parsePolyesqueFull
  have raw := headStr ++ bodyStr
  trace[«name_poly_vars»] m!"Declaring polynomial-like notation: {raw}"
  trace[«name_poly_vars»] m!"Result: {type}"
  trace[«name_poly_vars»] m!"Terms:"
  for (i, t) in terms do
    elabCommand <| ← `(command| local notation $(quote s!"{i.getId}"):str => ($t : $type))
    trace[«name_poly_vars»] m!"{i.getId} : {t}"
  elabCommand <| ← `(command| local syntax $(quote bodyStr):str : polyesque_declared)
  declaredExt.add (raw, if isHole then Sum.inr funcs else Sum.inl type) .local

/-- Retrieve the polynomial-like notation for a given head and body. -/
def retrievePolyesque (head : TermDecl) (body : String) : Term.TermElabM Term := do
  have d := declaredExt.getState (← getEnv)
  match d.get? (head.rawTermDecl ++ body) with
  | some (Sum.inl type) => return type
  | some (Sum.inr funcs) => funcs.foldlM (fun type func ↦ `($func $type)) head.term
  | none =>
    match d.get? ("_" ++ body) with
    | some (Sum.inl _) => throwError "unreachable"
    | some (Sum.inr funcs) => funcs.foldlM (fun type func ↦ `($func $type)) head.term
    | none => throwError m!"Undeclared polynomial-like notation: {head.rawTermDecl ++ body}"

/-- Elaborate the later references to the polynomial-like notation, e.g. `(Fin 37)[x,y,z][[t]]`. -/
@[term_elab polyesqueTerm]
def polyesqueElab : Term.TermElab := fun stx e => do
  let `(polyesqueTerm| $head:term_decl$body:polyesque_declared) := stx
    | throwError m!"Unrecognised syntax: {stx}"
  have bodyStr := parseDeclared body
  trace[«name_poly_vars»] m!"Retrieving polynomial-like notation: {head.rawTermDecl ++ bodyStr}"
  let type ← retrievePolyesque head bodyStr
  trace[«name_poly_vars»] m!"Result: {type}"
  Term.elabTerm type e

end Mathlib.Tactic.NamePolyVars
