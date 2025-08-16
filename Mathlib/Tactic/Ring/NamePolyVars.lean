/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Kenny Lau
-/
import Lean

/-!
The command `#name_poly_vars` names variables in any combination of `Polynomial`, `MvPolynomial`,
`RatFunc`, `PowerSeries`, `MvPowerSeries`, and `LaurentSeries`, where the `Mv` is restricted to
`Fin n`.

The notation introduced by `#name_poly_vars` is local.

Usage:

```lean
variable (R : Type) [CommRing R]

name_poly_vars R[[X,Y]][t]⸨a⸩(u)

#check X -- X : R[[X,Y]][t]⸨a⸩(u)
#check t -- t : R[[X,Y]][t]⸨a⸩(u)
```

For the edge case of `MvPolynomial (Fin 1) R`, use the syntax `R[u,]` with a trailing comma.

To register new polynomial-like functors, use the command `#register_poly_vars`:

```lean
#register_poly_vars "[" X "]" Polynomial Polynomial.C Polynomial.X
#register_poly_vars "[" X, ... "]" MvPolynomial MvPolynomial.C MvPolynomial.X
```

The registration is global and should only be done once for each functor.
-/

open Lean Elab Command

initialize registerTraceClass `name_poly_vars

namespace Mathlib.Tactic.NamePolyVars

structure NotationSignature where
  opening : String
  closing : String
  mv? : Bool
deriving Inhabited, DecidableEq, Hashable, Repr

structure Notation where
  opening : String
  closing : String
  mv? : Bool
  type : Term
  c : Term
  x : Term
deriving Inhabited, Repr

def Notation.signature (n : Notation) : NotationSignature where
  opening := n.opening
  closing := n.closing
  mv? := n.mv?

/-- The category that in the future will contain things like:
`syntax "[" vars "]" : polyesque_notation` -/
declare_syntax_cat polyesque_notation

abbrev PolyesqueNotation : Type := TSyntax `polyesque_notation

syntax vars := sepBy(ident,",",",",allowTrailingSep)

-- right = mv
def parseVars : TSyntax ``vars → Option (Ident ⊕ Array Ident)
  | `(vars| $var:ident) => pure (Sum.inl var)
  | `(vars| $var:ident,) => pure (Sum.inr #[var])
  | `(vars| $vars:ident,*) => pure (Sum.inr vars.getElems)
  | _ => .none

syntax var_decl := &"X" ("," "...")?

abbrev VarDecl : Type := TSyntax ``var_decl

def _root_.Lean.TSyntax.varDeclToBool : VarDecl → Bool
  | `(var_decl| X) => false
  | `(var_decl| X, ...) => true
  | _ => false

def _root_.Bool.toVarDecl : Bool → String
  | false => "X"
  | true => "X, ..."

/-- An unambiguous term declaration, which is either an identifier or a term enclosed in brackets -/
syntax term_decl := ident <|> ("(" term ")")

abbrev TermDecl : Type := TSyntax ``term_decl

/-- Convert a `TermDecl` to a term. -/
def _root_.Lean.TSyntax.term : TermDecl → Term
  | `(term_decl| $k:ident) => { raw := k.raw }
  | `(term_decl| ($u:term)) => u
  | _ => default

def _root_.Lean.TSyntax.rawTermDecl : TermDecl → String
  | `(term_decl| $k:ident) => s!"{k.getId}"
  | `(term_decl| ($u:term)) => s!"({u.raw.prettyPrint.pretty'})"
  | _ => ""

abbrev NotationTable := Std.HashMap NotationSignature Notation

abbrev NotationTableExt := SimpleScopedEnvExtension Notation NotationTable

initialize notationTableExt : NotationTableExt ← registerSimpleScopedEnvExtension <|
  { addEntry old new := insert (new.signature, new) old
    initial := {} }

/-- Usage:

```lean
register_poly_vars "[[" X "]]" Polynomial Polynomial.C Polynomial.X
register_poly_vars "[[" X, ... "]]" MvPowerSeries (MvPowerSeries.C _ _) MvPowerSeries.X
```
-/
syntax (name := register)
  "#register_poly_vars " str var_decl str term_decl term_decl term_decl : command

@[command_elab register]
def registerElab : CommandElab := fun stx ↦ do
  let `(command|#register_poly_vars $opening:str $mv?:var_decl $closing:str
      $type:term_decl $c:term_decl $x:term_decl) := stx
    | throwError m!"Unrecognised syntax: {stx}"
  have opening := opening.getString
  have closing := closing.getString
  have declared := notationTableExt.getState (← getEnv)
  if declared.keys.all fun s ↦ (s.opening, s.closing) ≠ (opening, closing) then
    -- Extend the polyesque_notation to include the new notation
    -- e.g. for polynomial, `syntax "[" vars "]" : polyesque_notation`
    elabCommand <| ← `(command|syntax $(quote opening):str vars $(quote closing):str :
      polyesque_notation)
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

abbrev Body : Type := Notation × (Ident ⊕ Array Ident)

def _root_.Lean.TSyntax.polyesqueNotation (p : PolyesqueNotation) : CoreM Body := do
  let .node _ _ #[.atom _ opening, v, .atom _ closing] := p.raw
    | throwError m!"Unrecognised polynomial-like notation: {p}"
  let `(vars|$v) := v
  let .some v := parseVars v
    | throwError m!"Unrecognised variable notation: {v}"
  have mv? : Bool := v.isRight
  let .some n := (notationTableExt.getState (← getEnv)).get? ⟨opening, closing, mv?⟩
    | throwError s!"Unrecognised polynomial-like syntax: {opening} {mv?.toVarDecl} {closing}"
  return (n, v)

def Body.mkType (b : Body) (type : Term) : CoreM Term :=
  match b.snd with
  | Sum.inl _ => `($b.fst.type $type)
  | Sum.inr ns => `($b.fst.type (Fin $(quote ns.size)) $type)

def Body.mkC (b : Body) (term : Term) : CoreM Term :=
  `($b.fst.c $term)

def Body.mkX (b : Body) : CoreM (Array (Ident × Term)) :=
  match b.snd with
  | Sum.inl n => return #[(n, b.fst.x)]
  | Sum.inr ns => ns.zipIdx.mapM fun n ↦ return (n.fst, ← `($b.fst.x $(quote n.snd)))

def Body.raw (b : Body) : String :=
  b.fst.opening ++
  (match b.snd with
    | Sum.inl n => s!"{n.getId}"
    | Sum.inr ns => ",".intercalate (ns.map fun n ↦ s!"{n.getId}").toList) ++
  b.fst.closing

syntax polyesque := term_decl noWs polyesque_notation+

abbrev Polyesque : Type := TSyntax ``polyesque

declare_syntax_cat polyesque_declared

syntax (name := polyesqueTerm) term_decl noWs polyesque_declared : term

def parseDeclared (stx : TSyntax `polyesque_declared) : String :=
  match stx.raw with
  | .node _ _ #[.atom _ str] => str
  | _ => ""

syntax (name := declare) "#name_poly_vars " polyesque : command

abbrev Declared := Std.HashMap String Term

abbrev DeclaredExt := SimpleScopedEnvExtension (String × Term) Declared

initialize declaredExt : DeclaredExt ← registerSimpleScopedEnvExtension <|
  { addEntry old new := insert new old
    initial := {} }

def _root_.Lean.TSyntax.parsePolyesqueRaw (p : Polyesque) : CoreM String := do
  let `(polyesque| $head:term_decl$body:polyesque_notation*) := p
    | throwError m!"Unrecognised syntax: {p}"
  return head.rawTermDecl ++ .join (← body.mapM fun p ↦ return (← p.polyesqueNotation).raw).toList

def _root_.Lean.TSyntax.parsePolyesqueFull (p : Polyesque) :
    CoreM (String × String × Term × Array (Ident × Term)) := do
  let `(polyesque| $head:term_decl$body:polyesque_notation*) := p
    | throwError m!"Unrecognised syntax: {p}"
  let mut type : Term := head.term
  let mut terms : Array (Ident × Term) := #[]
  let mut raw : String := ""
  for p in body do
    let b ← p.polyesqueNotation
    type ← b.mkType type
    terms := (← terms.mapM fun it ↦ return (it.fst, ← b.mkC it.snd)) ++ (← b.mkX)
    raw := raw ++ b.raw
  return (head.rawTermDecl, raw, type, terms)

@[command_elab declare]
def elabDeclarePolyVars : CommandElab := fun stx => do
  let `(command|#name_poly_vars $p:polyesque) := stx
    | throwError m!"Wrong command syntax: {stx}"
  let (headStr, bodyStr, type, terms) ← liftCoreM p.parsePolyesqueFull
  have raw := headStr ++ bodyStr
  trace[name_poly_vars] m!"Declaring polynomial-like notation: {raw}"
  trace[name_poly_vars] m!"Result: {type}"
  trace[name_poly_vars] m!"Terms:"
  for (i, t) in terms do
    elabCommand <| ← `(command| local notation $(quote s!"{i.getId}"):str => ($t : $type))
    trace[name_poly_vars] m!"  {i.getId} : {t}"
  elabCommand <| ← `(command| local syntax $(quote bodyStr):str : polyesque_declared)
  declaredExt.add (raw, type) .local

@[term_elab polyesqueTerm]
def polyesqueElab : Term.TermElab := fun stx e => do
  let `(polyesqueTerm| $head:term_decl$body:polyesque_declared) := stx
    | throwError m!"Unrecognised syntax: {stx}"
  have raw := head.rawTermDecl ++ parseDeclared body
  let .some type := (declaredExt.getState (← getEnv)).get? raw
    | throwError m!"Undeclared polynomial-like notation: {raw}"
  -- let .some type := (declaredExt.getState (← getEnv)).get? (head.rawTermDecl ++ body.getString)
  --   | throwError m!"Undeclared polynomial-like notation: {raw}"
  trace[name_poly_vars] m!"Retrieving polynomial-like notation: {raw}"
  trace[name_poly_vars] m!"Result: {type}"
  Term.elabTerm type e

end Mathlib.Tactic.NamePolyVars
