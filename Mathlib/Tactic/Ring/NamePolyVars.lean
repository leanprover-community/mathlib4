/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Kenny Lau, Jovan Gerbscheid
-/
import Mathlib.Util.Notation3

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

open Lean Elab Command Parser.Tactic PrettyPrinter.Delaborator

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
deriving Inhabited, DecidableEq, Hashable

/-- The content of a polynomial-like notation, consisting of the `type` (e.g. `Polynomial`), the
constant term `c` (e.g. `Polynomial.C`), and the formal variable(s) `x` (e.g. `Polynomial.X`). -/
structure Notation where
  /-- The polynomial-like type of the notation. -/
  type : Term
  /-- The constant term of the notation. -/
  c : Term
  /-- The formal variable(s) of the notation. -/
  x : Term
deriving Inhabited

/-- A syntax category for the opening bracket of a polynomial-like notation. -/
declare_syntax_cat poly_opening

/-- A syntax category for the closing bracket of a polynomial-like notation. -/
declare_syntax_cat poly_closing

/-- The category of polynomial-like variables. -/
declare_syntax_cat poly_var

/-- A polynomial-like variable. -/
abbrev PolyVar : Type := TSyntax `poly_var

/-- `poly_opening`, `poly_closing`, and `poly_var` are syntax categories that will all
contain only single atoms, and this function extracts the `String` of the single atoms. -/
def Lean.TSyntax.toString {n : Name} (v : TSyntax n) : String :=
  match v.raw with
  | .node _ _ #[.atom _ str] => str
  | _ => ""

/-- A list of variables in a polynomial-like notation. The special case of one-variable
multivariate notation is `X,` with a trailing comma. -/
syntax poly_vars := sepBy(poly_var, ",", ",", allowTrailingSep)

/-- A list of variables in a polynomial-like notation. The special case of one-variable
multivariate notation is `X,` with a trailing comma. -/
syntax poly_idents := sepBy(ident, ",", ",", allowTrailingSep)

/-- Parse `poly_idents` into either a single identifier or an array of identifiers. -/
def Lean.TSyntax.parsePolyIdents : TSyntax ``poly_idents → Option (String ⊕ Array String)
  | `(poly_idents| $v:ident) => pure (Sum.inl v.getId.toString)
  | `(poly_idents| $vs:ident,*) => pure (Sum.inr (vs.getElems.map fun v ↦ v.getId.toString))
  | _ => .none

-- An unambiguously bracketed term, which is `_`, an identifier, or a term enclosed in brackets.
-- This has no doc-string because that would show up in hover information.
syntax term_decl := hole <|> ident <|> ("(" term ")")
attribute [nolint docBlame] term_decl

/-- A type synonym for a term declaration, used to avoid ambiguity in the syntax. -/
abbrev TermDecl : Type := TSyntax ``term_decl

/-- Convert a `TermDecl` to a term. -/
def Lean.TSyntax.term : TermDecl → Term
  | `(term_decl| $u:hole) => ⟨u.raw⟩
  | `(term_decl| $k:ident) => ⟨k.raw⟩
  | `(term_decl| ($u:term)) => u
  | _ => default

/-- The table for storing registered polynomial-like notations. We use the signature for lookup. -/
abbrev NotationTable := Std.HashMap NotationSignature Notation

/-- The environment extension for registered polynomial-like notations. -/
abbrev NotationTableExt := SimpleScopedEnvExtension (NotationSignature × Notation) NotationTable

/-- Initialize the notation table extension. -/
initialize notationTableExt : NotationTableExt ← registerSimpleScopedEnvExtension <|
  { addEntry old new := insert new old
    initial := {} }

/-- The config for whether the notation is multivariate, stored as a `Bool`, default to `false`. -/
structure MvConfig where
  /-- Whether the notation is multivariate. -/
  mv : Bool := false

/-- Elaborate the multivariable config. -/
declare_command_config_elab elabMvConfig MvConfig

/-- Usage:

```lean
register_poly_vars "[[" "]]" PowerSeries PowerSeries.C PowerSeries.X
register_poly_vars (mv := true) "[[" "]]" MvPowerSeries MvPowerSeries.C MvPowerSeries.X
```
-/
elab "register_poly_vars " mv?:optConfig opening:str closing:str
    type:term:max c:term:max x:term:max : command => do
  have opening := opening.getString
  have closing := closing.getString
  have mv? := (← elabMvConfig mv?).mv
  have declared := notationTableExt.getState (← getEnv)
  if declared.keys.all (·.opening ≠ opening) then
    elabCommand <| ← `(command|
      /-- An opening bracket of a polynomial-like notation -/
      syntax $(quote opening):str : poly_opening)
  if declared.keys.all (·.closing ≠ closing) then
    elabCommand <| ← `(command|
      /-- A closing bracket of a polynomial-like notation -/
      syntax $(quote closing):str : poly_closing)
  -- register the new syntax to the global table
  trace[name_poly_vars] m!"Registering new syntax: (mv := {mv?}) {opening} {closing}"
  notationTableExt.add ({ opening, closing, mv? }, { type, c, x }) .global
  trace[name_poly_vars] m!"New table size: {(notationTableExt.getState (← getEnv)).size}"

/-- A locally declared polynomial-like variable. -/
syntax poly_var : term

/-- A parsed body for one polynomial-like notation, consisting of the type of the notation
(e.g. `MvPolynomial`) and the array of variable identifiers (or one identifier). -/
structure Body : Type where
  /-- The signature of the notation, which consists of the opening and closing brackets,
  and whether the notation is multivariable. -/
  signature : NotationSignature
  /-- The main notation, which consists of the type, constant, and variable parts. -/
  main : Notation
  /-- The names for the variables. -/
  vars : (String ⊕ Array String)

/-- The syntax for using a declared polynomial-like notation, e.g. `[x,y]` or `[[t]]`, which uses
`poly_var` instead of `ident`. -/
syntax polyesque_notation := atomic(poly_opening poly_vars poly_closing)

/-- The syntax for declaring a polynomial-like notation, e.g. `[x,y]` or `[[t]]`, which uses
`ident` instead of `poly_var`. -/
syntax polyesque_notation_input := atomic(poly_opening poly_idents poly_closing)

/-- Parse a `polyesque_notation_input` into its `Body`, `poly_opening`, and `poly_closing`. -/
def Lean.TSyntax.parsePolyesqueNotationInput (p : TSyntax ``polyesque_notation_input) :
    CoreM (Body × TSyntax `poly_opening × TSyntax `poly_closing) := do
  let `(polyesque_notation_input| $opening:poly_opening $v:poly_idents $closing:poly_closing) := p
    | throwError m!"Unrecognised polynomial-like notation: {p}"
  have openingS := opening.toString
  have closingS := closing.toString
  let some vars := v.parsePolyIdents
    | throwError m!"Unrecognised variable notation: {v}"
  have mv? : Bool := vars.isRight
  let some n := (notationTableExt.getState (← getEnv)).get? ⟨openingS, closingS, mv?⟩
    | throwError s!"Unrecognised polynomial-like syntax: (mv := {mv?}) {opening} {closing}"
  return (⟨⟨openingS, closingS, mv?⟩, n, vars⟩, opening, closing)

/-- Create the type for a polynomial-like notation, e.g. `[a,b]` gives `MvPolynomial (Fin 2) R`,
where `R` is the previous type. -/
def Body.mkType (b : Body) (type : Term) : CommandElabM Term :=
  match b.vars with
  | Sum.inl _ => `($b.main.type $type)
  | Sum.inr ns => do `($b.main.type $(← `(Fin $(quote ns.size))) $type)

/-- Create the constant term for a polynomial-like notation. -/
def Body.mkC (b : Body) (term : Term) : CommandElabM Term :=
  `($b.main.c $term)

/-- Create the formal variable term(s) for a polynomial-like notation. -/
def Body.mkX (b : Body) : CommandElabM (Array (String × Term)) :=
  match b.vars with
  | Sum.inl n => return #[(n, b.main.x)]
  | Sum.inr ns => ns.zipIdx.mapM fun n ↦ return (n.fst, ← `($b.main.x $(quote n.snd)))

/-- The syntax for polynomial-like notations, which is an unambiguous term declaration followed by
one or more polynomial-like notations, e.g. `(Fin 37)[x,y,z][[t]]`. -/
syntax polyesque := term_decl (noWs polyesque_notation)+

/-- The declared notations can be used later as terms. -/
syntax:max polyesque : term

/-- Dynamically build the syntax for a declared polynomial-like notation. -/
def mkBracketStx (opening : TSyntax `poly_opening) (closing : TSyntax `poly_closing) (mv? : Bool)
    (polyVars : Array (TSyntax `poly_var)) : CommandElabM (TSyntax ``polyesque_notation) := do
  let vars ← match mv?, polyVars with
    | true, #[v] => `(poly_vars| $v,)
    | _, _ => `(poly_vars| $(Syntax.TSepArray.ofElems polyVars):poly_var,*)
  `(polyesque_notation| $opening$vars$closing)

/-- Given one segment (e.g. `[x,y]`) of the declaration, extract all the relevant information:
the relevant functor (`MvPolynomial (Fin 2)`), the formal variables, and their meanings. Then,
register the variables (`x` and `y`) as polynomial variables (`poly_var`). -/
def Lean.TSyntax.processAndDeclarePolyesqueNotationInput (p : TSyntax ``polyesque_notation_input)
    (terms : Array (TSyntax `poly_var × Term)) (oldFunctor : Term → CommandElabM Term) :
    CommandElabM (TSyntax ``polyesque_notation × Array (TSyntax `poly_var × Term) ×
      (Term → CommandElabM Term) × Term) := do
  let (b, opening, closing) ← liftCoreM p.parsePolyesqueNotationInput
  let newTerms : Array (TSyntax `poly_var × Term) ← (← b.mkX).mapM fun (s, t) ↦ do
    -- Declares the new formal variables as `poly_var`.
    let kind ← elabSyntax <| ← `(command| local syntax $(quote s):str : poly_var)
    return (⟨mkNode kind #[mkAtom s]⟩, t)
  let bracketStx ← mkBracketStx opening closing b.1.mv? (newTerms.map (·.1))
  let terms ← terms.mapM fun (v, t) ↦ return (v, ← b.mkC t)
  let newFunctor := oldFunctor >=> b.mkType
  return (bracketStx, terms ++ newTerms, newFunctor, b.main.type)

/-- A helper function to elaborate macro rules and trace their declarations. -/
def elabMacroRulesAndTrace (p : TSyntax ``polyesque) (t : Term) : CommandElabM Unit := do
  trace[name_poly_vars] m!"Declaring polynomial-like notation: {p}\nResult: {t}"
  elabCommand <| ← `(command| local macro_rules | `($p:polyesque) => `($t))

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
elab "name_poly_vars " head:term_decl body:(noWs polyesque_notation_input)+ : command => do
  let mut terms : Array (TSyntax `poly_var × Term) := #[]
  let mut bodyVar : Array (TSyntax ``polyesque_notation) := #[]
  let mut functor : Term → CommandElabM Term := pure
  let mut lastHead : Term := default
  for p in body do
    let processed ← p.processAndDeclarePolyesqueNotationInput terms functor
    (terms, functor, lastHead) := processed.2
    bodyVar := bodyVar.push processed.1
  have body := Syntax.TSepArray.ofElems (sep := "") bodyVar
  let typeIdent ← functor (← `($$i:ident))
  let polyesqueIdent ← `(polyesque| $$i:ident$body:polyesque_notation*)
  let typeTerm ← functor (← `($$t:term))
  let polyesqueTerm ← `(polyesque| ($$t:term)$body:polyesque_notation*)
  let type : Term := ← match head with
  | `(term_decl| $_:hole) => do
    elabMacroRulesAndTrace (← `(polyesque| $$h:hole$body:polyesque_notation*))
      (← functor (← `($$h:hole)))
    elabMacroRulesAndTrace polyesqueIdent typeIdent
    elabMacroRulesAndTrace polyesqueTerm typeTerm
    -- if the head of the term is a constant, then deploy the unexpander.
    if let `($c:ident) := lastHead then
      trace[name_poly_vars] m!"Declaring unexpander for {c}"
      elabCommand <| ← `(command|
        @[local app_unexpander $c]
        private aux_def unexpand : Lean.PrettyPrinter.Unexpander := fun
          | `($typeIdent) => `($polyesqueIdent:polyesque)
          | `($typeTerm) => `($polyesqueTerm:polyesque)
          | _ => throw ())
    functor (← `(_))
  | _ => do
    let type ← functor head.term
    let polyesque ← `(polyesque| $head$body:polyesque_notation*)
    elabMacroRulesAndTrace polyesque type
    -- if the head of the term is a constant, then deploy the unexpander.
    if let `($c:ident) := lastHead then
      trace[name_poly_vars] m!"Declaring unexpander for {c}"
      match head with
      | `(term_decl| $R:ident) => do
        elabCommand <| ← `(command|
          @[local app_unexpander $c]
          private aux_def unexpand : Lean.PrettyPrinter.Unexpander := fun
            | `($typeIdent) => match i with
              | `($R) => `($polyesqueIdent:polyesque)
              | _ => throw ()
            | _ => throw ())
      | `(term_decl| ($R:term)) => do
        elabCommand <| ← `(command|
          @[local app_unexpander $c]
          private aux_def unexpand : Lean.PrettyPrinter.Unexpander := fun
            | `($typeTerm) => match t with
              | `($R) => `($polyesqueTerm:polyesque)
              | _ => throw ()
            | _ => throw ())
      | _ => pure ()
    return type
  for (v, t) in terms do
    let val ← `(($t : $type))
    elabCommand <| ← `(command| local macro_rules | `($v:poly_var) => `($val))
    trace[name_poly_vars] m!"Declaring polyesque variable {v} := {t}"
    -- The following code is essentially copied from the `notation3` implementation
    let some (keys, matcher) ←
      runTermElabM fun _ => (Notation3.mkExprMatcher val #[]).run | continue
    for key in keys do
      let bodyCore ← `($matcher Notation3.MatchState.empty >>= fun _ => `($v:poly_var))
      let body ← match key with
        | .app _ arity => `(withOverApp $(quote arity) $bodyCore)
        | _            => pure bodyCore
      elabCommand <| ← `(command|
        /-- Pretty printer defined by `name_poly_vars` command. -/
        @[local delab $(mkIdent key.key)]
        private aux_def delab_app : Delab :=
          whenPPOption getPPNotation <| whenNotPPOption getPPExplicit <| $body)

end Mathlib.Tactic.NamePolyVars
