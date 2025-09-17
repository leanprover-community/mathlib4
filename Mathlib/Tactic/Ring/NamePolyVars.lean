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

open Lean Elab Command Parser.Tactic

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
  /-- The polynomial-like type of the notation. -/
  type : Term
  /-- The constant term of the notation. -/
  c : Term
  /-- The formal variable(s) of the notation. -/
  x : Term
deriving Inhabited, Repr

-- /-- The category that in the future will contain things like:
-- `syntax "[" vars "]" : polyesque_notation` -/
-- declare_syntax_cat polyesque_notation

-- /-- A polynomial-like notation. -/
-- abbrev PolyesqueNotation : Type := TSyntax `polyesque_notation

declare_syntax_cat poly_opening

abbrev Opening : Type := TSyntax `poly_opening

declare_syntax_cat poly_closing

abbrev Closing : Type := TSyntax `poly_closing

/-- The category of polynomial-like variables. -/
declare_syntax_cat poly_var

/-- A polynomial-like variable. -/
abbrev PolyVar : Type := TSyntax `poly_var

def Lean.TSyntax.toString {n : Name} (v : TSyntax n) : String :=
  match v.raw with
  | .node _ _ #[.atom _ str] => str
  | _ => ""

def String.toTSyntax {n : Name} (s : String) (kind : SyntaxNodeKind) : TSyntax n :=
  ⟨mkNode kind #[mkAtom s]⟩

/-- A syntax for variables in a polynomial-like notation. The special case of one-variable
multivariate notation is `X,` with a trailing comma. -/
syntax vars := sepBy(poly_var, ",", ",", allowTrailingSep)

/-- Parse variables in a polynomial-like notation. One-variable goes to `Sum.inl`, and multivariate
goes to `Sum.inr`. -/
def Lean.TSyntax.parseVars : TSyntax ``vars → Option (String ⊕ Array String)
  | `(vars| $var:poly_var) => pure (Sum.inl var.toString)
  | `(vars| $var:poly_var,) => pure (Sum.inr #[var.toString])
  | `(vars| $vars:poly_var,*) => pure (Sum.inr (vars.getElems.map Lean.TSyntax.toString))
  | _ => .none

syntax poly_idents := sepBy(ident, ",", ",", allowTrailingSep)

-- def Lean.TSyntax.identToPolyVar : TSyntax `ident → CoreM PolyVar
--   | `(ident| $v:ident) => `(poly_var| $(v.getId.toString.toTSyntax))
--   | _ => default

def Lean.TSyntax.parsePolyIdents : TSyntax ``poly_idents → Option (String ⊕ Array String)
  | `(poly_idents| $v:ident) => pure (Sum.inl v.getId.toString)
  | `(poly_idents| $v:ident,) => pure (Sum.inr #[v.getId.toString])
  | `(poly_idents| $vs:ident,*) => pure (Sum.inr (vs.getElems.map fun v ↦ v.getId.toString))
  | _ => .none

-- def Lean.TSyntax.polyIdentsToVars : TSyntax ``poly_idents → CoreM (TSyntax ``vars)
--   | `(poly_idents| $v:ident) => do `(vars| $(← v.identToPolyVar):poly_var)
--   | `(poly_idents| $v:ident,) => do `(vars| $(← v.identToPolyVar):poly_var,)
--   | `(poly_idents| $vs:ident,*) => do
--       return ⟨.node default default (Syntax.TSepArray.ofElems (sep := ",") <|
--         ← vs.getElems.mapM Lean.TSyntax.identToPolyVar)⟩
--   | _ => `(vars|)

-- /-- A syntax to declare whether the polynomial notation is for one-variable or multivariate. -/
-- syntax mv_decl := ("(" &"mv" ":=" (&"true" <|> &"false") ")")?

-- /-- The syntax for declaring multivariable in a polynomial-like notation. -/
-- abbrev MvDecl : Type := TSyntax ``mv_decl

-- def Lean.TSyntax.mvDeclToBool : MvDecl → Bool
--   | `(mv_decl| (mv := true)) => true
--   | _ => false

-- /-- Convert a `Bool` to a multivariable declaration. -/
-- def Bool.toMvDecl : Bool → String
--   | false => ""
--   | true => " (mv := true)"

/-- An unambiguous term declaration, which is `_`, an identifier, or a term enclosed in brackets -/
syntax term_decl := hole <|> ident <|> ("(" term ")")

/-- A type synonym for a term declaration, used to avoid ambiguity in the syntax. -/
abbrev TermDecl : Type := TSyntax ``term_decl

-- macro t:term_decl : term =>
--   match t with
--   | `($u:hole) => `(term| $u:hole)
--   | `($k:ident) => `(term| $k:ident)
--   | `(($t:term)) => `(term| ($t:term))
--   | _ => default

-- syntax:max term_decl : term

-- macro_rules
--   | `(term_decl| $u:hole) => `($u:hole)
--   | `(term_decl| $k:ident) => `($k:ident)
--   | `(term_decl| ($u:term)) => `(($u:term))

-- elab t:term_decl : term => do
--   match t with
--   | `(term_decl| $u:hole) => Term.elabTerm (← `(_)) _
--   | `(term_decl| $k:ident) => Term.elabTerm (← `($(k.getId))) _

/-- Convert a `TermDecl` to a term. -/
def Lean.TSyntax.term : TermDecl → Term
  | `(term_decl| $u:hole) => ⟨u.raw⟩
  | `(term_decl| $k:ident) => ⟨k.raw⟩
  | `(term_decl| ($u:term)) => u
  | _ => default

-- /-- Convert a `TermDecl` to a string. -/
-- def Lean.TSyntax.rawTermDecl : TermDecl → String
--   | `(term_decl| $_:hole) => "_"
--   | `(term_decl| $k:ident) => s!"{k.getId}"
--   | `(term_decl| ($u:term)) => s!"({u.raw.prettyPrint.pretty'})"
--   | _ => ""

/-- The table for storing registered polynomial-like notations. We use the signature for lookup. -/
abbrev NotationTable := Std.HashMap NotationSignature Notation

/-- The environmental extension for registered polynomial-like notations. -/
abbrev NotationTableExt := SimpleScopedEnvExtension (NotationSignature × Notation) NotationTable

/-- Initialize the notation table extension. -/
initialize notationTableExt : NotationTableExt ← registerSimpleScopedEnvExtension <|
  { addEntry old new := insert (new.1, new.2) old
    initial := {} }

structure MvConfig where
  mv : Bool := false
  deriving Repr

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
  if declared.keys.all fun s ↦ s.opening ≠ opening then
    elabCommand <| ← `(command|/-- Register an open bracket for polynomial-like notation. -/
      syntax $(quote opening):str : poly_opening)
  if declared.keys.all fun s ↦ s.closing ≠ closing then
    elabCommand <| ← `(command|/-- Register a closing bracket for polynomial-like notation. -/
      syntax $(quote closing):str : poly_closing)
  -- register the new syntax to the global table
  trace[name_poly_vars] m!"Registering new syntax: (mv := {mv?}) {opening} {closing}"
  notationTableExt.add
    ({  opening := opening
        closing := closing
        mv? := mv? },
      { type := type
        c := c
        x := x })
    .global
  trace[name_poly_vars] m!"New table size: {(notationTableExt.getState (← getEnv)).size}"

-- syntax (name := register)
--   "register_poly_vars " mv_decl str str term_decl term_decl term_decl : command

-- /-- Elaborate the `register_poly_vars` command. -/
-- @[command_elab register]
-- def registerElab : CommandElab := fun stx ↦ do
--   let `(command|register_poly_vars $mv?:mv_decl $opening:str $closing:str
--       $type:term_decl $c:term_decl $x:term_decl) := stx
--     | throwError m!"Unrecognised syntax: {stx}"
--   have opening := opening.getString
--   have closing := closing.getString
--   have declared := notationTableExt.getState (← getEnv)
--   if declared.keys.all fun s ↦ (s.opening, s.closing) ≠ (opening, closing) then
--     -- Extend the polyesque_notation to include the new notation
--     -- e.g. for polynomial, `syntax "[" vars "]" : polyesque_notation`
--     elabCommand <| ← `(command|/-- Register a polynomial-like notation. -/
--       syntax $(quote opening):str vars $(quote closing):str : polyesque_notation)
--   -- register the new syntax to the global table
--   trace[name_poly_vars] m!"Registering new syntax: {mv?} {opening} {closing}"
--   notationTableExt.add
--     ({  opening := opening
--         closing := closing
--         mv? := mv?.mvDeclToBool },
--       { type := type.term
--         c := c.term
--         x := x.term })
--     .global
--   trace[name_poly_vars] m!"New table size: {(notationTableExt.getState (← getEnv)).size}"

-- /-- A table for storing variable names to their corresponding terms. -/
-- abbrev VarTable := Std.HashMap String Term

-- /-- The environmental extension for storing variable names to their corresponding terms. -/
-- abbrev VarTableExt := SimpleScopedEnvExtension (String × Term) VarTable

-- /-- Initialize the variable table extension. -/
-- initialize varTableExt : VarTableExt ← registerSimpleScopedEnvExtension <|
--   { addEntry old new := insert new old
--     initial := {} }

/-- A locally declared polynomial-like variable. -/
syntax /- (name := poly_var_term) -/ poly_var : term

-- /-- Elaborate a polynomial-like variable. -/
-- @[term_elab poly_var_term]
-- def varTermElab : Term.TermElab := fun stx e => do
--   let `(poly_var_term| $v:poly_var) := stx
--     | throwError m!"Unrecognised syntax: {stx}"
--   let name := v.polyVarToString
--   let d := varTableExt.getState (← getEnv)
--   match d.get? name with
--   | some term => Term.elabTerm term e
--   | none => throwError m!"Undeclared polynomial-like variable: {name}"

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

syntax polyesque_notation := poly_opening vars poly_closing

abbrev PolyesqueNotation : Type := TSyntax ``polyesque_notation

-- /-- Get the `Body` from a polynomial-like notation. -/
-- def Lean.TSyntax.parsePolyesqueNotation (p : PolyesqueNotation) : CoreM Body := do
--   let `(polyesque_notation| $opening:poly_opening $v:vars $closing:poly_closing) := p
--     | throwError m!"Unrecognised polynomial-like notation: {p}"
--   have opening := opening.toString
--   have closing := closing.toString
--   let .some v := parseVars v
--     | throwError m!"Unrecognised variable notation: {v}"
--   have mv? : Bool := v.isRight
--   let .some n := (notationTableExt.getState (← getEnv)).get? ⟨opening, closing, mv?⟩
--     | throwError s!"Unrecognised polynomial-like syntax:{mv?.toMvDecl} {opening} {closing}"
--   return ⟨⟨opening, closing, mv?⟩, n, v⟩

syntax polyesque_notation_input := poly_opening poly_idents poly_closing

abbrev PolyesqueNotationInput : Type := TSyntax ``polyesque_notation_input

def Lean.TSyntax.parsePolyesqueNotationInput (p : PolyesqueNotationInput) :
    CoreM (Body × Opening × Closing) := do
  let `(polyesque_notation_input| $opening:poly_opening $v:poly_idents $closing:poly_closing) := p
    | throwError m!"Unrecognised polynomial-like notation: {p}"
  have openingS := opening.toString
  have closingS := closing.toString
  let .some vars := v.parsePolyIdents
    | throwError m!"Unrecognised variable notation: {v}"
  have mv? : Bool := vars.isRight
  let .some n := (notationTableExt.getState (← getEnv)).get? ⟨openingS, closingS, mv?⟩
    | throwError s!"Unrecognised polynomial-like syntax: (mv := {mv?}) {opening} {closing}"
  return (⟨⟨openingS, closingS, mv?⟩, n, vars⟩, opening, closing)

/-- Create the functor for a polynomial-like notation, e.g. `[a,b]` gives `MvPolynomial (Fin 2)`. -/
def Body.mkFunctor (b : Body) : CoreM Term :=
  match b.vars with
  | Sum.inl _ => `($b.main.type)
  | Sum.inr ns => `($b.main.type (Fin $(quote ns.size)))

/-- Create the constant term for a polynomial-like notation. -/
def Body.mkC (b : Body) (term : Term) : CoreM Term :=
  `($b.main.c $term)

/-- Create the formal variable term(s) for a polynomial-like notation. -/
def Body.mkX (b : Body) : CoreM (Array (String × Term)) :=
  match b.vars with
  | Sum.inl n => return #[(n, b.main.x)]
  | Sum.inr ns => ns.zipIdx.mapM fun n ↦ return (n.fst, ← `($b.main.x $(quote n.snd)))

-- /-- Convert the notation to a raw string. -/
-- def Body.raw (b : Body) : String :=
--   b.signature.opening ++
--   (match b.vars with
--     | Sum.inl n => s!"{n}"
--     | Sum.inr ns => ",".intercalate (ns.map fun n ↦ s!"{n}").toList) ++
--   b.signature.closing

/-- The syntax for polynomial-like notations, which is an unambiguous term declaration followed by
one or more polynomial-like notations, e.g. `(Fin 37)[x,y,z][[t]]`. -/
syntax polyesque := term_decl noWs polyesque_notation+

/-- The type of polynomial-like syntaxes. -/
abbrev Polyesque : Type := TSyntax ``polyesque

syntax polyesque : term

syntax polyesque_input := term_decl noWs polyesque_notation_input+

abbrev PolyesqueInput : Type := TSyntax ``polyesque_input

-- /-- A syntax category for declared polynomial-like notations, stored as raw strings literals.
-- For example, after `(Fin 37)[x,y,z]` is declared, this will store the string literal `"[x,y,z]"`.
-- This is used to retrieve the declared notation, e.g. `(Fin 37)[x,y,z]` as a term will now be parsed
-- as the term declaration `(Fin 37)` followed by the atom `"[x,y,z]"`. -/
-- declare_syntax_cat polyesque_declared

-- /-- The syntax category for retrieving declared notations, which is an umambiguous term declaration
-- followed by a declared polynomial-like notation, e.g. `(Fin 37)` followed by `"[x,y,z][[t]]"`. -/
-- syntax (name := polyesqueTerm) term_decl noWs polyesque_declared : term

-- /-- Parse a declared polynomial-like notation. -/
-- def parseDeclared (stx : TSyntax `polyesque_declared) : String :=
--   match stx.raw with
--   | .node _ _ #[.atom _ str] => str
--   | _ => ""

-- /-- Declare a local polynomial-like notation. Usage:
-- ```lean
-- name_poly_vars (Fin 37)[x,y,z][[t]]
-- #check x
-- #check t
-- #check (Fin 37)[x,y,z][[t]]
-- ```

-- Use `_` to declare it for all base rings. Usage:
-- ```lean
-- name_poly_vars _[a,b,c,d]
-- #check R[a,b,c,d]
-- #check S[a,b,c,d]
-- ```
-- -/
-- syntax (name := declare) "name_poly_vars " polyesque : command

-- /-- The table to store local polynomial-like notations, indexed by the raw string representation.
-- If the head is a hole `_`, then the array of functors will be stored. Otherwise, we store the
-- one resulting term.

-- E.g. for `_[a,b][c]`, we store the array ``#[`(MvPolynomial (Fin 2)), `(Polynomial)]``;

-- for `R[a,b][c]`, we store the one term `Polynomial (MvPolynomial (Fin 2) R))` -/
-- abbrev Declared := Std.HashMap String (Term ⊕ Array Term)

-- /-- The environmental extension to locally store polynomial-like notations. -/
-- abbrev DeclaredExt := SimpleScopedEnvExtension (String × (Term ⊕ Array Term)) Declared

-- /-- A local instance to help prove that `DeclaredExt` is inhabited. -/
-- @[local instance] def inhabitedSum {α β : Type _} [Inhabited α] : Inhabited (α ⊕ β) :=
--   ⟨.inl default⟩

-- /-- Initialise the environmental extension to locally store polynomial-like notations. -/
-- initialize declaredExt : DeclaredExt ← registerSimpleScopedEnvExtension <|
--   { addEntry old new := insert new old
--     initial := {} }

-- /-- Given a declaration of polynomial-like notation (e.g. `(Fin 37)[x,y,z][[t]]`), parse it fully to
-- return the head (e.g. `(Fin 37)`), the raw body (e.g. `"[x,y,z][[t]]`"), the total type generated
-- (e.g. `PowerSeries (MvPolynomial (Fin 3) (Fin 37))`), and the terms corresponding to each declared
-- identifier (e.g. `x := PowerSeries.C (MvPolynomial.X 0)`).

-- The head and body are returned as strings here so that they can be stored in a table in the
-- environment. -/
-- def parsePolyesqueInputFull (head : TermDecl) (body : TSyntaxArray ``polyesque_notation_input) :
--     CoreM (TSyntaxArray ``polyesque_notation × Bool ×
--       Term × (Term → CoreM Term) × Array (String × Term)) := do
--   have isHole : Bool := match head with
--     | `(term_decl| $_:hole) => true
--     | _ => false
--   let mut type : Term := head.term
--   let mut funcs : Array Term := #[]
--   let mut terms : Array (String × Term) := #[]
--   let mut bodyVar : Array PolyesqueNotation := #[]
--   for p in body do
--     let (norm, b) ← p.parsePolyesqueNotationInput
--     let func ← b.mkFunctor
--     type ← `($func $type)
--     funcs := funcs ++ #[func]
--     terms := (← terms.mapM fun it ↦ return (it.fst, ← b.mkC it.snd)) ++ (← b.mkX)
--     bodyVar := bodyVar ++ #[norm]
--   return (bodyVar, isHole, type, fun hd ↦ funcs.foldlM (fun a b ↦ `($b $a)) hd, terms)

def mkNotation (opening : Opening) (closing : Closing) (mv? : Bool) (polyVars : Array PolyVar) :
    CoreM PolyesqueNotation := do
  have vars : TSyntax ``vars := ← match mv?, polyVars with
    | true, #[v] => `(vars|$v,)
    | _, _ => `(vars|$(Syntax.TSepArray.ofElems polyVars):poly_var,*)
  return ← `(polyesque_notation| $opening$vars$closing)

-- declare the variables
def Lean.TSyntax.processAndDeclarePolyesqueNotationInput (p : PolyesqueNotationInput)
    (terms : Array (PolyVar × Term)) (oldFunctor : Term → CommandElabM Term) :
    CommandElabM (PolyesqueNotation × Array (PolyVar × Term) × (Term → CommandElabM Term)) := do
  let (b, opening, closing) ← liftCoreM p.parsePolyesqueNotationInput
  let newVarTerm : Array (PolyVar × Term) ← (← liftCoreM b.mkX).mapM fun ⟨i, t⟩ ↦ do
    let kind ← elabSyntax <| ← `(command| local syntax $(quote i):str : poly_var)
    return (i.toTSyntax kind, t)
  let newNotation ← liftCoreM <| mkNotation opening closing b.1.mv? (newVarTerm.map (·.1))
  let terms := (← terms.mapM fun ⟨v, t⟩ ↦ return (v, ← liftCoreM <| b.mkC t)) ++ newVarTerm
  let newFunctor := fun type ↦ do `($(← liftCoreM b.mkFunctor) $(← oldFunctor type))
  return (newNotation, terms, newFunctor)

def elabMacroRulesAndTrace (p : Polyesque) (t : Term) : CommandElabM Unit := do
  trace[«name_poly_vars»] m!"Declaring polynomial-like notation: {p}"
  trace[«name_poly_vars»] m!"Result: {t}"
  elabCommand <| ← `(command| local macro_rules | `(term| $p:polyesque) => `($t))

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
elab "name_poly_vars " head:term_decl noWs body:polyesque_notation_input+ : command => do
  -- let (body, isHole, type, functor, terms) ← liftCoreM (parsePolyesqueInputFull head body)
  -- -- if `head` is a hole `_`, then use `$head` as the head in the macro rule later.
  -- have head : TermDecl := ← match head with
  --   | `(term_decl| $_:hole) => `(term_decl| $$head)
  --   | t => return t
  -- let mut type : Term := head.term
  let mut terms : Array (PolyVar × Term) := #[]
  let mut bodyVar : Array PolyesqueNotation := #[]
  let mut functor : Term → CommandElabM Term := pure
  for p in body do
    let processed ← p.processAndDeclarePolyesqueNotationInput terms functor
    terms := processed.2.1
    functor := processed.2.2
    bodyVar := bodyVar ++ #[processed.1]
  have body := Syntax.TSepArray.ofElems (sep := "") bodyVar
  let type : Term := ← match head with
  | `(term_decl| $_:hole) => do
    let typeHole := ← functor (← `(_))
    elabMacroRulesAndTrace (← `(polyesque| _$body:polyesque_notation*)) (← `(term| $typeHole))
    elabMacroRulesAndTrace (← `(polyesque| $$i:ident$body:polyesque_notation*))
      (← functor (← `(term| $$i:ident)))
    elabMacroRulesAndTrace (← `(polyesque| ($$t:term)$body:polyesque_notation*))
      (← functor (← `(term| ($$t:term))))
    return typeHole
  | _ => do
    let type := ← functor head.term
    elabMacroRulesAndTrace (← `(polyesque| $head$body:polyesque_notation*)) (← `(term| $type))
    return type
  trace[«name_poly_vars»] m!"Terms:"
  for (v, t) in terms do
    elabCommand <| ← `(command| local macro_rules | `(term| $v:poly_var) => `(($t : $type)))
    trace[«name_poly_vars»] m!"{v} : {t}"
  -- have raw := headStr ++ bodyStr
  -- trace[«name_poly_vars»] m!"Terms:"
  -- for (i, t) in terms do
  --   let kind ← elabSyntax <| ← `(command| local syntax $(quote i):str : poly_var)
  --   elabCommand <| ← `(command| local macro_rules
  --     | `(poly_var| $(i.toTSyntax kind)) => `(($t : $type)))
  --   trace[«name_poly_vars»] m!"{i} : {t}"
  -- if isHole then
  --   elabCommand <| ← `(command| local macro_rules
  --     | `(polyesque| $$head:term_decl$body:polyesque_notation*) =>
  --         $(← liftCoreM <| functor (← `($$head))))
  -- else
  --   elabCommand <| ← `(command| local macro_rules
  --     | `(polyesque| $head$body:polyesque_notation*) => `($type))
  -- elabCommand <| ← `(command| local syntax $(quote bodyStr):str : polyesque_declared)
  -- declaredExt.add (raw, if isHole then Sum.inr funcs else Sum.inl type) .local

-- /-- Elaborate the command `name_poly_vars`. -/
-- @[command_elab declare]
-- def elabDeclarePolyVars : CommandElab := fun stx => do
--   let `(command|name_poly_vars $p:polyesque) := stx
--     | throwError m!"Wrong command syntax: {stx}"
--   let (headStr, bodyStr, isHole, type, funcs, terms) ← liftCoreM p.parsePolyesqueFull
--   have raw := headStr ++ bodyStr
--   trace[«name_poly_vars»] m!"Declaring polynomial-like notation: {raw}"
--   trace[«name_poly_vars»] m!"Result: {type}"
--   trace[«name_poly_vars»] m!"Terms:"
--   for (i, t) in terms do
--     elabCommand <| ← `(command| local syntax $(quote i):str : poly_var)
--     varTableExt.add (i, ← `(($t : $type))) .local
--     trace[«name_poly_vars»] m!"{i} : {t}"
--   elabCommand <| ← `(command| local syntax $(quote bodyStr):str : polyesque_declared)
--   declaredExt.add (raw, if isHole then Sum.inr funcs else Sum.inl type) .local

-- /-- Retrieve the polynomial-like notation for a given head and body. -/
-- def retrievePolyesque (head : TermDecl) (body : String) : Term.TermElabM Term := do
--   have d := declaredExt.getState (← getEnv)
--   match d.get? (head.rawTermDecl ++ body) with
--   | some (Sum.inl type) => return type
--   | some (Sum.inr funcs) => funcs.foldlM (fun type func ↦ `($func $type)) head.term
--   | none =>
--     match d.get? ("_" ++ body) with
--     | some (Sum.inl _) => throwError "unreachable"
--     | some (Sum.inr funcs) => funcs.foldlM (fun type func ↦ `($func $type)) head.term
--     | none => throwError m!"Undeclared polynomial-like notation: {head.rawTermDecl ++ body}"

-- /-- Elaborate the later references to the polynomial-like notation, e.g. `(Fin 37)[x,y,z][[t]]`. -/
-- @[term_elab polyesqueTerm]
-- def polyesqueElab : Term.TermElab := fun stx e => do
--   let `(polyesqueTerm| $head:term_decl$body:polyesque_declared) := stx
--     | throwError m!"Unrecognised syntax: {stx}"
--   have bodyStr := parseDeclared body
--   trace[«name_poly_vars»] m!"Retrieving polynomial-like notation: {head.rawTermDecl ++ bodyStr}"
--   let type ← retrievePolyesque head bodyStr
--   trace[«name_poly_vars»] m!"Result: {type}"
--   Term.elabTerm type e

end Mathlib.Tactic.NamePolyVars
