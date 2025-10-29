/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Kenny Lau, Jovan Gerbscheid
-/
import Mathlib.Util.Notation3

/-!
The command `poly_variable` names variables in any combination of `Polynomial`, `MvPolynomial`,
`RatFunc`, `PowerSeries`, `MvPowerSeries`, and `LaurentSeries`, where the `Mv` is restricted to
`Fin n`. This list of functors can be expanded easily if and when more polynomial-like functors are
introduced (using `register_poly_notation`, see below).

The notation introduced by `poly_variable` is local.

Usage: (this section assumes that the brackets have been registered: see instructions below for
how to register new brackets, which should be done only once in the library for each new
polynomial-like functor)

```lean
variable (R : Type) [CommRing R]

-- This produces `R[[x,y]][t] := Polynomial (MvPowerSeries (Fin 2) R)`, and
-- `x := Polynomial.C (MvPowerSeries.X 0) : R[[x,y]][t]`, and
-- `y := Polynomial.C (MvPowerSeries.X 1) : R[[x,y]][t]`, and
-- `t := Polynomial.X : R[[x,y]][t]`
poly_variable R[[x,y]][t]

poly_variable (ZMod 37)[a]

-- Leaving the base ring as underscore creates notation for every ring.
poly_variable _[r]
-- So for example `Int[r]` is now valid and refers to `Polynomial Int`, and
-- `r` can refer to `Polynomial.X` with any base ring.

-- The two commands below produce `R[p] := Polynomial R`, and then
-- `(R[p])[[q]] := PowerSeries R[p]` which is `PowerSeries (Polynomial R)`, and also
-- `p := Polynomial.X : R[p]`, and
-- `q := PowerSeries.X : (R[p])[[q]]`
poly_variable R[p]
poly_variable (R[p])[[q]]

poly_variable R[u,] -- produces `R[u,] := MvPolynomial (Fin 1) R` where `u` is the formal variable.
poly_variable R[] -- produces `R[] := MvPolynomial (Fin 0) R` with no formal variables.
```

It is used with exactly one expression as input (`R[[x,y]][t]` above), and does the following:
1. First, it identifies the base ring in the following way: if the first part of the input is one
  identifier (which can be a section variable like `R` or a constant like `ℕ`), then it is taken as
  the base ring, no matter what follows it. Otherwise, if the user wishes to specify a base ring
  that is a more complicated term (such as `ZMod 37` or `R[p]`), then parentheses are **required**.
  In the above, this is exemplified by `(ZMod 37)[a]` and `(R[p])[q]`. There is a special usecase:
  if the base ring is an underscore `_` (such as `_[r]` above), then it is allowed to be any ring.
2. Then, it computes the term corresponding to the whole ring recursively using the rest of the
  input, so for example `R[[x,y]][t]` has base ring `R`, so the whole expression computes to
  `Polynomial (MvPowerSeries (Fin 2) R)`. It is done from left to right (in the input), which
  corresponds to the order from inwards to outwards (in the output).
3. To do so, the input is broken down into parts, where each part has an opening bracket, a
  comma-separated list of variables, and a closing bracket. In the example `R[[x,y]][t]`, after the
  base ring, the input is broken down into two parts: the first part is `[[x,y]]` where `[[` is the
  opening bracket, `]]` is the closing bracket, and the list of variables is `x,y` with two
  variables; and the second part is `[t]` with opening bracket being `[`, closing bracket being `]`,
  and the list is `t` with only one variable and no commas.
4. The parts are then evaluated from left to right. Firstly, we determine whether this is a
  multivariate notation (which usually has `Mv` in the name, such as `MvPolynomial`) or a univariate
  notation (which has no `Mv`, such as `Polynomial`), using the following procedure: if the list of
  variables consists of exactly one variable with no commas (such as `t` above), then the part
  (`[t]`) is treated as a univariate notation; otherwise, it is treated as a multivariate notation,
  so the part `[[x,y]]` combined with the base ring `R` produces `MvPowerSeries (Fin 2) R`, where
  `2` is just the length of the list of variables. (See edge cases below.)
5. Then the whole term is computed recursively, starting with the base ring `R`, it reads the part
  `[[x,y]]` and produces `MvPowerSeries (Fin 2) R`, and then it reads the part `[t]` and produces
  `Polynomial (MvPowerSeries (Fin 2) R)`, which is the result of the big ring.
6. Then the notation is set up so that one can type `R[[x,y]][t]` in any code that follows, and
  refer to the big ring `Polynomial (MvPowerSeries (Fin 2) R)`. The delaborator is also set up in
  the reverse direction, which means that any occurrence of `Polynomial (MvPowerSeries (Fin 2) R)`
  in the code below will be printed as `R[[x,y]][t]`.
7. Afterwards, each variable is assigned a meaning, which is an element of the big ring. This is
  done by repeatedly applying the appropriate `.X` and `.C` functions of the functors, for example
  `x` in `R[[x,y]]` is `MvPowerSeries.X 0`, and then we use `Polynomial.C` to transport it to the
  following `[t]` part, so in conclusion `x` in `R[[x,y]][t]` is `Polynomial.C (MvPowerSeries.X 0)`.
  Similarly, `y` in `R[[x,y]][t]` computes to `Polynomial.C (MvPowerSeries.X 1)`, and `t` computes
  to `Polynomial.X`.
8. Note that all of these variables (`x`, `y`, and `t`) are assumed to be elements of the big ring
  (which is `R[[x,y]][t]`, which is `Polynomial (MvPowerSeries (Fin 2) R)`).
9. The only valid variable inputs are identifiers, which means a variable cannot contain spaces, and
  cannot already have an assigned meaning (so `Nat` is not valid).
10. Then, notation is set up again so that `x` is a valid term that means
  `Polynomial.C (MvPowerSeries.X 0)`, and again any occurrence of `Polynomial.C (MvPowerSeries.X 0)`
  prints as `x`.
11. Multivariate functors (such as `MvPolynomial` and `MvPowerSeries`) typically allow any indexing
  type, but this notation only produces `Fin n` where `n` is the length of the list of variables.

For the edge case of `MvPolynomial (Fin 1) R`, use the syntax `R[u,]` with a trailing comma. And the
edge case of `MvPolynomial (Fin 0) R` is just `R[]`.

Using more code to explain, the command `poly_variable R[a,b][c]` is roughly equivalent to the
following code:
```lean
local notation3 "R" "[" "a" "," "b" "]" "[" "c" "]" => Polynomial (MvPolynomial (Fin 2) R)
local notation3 "a" => (Polynomial.C (MvPolynomial.X 0) : R[a,b][c])
local notation3 "b" => (Polynomial.C (MvPolynomial.X 1) : R[a,b][c])
local notation3 "c" => (Polynomial.X : R[a,b][c])
```
where one can see that the notation is set up for the big ring, and also for each variable that
occurs.

To register new polynomial-like functors (should be done only once in the library for each
polynomial-like functor), use the command `register_poly_notation`:

```lean
register_poly_notation "[" "]" Polynomial Polynomial.C Polynomial.X
register_poly_notation (mv := true) "[" "]" MvPolynomial MvPolynomial.C MvPolynomial.X
```

The user needs to supply (in this exact order):
1. optionally `(mv := true)` to denote a multivariate notation, or omit it to mean univariate;
2. the opening bracket, which is `"["` above;
3. the closing bracket, which is `"]"` above;
4. the functor itself, which is `Polynomial` above;
5. the constant function, which is `Polynomial.C` above; this is the map from the base ring `R` to
  the polynomial ring `Polynomial R`, meaning that we have `Polynomial.C : R → Polynomial R`.
  (It does not matter that in the actual implementation this is actually a ring homomorphism,
  because the syntax `Polynomial.C r` works regardless.)
6. the formal variable function, which is `Polynomial.X`. This produces one constant in
  `Polynomial R` since it is univariate, and for the multivariate situation, `MvPolynomial.X` is a
  function from the indexing set (which is `Fin n` in this notation) to the polynomial ring. In
  effect, for univariate we have `Polynomial.X : Polynomial R`, and for multivariate we have
  `MvPolynomial.X : Fin n → MvPolynomial (Fin n) R`.

The last three inputs are **not required** to be constants, meaning that they can be more
complicated terms such as `(HahnSeries.single 1 1)` for the functor `LaurentSeries`. In this case,
again parentheses are required.

The registration is global and should only be done once for each functor.
-/

open Lean Elab Command Parser.Tactic PrettyPrinter.Delaborator

initialize registerTraceClass `poly_variable

namespace Mathlib.Tactic.PolyVariable

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
def parseBracket {n : Name} (v : TSyntax n) : String :=
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
def parsePolyIdents : TSyntax ``poly_idents → Option (String ⊕ Array String)
  | `(poly_idents| $v:ident) => some (.inl v.getId.toString)
  | `(poly_idents| $vs:ident,*) => some (.inr (vs.getElems.map fun v ↦ v.getId.toString))
  | _ => none

-- An unambiguously bracketed term, which is `_`, an identifier, or a term enclosed in brackets.
-- This has no doc-string because that would show up in hover information.
syntax term_decl := hole <|> ident <|> ("(" term ")")
attribute [nolint docBlame] term_decl

/-- Convert a `term_decl` to a `term`. -/
def termDeclToTerm : TSyntax ``term_decl → Term
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
register_poly_notation "[[" "]]" PowerSeries PowerSeries.C PowerSeries.X
register_poly_notation (mv := true) "[[" "]]" MvPowerSeries MvPowerSeries.C MvPowerSeries.X
```
-/
elab "register_poly_notation " mv?:optConfig opening:str closing:str
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
  trace[poly_variable] m!"Registering new syntax: (mv := {mv?}) {opening} {closing}"
  notationTableExt.add ({ opening, closing, mv? }, { type, c, x }) .global
  trace[poly_variable] m!"New table size: {(notationTableExt.getState (← getEnv)).size}"

/-- A locally declared polynomial-like variable. -/
scoped syntax poly_var : term

/-- A parsed body for one polynomial-like notation, consisting of the type of the notation
(e.g. `MvPolynomial`) and the array of variable identifiers (or one identifier). -/
structure DeclaredNotationPart extends Notation where
  /-- The declared names for the variables. -/
  vars : (String ⊕ Array String)
  /-- The opening bracket -/
  openingStx : TSyntax `poly_opening
  /-- The closing bracket -/
  closingStx : TSyntax `poly_closing

/-- The syntax for using a declared polynomial-like notation, e.g. `[x,y]` or `[[t]]`, which uses
`poly_var` instead of `ident`. -/
syntax polyesque_notation := atomic(poly_opening poly_vars poly_closing)

/-- The syntax for declaring a polynomial-like notation, e.g. `[x,y]` or `[[t]]`, which uses
`ident` instead of `poly_var`. -/
syntax polyesque_notation_input := atomic(poly_opening poly_idents poly_closing)

section
variable {m : Type → Type} [Monad m] [MonadError m] [MonadEnv m] [MonadQuotation m]

/-- Parse a `polyesque_notation_input` into a `DeclaredNotationPart`. -/
def parsePolyesqueNotationInput (p : TSyntax ``polyesque_notation_input) :
    m DeclaredNotationPart := do
  let `(polyesque_notation_input| $openingStx $v $closingStx) := p
    | throwError m!"Unrecognised polynomial-like notation: {p}"
  have opening := parseBracket openingStx
  have closing := parseBracket closingStx
  let some vars := parsePolyIdents v
    | throwError m!"Unrecognised variable notation: {v}"
  have mv? : Bool := vars.isRight
  let some n := (notationTableExt.getState (← getEnv)).get? { opening, closing, mv? }
    | throwError s!"Unrecognised polynomial-like syntax: (mv := {mv?}) {openingStx} {closingStx}"
  return { n with vars, openingStx, closingStx }

/-- Create the type for a polynomial-like notation, e.g. `[a,b]` gives `MvPolynomial (Fin 2) R`,
where `R` is the previous type. -/
def DeclaredNotationPart.mkType (d : DeclaredNotationPart) (type : Term) : m Term :=
  match d.vars with
  | .inl _ => `($d.type $type)
  | .inr ns => do `($d.type $(← `(Fin $(quote ns.size))) $type)

/-- Create the constant term for a polynomial-like notation. -/
def DeclaredNotationPart.mkC (d : DeclaredNotationPart) (term : Term) : m Term :=
  `($d.c $term)

/-- Create the formal variable term(s) for a polynomial-like notation. -/
def DeclaredNotationPart.mkX (d : DeclaredNotationPart) : m (Array (String × Term)) :=
  match d.vars with
  | .inl n => return #[(n, d.x)]
  | .inr ns => ns.zipIdx.mapM fun (n, i) ↦ return (n, ← `($d.x $(quote i)))

/-- The syntax for polynomial-like notations, which is an unambiguous term declaration followed by
one or more polynomial-like notations, e.g. `(Fin 37)[x,y,z][[t]]`. -/
syntax polyesque := term_decl (noWs polyesque_notation)+

/-- The declared notations can be used later as terms. -/
scoped syntax:max (name := polyesque_term) polyesque : term

/-- Fallback for undeclared polynomial-like notations, which makes an error. This is triggered by
default, and overridden by the `local macro_rules` commands generated by `poly_variable`. -/
@[term_elab polyesque_term] def polyesqueFallback : Term.TermElab := fun stx _ ↦
  throwError "{stx} is not a declared polynomial-like notation."

/-- Dynamically build the syntax for a declared polynomial-like notation. -/
def mkBracketStx (d : DeclaredNotationPart) (polyVars : Array (TSyntax `poly_var)) :
    m (TSyntax ``polyesque_notation) := do
  let vars ← match d.vars, polyVars with
    | .inr _, #[v] => `(poly_vars| $v,)
    | _, _ => `(poly_vars| $(Syntax.TSepArray.ofElems polyVars):poly_var,*)
  `(polyesque_notation| $d.openingStx$vars$d.closingStx)

end

/-- Given one segment (e.g. `[x,y]`) of the declaration, extract all the relevant information:
the relevant functor (`MvPolynomial (Fin 2)`), the formal variables, and their meanings. Then,
register the variables (`x` and `y`) as polynomial variables (`poly_var`). -/
def processAndDeclarePolyesqueNotationInput (p : TSyntax ``polyesque_notation_input)
    (oldTerms : Array (TSyntax `poly_var × Term)) (oldFunctor : Term → CommandElabM Term) :
    CommandElabM (TSyntax ``polyesque_notation × Array (TSyntax `poly_var × Term) ×
      (Term → CommandElabM Term) × Term) := do
  let d ← parsePolyesqueNotationInput p
  let newTerms ← (← d.mkX).mapM fun (s, t) ↦ do
    -- Declares the new formal variables as `poly_var`.
    let kind ← elabSyntax <| ← `(command| local syntax $(quote s):str : poly_var)
    return (⟨mkNode kind #[mkAtom s]⟩, t)
  let bracketStx ← mkBracketStx d (newTerms.map (·.1))
  let oldTerms ← oldTerms.mapM fun (v, t) ↦ return (v, ← d.mkC t)
  let newFunctor := oldFunctor >=> d.mkType
  return (bracketStx, oldTerms ++ newTerms, newFunctor, d.type)

/-- A helper function to elaborate macro rules and trace their declarations. -/
def elabPolyesqueMacroRules (p : TSyntax ``polyesque) (t : Term) : CommandElabM Unit := do
  trace[poly_variable] m!"Declaring polynomial-like notation: {p}\nResult: {t}"
  elabCommand <| ← `(command| local macro_rules | `($p:polyesque) => `($t))

/-- A helper function to process declarations with a hole (`_`) as the base ring, such as:
```lean
poly_variable _[a,b][c]
```

This is a special case, and the specification of its behaviour is that:
* It will process the notation as usual, in this case it will declare `_[a,b][c]` as notation for
  `Polynomial (MvPolynomial (Fin 2) _)`.
* It will also accept an arbitrary identifier in place of the hole, i.e. it will declare
  `$i[a,b][c]` as notation for `Polynomial (MvPolynomial (Fin 2) $i)`, where `$i` is a placeholder
  for an arbitrary `ident` (identifier). Note that this is referring to literally `$i` being passed
  to the macro declaration.
* It will also accept an arbitrary term in place of the hole, similar to the point above.
  In this example, `$t[a,b][c]` will be declared for `Polynomial (MvPolynomial (Fin 2) $t)`, where
  `$t` is a placeholder for an arbitrary `term`.
* For all of these three cases above, an unexpander is then written to do the reverse direction
  during delaboration.

It accepts the following inputs:
* `bodyStx`: the rest of the notation, passed in as a `TSepArray` separated by `""`. In this
  example, it is `[a,b][c]`.
* `functor`: the whole functor that this notation represents. In this example, it is
  `R ↦ Polynomial (MvPolynomial (Fin 2) R)`.
* `typeIdent`: the syntax `Polynomial (MvPolynomial (Fin 2) $i)` as in the above discussion.
* `polyesqueIdent`: the syntax `$i[a,b][c]` as in the above discussion.
* `typeTerm`: the syntax `Polynomial (MvPolynomial (Fin 2) $t)` as in the above discussion.
* `polyesqueTerm`: the syntax `$t[a,b][c]` as in the above discussion.
* `lastHead`: the outermost functor as a term, which is `Polynomial` in the example, used to trigger
  the delaborator.

And at the end it outputs the syntax that is the elaborated syntax with the hole, which in the
example is `Polynomial (MvPolynomial (Fin 2) _)`.
-/
def declareNotationWithHole
    (bodyStx : Syntax.TSepArray ``polyesque_notation "")
    (functor : Term → CommandElabM Term)
    (typeIdent : Term) (polyesqueIdent : TSyntax ``polyesque)
    (typeTerm : Term) (polyesqueTerm : TSyntax ``polyesque)
    (lastHead : Term) :
    CommandElabM Term := do
  elabPolyesqueMacroRules (← `(polyesque| $$h:hole$bodyStx:polyesque_notation*))
    (← functor (← `($$h:hole)))
  elabPolyesqueMacroRules polyesqueIdent typeIdent
  elabPolyesqueMacroRules polyesqueTerm typeTerm
  -- if the head of the term is a constant, then deploy the unexpander.
  if let `($c:ident) := lastHead then
    trace[poly_variable] m!"Declaring unexpander for {c}"
    elabCommand <| ← `(command|
      @[local app_unexpander $c]
      private aux_def unexpand : Lean.PrettyPrinter.Unexpander := fun
        | `($typeIdent) => `($polyesqueIdent:polyesque)
        | `($typeTerm) => `($polyesqueTerm:polyesque)
        | _ => throw ())
  functor (← `(_))

/-- A helper function to process declarations where the base ring is not a hole, such as:
```lean
poly_variable R[a,b][c]
poly_variable (ZMod 37)[a,b][c]
```

It does the following:
* It generates the correct elaborated term and declares the notation, e.g. it declares
  `R[a,b][c]` to be notation for `Polynomial (MvPolynomial (Fin 2) R)`.
* Then it generates an unexpander, depending on if the given term is an identifier or a term.

It accepts the following inputs:
* `functor`: the whole functor that this notation represents. In this example, it is
  `R ↦ Polynomial (MvPolynomial (Fin 2) R)`.
* `head`: the base ring, which is `R` or `ZMod 37` in the examples.
* `bodyStx`: the rest of the notation, passed in as a `TSepArray` separated by `""`. In this
  example, it is `[a,b][c]`.
* `lastHead`: the outermost functor as a term, which is `Polynomial` in the example, used to trigger
  the delaborator.

The remaining four inputs are for the delaborator, which will be mainly explained by example:
* `typeIdent`: the full term where the base ring is replaced with a placeholder identifier;
  in the example it is `Polynomial (MvPolynomial (Fin 2) $i)`.
* `polyesqueIdent`: the notation where the base ring is replaced with a placeholder identifier;
  in the example it is `$i[a,b][c]`.
* `typeTerm`: the full term where the base ring is replaced with a placeholder term;
  in the example it is `Polynomial (MvPolynomial (Fin 2) $t)`.
* `polyesqueTerm`: the notation where the base ring is replaced with a placeholder term;
  in the example it is `$t[a,b][c]`.

And at the end it outputs the elaborated term, which in the example is
`Polynomial (MvPolynomial (Fin 2) R)`.
-/
def declareNotation
    (functor : Term → CommandElabM Term)
    (head : TSyntax ``term_decl)
    (bodyStx : Syntax.TSepArray ``polyesque_notation "")
    (lastHead : Term)
    (typeIdent : Term) (polyesqueIdent : TSyntax ``polyesque)
    (typeTerm : Term) (polyesqueTerm : TSyntax ``polyesque) :
    CommandElabM Term := do
  let type ← functor (termDeclToTerm head)
  let polyesque ← `(polyesque| $head$bodyStx:polyesque_notation*)
  elabPolyesqueMacroRules polyesque type
  -- if the head of the term is a constant, then deploy the unexpander.
  if let `($c:ident) := lastHead then
    trace[poly_variable] m!"Declaring unexpander for {c}"
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

/-- A helper fuction to declare one variable from the notation. For example, consider:
```lean
poly_variable R[a,b][c]
```

Then here `a`, `b`, and `c` are the variables, and this function declares the correct notation
for one variable, and then generates a delaborator for the reverse direction.

For example, this function declares `b` to mean `Polynomial.C (MvPolynomial.X 0)`, and then
sets up the delaborator to delaborate `Polynomial.C (MvPolynomial.X 0)` back into `b`.

It accepts the following inputs:
* `v`: the syntax for the variable, which is `b` in the above example
* `t`: the correct term it should elaborate into, which is `Polynomial.C (MvPolynomial.X 0)` in
  the above example.
* `type`: the underlying type that is the whole ring, which is `Polynomial (MvPolynomial (Fin 2) R)`
  in the above example.
-/
def declareVariableNotation (v : TSyntax `poly_var) (t type : Term) :
    CommandElabM Unit := do
  let val ← `(($t : $type))
  elabCommand <| ← `(command| local macro_rules | `($v:poly_var) => `($val))
  trace[poly_variable] m!"Declaring polyesque variable {v} := {t}"
  -- The following code is essentially copied from the `notation3` implementation
  let some (keys, matcher) ←
    runTermElabM fun _ => (Notation3.mkExprMatcher val #[]).run | return
  for key in keys do
    let bodyCore ← `($matcher Notation3.MatchState.empty *> `($v:poly_var))
    let body ← match key with
      | .app _ arity => `(withOverApp $(quote arity) $bodyCore)
      | _            => pure bodyCore
    elabCommand <| ← `(command|
      /-- Pretty printer defined by `poly_variable` command. -/
      @[local delab $(mkIdent key.key)]
      private aux_def delab_app : Delab :=
        whenPPOption getPPNotation <| whenNotPPOption getPPExplicit <| $body)

/-- Declare a local polynomial-like notation. Usage:
```lean
poly_variable (Fin 37)[x,y,z][[t]]
#check x
#check t
#check (Fin 37)[x,y,z][[t]]
```

Use `_` to declare it for all base rings. Usage:
```lean
poly_variable _[a,b,c,d]
#check R[a,b,c,d]
#check S[a,b,c,d]
```

For example, `poly_variable R[a,b][c]` is roughly equivalent to (but not exactly) the following
code:
```lean
local notation3 "R" "[" "a" "," "b" "]" "[" "c" "]" => Polynomial (MvPolynomial (Fin 2) R)
local notation3 "a" => (Polynomial.C (MvPolynomial.X 0) : R[a,b][c])
local notation3 "b" => (Polynomial.C (MvPolynomial.X 1) : R[a,b][c])
local notation3 "c" => (Polynomial.X : R[a,b][c])
```
It searches through the registered polynomial-like notations (registered using
`register_poly_notation`), and builds the correct terms given the input, so `R[a,b][c]` computes to
`Polynomial (MvPolynomial (Fin 2) R)`, and then each variable name (`a`, `b`, and `c` in this
example) is also computed to the correct term of the type `R[a,b][c]`. And then finally, unexpanders
and delaborators are implemented to go the "other direction", i.e. to make sure that the computed
terms print back to the notation declared. The last part can be disabled with
`set_option pp.notation false`.

If the brackets have not been registered, you might see an error message such as:
* unexpected token `'{'`; expected poly_opening
or:
* unexpected token `'['`; expected poly_closing

In that case, please go to the file where the polynomial-like functor is defined, and register it
using the following syntax:
```lean
register_poly_notation "[" "]" Polynomial Polynomial.C Polynomial.X
register_poly_notation (mv := true) "[" "]" MvPolynomial MvPolynomial.C MvPolynomial.X
```
-/
elab "poly_variable " head:term_decl body:(noWs polyesque_notation_input)+ : command => do
  elabCommand <| ← `(command| open scoped Mathlib.Tactic.PolyVariable)
  let mut terms : Array (TSyntax `poly_var × Term) := #[]
  let mut bodyStxs : Array (TSyntax ``polyesque_notation) := #[]
  let mut functor : Term → CommandElabM Term := pure
  let mut lastHead : Term := default
  for p in body do
    let processed ← processAndDeclarePolyesqueNotationInput p terms functor
    (terms, functor, lastHead) := processed.2
    bodyStxs := bodyStxs.push processed.1
  have bodyStx := Syntax.TSepArray.ofElems (sep := "") bodyStxs
  let typeIdent ← functor (← `($$i:ident))
  let polyesqueIdent ← `(polyesque| $$i:ident$bodyStx:polyesque_notation*)
  let typeTerm ← functor (← `($$t:term))
  let polyesqueTerm ← `(polyesque| ($$t:term)$bodyStx:polyesque_notation*)
  let type : Term := ← match head with
  | `(term_decl| $_:hole) => declareNotationWithHole bodyStx functor
      typeIdent polyesqueIdent typeTerm polyesqueTerm lastHead
  | _ => declareNotation functor head bodyStx lastHead
      typeIdent polyesqueIdent typeTerm polyesqueTerm
  for (v, t) in terms do
    declareVariableNotation v t type

end Mathlib.Tactic.PolyVariable
