/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public meta import Mathlib.Tactic.Sat.Basic

public meta section

/-!
# `lrat_proof` command

Defines a macro for producing SAT proofs from CNF / LRAT files.
These files are commonly used in the SAT community for writing proofs.

Most SAT solvers support export to [DRAT](https://arxiv.org/abs/1610.06229) format,
but this format can be expensive to reconstruct because it requires recomputing all
unit propagation steps. The [LRAT](https://arxiv.org/abs/1612.02353) format solves this
issue by attaching a proof to the deduction of each new clause.
(The L in LRAT stands for Linear time verification.)
There are several verified checkers for the LRAT format, and the program implemented here
makes it possible to use the lean kernel as an LRAT checker as well and expose the results
as a standard propositional theorem.

The input to the `lrat_proof` command is the name of the theorem to define,
and the statement (written in CNF format) and the proof (in LRAT format).
For example:
```
lrat_proof foo
  "p cnf 2 4  1 2 0  -1 2 0  1 -2 0  -1 -2 0"
  "5 -2 0 4 3 0  5 d 3 4 0  6 1 0 5 1 0  6 d 1 0  7 0 5 2 6 0"
```
produces a theorem:
```
foo : ∀ (a a_1 : Prop), (¬a ∧ ¬a_1 ∨ a ∧ ¬a_1) ∨ ¬a ∧ a_1 ∨ a ∧ a_1
```

* You can see the theorem statement by hovering over the word `foo`.
* You can use the `example` keyword in place of `foo` to avoid generating a theorem.
* You can use the `include_str` macro in place of the two strings
  to load CNF / LRAT files from disk.
-/

open Lean hiding Literal
open Std (HashMap)

namespace Mathlib.Tactic.Sat

/-- The representation of a global clause. -/
structure Clause where
  /-- The list of literals as read from the input file -/
  lits : Array Int
  /-- The clause expression of type `Clause` -/
  expr : Expr
  /-- A proof of `⊢ ctx.proof c`.
  Note that we do not use `have` statements to cache these proofs:
  this is literally the proof expression itself. As a result, the proof terms
  rely heavily on dag-like sharing of the expression, and printing these proof terms
  directly is likely to crash lean for larger examples. -/
  proof : Expr

/-- Construct the clause expression from the input list. For example `[1, -2]` is translated to
`Clause.cons (Literal.pos 1) (Clause.cons (Literal.neg 2) Clause.nil)`. -/
def buildClause (arr : Array Int) : Expr :=
  let nil  := mkConst ``Sat.Clause.nil
  let cons := mkConst ``Sat.Clause.cons
  arr.foldr (fun i e ↦ mkApp2 cons (toExpr <| Sat.Literal.ofInt i) e) nil

/-- Constructs the formula expression from the input CNF, as a balanced tree of `Fmla.and` nodes. -/
partial def buildConj (arr : Array (Array Int)) (start stop : Nat) : Expr :=
  match stop - start with
  | 0 => panic! "empty"
  | 1 => mkApp (mkConst ``Sat.Fmla.one) (buildClause arr[start]!)
  | len =>
    let mid := start + len / 2
    mkApp2 (mkConst ``Sat.Fmla.and) (buildConj arr start mid) (buildConj arr mid stop)

/-- Constructs the proofs of `⊢ ctx.proof c` for each clause `c` in `ctx`.
The proofs are stashed in a `HashMap` keyed on the clause ID. -/
partial def buildClauses (arr : Array (Array Int)) (ctx : Expr) (start stop : Nat)
    (f p : Expr) (accum : Nat × HashMap Nat Clause) : Nat × HashMap Nat Clause :=
  match stop - start with
  | 0 => panic! "empty"
  | 1 =>
    let c := f.appArg!
    let proof := mkApp3 (mkConst ``Sat.Fmla.proof_of_subsumes) ctx c p
    let n := accum.1 + 1
    (n, accum.2.insert n { lits := arr[start]!, expr := c, proof })
  | len =>
    let mid := start + len / 2
    let f₁ := f.appFn!.appArg!
    let f₂ := f.appArg!
    let p₁ := mkApp4 (mkConst ``Sat.Fmla.subsumes_left) ctx f₁ f₂ p
    let p₂ := mkApp4 (mkConst ``Sat.Fmla.subsumes_right) ctx f₁ f₂ p
    let accum := buildClauses arr ctx start mid f₁ p₁ accum
    buildClauses arr ctx mid stop f₂ p₂ accum

/-- A localized clause reference.
It is the same as `Clause` except that the proof is now a local variable. -/
structure LClause where
  /-- The list of literals as read from the input file -/
  lits : Array Int
  /-- The clause expression of type `Clause` -/
  expr : Expr
  /-- The bound variable index of the hypothesis asserting `⊢ ctx.proof c`,
  _counting from the outside and 1-based_. (We use this numbering because we will need to
  reference the variable from multiple binder depths.) -/
  depth : Nat

/-- Construct an individual proof step `⊢ ctx.proof c`.

  * `db`: the current global context
  * `ns`, `clause`: the new clause
  * `pf`: the LRAT proof trace
  * `ctx`: the main formula

  The proof has three steps:

  1. Introduce local assumptions `have h1 : ctx.proof c1 := p1` for each clause `c1`
     referenced in the proof. We actually do all the introductions at once,
     as in `(fun h1 h2 h3 ↦ ...) p1 p2 p3`, because we want `p_i` to not be under any binders
     to avoid the cost of `instantiate` during typechecking and get the benefits of dag-like
     sharing in the `pi` (which are themselves previous proof steps which may be large terms).
     The hypotheses are in `gctx`, keyed on the clause ID.

  2. Unfold `⊢ ctx.proof [a, b, c]` to
     `∀ v, v.satisfies_fmla ctx → v.neg a → v.neg b → v.neg c → False` and `intro v hv ha hb hc`,
     storing each `ha : v.neg a` in `lctx`, keyed on the literal `a`.

  3. For each LRAT step `hc : ctx.proof [x, y]`, `hc v hv : v.neg x → v.neg y → False`.
     We look for a literal that is not falsified in the clause. Since it is a unit propagation
     step, there can be at most one such literal.
     * If `x` is the non-falsified clause, let `x'` denote the negated literal of `x`.
       Then `x'.negate` reduces to `x`, so `hnx : v.neg x'.negate |- hc v hv hnx hy : False`,
       so we construct the term
         `by_cases (fun hnx : v.neg x'.negate ↦ hc v hv hnx hy) (fun hx : v.neg x ↦ ...)`
       and `hx` is added to the local context.
     * If all clauses are falsified, then we are done: `hc v hv hx hy : False`.
-/
partial def buildProofStep (db : HashMap Nat Clause)
    (ns pf : Array Int) (ctx clause : Expr) : Except String Expr := Id.run do
  let mut lams := #[]
  let mut args := #[]
  let mut gctx : HashMap Nat LClause := {}
  -- step 1
  for i in pf do
    let i := i.natAbs
    let some cl := db[i]? | return Except.error "missing clause"
    if !gctx.contains i then
      lams := lams.push (mkApp2 (mkConst ``Sat.Fmla.proof) ctx cl.expr)
      args := args.push cl.proof
      gctx := gctx.insert i {
        lits := cl.lits
        expr := cl.expr
        depth := args.size
      }
  let n := args.size
  -- step 2
  let mut f :=
    (mkAppN · args) ∘
    lams.foldr (mkLambda `c default) ∘
    mkLambda `v default (mkConst ``Sat.Valuation) ∘
    mkLambda `hv default (mkApp2 (mkConst ``Sat.Valuation.satisfies_fmla) (mkBVar 0) ctx)
  let v depth := mkBVar (depth + 1)
  let hv depth := mkBVar depth
  lams := #[]
  let mut clause := clause
  let mut depth := 0
  let mut lctx : HashMap Int Nat := {}
  for i in ns do
    let l := clause.appFn!.appArg!
    clause := clause.appArg!
    lams := lams.push (mkApp2 (mkConst ``Sat.Valuation.neg) (v depth) l)
    depth := depth.succ
    lctx := lctx.insert i depth
  f := f ∘ lams.foldr (mkLambda `h default)
  -- step 3
  for (step : Int) in pf do
    if step < 0 then return Except.error "unimplemented: RAT step"
    let some cl := gctx[step.toNat]? | return Except.error "missing clause"
    let mut unit := none
    for i in cl.lits do
      unless lctx.contains i do
        if unit.isSome then return Except.error s!"not unit: {cl.lits}"
        depth := depth.succ
        unit := some i
    let mut pr := mkApp2 (mkBVar (depth + n + 2 - cl.depth)) (v depth) (hv depth)
    for i in cl.lits do
      pr := mkApp pr <| mkBVar (match lctx[i]? with | some k => depth - k | _ => 0)
    let some u := unit | return Except.ok <| f pr
    let lit := toExpr <| Sat.Literal.ofInt u
    let nlit := toExpr <| Sat.Literal.ofInt (-u)
    let d1 := depth-1
    let app := mkApp3 (mkConst ``Sat.Valuation.by_cases) (v d1) nlit <|
      mkLambda `h default (mkApp2 (mkConst ``Sat.Valuation.neg) (v d1) lit) pr
    let dom := mkApp2 (mkConst ``Sat.Valuation.neg) (v d1) nlit
    f := fun e ↦ f <| mkApp app <| mkLambda `h default dom e
    lctx := lctx.insert (-u) depth
  return Except.error s!"no refutation: {ns}, {pf}, {lctx.toList}"

/-- An LRAT step is either an addition or a deletion step. -/
inductive LRATStep
  | /-- An addition step, with the clause ID, the clause literal list, and the proof trace -/
    add (id : Nat) (lits : Array Int) (proof : Array Int) : LRATStep
  | /-- A (multiple) deletion step, which deletes all the listed clause IDs from the context -/
    del (ids : Array Nat) : LRATStep

/-- Build the main proof of `⊢ ctx.proof []` using the LRAT proof trace.

  * `arr`: The input CNF
  * `ctx`: The abbreviated formula, a constant like `foo.ctx_1`
  * `ctx'`: The definitional expansion of the formula, a tree of `Fmla.and` nodes
  * `steps`: The input LRAT proof trace
-/
partial def buildProof (arr : Array (Array Int)) (ctx ctx' : Expr)
    (steps : Array LRATStep) : MetaM Expr := do
  let p := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db := (buildClauses arr ctx 0 arr.size ctx' p default).2
  for step in steps do
    match step with
    | LRATStep.del ds => db := ds.foldl (·.erase ·) db
    | LRATStep.add i ns pf =>
      let e := buildClause ns
      match buildProofStep db ns pf ctx e with
      | Except.ok proof =>
        if ns.isEmpty then return proof
        db := db.insert i { lits := ns, expr := e, proof }
      | Except.error msg => throwError msg
  throwError "failed to prove empty clause"

/-- Build the type and value of the reified theorem. This rewrites all the SAT definitions
into standard operators on `Prop`, for example if the formula is `[[1, 2], [-1, 2], [-2]]` then
this produces a proof of `⊢ ∀ a b : Prop, (a ∧ b) ∨ (¬a ∧ b) ∨ ¬b`. We use the input `nvars` to
decide how many quantifiers to use.

Most of the proof is under `2 * nvars + 1` quantifiers
`a1 .. an : Prop, v : Valuation, h1 : v 0 ↔ a1, ... hn : v (n-1) ↔ an ⊢ ...`, and we do the index
arithmetic by hand.

  1. First, we call `reifyFormula ctx'` which returns `a` and `pr : reify v ctx' a`
  2. Then we build `fun (v : Valuation) (h1 : v 0 ↔ a1) ... (hn : v (n-1) ↔ an) ↦ pr`
  3. We have to lower expression `a` from step 1 out of the quantifiers by lowering all variable
     indices by `nvars+1`. This is okay because `v` and `h1..hn` do not appear in `a`.
  4. We construct the expression `ps`, which is `a1 .. an : Prop ⊢ [a1, ..., an] : List Prop`
  5. `refute ctx (hf : ctx.proof []) (fun v h1 .. hn ↦ pr) : a` forces some definitional unfolding
     since `fun h1 .. hn ↦ pr` should have type `implies v (reify v ctx a) [a1, ..., an] a`,
     which involves unfolding `implies` n times as well as `ctx ↦ ctx'`.
  6. Finally, we `intro a1 ... an` so that we have a proof of `∀ a1 ... an, a`.
-/
partial def buildReify (ctx ctx' proof : Expr) (nvars : Nat) : Expr × Expr := Id.run do
  let (e, pr) := reifyFmla ctx'
  let mut pr := pr
  for i in [0:nvars] do
    let j := nvars-i-1
    let ty := mkApp2 (mkConst ``Iff) (mkApp (mkBVar j) (mkRawNatLit j)) (mkBVar nvars)
    pr := mkLambda `h default ty pr
  pr := mkLambda `v default (mkConst ``Sat.Valuation) pr
  let mut e := e.lowerLooseBVars (nvars+1) (nvars+1)
  let cons := mkApp (mkConst ``List.cons [levelZero]) (mkSort levelZero)
  let nil := mkApp (mkConst ``List.nil [levelZero]) (mkSort levelZero)
  let rec mkPS depth e
  | 0 => e
  | n + 1 => mkPS (depth+1) (mkApp2 cons (mkBVar depth) e) n
  pr := mkApp5 (mkConst ``Sat.Fmla.refute) e (mkPS 0 nil nvars) ctx proof pr
  for _ in [0:nvars] do
    e := mkForall `a default (mkSort levelZero) e
    pr := mkLambda `a default (mkSort levelZero) pr
  pure (e, pr)
where
  /-- The `v` variable under the `a1 ... an, v, h1 ... hn` context -/
  v := mkBVar nvars
  /-- Returns `a` and `pr : reify v f a` given a formula `f` -/
  reifyFmla f :=
    match f.getAppFn.constName! with
    | ``Sat.Fmla.and =>
      let f₁ := f.appFn!.appArg!
      let f₂ := f.appArg!
      let (e₁, h₁) := reifyFmla f₁
      let (e₂, h₂) := reifyFmla f₂
      (mkApp2 (mkConst ``Or) e₁ e₂, mkApp7 (mkConst ``Sat.Fmla.reify_or) v f₁ e₁ f₂ e₂ h₁ h₂)
    | ``Sat.Fmla.one =>
      let c := f.appArg!
      let (e, h) := reifyClause c
      (e, mkApp4 (mkConst ``Sat.Fmla.reify_one) v c e h)
    | _ => panic! "not a valid formula"
  /-- Returns `a` and `pr : reify v c a` given a clause `c` -/
  reifyClause c :=
    if c.appFn!.isConst then
      (mkConst ``True, mkApp (mkConst ``Sat.Clause.reify_zero) v)
    else reifyClause1 c
  /-- Returns `a` and `pr : reify v c a` given a nonempty clause `c` -/
  reifyClause1 c :=
    let l := c.appFn!.appArg!
    let c := c.appArg!
    let (e₁, h₁) := reifyLiteral l
    if c.isConst then
      (e₁, mkApp4 (mkConst ``Sat.Clause.reify_one) v l e₁ h₁)
    else
      let (e₂, h₂) := reifyClause1 c
      (mkApp2 (mkConst ``And) e₁ e₂, mkApp7 (mkConst ``Sat.Clause.reify_and) v l e₁ c e₂ h₁ h₂)
  /-- Returns `a` and `pr : reify v l a` given a literal `c` -/
  reifyLiteral l :=
    let n := l.appArg!
    let (e, h) := reifyVar n
    match l.appFn!.constName! with
    | ``Sat.Literal.pos =>
      (mkApp (mkConst ``Not) e, mkApp4 (mkConst ``Sat.Literal.reify_pos) v e n h)
    | ``Sat.Literal.neg =>
      (e, mkApp4 (mkConst ``Sat.Literal.reify_neg) v e n h)
    | _ => panic! "not a valid literal"
  /-- Returns `a` and `pr : v n ↔ a` given a variable index `n`.
  These are both lookups into the context
  `(a0 .. a(n-1) : Prop) (v) (h1 : v 0 ↔ a0) ... (hn : v (n-1) ↔ a(n-1))`. -/
  reifyVar v :=
    let n := v.rawNatLit?.get!
    (mkBVar (2 * nvars - n), mkBVar (nvars - n - 1))
open Lean

namespace Parser
open Lean Std.Internal.Parsec String

/-- Parse a natural number -/
def parseNat : String.Parser Nat := Json.Parser.natMaybeZero

/-- Parse an integer -/
def parseInt : String.Parser Int := do
  if (← peek!) = '-' then skip; pure <| -(← parseNat) else parseNat

/-- Parse a list of integers terminated by 0 -/
partial def parseInts (arr : Array Int := #[]) : String.Parser (Array Int) := do
  match ← parseInt <* ws with
  | 0 => pure arr
  | n => parseInts (arr.push n)

/-- Parse a list of natural numbers terminated by 0 -/
partial def parseNats (arr : Array Nat := #[]) : String.Parser (Array Nat) := do
  match ← parseNat <* ws with
  | 0 => pure arr
  | n => parseNats (arr.push n)

/-- Parse a DIMACS format `.cnf` file.
This is not very robust; we assume the file has had comments stripped. -/
def parseDimacs : String.Parser (Nat × Array (Array Int)) := do
  pstring "p cnf" *> ws
  let nvars ← parseNat <* ws
  let nclauses ← parseNat <* ws
  let mut clauses := Array.mkEmpty nclauses
  for _ in [:nclauses] do
    clauses := clauses.push (← parseInts)
  pure (nvars, clauses)

/-- Parse an LRAT file into a list of steps. -/
def parseLRAT : String.Parser (Array LRATStep) := many do
  let step ← parseNat <* ws
  if (← peek!) = 'd' then skip <* ws; pure <| LRATStep.del (← parseNats)
  else ws; pure <| LRATStep.add step (← parseInts) (← parseInts)

end Parser

open Std.Internal

/-- Core of `fromLRAT`. Constructs the context and main proof definitions,
but not the reification theorem. Returns:

  * `nvars`: the number of variables specified in the CNF file
  * `ctx`: The abbreviated formula, a constant like `foo.ctx_1`
  * `ctx'`: The definitional expansion of the formula, a tree of `Fmla.and` nodes
  * `proof`: A proof of `ctx.proof []`
-/
def fromLRATAux (cnf lrat : String) (name : Name) : MetaM (Nat × Expr × Expr × Expr) := do
  let Parsec.ParseResult.success _ (nvars, arr) := Parser.parseDimacs cnf.mkIterator
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  let ctx' := buildConj arr 0 arr.size
  let ctxName ← mkAuxDeclName (name ++ `ctx)
  addDecl <| Declaration.defnDecl {
    name := ctxName
    levelParams := []
    type        := mkConst ``Sat.Fmla
    value       := ctx'
    hints       := ReducibilityHints.regular 0
    safety      := DefinitionSafety.safe
  }
  let ctx := mkConst ctxName
  let Parsec.ParseResult.success _ steps := Parser.parseLRAT lrat.mkIterator
    | throwError "parse LRAT failed"
  let proof ← buildProof arr ctx ctx' steps
  let declName ← mkAuxDeclName (name ++ `proof)
  addDecl <| Declaration.thmDecl {
    name := declName
    levelParams := []
    type        := mkApp2 (mkConst ``Sat.Fmla.proof) ctx (buildClause #[])
    value       := proof
  }
  return (nvars, ctx, ctx', mkConst declName)

/-- Main entry point. Given strings `cnf` and `lrat` with unparsed file data, and a name `name`,
adds `theorem name : type := proof` where `type` is a propositional theorem like
`∀ (a a_1 : Prop), (¬a ∧ ¬a_1 ∨ a ∧ ¬a_1) ∨ ¬a ∧ a_1 ∨ a ∧ a_1`.

Also creates auxiliaries named `name.ctx_1` (for the CNF formula)
and `name.proof_1` (for the LRAT proof), with `name` itself containing the reification proof. -/
def fromLRAT (cnf lrat : String) (name : Name) : MetaM Unit := do
  let (nvars, ctx, ctx', proof) ← fromLRATAux cnf lrat name
  let (type, value) := buildReify ctx ctx' proof nvars
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

open Elab Term


/--
A macro for producing SAT proofs from CNF / LRAT files.
These files are commonly used in the SAT community for writing proofs.

The input to the `lrat_proof` command is the name of the theorem to define,
and the statement (written in CNF format) and the proof (in LRAT format).
For example:
```
lrat_proof foo
  "p cnf 2 4  1 2 0  -1 2 0  1 -2 0  -1 -2 0"
  "5 -2 0 4 3 0  5 d 3 4 0  6 1 0 5 1 0  6 d 1 0  7 0 5 2 6 0"
```
produces a theorem:
```
foo : ∀ (a a_1 : Prop), (¬a ∧ ¬a_1 ∨ a ∧ ¬a_1) ∨ ¬a ∧ a_1 ∨ a ∧ a_1
```

* You can see the theorem statement by hovering over the word `foo`.
* You can use the `example` keyword in place of `foo` to avoid generating a theorem.
* You can use the `include_str` macro in place of the two strings
  to load CNF / LRAT files from disk.
-/
elab "lrat_proof " n:(ident <|> "example")
    ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ if n.1.isIdent then n.1.getId else `_example
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (mkConst ``String) lrat
    let go := do
      fromLRAT cnf lrat name
      withSaveInfoContext do
        Term.addTermInfo' n (mkConst name) (isBinder := true)
    if n.1.isIdent then go else withoutModifyingEnv go

lrat_proof example
  -- The CNF file
  "p cnf 2 4
   1 2 0
   -1 2 0
   1 -2 0
   -1 -2 0"
  -- The LRAT file
  "5 -2 0 4 3 0
   5 d 3 4 0
   6 1 0 5 1 0
   6 d 1 0
   7 0 5 2 6 0"

-- lrat_proof full2
--   (include_str "full2.cnf")
--   (include_str "full2.lrat")

/--
A macro for producing SAT proofs from CNF / LRAT files.
These files are commonly used in the SAT community for writing proofs.

The input to the `from_lrat` term syntax is two string expressions with
the statement (written in CNF format) and the proof (in LRAT format).
For example:
```
def foo := from_lrat
  "p cnf 2 4  1 2 0  -1 2 0  1 -2 0  -1 -2 0"
  "5 -2 0 4 3 0  5 d 3 4 0  6 1 0 5 1 0  6 d 1 0  7 0 5 2 6 0"
```
produces a theorem:
```
foo : ∀ (a a_1 : Prop), (¬a ∧ ¬a_1 ∨ a ∧ ¬a_1) ∨ ¬a ∧ a_1 ∨ a ∧ a_1
```

* You can use this term after `have :=` or in `def foo :=` to produce the term
  without constraining the type.
* You can use it when a specific type is expected, but it currently does not
  pay any attention to the shape of the goal and always produces the same theorem,
  so you can only use this to do alpha renaming.
* You can use the `include_str` macro in place of the two strings
  to load CNF / LRAT files from disk.
-/
elab "from_lrat " cnf:term:max ppSpace lrat:term:max : term => do
  let cnf ← unsafe evalTerm String (mkConst ``String) cnf
  let lrat ← unsafe evalTerm String (mkConst ``String) lrat
  let name ← mkAuxName `lrat
  fromLRAT cnf lrat name
  return mkConst name

example : ∀ (a b : Prop), (¬a ∧ ¬b ∨ a ∧ ¬b) ∨ ¬a ∧ b ∨ a ∧ b := from_lrat
  "p cnf 2 4  1 2 0  -1 2 0  1 -2 0  -1 -2 0"
  "5 -2 0 4 3 0  5 d 3 4 0  6 1 0 5 1 0  6 d 1 0  7 0 5 2 6 0"

end Sat

end Mathlib.Tactic
