/-
Copyright (c) 2022 Dhruv Bhatia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Bhatia, Eric Wieser, Mario Carneiro, Thomas Zhu
-/
import Mathlib.Tactic.LinearCombination

/-!

# polyrith Tactic

In this file, the `polyrith` tactic is created.  This tactic, which
works over `Field`s, attempts to prove a multivariate polynomial target over said
field by using multivariable polynomial hypotheses/proof terms over the same field.
Used as is, the tactic makes use of those hypotheses in the local context that are
over the same field as the target. However, the user can also specify which hypotheses
from the local context to use, along with proof terms that might not already be in the
local context. Note: since this tactic uses SageMath via an API call,
it can only be used with a working internet connection.

## Implementation Notes

The tactic `linear_combination` is often used to prove such goals by allowing the user to
specify a coefficient for each hypothesis. If the target polynomial can be written as a
linear combination of the hypotheses with the chosen coefficients, then the `linear_combination`
tactic succeeds. In other words, `linear_combination` is a certificate checker, and it is left
to the user to find a collection of good coefficients. The `polyrith` tactic automates this
process using the theory of Groebner bases.

Polyrith does this by first parsing the relevant hypotheses into a form that SageMath can
understand. It then calls the SageMath API to compute the coefficients. These coefficients are
then sent back to Lean, which parses them into pexprs. The information is then given to the
`linear_combination` tactic, which completes the process by checking the certificate.

In fact, `polyrith` uses Sage to test for membership in the *radical* of the ideal.
This means it searches for a linear combination of hypotheses that add up to a *power* of the goal.
When this power is not 1, it uses the `(exp := n)` feature of `linear_combination` to report the
certificate.

## TODO

* Give Sage more information about the specific ring being used for the coefficients. For now,
  we always use ℚ (or `QQ` in Sage).
* Handle `•` terms.
* Support local Sage installations.

## References

* See the book [*Ideals, Varieties, and Algorithms*][coxlittleOshea1997] by David Cox, John Little,
  and Donal O'Shea for the background theory on Groebner bases
* This code was heavily inspired by the code for the tactic `linarith`, which was written by
  Robert Y. Lewis, who advised me on this project as part of a Computer Science independent study
  at Brown University.

-/

namespace Mathlib.Tactic.Polyrith
open Lean
open Meta Ring Qq PrettyPrinter AtomM
initialize registerTraceClass `Meta.Tactic.polyrith

/-! # Poly Datatype -/

/--
A datatype representing the semantics of multivariable polynomials.
Each `Poly` can be converted into a string.
-/
inductive Poly
  | const : ℚ → Poly
  | var : ℕ → Poly
  | hyp : Term → Poly
  | add : Poly → Poly → Poly
  | sub : Poly → Poly → Poly
  | mul : Poly → Poly → Poly
  | div : Poly → Poly → Poly
  | pow : Poly → Poly → Poly
  | neg : Poly → Poly
  deriving BEq, Repr

/--
This converts a poly object into a string representing it. The string
maintains the semantic structure of the poly object.

The output of this function must be valid Python syntax, and it assumes the variables `vars`
(see `sageCreateQuery`).
-/
def Poly.format : Poly → Lean.Format
  | .const z => toString z
  | .var n => s!"vars[{n}]" -- this references variable `vars`, which need to be bounded (below)
  | .hyp e => s!"hyp{e}" -- this one can't be used by python
  | .add p q => s!"({p.format} + {q.format})"
  | .sub p q => s!"({p.format} - {q.format})"
  | .mul p q => s!"({p.format} * {q.format})"
  | .div p q => s!"({p.format} / {q.format})" -- this one can't be used by python
  | .pow p q => s!"({p.format} ^ {q.format})"
  | .neg p => s!"-{p.format}"

instance : Lean.ToFormat Poly := ⟨Poly.format⟩
instance : ToString Poly := ⟨(toString ·.format)⟩
instance : Repr Poly := ⟨fun p _ => p.format⟩
instance : Inhabited Poly := ⟨Poly.const 0⟩

instance : Quote ℤ where quote
  | .ofNat n => quote n
  | .negSucc n => Unhygienic.run `(-$(quote (n + 1)))

instance : Quote ℚ where
  quote q :=
    if q.den = 1 then quote q.num
    else Unhygienic.run `($(quote q.num) / $(quote q.den))

variable (vars : Array Syntax.Term) in
/-- Converts a `Poly` expression into a `Syntax` suitable as an input to `linear_combination`. -/
def Poly.toSyntax : Poly → Unhygienic Syntax.Term
  | .const z => pure (quote z)
  | .var n => pure vars[n]!
  | .hyp stx => pure stx
  | .add p q => do `($(← p.toSyntax) + $(← q.toSyntax))
  | .sub p q => do `($(← p.toSyntax) - $(← q.toSyntax))
  | .mul p q => do `($(← p.toSyntax) * $(← q.toSyntax))
  | .div p q => do `($(← p.toSyntax) / $(← q.toSyntax))
  | .pow p q => do `($(← p.toSyntax) ^ $(← q.toSyntax))
  | .neg p => do `(-$(← p.toSyntax))

attribute [local instance] monadLiftOptionMetaM in
/-- Reifies a ring expression of type `α` as a `Poly`. -/
partial def parse {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    (c : Ring.Cache sα) (e : Q($α)) : AtomM Poly := do
  let els := do
    try pure <| Poly.const (← (← NormNum.derive e).toRat)
    catch _ => pure <| Poly.var (← addAtom e).1
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα with
  | ``HAdd.hAdd, _ | ``Add.add, _ => match e with
    | ~q($a + $b) => pure <| (← parse sα c a).add (← parse sα c b)
    | _ => els
  | ``HMul.hMul, _ | ``Mul.mul, _ => match e with
    | ~q($a * $b) => pure <| (← parse sα c a).mul (← parse sα c b)
    | _ => els
  | ``HSMul.hSMul, _ => match e with
    | ~q(($a : ℕ) • ($b : «$α»)) => pure <| (← parse sℕ .nat a).mul (← parse sα c b)
    | _ => els
  | ``HPow.hPow, _ | ``Pow.pow, _ => match e with
    | ~q($a ^ $b) =>
      try pure <| (← parse sα c a).pow (.const (← (← NormNum.derive (u := .zero) b).toRat))
      catch _ => els
    | _ => els
  | ``Neg.neg, some _ => match e with
    | ~q(-$a) => pure <| (← parse sα c a).neg
  | ``HSub.hSub, some _ | ``Sub.sub, some _ => match e with
    | ~q($a - $b) => pure <| (← parse sα c a).sub (← parse sα c b)
    | _ => els
  | _, _ => els

/-- The possible hypothesis sources for a polyrith proof. -/
inductive Source where
  /-- `input n` refers to the `n`'th input `ai` in `polyrith [a1, ..., an]`. -/
  | input : Nat → Source
  /-- `fvar h` refers to hypothesis `h` from the local context. -/
  | fvar : FVarId → Source

/-- The first half of `polyrith` produces a list of arguments to be sent to Sage. -/
def parseContext (only : Bool) (hyps : Array Expr) (target : Expr) :
    AtomM (Expr × Array (Source × Poly) × Poly) := do
  let fail {α} : AtomM α := throwError "polyrith failed: target is not an equality in semirings"
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars target).eq? | fail
  let .sort u ← instantiateMVars (← whnf (← inferType α)) | unreachable!
  let some v := u.dec | throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let sα ← synthInstanceQ q(CommSemiring $α)
  let c ← mkCache sα
  let target := (← parse sα c e₁).sub (← parse sα c e₂)
  let rec
    /-- Parses a hypothesis and adds it to the `out` list. -/
    processHyp src ty out := do
      if let some (β, e₁, e₂) := (← instantiateMVars ty).eq? then
        if ← withTransparency (← read).red <| isDefEq α β then
          return out.push (src, (← parse sα c e₁).sub (← parse sα c e₂))
      pure out
  let mut out := #[]
  if !only then
    for ldecl in ← getLCtx do
      out ← processHyp (.fvar ldecl.fvarId) ldecl.type out
  for hyp in hyps, i in [:hyps.size] do
    out ← processHyp (.input i) (← inferType hyp) out
  pure (α, out, target)

/-- A JSON parser for `ℚ` specific to the return value of Sage. -/
local instance : FromJson ℚ where fromJson?
  | .arr #[a, b] => return (← fromJson? a : ℤ) / (← fromJson? b : ℕ)
  | _ => .error "expected array with two elements"

/-- Removes an initial `-` sign from a polynomial with negative leading coefficient. -/
def Poly.unNeg? : Poly → Option Poly
  | .mul a b => return .mul (← a.unNeg?) b
  | .const i => if i < 0 then some (.const (-i)) else none
  | .neg p => p
  | _ => none

/-- Adds two polynomials, performing some simple simplifications for presentation like
`a + -b = a - b`. -/
def Poly.add' : Poly → Poly → Poly
  | .const 0, p => match p.unNeg? with
    | some np => .neg np
    | none => p
  | p, .const 0 => p
  | a, b => match b.unNeg? with
    | some nb => a.sub nb
    | none => a.add b

/-- Multiplies two polynomials, performing some simple simplifications for presentation like
`1 * a = a`. -/
def Poly.mul' : Poly → Poly → Poly
  | .const 0, _ => .const 0
  | .const 1, p
  | p, .const 1 => p
  | a, b => a.mul b

/-- Extracts the divisor `c : ℕ` from a polynomial of the form `1/c * b`. -/
def Poly.unDiv? : Poly → Option (Poly × ℕ)
  | .mul a b => do let (a, r) ← a.unDiv?; return (.mul' a b, r)
  | .const r => if r.num = 1 ∧ r.den ≠ 1 then some (.const r.num, r.den) else none
  | .neg p => do let (p, r) ← p.unDiv?; return (.neg p, r)
  | _ => none

/-- Constructs a power expression `v_i ^ j`, performing some simplifications in trivial cases. -/
def Poly.pow' : ℕ → ℕ → Poly
  | _, 0 => .const 1
  | i, 1 => .var i
  | i, k => .pow (.var i) (.const k)

/-- Constructs a sum from a monadic function supplying the monomials. -/
def Poly.sumM {m : Type → Type*} {α : Type*} [Monad m] (a : Array α) (f : α → m Poly) : m Poly :=
  a.foldlM (init := .const 0) fun p a => return p.add' (← f a)

instance : FromJson Poly where
  fromJson? j := do
    Poly.sumM (← j.getArr?) fun j => do
      let mut mon := .const (← fromJson? (← j.getArrVal? 1))
      for j in ← (← j.getArrVal? 0).getArr? do
        mon := mon.mul' (.pow' (← fromJson? (← j.getArrVal? 0)) (← fromJson? (← j.getArrVal? 1)))
      pure mon

/-- A schema for the data reported by the Sage calculation -/
structure SageCoeffAndPower where
  /-- The function call produces an array of polynomials
  parallel to the input list of hypotheses. -/
  coeffs : Array Poly
  /-- Sage produces an exponent (default 1) in the case where the hypothesess
  sum to a power of the goal. -/
  power  : ℕ
  deriving FromJson, Repr

/-- The result of a sage call in the success case. -/
structure SageSuccess where
  /-- The script returns a string containing python script to be sent to the remote server,
  when the tracing option is set. -/
  trace : Option String := none
  /-- The main result of the function call is an array of polynomials
  parallel to the input list of hypotheses and an exponent for the goal. -/
  data : Option SageCoeffAndPower := none
  deriving FromJson, Repr

/-- The result of a sage call in the failure case. -/
structure SageError where
  /-- The error kind -/
  name : String
  /-- The error message -/
  value : String
  deriving FromJson

/-- The result of a sage call. -/
def SageResult := Except SageError SageSuccess


section SageMathApi

/-! # Interaction with SageMath -/

/--
These are Sage functions that test membership in the radical and format the output. See
https://github.com/sagemath/sage/blob/f8df80820dc7321dc9b18c9644c3b8315999670b/src/sage/rings/polynomial/multi_polynomial_libsingular.pyx#L4472-L4518
for a description of `MPolynomial_libsingular.lift`.
-/
def sageHelperFunctions : String :=
  include_str ".."/".."/"scripts"/"polyrith_sage_helper.py"

/--
The Sage type to use, given a base type of the target. Currently always rational numbers (`QQ`).
Future extensions may change behavior depending on the base type.
-/
@[nolint unusedArguments]
def sageTypeStr (_ : Expr) : String := "QQ"

/--
Create a Sage script to send to SageMath API.
-/
def sageCreateQuery (α : Expr) (atoms : Nat) (hyps : Array (Source × Poly)) (target : Poly) :
    IO String := do
  -- since `hyps` and `target` reference the variable list `vars` (see `Poly.format`),
  -- `hyps` and `target` are wrapped as functions where `vars` is bounded using `lambda`
  let hypsListPython := "[" ++ ",".intercalate (hyps.map (toString ·.2) |>.toList) ++ "]"
  let mkHypsListPython := s!"lambda vars: {hypsListPython}"
  let mkTargetPython := s!"lambda vars: {target}"
  let command :=
    s!"main({sageTypeStr α}, {atoms}, {mkHypsListPython}, {mkTargetPython})"
  return sageHelperFunctions ++ "\n" ++ command

/-- Parse a `SageResult` from the raw SageMath API output. -/
instance : FromJson SageResult where fromJson? j := do
  -- we expect the output has either "success": true and contains "stdout",
  -- or has "success": false and error information under "execute_reply"
  if let .ok true := j.getObjValAs? Bool "success" then
    -- parse SageSuccess from stdout, which is formatted as SageCoeffAndPower
    -- (see sageCreateQuery for the format of stdout)
    let stdout ← j.getObjValAs? String "stdout"
    let coeffAndPower ← Json.parse stdout >>= fromJson?
    let sageSuccess := { data := some coeffAndPower }
    return .ok sageSuccess
  else
    -- parse SageError from execute_reply
    let executeReply ← j.getObjVal? "execute_reply"
    let errorName ← executeReply.getObjValAs? String "ename"
    let errorValue ← executeReply.getObjValAs? String "evalue"
    return .error { name := errorName, value := errorValue }

/-- The User-Agent header value for HTTP calls to SageMath API -/
register_option polyrith.sageUserAgent : String :=
  { defValue := "LeanProver (https://leanprover-community.github.io/)"
    group := "polyrith"
    descr := "The User-Agent header value for HTTP calls to SageMath API" }

/--
This function calls the Sage API at <https://sagecell.sagemath.org/service>.
The output is parsed as `SageResult`.
-/
def runSage (trace : Bool) (α : Expr) (atoms : Nat) (hyps : Array (Source × Poly)) (target : Poly) :
    CoreM SageResult := do
  let query ← sageCreateQuery α atoms hyps target
  if trace then
    -- dry run enabled
    return .ok { trace := query }

  -- send query to SageMath API
  let apiUrl := "https://sagecell.sagemath.org/service"
  let data := s!"code={System.Uri.escapeUri query}"
  let curlArgs := #[
    "-X", "POST",
    "--user-agent", polyrith.sageUserAgent.get (← getOptions),
    "--data-raw", data,
    apiUrl
  ]
  let out ← IO.Process.output { cmd := "curl", args := curlArgs }
  if out.exitCode != 0 then
    IO.throwServerError <|
      "Could not send API request to SageMath. " ++
      s!"curl exited with code {out.exitCode}:\n{out.stderr}"

  -- parse results
  match Json.parse out.stdout >>= fromJson? with
  | .ok result => return result
  | .error e => IO.throwServerError <|
      s!"Could not parse SageMath output (error: {e})\nSageMath output:\n{out.stdout}"

end SageMathApi


/-! # Main function -/

/--
This is the main body of the `polyrith` tactic. It takes in the following inputs:
* `only : Bool` - This represents whether the user used the key word "only"
* `hyps : Array Expr` - the hypotheses/proof terms selected by the user
* `traceOnly : Bool` - If enabled, the returned syntax will be `.missing`

First, the tactic converts the target into a `Poly`, and finds out what type it
is an equality of. (It also fills up a list of `Expr`s with its atoms). Then, it
collects all the relevant hypotheses/proof terms from the context, and from those
selected by the user, taking into account whether `only` is true. (The list of atoms is
updated accordingly as well).

This information is used to create an appropriate SageMath script that executes a
Groebner basis computation, which is sent to SageMath's API server.
The output of this computation is a JSON representing the certificate.
This JSON is parsed into the power of the goal and a list of `Poly` objects
that are then converted into `Expr`s (using the updated list of atoms).

the names of the hypotheses, along with the corresponding coefficients are
given to `linear_combination`. If that tactic succeeds, the user is prompted
to replace the call to `polyrith` with the appropriate call to
`linear_combination`.

Returns `.error g` if this was a "dry run" attempt that does not actually invoke sage.
-/
def polyrith (g : MVarId) (only : Bool) (hyps : Array Expr)
    (traceOnly := false) : MetaM (Except MVarId (TSyntax `tactic)) := do
  IO.sleep 10 -- otherwise can lead to weird errors when actively editing code with polyrith calls
  g.withContext <| AtomM.run .reducible do
    let (α, hyps', target) ← parseContext only hyps (← g.getType)
    let rec
      /-- Try to prove the goal by `ring` and fail with the given message otherwise. -/
      byRing msg := do
        let stx ← `(tactic| ring)
        try
          let ([], _) ← Elab.runTactic g stx | failure
          return .ok stx
        catch _ => throwError "{msg} and the goal is not provable by ring"
    if hyps'.isEmpty then
      return ← byRing "polyrith did not find any relevant hypotheses"
    let vars := (← get).atoms.size
    match ← runSage traceOnly α vars hyps' target with
    | .ok { trace, data } =>
      if let some trace := trace then logInfo trace
      if let some {coeffs := polys, power := pow} := data then
        let vars ← liftM <| (← get).atoms.mapM delab
        let p ← Poly.sumM (polys.zip hyps') fun (p, src, _) => do
          let h := .hyp (← delab (match src with | .input i => hyps[i]! | .fvar h => .fvar h))
          pure <| match p.unDiv? with
          | some (p, den) => (p.mul' h).div (.const den)
          | none => p.mul' h
        let stx := (withRef (← getRef) <| p.toSyntax vars).run
        let tac ←
          if let .const 0 := p then `(tactic| linear_combination)
          else if pow = 1 then `(tactic| linear_combination $stx:term)
          else `(tactic| linear_combination (exp := $(quote pow)) $stx:term)
        try
          guard (← Elab.runTactic g tac).1.isEmpty
        catch _ => throwError
          "polyrith found the following certificate, but it failed to close the goal:\n{stx}"
        pure <| .ok tac
      else if traceOnly then
        return .error g
      else throwError "internal error: no output available"
    | .error { name, value } =>
      throwError "polyrith failed to retrieve a solution from Sage! {name}: {value}"

/--
Attempts to prove polynomial equality goals through polynomial arithmetic
on the hypotheses (and additional proof terms if the user specifies them).
It proves the goal by generating an appropriate call to the tactic
`linear_combination`. If this call succeeds, the call to `linear_combination`
is suggested to the user.

* `polyrith` will use all relevant hypotheses in the local context.
* `polyrith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `polyrith only [h1, h2, h3, t1, t2, t3]` will use only local hypotheses
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

Notes:
* This tactic only works with a working internet connection, since it calls Sage
  using the SageCell web API at <https://sagecell.sagemath.org/>.
  Many thanks to the Sage team and organization for allowing this use.
* This tactic assumes that the user has `curl` available on path.

Examples:

```lean
example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
    x*y = -2*y + 1 := by
  polyrith
-- Try this: linear_combination h1 - 2 * h2

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w := by
  polyrith
-- Try this: linear_combination (2 * y + x) * hzw

axiom scary : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0) : a + b + c + d = 0 := by
  polyrith only [scary c d, h]
-- Try this: linear_combination scary c d + h
```
-/
syntax "polyrith" (&" only")? (" [" term,* "]")? : tactic

open Elab Tactic
elab_rules : tactic
  | `(tactic| polyrith%$tk $[only%$onlyTk]? $[[$hyps,*]]?) => do
    let hyps ← hyps.map (·.getElems) |>.getD #[] |>.mapM (elabTerm · none)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.polyrith
    match ← polyrith (← getMainGoal) onlyTk.isSome hyps traceMe with
    | .ok stx =>
      replaceMainGoal []
      if !traceMe then Lean.Meta.Tactic.TryThis.addSuggestion tk stx
    | .error g => replaceMainGoal [g]

end Mathlib.Tactic.Polyrith
