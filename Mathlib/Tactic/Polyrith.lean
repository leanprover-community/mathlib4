/-
Copyright (c) 2022 Dhruv Bhatia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Bhatia, Eric Wieser, Mario Carneiro
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.LinearCombination

/-!

# polyrith Tactic

In this file, the `polyrith` tactic is created.  This tactic, which
works over `Field`s, attempts to prove a multivariate polynomial target over said
field by using multivariable polynomial hypotheses/proof terms over the same field.
Used as is, the tactic makes use of those hypotheses in the local context that are
over the same field as the target. However, the user can also specify which hypotheses
from the local context to use, along with proof terms that might not already be in the
local context. Note: since this tactic uses SageMath via an API call done in Python,
it can only be used with a working internet connection, and with a local installation of Python.

## Implementation Notes

The tactic `linear_combination` is often used to prove such goals by allowing the user to
specify a coefficient for each hypothesis. If the target polynomial can be written as a
linear combination of the hypotheses with the chosen coefficients, then the `linear_combination`
tactic succeeds. In other words, `linear_combination` is a certificate checker, and it is left
to the user to find a collection of good coefficients. The `polyrith` tactic automates this
process using the theory of Groebner bases.

Polyrith does this by first parsing the relevant hypotheses into a form that Python can understand.
It then calls a Python file that uses the SageMath API to compute the coefficients. These
coefficients are then sent back to Lean, which parses them into pexprs. The information is then
given to the `linear_combination` tactic, which completes the process by checking the certificate.

In fact, `polyrith` uses Sage to test for membership in the *radical* of the ideal.
This means it searches for a linear combination of hypotheses that add up to a *power* of the goal.
When this power is not 1, it uses the `(exp := n)` feature of `linear_combination` to report the
certificate.

`polyrith` calls an external python script `scripts/polyrith_sage.py`. Because this is not a Lean
file, changes to this script may not be noticed during Lean compilation if you have already
generated olean files. If you are modifying this python script, you likely know what you're doing;
remember to force recompilation of any files that call `polyrith`.

## TODO

* Give Sage more information about the specific ring being used for the coefficients. For now,
  we always use ℚ (or `QQ` in Sage).
* Handle `•` terms.
* Support local Sage installations.

## References

* See the book [*Ideals, Varieties, and Algorithms*][coxlittleOshea1997] by David Cox, John Little,
  and Donal O'Shea for the background theory on Groebner bases
* This code was heavily inspired by the code for the tactic `linarith`, which was written by
  Robert Lewis, who advised me on this project as part of a Computer Science independent study
  at Brown University.

-/

set_option autoImplicit true

namespace Mathlib.Tactic.Polyrith
open Lean hiding Rat
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

The output of this function must be valid Python syntax, and it assumes the variables `varN` from
`scripts/polyrith.py.`
-/
def Poly.format : Poly → Lean.Format
  | .const z => toString z
  | .var n => s!"var{n}"
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
  | .negSucc n => Unhygienic.run `(-$(quote n))

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

/-- Reifies a ring expression of type `α` as a `Poly`. -/
partial def parse {u} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    (c : Ring.Cache sα) (e : Q($α)) : AtomM Poly := do
  let els := do
    try pure <| Poly.const (← (← NormNum.derive e).toRat)
    catch _ => pure <| Poly.var (← addAtom e)
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
def parseContext (only : Bool) (hyps : Array Expr) (tgt : Expr) :
    AtomM (Expr × Array (Source × Poly) × Poly) := do
  let fail {α} : AtomM α := throwError "polyrith failed: target is not an equality in semirings"
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars tgt).eq? | fail
  let .sort u ← instantiateMVars (← whnf (← inferType α)) | unreachable!
  let some v := u.dec | throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let sα ← synthInstanceQ (q(CommSemiring $α) : Q(Type v))
  let c ← mkCache sα
  let tgt := (← parse sα c e₁).sub (← parse sα c e₂)
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
  pure (α, out, tgt)

/-- Constructs the list of arguments to pass to the external sage script `polyrith_sage.py`. -/
def createSageArgs (trace : Bool) (α : Expr) (atoms : Nat)
    (hyps : Array (Source × Poly)) (tgt : Poly) : Array String :=
  let hyps := hyps.map (toString ·.2) |>.toList.toString
  #[toString trace, toString α, toString atoms, hyps, toString tgt]

/-- A JSON parser for `ℚ` specific to the return value of `polyrith_sage.py`. -/
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
def Poly.sumM [Monad m] (a : Array α) (f : α → m Poly) : m Poly :=
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

instance : FromJson SageResult where fromJson? j := do
  if let .ok true := fromJson? <| j.getObjValD "success" then
    return .ok (← fromJson? j)
  else
    return .error (← fromJson? j)

/--
This tactic calls python from the command line with the args in `arg_list`.
The output printed to the console is parsed as a `Json`.
It assumes that `python3` is available on the path.
-/
def sageOutput (args : Array String) : IO SageResult := do
  let path := (← getMathlibDir) / "scripts" / "polyrith_sage.py"
  unless ← path.pathExists do
    throw <| IO.userError "could not find python script scripts/polyrith_sage.py"
  let out ← IO.Process.output { cmd := "python3", args := #[path.toString] ++ args }
  if out.exitCode != 0 then
    throw <| IO.userError <|
      s!"scripts/polyrith_sage.py exited with code {out.exitCode}:\n\n{out.stderr}"
  match Json.parse out.stdout >>= fromJson? with
  | .ok v => return v
  | .error e => throw <| .userError e

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

This information is used to create a list of args that get used in a call to
the appropriate python file that executes a grobner basis computation. The
output of this computation is a `String` representing the certificate. This
string is parsed into a list of `Poly` objects that are then converted into
`Expr`s (using the updated list of atoms).

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
    let (α, hyps', tgt) ← parseContext only hyps (← g.getType)
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
    match ← sageOutput (createSageArgs traceOnly α vars hyps' tgt) with
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
* This tactic assumes that the user has `python3` installed and available on the path.
  (Test by opening a terminal and executing `python3 --version`.)
  It also assumes that the `requests` library is installed: `python3 -m pip install requests`.

Examples:

```lean
example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
    x*y = -2*y + 1 := by
  polyrith
-- Try this: linear_combination h1 - 2 * h2

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w := by
  polyrith
-- Try this: linear_combination (2 * y + x) * hzw

constant scary : ∀ a b : ℚ, a + b = 0

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
