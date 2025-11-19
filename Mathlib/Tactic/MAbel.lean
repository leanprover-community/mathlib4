/-
Copyright (c) 2024 Sam Ezeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Ezeh
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Util.AtomM
import Mathlib.Tactic.Abel
import Qq
import Mathlib.Tactic.TryThis

/-!
# The `mabel` tactic

Evaluate expressions in the language of multiplicative, commutative monoids and groups.

-/

namespace Mathlib.Tactic.MAbel
open Lean Elab Meta Tactic Qq Expr PrettyPrinter Elab.Tactic Parser.Tactic

initialize registerTraceClass `mabel
initialize registerTraceClass `mabel.detail

variable {α : Type*}

private abbrev ofMul' (α : Type*) := Additive.ofMul (α := α)
lemma ofMul_mul' [CommMonoid α] (x y : α) :
    Additive.ofMul.toFun (x * y) = Additive.ofMul.toFun x + Additive.ofMul.toFun y := rfl
lemma ofMul_pow' [CommMonoid α] (x : α) (n : ℕ) :
    Additive.ofMul.toFun (x^n) = n • Additive.ofMul.toFun x := rfl
lemma ofMul_one' [CommMonoid α] :
    Additive.ofMul.toFun (1 : α) = 0 := rfl
lemma ofMul_inv' [Inv α] (x : α) :
    Additive.ofMul.toFun x⁻¹ = -Additive.ofMul.toFun x := rfl
lemma ofMul_div' [Div α] (x y : α) :
    Additive.ofMul.toFun (x / y) = Additive.ofMul.toFun x - Additive.ofMul.toFun y := rfl
lemma ofMul_zpow' [CommGroup α] (x : α) (z : ℤ) :
    Additive.ofMul.toFun (x^z) = z • Additive.ofMul.toFun x := rfl
lemma ofMul'_eq_ofMul (x : α)  : (ofMul' _).toFun x = Additive.ofMul.toFun x := rfl
lemma ofMul_eq_zero' [CommMonoid α] (x : α) : ofMul' _ x = 0 ↔ x = 1 := ofMul_eq_zero

/-- Tactic for converting equations in the language of
multiplicative, commutative monoids and groups to those in the language
of additive, commutative monoids and groups.
-/
syntax (name := to_additive) "to_additive"  (location)? : tactic

/-- The core of `to_additive` which converts multiplicative structures
to additive structures. -/
partial def toAdditiveCore (e : Expr) : MetaM Simp.Result := do
 let thms := [
    ``ofMul'_eq_ofMul,
    ``ofMul_mul',  ``ofMul_pow',
    ``ofMul_one', ``ofMul_inv', ``ofMul_div',
    ``ofMul_zpow', ``ofMul_eq_zero', ``ofMul_div'
  ]
  let ctx ← Simp.mkContext
    (simpTheorems := #[← thms.foldlM (·.addConst ·) {:_}])
    (congrTheorems := ← getSimpCongrTheorems)

  let rec
    /-- Convert multiplicative expressions to additive expressions.
        Stop recursing after seeing the first multiplicative expression.
        For example: (f a) * (f b) -> (f a) + (f b)
        but f (x * y) * f (w * z) -> f(x * y) + f (w * z)
        -/
    to_additive (e : Expr) := do
      let is_multiplicative_operation : Name → Bool
        | ``HMul.hMul => True
        | ``HDiv.hDiv => True
        | _ => False
      let rec
        /-- Returns true when an operation is multiplication of division --/
        should_convert : Expr → Bool
          | .app (.const name _) _ => is_multiplicative_operation name
          | .app (application@(.app _ _)) _ => should_convert application
          | _ => False
      let rec
        /-- Recursive step for to_additive -/
        go : Expr → MetaM Expr
          | .app fn arg
              => if should_convert fn then
                  return ← to_additive (.app fn arg)
                else
                  return .app (← (to_additive fn)) (← (to_additive arg))
          | exp@(.bvar _) => return ← to_additive exp
          | .lam name e₁ e₂ binfo => return .lam name (← to_additive e₁) (← to_additive e₂) binfo
          | .forallE name btype body binfo => return .forallE name btype (← to_additive body) binfo
          | .letE name type value body nonDep
            => return .letE name type (← to_additive value) (← to_additive body) nonDep
          | exp => return exp
      let α ← inferType e
      let e' ← match (← synthInstance? (← mkAppM ``CommMonoid #[α])) with
        | .some _ => mkAppM ``Equiv.toFun #[← mkAppM ``ofMul' #[α], e]
        | .none => go e
      return e'
  return (← (Meta.simp (← to_additive e) ctx)).1

/-- Use `to_additive` to rewrite the main goal. -/
def toAdditiveTarget : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← withReducible goal.getType'
  let result ← toAdditiveCore tgt
  if result.expr.isConstOf ``True then
    goal.assign (← mkOfEqTrue (← result.getProof))
    replaceMainGoal []
  else
    if result.expr == tgt then throwError "to_additive made no progress"
    replaceMainGoal [← applySimpResultToTarget goal tgt result]


/-- Use `to_additive` to rewrite hypothesis `h`. -/
def toAdditiveLocalDecl (fvarId : FVarId) : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← fvarId.getType)
  let goal ← getMainGoal
  let result ← toAdditiveCore tgt
  if result.expr == tgt then throwError "to_additive made no progress"
  match ← applySimpResultToLocalDecl goal fvarId result false with
    | none => replaceMainGoal []
    | some (_, newGoal) => replaceMainGoal [newGoal]

/-- The `to_additive` tactic, which solves converts equations in the language of
multiplicative commutative additive groups (or monoids) to those in additive structures. -/
elab_rules : tactic | `(tactic| to_additive $[$loc]?) => do
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  withLocation loc
    (atLocal := toAdditiveLocalDecl)
    (atTarget := toAdditiveTarget)
    (failed := fun _ ↦ throwError "to_additive made no progress")


open Lean Elab Meta Tactic
/-- The `mabel1` tactic, which solves equations in the language of
multiplicative commutative additive groups (or monoids). -/
syntax (name := mabel1) "mabel1" "!"? : tactic
elab_rules : tactic | `(tactic| mabel1 $[!%$tk]?) => withMainContext do
  try toAdditiveTarget
  catch | e => throwError "mabel1 made no progress: {e.toMessageData}"
  let tm := if tk.isSome then .default else .reducible
  let some (_, e₁, e₂) := (← whnfR <| ← getMainTarget).eq?
    | throwError "mabel1 made no progress"
  trace[mabel] "running on an equality `{e₁} = {e₂}`."
  let c ← Abel.mkContext e₁
  closeMainGoal `mabel1 <| ← AtomM.run tm <| ReaderT.run (r := c) do
    let (e₁', p₁) ← Abel.eval e₁
    trace[mabel] "found `{p₁}`, a proof that `{e₁} = {e₁'.e}`"
    let (e₂', p₂) ← Abel.eval e₂
    trace[mabel] "found `{p₂}`, a proof that `{e₂} = {e₂'.e}`"
    unless ← isDefEq e₁' e₂' do
      throwError "mabel1 found that the two sides were not equal"
    trace[mabel] "verified that the simplified forms are identical"
    mkEqTrans p₁ (← mkEqSymm p₂)

@[inherit_doc mabel1] macro (name := mabel1!) "mabel1!" : tactic => `(tactic| mabel1 !)

/--
Tactic for evaluating expressions in multiplicative abelian groups.
Fails if the target is not an equality.

* `mabel!` will use a more aggressive reducibility setting to determine equality of atoms.

For example:

```
example [CommMonoid α] (a b : α) : a * (b * a) = a * a * b := by mabel
example [CommGroup α] (a : α) : a^(3 : ℤ) = a * a^(2 : ℤ) := by mabel
```

See also the `abel` tactic.
-/
macro (name := mabel) "mabel" : tactic =>
  `(tactic| first | mabel1)
@[inherit_doc mabel] macro "mabel!" : tactic =>
  `(tactic| first | mabel1!)

/--
Simplification tactic for expressions in the language of multiplicative abelian groups,
which rewrites all group expressions into a normal form.
* `mabel_nf!` will use a more aggressive reducibility setting to identify atoms.
* `mabel_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `mabel_nf` will also recurse into atoms
* `mabel_nf` works as both a tactic and a conv tactic.
  In tactic mode, `mabel_nf at h` can be used to rewrite in a hypothesis.
-/
elab (name := mabelNF) "mabel_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do
  let mut cfg ← Abel.elabAbelNFConfig cfg
  if tk.isSome then cfg := { cfg with red := .default }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  try
    withLocation loc (toAdditiveLocalDecl) (toAdditiveTarget)
      fun _ ↦ throwError "mabel_nf made no progress"
  catch
    | _ => throwError "mabel_nf made no progress"
  withLocation loc (Abel.abelNFLocalDecl s cfg) (Abel.abelNFTarget s cfg)
     fun _ ↦ throwError "mabel_nf made no progress"

/--
The tactic `mabel` evaluates expressions in multiplicative abelian groups.
This is the conv tactic version, which rewrites a target which is an abel equality to `True`.

See also the `mabel` tactic.
-/
macro (name := abelConv) "mabel" : conv =>
  `(conv| first | discharge => mabel1)
@[inherit_doc abelConv] macro "mabel!" : conv =>
  `(conv| first | discharge => mabel1!)
end Mathlib.Tactic.MAbel
