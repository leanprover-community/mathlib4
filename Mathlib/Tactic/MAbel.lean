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

lemma Additive_identity : Additive α = α := rfl

lemma ofMul_identity (x : α) : Additive.ofMul x = x := rfl

/-- Tactic for converting equations in the language of
multiplicative, commutative monoids and groups to those in the language
of additive, commutative monoids and groups.
-/
syntax (name := to_additive) "to_additive"  (location)? : tactic


/-- The core of `to_additive` which converts an equalites over
multiplicative structures to equalities over additive structures. -/
def toAdditiveCore (e₁ : Expr) (e₂ : Expr) : TacticM Unit := do
  -- TODO: Rewrite using Simp.Result
  let lhs ← delab e₁
  let rhs ← delab e₂
  evalTactic <| ← `(tactic|
    conv => {
      lhs
      rw [← ofMul_identity $lhs];
    } <;>
    conv => {
      rhs
      rw [ ← ofMul_identity $rhs]
    } <;>
    simp only [
      ofMul_mul, ofMul_pow, ofMul_one,
      ofMul_inv, ofMul_div, ofMul_zpow,
      ofMul_eq_zero, ofMul_div
    ])

/-- Use `to_additive` to rewrite the main goal. -/
def toAdditiveTarget : TacticM Unit := withMainContext do
  let some (_, e₁, e₂) := (← whnfR <| ← getMainTarget).eq?
    | throwError "to_additive requires an equality goal"
  try toAdditiveCore e₁ e₂
  catch | _ => throwError "to_additive made no progress"

/-- Use `to_additive` to rewrite hypothesis `h`. -/
def toAdditiveLocalDecl (fvarId : FVarId) : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← fvarId.getType)
  let some (_, e₁, e₂) := (← whnfR <| tgt).eq?
    | throwError "to_additive requires an equality goal"
  try toAdditiveCore e₁ e₂
  catch | _ => throwError "to_additive made no progress"
 

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
  let some (_, e₁, e₂) := (← whnfR <| ← getMainTarget).eq?
    | throwError "mabel1 requires an equality goal"
  try toAdditiveCore e₁ e₂
  catch | _ => throwError "mabel1 made no progress"
  try
    if tk.isSome then do
      evalTactic (← `(tactic| abel1!))
    else do
      evalTactic (← `(tactic| abel1))
  catch
    | e => throwError "mabel1 made no progress: {e.toMessageData}"

@[inherit_doc mabel1] macro (name := mabel1!) "mabel1!" : tactic => `(tactic| mabel1 !)

/--
Tactic for evaluating expressions in multiplicative abelian groups.

* `mabel!` will use a more aggressive reducibility setting to determine equality of atoms.
* `mabel1` fails if the target is not an equality.

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
  withLocation loc (toAdditiveLocalDecl) (toAdditiveTarget)
    fun _ ↦ throwError "mabel_nf made no progress"
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
