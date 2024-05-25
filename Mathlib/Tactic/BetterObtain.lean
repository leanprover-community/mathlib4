import Mathlib.Tactic.Basic

/-! ## Attempt to remove stream-of-conciousness syntax from `obtain`

Create a clone `myobtain` which requires a proof directly. -/

namespace Lean.Elab.Tactic.RCases
open Lean.Meta Parser Tactic

/--
The `myobtain` tactic is a combination of `have` and `rcases`. See `rcases` for
a description of supported patterns.

```lean
myobtain ⟨patt⟩ : type := proof
```
is equivalent to
```lean
have h : type := proof
rcases h with ⟨patt⟩
```

If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

Unlike in the core lean version, `:= proof` is required, even if `type` is omitted.
-/
syntax (name := myobtain) "myobtain" (ppSpace Tactic.rcasesPatMed)? (" : " term)? " := " term,+ : tactic

--@[builtin_tactic Lean.Parser.Tactic.obtain]
@[tactic Lean.Parser.Tactic.RCases.myobtain]
def evalObtain' : Tactic := fun stx => do
  match stx with
  | `(tactic| myobtain%$tk $[$pat?:rcasesPatMed]? $[: $ty?]? := $val,*) =>
    let pat? ← liftM <| pat?.mapM RCasesPatt.parse
    if true then
      let pat  := pat?.getD (RCasesPatt.one tk `_)
      let pat  := pat.typed? tk ty?
      let tgts := val.getElems.map fun val => (none, val.raw)
      let g ← getMainGoal
      g.withContext do replaceMainGoal (← RCases.rcases tgts pat g)
  | _ => throwUnsupportedSyntax
