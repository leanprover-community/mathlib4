/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kyle Miller, Damiano Testa
-/
import Std.Lean.Meta.Inaccessible

/-!
#  `extract_goal`: Format the current goal as a stand-alone example

Useful for testing tactics or creating
[minimal working examples](https://leanprover-community.github.io/mwe.html).

```lean
example (i j k : Nat) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := by
  extract_goal

/-
theorem extracted_1 (i j k : Nat) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := sorry
-/
```

* TODO: Add tactic code actions?
* Output may produce lines with more than 100 characters

### Caveat

The extracted goal may depend on imports, since it relies on delaboration(?).
Also, the extracted goal may not be equivalent to the given goal.

```lean
-- `theorem int_eq_nat` is the output of the `extract_goal` from the example below
-- the type ascription is removed and the `↑` is replaced by `Int.ofNat`:
-- Lean infers the correct (false) statement
theorem int_eq_nat {z : Int} : ∃ n, Int.ofNat n = z := sorry

example {z : Int} : ∃ n : Nat, ↑n = z := by
  extract_goal  -- produces `int_eq_nat`
  apply int_eq_nat  -- works
```

However, importing `Std.Classes.Cast`, makes `extract_goal` produce a different theorem

```lean
import Std.Classes.Cast

-- `theorem extracted_1` is the output of the `extract_goal` from the example below
-- the type ascription is erased and the `↑` is untouched:
-- Lean infers a different statement, since it fills in `↑` with `id` and uses `n : Int`
theorem extracted_1 {z : Int} : ∃ n, ↑n = z := ⟨_, rfl⟩

example {z : Int} : ∃ n : Nat, ↑n = z := by
  extract_goal
  apply extracted_1
/-
tactic 'apply' failed, failed to unify
  ∃ n, n = ?z
with
  ∃ n, ↑n = z
z: Int
⊢ ∃ n, ↑n = z
-/
```

Similarly, the extracted goal may fail to type-check:
```lean
example (a : α) : ∃ f : α → α, f a = a := by
  extract_goal
  exact ⟨id, rfl⟩

theorem extracted_1.{u_1} {α : Sort u_1} (a : α) : ∃ f, f a = a := sorry
-- `f` is uninterpreted: `⊢ ∃ f, sorryAx α true = a`
```
-/

open Lean Elab Tactic

/--
`extract_goal` formats the current goal as a stand-alone theorem or definition.
It tries to produce an output that can be copy-pasted and just work.

By default it cleans up the local context. To use the full local context, use `extract_goal*`.
-/
elab (name := extractGoal) "extract_goal" full?:&"*"? name?:(colGt ppSpace ident)? : tactic => do
  let name ← if let some name := name?
             then pure name.getId
             else mkAuxName ((← getCurrNamespace) ++ `extracted) 1
  let msg ← withoutModifyingEnv <| withoutModifyingState do
    let mut g ← getMainGoal
    unless full?.isSome do
      g ← g.cleanup
    (g, _) ← g.renameInaccessibleFVars
    (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := true) (← g.getDecl).lctx.getFVarIds
    let ty ← instantiateMVars (← g.getType)
    if ty.hasExprMVar then
      -- TODO: turn metavariables into new hypotheses?
      throwError "Extracted goal has metavariables: {ty}"
    let ty ← Term.levelMVarToParam ty
    let seenLevels := collectLevelParams {} ty
    let levels := (← Term.getLevelNames).filter
                    fun u => seenLevels.visitedLevel.contains (.param u)
    addAndCompile <| Declaration.axiomDecl
      { name := name
        levelParams := levels
        isUnsafe := false
        type := ty }
    let sig ← addMessageContext <| MessageData.ofPPFormat { pp := fun
                | some ctx => ctx.runMetaM <| PrettyPrinter.ppSignature name
                | none     => unreachable!
              }
    let cmd := if ← Meta.isProp ty then "theorem" else "def"
    pure m!"{cmd} {sig} := sorry"
  logInfo msg
