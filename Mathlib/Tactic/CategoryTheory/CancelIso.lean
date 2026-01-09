/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public meta import Mathlib.Tactic.Push
public import Mathlib.CategoryTheory.Iso

public meta section
open Lean Meta CategoryTheory

def cancelIso : Simp.Simproc := fun e => do
  let e_whnf ← whnf e
  logInfo "hello!"
  let_expr CategoryStruct.comp _ _ x₀ y₀ z₀ f gh := e_whnf |
    return .continue -- fails silently, but should’t happen.
  logInfo m!"first is {f}"
  logInfo m!"second  or second ≫ third gh is {gh}"
  let_expr CategoryStruct.comp _ _ y₁ z₁ t₁ g h := gh |
    logInfo "Binary comp was reached, continue"
    -- Now, we should check : is z₀ = x₀?
    if (← whnf z₀) == (← whnf x₀) then
      logInfo "loop!"
      -- Then, we might be lucky and we can try checking if f is an iso
      let some inst := ← (synthInstance? <| ← mkAppM ``IsIso #[f]) | 
        logInfo "not an iso, continuing"
        return .continue
      logInfo "it’s an iso!"
      return .continue
    else
      return .continue
  logInfo m!"it was second ≫ third and sec g is {g}"
  logInfo m!"third h is {h}"
  return .continue
  -- return .done { expr := e_whnf }

simproc_decl cancel_iso (CategoryStruct.comp (self := ?x) _ _) := cancelIso

example {C : Type*} [Category* C] {x y z t : C} (f : x ⟶ y) [IsIso g] (g : y ⟶ x) : f ≫ g  = 𝟙 _ := by
  simp [cancel_iso]

end

