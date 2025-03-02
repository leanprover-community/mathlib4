/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Category.Basic

/-!
The `check_compositions` tactic,
which checks the typing of categorical compositions in the goal,
reporting discrepancies at "instances and reducible" transparency.

Reports from this tactic do not necessarily indicate a problem,
although typically `simp` should reduce rather than increase the reported discrepancies.

`check_compositions` may be useful in diagnosing uses of `erw` in the category theory library.
-/

namespace Mathlib.Tactic.CheckCompositions

open CategoryTheory

open Lean Meta Elab Tactic

/-- Find appearances of `CategoryStruct.comp C inst X Y Z f g`, and apply `f` to each. -/
def forEachComposition (e : Expr) (f : Expr → MetaM Unit) : MetaM Unit := do
  e.forEach (fun e ↦ if e.isAppOfArity ``CategoryStruct.comp 7 then f e else pure ())

/-- Given a composition `CategoryStruct.comp _ _ X Y Z f g`,
infer the types of `f` and `g` and check whether their sources and targets agree,
at "instances and reducible" transparency, with `X`, `Y`, and `Z`,
reporting any discrepancies. -/
def checkComposition (e : Expr) : MetaM Unit := do
  match_expr e with
  | CategoryStruct.comp _ _ X Y Z f g =>
    match_expr ← inferType f with
    | Quiver.Hom _ _ X' Y' =>
      withReducibleAndInstances do
        if !(← isDefEq X' X) then
          logInfo m!"In composition\n  {e}\nthe source of\n  {f}\nis\n  {X'}\nbut should be\n  {X}"
        if !(← isDefEq Y' Y) then
          logInfo m!"In composition\n  {e}\nthe target of\n  {f}\nis\n  {Y'}\nbut should be\n  {Y}"
    | _ => throwError "In composition\n  {e}\nthe type of\n  {f}\nis not a morphism."
    match_expr ← inferType g with
    | Quiver.Hom _ _ Y' Z' =>
      withReducibleAndInstances do
        if !(← isDefEq Y' Y) then
          logInfo m!"In composition\n  {e}\nthe source of\n  {g}\nis\n  {Y'}\nbut should be\n  {Y}"
        if !(← isDefEq Z' Z) then
          logInfo m!"In composition\n  {e}\nthe target of\n  {g}\nis\n  {Z'}\nbut should be\n  {Z}"
    | _ => throwError "In composition\n  {e}\nthe type of\n  {g}\nis not a morphism."
  | _ => throwError "{e} is not a composition."

/-- Check the typing of categorical compositions in an expression. -/
def checkCompositions (e : Expr) : MetaM Unit := do
  forEachComposition e checkComposition

/-- Check the typing of categorical compositions in the goal. -/
def checkCompositionsTac : TacticM Unit := withMainContext do
  let e ← getMainTarget
  checkCompositions e

/-- For each composition `f ≫ g` in the goal,
which internally is represented as `CategoryStruct.comp C inst X Y Z f g`,
infer the types of `f` and `g` and check whether their sources and targets agree
with `X`, `Y`, and `Z` at "instances and reducible" transparency,
reporting any discrepancies.

An example:

```
example (j : J) :
    colimit.ι ((F ⋙ G) ⋙ H) j ≫ (preservesColimitIso (G ⋙ H) F).inv =
      H.map (G.map (colimit.ι F j)) := by

  -- We know which lemma we want to use, and it's even a simp lemma, but `rw`
  -- won't let us apply it
  fail_if_success rw [ι_preservesColimitIso_inv]
  fail_if_success rw [ι_preservesColimitIso_inv (G ⋙ H)]
  fail_if_success simp only [ι_preservesColimitIso_inv]

  -- This would work:
  -- erw [ι_preservesColimitIso_inv (G ⋙ H)]

  -- `check_compositions` checks if the two morphisms we're composing are
  -- composed by abusing defeq, and indeed it tells us that we are abusing
  -- definitional associativity of composition of functors here: it prints
  -- the following.

  -- info: In composition
  --   colimit.ι ((F ⋙ G) ⋙ H) j ≫ (preservesColimitIso (G ⋙ H) F).inv
  -- the source of
  --   (preservesColimitIso (G ⋙ H) F).inv
  -- is
  --   colimit (F ⋙ G ⋙ H)
  -- but should be
  --   colimit ((F ⋙ G) ⋙ H)

  check_compositions

  -- In this case, we can "fix" this by reassociating in the goal, but
  -- usually at this point the right thing to do is to back off and
  -- check how we ended up with a bad goal in the first place.
  dsimp only [Functor.assoc]

  -- This would work now, but it is not needed, because simp works as well
  -- rw [ι_preservesColimitIso_inv]

  simp
```
-/
elab "check_compositions" : tactic => checkCompositionsTac

end Mathlib.Tactic.CheckCompositions
