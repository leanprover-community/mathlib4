/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.Tactic.Push
public import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Translate.ToDual
import Mathlib.Util.CompileInductive

/-!
# Simproc for canceling morphisms with their inverses

This module implements the `cancelIso` simproc, which simplifies the composition of a
morphism and its inverse, given an expression of the form `f ≫ g`.

Assuming `f` is not a composition (as `Category.assoc` is tagged `@[simp]`),
if `g` is not a composition itself, it checks whether `f` is inverse to `g`
by checking if `f` has an `IsIso` instance and then by running `push inv` on `inv f` and on `g`.
If the check succeeds, then `f ≫ g` is rewritten to `𝟙 _`.

If `g` is of the form `h ≫ k`, the procedure instead checks if `f` and `h` are inverses to each
other, and the procedure rewrites `f ≫ h ≫ k` to `k` if that is the case.
This special case is useful as `f ≫ (h ≫ k)` is in simp-normal form and does not
contain `f ≫ g` directly as a subterm.

For instance, the simproc will successfully rewrite expressions such as
`F.map (G.map (inv (H.map (e.hom)))) ≫ F.map (G.map (H.map (e.inv)))` to `𝟙 _`
because `CategoryTheory.Functor.map_inv` is a `@[push ←]` lemma, and
`CategoryTheory.IsIso.Iso.inv_hom` is a `@[push]` lemma.

This procedure is mostly intended as a post-procedure: it will work better if `f` and `g`
have already been traversed beforehand.
-/

public meta section
open Lean Meta CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.CancelIso

/-- Version of `IsIso.hom_inv_id` for internal use of the `cancelIso` simproc. Do not use. -/
@[to_dual none]
lemma hom_inv_id_of_eq {C : Type*} [Category* C] {x y : C}
    (f : x ⟶ y) [IsIso f] (g : y ⟶ x) (h : inv f = g) : f ≫ g = 𝟙 _ := by
  rw [← h]
  exact IsIso.hom_inv_id f

/-- Version of `IsIso.hom_inv_id_assoc` for internal use of the `cancelIso` simproc. Do not use. -/
@[to_dual none]
lemma hom_inv_id_of_eq_assoc {C : Type*} [Category* C] {x y : C}
    (f : x ⟶ y) [IsIso f] (g : y ⟶ x) (h : inv f = g) {z : C} (k : x ⟶ z) : f ≫ g ≫ k = k := by
  rw [← h]
  exact IsIso.hom_inv_id_assoc f k

/-- Given expressions `C x y z f g` assumed to represent
composable morphisms `f : x ⟶ y` and `g : y ⟶ z` in a category `C`,
check if `g` is equal to the inverse of `f` by
1. first checking the objects match (i.e x = z).
2. Checking that `f` is an isomorphism by looking for an `IsIso` instance,
  allowing us to write `inv f`.
3. running `push inv` on both `inv f` and `g`, and checking that the results are equal.

If they are inverse, return a proof of `inv f = g`.
If any of the tests above fail, return none. -/
def tryCancelPair (C x y z f g : Expr) : MetaM (Option Expr) := do
  -- Check the objects match
  unless ← withNewMCtxDepth (isDefEq z x) do return none
  -- Run `push` on both sides.
  let inv_f ← try mkAppOptM ``CategoryTheory.inv #[C, none, x, y, f, none] catch _ => return none
  let pushed_inv ← Push.pushCore (.const ``CategoryTheory.inv) {} none inv_f
  let pushed_g ← Push.pushCore (.const ``CategoryTheory.inv) {} none g
  -- Check if the "inv"-normal forms match
  unless ← withNewMCtxDepth (isDefEq pushed_inv.expr pushed_g.expr) do return none
  -- builds and return the proof of `inv f = g`.
  return ← mkEqTrans
    (← pushed_inv.proof?.getDM (mkEqRefl inv_f))
    (← (← pushed_g.proof?.mapM mkEqSymm).getDM (mkEqRefl g))

/-- `cancelIso` simplifies the composition of a morphism and its inverse,
given an expression of the form `f ≫ g`.

Assuming `f` is not a composition (as `Category.assoc` is tagged `@[simp]`),
if `g` is not a composition itself, it checks whether `f` is inverse to `g`
by checking if `f` has an `IsIso` instance and then by running `push inv` on `inv f` and on `g`.
If the check succeeds, then `f ≫ g` is rewritten to `𝟙 _`.

If `g` is of the form `h ≫ k`, the procedure instead checks if `f` and `h` are inverses to each
other, and the procedure rewrites `f ≫ h ≫ k` to `k` if that is the case.
This special case is useful as `f ≫ (h ≫ k)` is in simp-normal form and does not
contain `f ≫ g` directly as a subterm.

For instance, the simproc will successfully rewrite expressions such as
`F.map (G.map (inv (H.map (e.hom)))) ≫ F.map (G.map (H.map (e.inv)))` to `𝟙 _`
because `CategoryTheory.Functor.map_inv` is a `@[push ←]` lemma, and
`CategoryTheory.IsIso.Iso.inv_hom` is a `@[push]` lemma.

This procedure is mostly intended as a post-procedure: it will work better if `f` and `g`
have already been traversed beforehand. -/
def cancelIsoSimproc : Simp.Simproc := fun e => do
  let_expr CategoryStruct.comp C instCat x y t f g := e | return .continue
  match_expr g with
  -- Right-associated expressions needs their own logic.
  | CategoryStruct.comp _ _ _ z _ g h =>
    let some p₀ ← tryCancelPair C x y z f g | return .continue
    -- Builds the proof that `f ≫ g ≫ h = h.
    let P ← mkAppOptM ``hom_inv_id_of_eq_assoc #[C, none, x, y, f, none, g, p₀, none, h]
    return .done {expr := h, proof? := P}
  -- Otherwise, same logic but with hom_inv_id_of_eq instead of hom_inv_id_of_eq_assoc
  | _ =>
    let some p₀ ← tryCancelPair C x y t f g | return .continue
    let P ← mkAppOptM ``hom_inv_id_of_eq #[C, none, x, y, f, none, g, p₀]
    return .done {expr := ← mkAppOptM ``CategoryStruct.id #[C, instCat, x], proof? := P}

simproc _root_.cancelIso (CategoryStruct.comp (self := _) _ _) := cancelIsoSimproc

-- We can’t @[inherit_doc] directly on the simproc command.
attribute [inherit_doc cancelIsoSimproc] cancelIso

end Mathlib.Tactic.CategoryTheory.CancelIso
