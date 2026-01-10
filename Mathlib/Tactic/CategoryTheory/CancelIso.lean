/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public meta import Mathlib.Tactic.Push
public import Mathlib.CategoryTheory.Iso

/-!
# Simproc for canceling morphisms with their inverses

This module implements the `cancelIso` simproc, which triggers on expressions of the form `f ≫ g`.

If `g` is not a composition itself, it checks whether `f` is inverse to `g`,
by checking if `f` has an `IsIso` instance, and then running `push inv` on `inv f` and on `g`.
If the check succeeds, then `f ≫ g` is rewritten to `𝟙 _`.

The procedure handles the case of an expression of the `g = h ≫ k` as a special case, in this case,
the procedure checks if `f` and `h` are inverses to each other, and the procedure thus rewrites
`f ≫ g ≫ h` to `h`. This is useful as simp-normal forms in category theory are right-associated.

For instance, the simproc will successfully rewrite expressions such as
`F.map (G.map (inv (H.map (e.hom)))) ≫ F.map (G.map (H.map (e.inv)))` to `𝟙 _`
because `CategoyTheory.Functor.map_inv` is a `@[push ←]` lemma, and
`CategoyTheory.IsIso.Iso.inv_hom` is a `[push]` lemma.

This procedure is mostly intended as a post-procedure: it will work better if `f` and `g`
have already been traversed beforehand.

-/

public meta section
open Lean Meta CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.CancelIso

/-- Version of `IsIso.hom_inv_id` for internal use of the `cancelIso` simproc. Do not use. -/
lemma hom_inv_id_of_eq {C : Type*} [Category* C] {x y : C}
    (f : x ⟶ y) [IsIso f] (g : y ⟶ x) (h : inv f = g) : f ≫ g = 𝟙 _ := by
  rw [← h]
  exact IsIso.hom_inv_id f

/-- Version of `IsIso.hom_inv_id_assoc` for internal use of the `cancelIso` simproc. Do not use. -/
lemma hom_inv_id_of_eq_assoc {C : Type*} [Category* C] {x y : C}
    (f : x ⟶ y) [IsIso f] (g : y ⟶ x) (h : inv f = g) {z : C} (k : x ⟶ z) : f ≫ g ≫ k = k := by
  rw [← h]
  exact IsIso.hom_inv_id_assoc f k

/-- The `cancelIso` simproc triggers on expressions of the form `f ≫ g`.

If `g` is not a composition itself, it checks whether `f` is inverse to `g`
by checking if `f` has an `IsIso` instance and then by running `push inv` on `inv f` and on `g`.
If the check succeeds, then `f ≫ g` is rewritten to `𝟙 _`.

The procedure handles the case of an expression of the `g = h ≫ k` as a special case, in this case,
the procedure checks if `f` and `h` are inverses to each other, and the procedure rewrites
`f ≫ g ≫ h` to `h` if that is the case.
This is useful as simp-normal forms in category theory are right-associated.

For instance, the simproc will successfully rewrite expressions such as
`F.map (G.map (inv (H.map (e.hom)))) ≫ F.map (G.map (H.map (e.inv)))` to `𝟙 _`
because `CategoyTheory.Functor.map_inv` is a `@[push ←]` lemma, and
`CategoyTheory.IsIso.Iso.inv_hom` is a `[push]` lemma.

This procedure is mostly intended as a post-procedure: it will work better if `f` and `g`
have already been traversed beforehand. -/
def cancelIsoSimproc : Simp.Simproc := fun e => withReducible do -- is withReducible necessary here?
  let e_whnf ← whnf e
  let_expr CategoryStruct.comp C instCat x y t f g := e_whnf | return .continue
  match_expr g with
  -- Right_associated expressions needs their own logic.
  | CategoryStruct.comp _ _ _ z _ g h =>
    -- Can’t expect a cancelation if the objects don’t match
    unless z == x do return .continue
    -- Can’t expect a cancellation if `f` is not an iso.
    let some inst ← synthInstance? <| ← mkAppM ``IsIso #[f] | return .continue
    let inv_f ← mkAppOptM ``CategoryTheory.inv #[none, none, none, none, f, inst]
    let pushed_inv ← Mathlib.Tactic.Push.pushCore (.const ``CategoryTheory.inv) {} none inv_f
    let pushed_g ← Mathlib.Tactic.Push.pushCore (.const ``CategoryTheory.inv) {} none <| g
    unless ← isDefEq pushed_inv.expr pushed_g.expr do return .continue
    -- Builds the proof inv f = g first:
    let p₀ ← mkEqTrans (pushed_inv.proof?.getD (← mkEqRefl inv_f))
      (← mkEqSymm <| pushed_g.proof?.getD (← mkEqRefl g))
    -- Builds the proof that `f ≫ g ≫ h = h.
    let P ← mkAppOptM ``hom_inv_id_of_eq_assoc #[C, none, x, y, f, inst, g, p₀, none, h]
    return .done (.mk h (.some P) false)
  -- Otherwise, same logic but with hom_inv_id_of_eq instead of hom_inv_id_of_eq_assoc
  | _ =>
    unless t == x do return .continue
    let some inst ← synthInstance? <| ← mkAppM ``IsIso #[f] | return .continue
    let inv_f ← mkAppOptM ``CategoryTheory.inv #[none, none, none, none, f, inst]
    let pushed_inv ← Mathlib.Tactic.Push.pushCore (.const ``CategoryTheory.inv) {} none inv_f
    let pushed_g ← Mathlib.Tactic.Push.pushCore (.const ``CategoryTheory.inv) {} none <| g
    unless ← isDefEq pushed_inv.expr pushed_g.expr do return .continue
    let p₀ ← mkEqTrans (pushed_inv.proof?.getD (← mkEqRefl inv_f))
      (← mkEqSymm <| pushed_g.proof?.getD (← mkEqRefl g))
    let P ← mkAppOptM ``hom_inv_id_of_eq #[C, none, x, y, f, inst, g, p₀]
    return .done (.mk (← mkAppOptM ``CategoryStruct.id #[C, instCat, x]) (.some P) false)

end Mathlib.Tactic.CategoryTheory.CancelIso

/-- The `cancelIso` simproc triggers on expressions of the form `f ≫ g`.

If `g` is not a composition itself, it checks whether `f` is inverse to `g`
by checking if `f` has an `IsIso` instance and then by running `push inv` on `inv f` and on `g`.
If the check succeeds, then `f ≫ g` is rewritten to `𝟙 _`.

The procedure handles the case of an expression of the `g = h ≫ k` as a special case, in this case,
the procedure checks if `f` and `h` are inverses to each other, and the procedure rewrites
`f ≫ g ≫ h` to `h` if that is the case.
This is useful as simp-normal forms in category theory are right-associated.

For instance, the simproc will successfully rewrite expressions such as
`F.map (G.map (inv (H.map (e.hom)))) ≫ F.map (G.map (H.map (e.inv)))` to `𝟙 _`
because `CategoyTheory.Functor.map_inv` is a `@[push ←]` lemma, and
`CategoyTheory.IsIso.Iso.inv_hom` is a `[push]` lemma.

This procedure is mostly intended as a post-procedure: it will work better if `f` and `g`
have already been traversed beforehand. -/
simproc_decl cancelIso (CategoryStruct.comp (self := ?x) _ _) :=
  Mathlib.Tactic.CategoryTheory.CancelIso.cancelIsoSimproc
