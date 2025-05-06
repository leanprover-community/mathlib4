/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.Tactic.CategoryTheory.RotateIsos.Lemmas -- contains the initial set of `Cancelable`

/-!
# The `rotate_isos` tactic

Given a term of the form `e : α₁ ≫ ⋯ ≫ αₖ = β₁ ≫ ⋯ ≫ βₗ`, or of the form
`e : α₁ ≪≫ ⋯ ≪≫ αₖ = β₁ ≪≫ ⋯ ≪≫ βₗ` (possibly not fully right-associated, or under ∀ binders),
the `rotate_isos` tactic moves specified numbers
of isomorphisms from the left-hand side of the equality to the right-hand side.
Depending on a flag given to the tactic, the isomorphisms are moved from the lhs starting from
the leftmost morphism or from the rightmost morphism.

```lean
variable {C : Type*} [Category C]

example (a b c d e : C) (g : b ≅ c) (h : d ≅ c) (i : d ⟶ e) (k : a ⟶ e)
    (hyp : ∀ (f : a ≅ b), f.hom ≫ g.hom ≫ h.inv ≫ i = k) :
    ∀ (f : a ≅ b), i = h.hom ≫ g.inv ≫ f.inv ≫ k := by
  rotate_isos ← 0 3 using hyp

```

The tactic analyzes terms in the given composition and detects morphisms that are isomorphisms
("movable") and constructs their inverses based on the following rules:
- The term is of type `e : X ≅ Y`. In this case, the term added to the opposite side of the equality
  is `e.symm`
- The term is of type `e.hom` (resp. `e.inv') for `e : _ ≅ _`. In this case, the term added to
  the opposite side of the equality is `e.inv` (resp. e.hom).
- The term is of type `e.app x` for a movable natural transformation `e`. In this case the term
  added to the opposite side of the equality is `e'.app _` where `e'` is the constructed inverse of
  `e`.
- The term is of type `F.map f` for a functor `F` and `f` is movable. In this case, the term
  added to the opposite side of the equality is `F.map f'` where `f'` is the constructed inverse
  of `f`.
- The term is of type `f` and `f` has an `IsIso` instance. In this case, the inverse is `inv f`.

This file also provides two terms elaborators: `rotate_isos%` and `rotate_isos_iff%`, that
are used to apply the tactic at a term and use it as a `e.g` a rewrite rule or as simp lemmas.

-/

open Lean Parser.Tactic Elab Command Elab.Tactic Meta _root_.CategoryTheory

namespace Tactic.CategoryTheory.RotateIsos

section Lemmas

variable {C : Type*} [Category C] {X Y : C}

/-- Version of `trans_assoc` used to left_associate compositions in a `simpOnlyNames` call within a
tactic. -/
theorem trans_assoc_rev {Z Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z') :
    α ≪≫ β ≪≫ γ = (α ≪≫ β) ≪≫ γ :=
  Iso.trans_assoc α β γ|>.symm

/-- Version of `comp_assoc` used to left_associate compositions in a `simpOnlyNames` call within a
tactic. -/
theorem comp_assoc_rev {Z Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ Z') :
    f ≫ g ≫ h = (f ≫ g) ≫ h :=
  Category.assoc f g h|>.symm

end Lemmas

/-- Auxiliary definition for `RotateIsosCore`, isolating the main loop of
the tactic. -/
def rotateIsosCoreAux (e : Expr) (a : ℕ) (rev : Bool) (try_id : Bool)
    (cancels : List Cancelable × Bool) :
    MetaM Expr := do
  match a with
  | 0 => return e
  | a' + 1 =>
    let (c::cancels', v) := cancels | throwError "Not enough cancelable morphisms in one \
      of the sides of the provided equality."
    -- We need to check the edge case in which there is only one morphism left to cancel
    -- In this case, we must use the `id_` versions of the lemmas in the
    -- `Cancelable` structure.
    -- We know we're in this case if we reached the last element of `cancels` and if the
    -- boolean value in the return type of `getCancelables` is set to true.
    -- We also check for edge cases where the rhs is an identity.
    match rev, (try_id && v && cancels'.length == 0) with
    | false, false =>
      -- Expression is of the form expr ≫ h = h' and we use `eq_inv_comp`.
      rotateIsosCoreAux (← mkAppM' c.eq_inv_comp #[e]) a' rev try_id (cancels', v)
    | false, true =>
      -- Expression is of the form expr = h, and we use `id_eq_inv_comp`.
      rotateIsosCoreAux (← mkAppM' c.id_eq_inv_comp #[e]) a' rev try_id (cancels', v)
    | true, false =>
      -- Expression is of the form h ≫ expr = h' and we use `eq_comp_inv`.
      rotateIsosCoreAux (← mkAppM' c.eq_comp_inv #[e]) a' rev try_id (cancels', v)
    | true, true =>
      -- Expression is of the form expr = h' and we use `id_eq_comp_inv`.
      rotateIsosCoreAux (← mkAppM' c.id_eq_comp_inv #[e]) a' rev try_id (cancels', v)

/-- Core for the rotate_isos tactic. Take as input an expression of the form
`f = g` between two (iso)morphisms in a category, as well as the number of
of cancellable morphisms to moves from the lhs to the rhs, and from the
rhs to the lhs, and returns an expression of type `e → e'`, where `e` is the original equality,
and `e'` is the equality in which the (iso)morphisms have been moved according to the arguments, as
well as a proof of the implication. -/
def rotateIsosCore (e : Expr) (a b : ℕ) (rev : Bool) : MetaM (Expr × Expr) := do
  -- We start by re-associating everything in the expression. We need to reassociate differently
  -- depending on wether we want to remove terms from the left or from the right, which depends
  -- `rev`
  -- SimpEq throws an error for us if `e` is not an equality.
  -- `g` will be abstracted in the return type.
  let e' ← whnfR e
  let g ← mkFreshExprMVar <| ← instantiateMVars e'
  let (s_e, p_e) ←
    if rev then simpEq (fun e => simpOnlyNames
        [``Iso.trans_symm, ``trans_assoc_rev, ``comp_assoc_rev]
      e (config := { decide := false })) e' g
    else simpEq (fun e => simpOnlyNames
        [``Iso.trans_symm, ``Iso.trans_assoc, ``Category.assoc]
      e (config := { decide := false })) e' g
  let some (_, lhs, rhs) := s_e.eq? | throwError "unreachable"
  let (cancels_lhs, cancels_rhs) :=
    (← getCancelables lhs false rev, ← getCancelables rhs true rev)
  let e' ← (do
    -- First pass.
    let e₁ ← rotateIsosCoreAux p_e a rev true cancels_lhs
    -- If we need to also move things from the rhs to the lhs, we first take the symmetric of the
    -- result of the first pass, reassociate in the opposite direction, and then do a second pass
    if b != 0 then
      let symm ← mkAppM ``Eq.symm #[e₁]
      let s_e ←
        if rev then simpEq (fun e => simpOnlyNames
            [``Iso.trans_symm, ``Iso.trans_assoc, ``Category.assoc]
          e (config := { decide := false })) (← inferType symm) symm
        else simpEq (fun e => simpOnlyNames
            [``Iso.trans_symm, ``trans_assoc_rev, ``comp_assoc_rev]
          e (config := { decide := false })) (← inferType symm) symm
      return ← mkAppM ``Eq.symm #[← rotateIsosCoreAux s_e.2 b (not rev) (a == 0) cancels_rhs]
    else return e₁)
  let final_expr ← simpEq (fun e => simpOnlyNames
      [``Iso.trans_symm, ``Iso.trans_assoc, ``Iso.symm_symm_eq, ``IsIso.inv_inv,
        ``Functor.mapIso_symm, ``Category.assoc, ``Category.id_comp, ``Category.comp_id,
        ``Iso.trans_refl, ``Iso.refl_trans]
      e (config := { decide := false })) (← inferType e') e'
  return (← mkLambdaFVars #[g] (← mkExpectedTypeHint final_expr.2 final_expr.1)
    (binderInfoForMVars := .default), final_expr.1)

/-- A variant of `rotateIsosCore` in which we return an expression of the form `e ↔ e'`
(see the `rotateIsosCore` docstring for interpretation of `e` and `e''`) which is useful in case
we want to use the tactic at a goal and need the reverse direction to close the goal. -/
def rotateIsosCoreIff (e : Expr) (a b : ℕ) (rev : Bool) : MetaM (Expr × Expr) := do
  -- The idea is to apply `rotateIsosCore` twice: once with the given expression, and then
  -- apply it again to the result, with `a` and `b` swapped, as well as the truth value of `rev`.
  -- This yields an expression equivalent to the original up to some simp lemmas.
  let (mp, e') ← rotateIsosCore e a b rev
  let (mp', e'') ← rotateIsosCore e' b a !rev
  -- We build a proof that the target of `e''` is equivalent to `e`.
  let some r ← Simp.Result.ofTrue <| ← simpOnlyNames
      [``Iso.trans_symm, ``Iso.trans_assoc, ``Iso.symm_symm_eq, ``IsIso.inv_inv,
        ``Functor.mapIso_symm, ``Category.assoc, ``Category.id_comp, ``Category.comp_id,
        ``Iso.trans_refl, ``Iso.refl_trans]
      (mkIff e e'') (config := { decide := false }) | throwError "Could not prove that {e} ↔ {e''}"
  let g ← mkFreshExprMVar e'
  let m₀ ← mkAppM' mp' #[g] -- of type e''
  return (← mkAppM ``Iff.intro #[mp, ← mkLambdaFVars #[g] <| ← mkAppM ``Iff.mpr #[r, m₀]], e')

/-- Wrapper to apply `RotateIsosCore` for expressions in binders. -/
def rotateIsosForallTelescope (e : Expr) (a b : ℕ) (rev : Bool) : MetaM Expr := do
  mapForallTelescope (fun e => do mkAppM' (← rotateIsosCore (← inferType e) a b rev).1 #[e]) e

/-- Wrapper to apply `RotateIsosCore` for expressions in binders. -/
def rotateIsosForallTelescopeIff (e : Expr) (a b : ℕ) (rev : Bool) : MetaM Expr := do
  mapForallTelescope (fun e => do return (← rotateIsosCoreIff (← inferType e) a b rev).1) e

open Term in
/-- A term elaborator to produce the result of `rotate_isos` at a term.. -/
elab "rotate_isos% " p:patternIgnore("←" <|> "<-")? ppSpace n:num ppSpace m:num ppSpace t:term :
    term => do rotateIsosForallTelescope (← elabTerm t none) n.getNat m.getNat p.isSome

open Term in
/-- A term elaborator to produce the iff statement betwen the given term and the result of
running `rotate_isos` at that term. -/
elab "rotate_isos_iff% " p:patternIgnore("←" <|> "<-")? ppSpace n:num ppSpace m:num ppSpace t:term :
    term => do rotateIsosForallTelescopeIff (← elabTerm t none) n.getNat m.getNat p.isSome

/-- Wrapper to run `rotateIsosForallTelescope` at an hypothesis in the local context. -/
def rotateIsosAtHyp (a b : ℕ) (rev : Bool) (h : FVarId) (g : MVarId) :
    TacticM MVarId := do
  let d ← h.getDecl
  let new_h ← rotateIsosForallTelescope (← instantiateMVars <| .fvar h) a b rev
  let g ← g.clear h
  let (_, g) ← g.note d.userName new_h
  return g

/-- Wrapper to run `rotateIsosForallTelescope` at the current goal. -/
def rotateIsosAtGoal (a b : ℕ) (rev : Bool) (g : MVarId) : TacticM MVarId := withMainContext do
  let gty ← whnfR <| ← instantiateMVars <| ← g.getType
  let forall_iff ← rotateIsosForallTelescopeIff (.mvar g) a b rev
  let target_type ← forallTelescope (← inferType forall_iff)
    (fun xs t => do mkForallFVars xs t.appArg!)
  let (args, _, _) ← forallMetaTelescope <| gty
  -- g' is for the new goal
  let g' ← mkFreshExprSyntheticOpaqueMVar (target_type) (← g.getTag)
  let e₂ ← mkLambdaFVars args <|
    ← mkAppM'
      (← mkAppM ``Iff.mpr #[← mkAppOptM' forall_iff (args.map pure)])
      #[← mkAppOptM' g' (args.map pure)]
  -- The metavariable `g` might be a syntheticOpaque MVar so IsDefeq can’t assign it.
  let _ ← isDefEq (← g.getType) (← instantiateMVars <| ← inferType e₂)
  let _ ← isDefEq (.mvar g) (← instantiateMVars e₂)
  g.assign e₂
  return (← instantiateMVars g').mvarId!

/--
# The `rotate_isos` tactic

Given a term of the form `e : α₁ ≫ ⋯ ≫ αₖ = β₁ ≫ ⋯ ≫ βₗ`, or of the form
`e : α₁ ≪≫ ⋯ ≪≫ αₖ = β₁ ≪≫ ⋯ ≪≫ βₗ` (possibly not fully right-associated, or under ∀ binders),
the `rotate_isos` tactic moves specified numbers
of isomorphisms from the left-hand side of the equality to the right-hand side.
Depending on a flag given to the tactic, the isomorphisms are moved from the lhs starting from
the leftmost morphism or from the rightmost morphism.

Note that the tactic will first simplify the given expression according to some basic category
theory rules, such as `Functor.map_comp` and `Iso.trans_hom`.
In particular, within the expression `F.map (f ≪≫ g).hom`, the first morphism the tactic recognizes
will be `F.map f.hom`. So beware that in the event that a composition `f ≫ g` is an isomorphisms but
neither `f` nor `g` is, the tactic might not count `f ≫ g` as an isomorphisms.

Valid syntaxes are
* `rotate_isos n m` : move the first `n` (starting from the left) morphism from the lhs to the
  rhs of the current goal, and move the last `m` morphisms from the rhs to the rhs.
  The resulting expression is ther reasociated from left to right, composition of a morphism with
  its inverse are removed, and composition with idenitiy are removed.
* `rotate_isos ← n m`: same as above, but instead moves the last `n` morphism of the lhs to the rhs
  and the first `m` morphism of the rhs to the lhs.
* `rotate_isos n m at h₁,⋯,hₙ` or `rotate_isos ← n m at h₁, …, hₙ`: replace local hypotheses
  `h₁, …, hₙ` with the result of running `rotate_isos` at their expressions.
* `rotate_isos n m using t` or `rotate_isos ← n m using t`: runs `rotate_isos` at the goal, and then
  tries to close it by matching it with the term obtained from `t` by left-associating compositions
  removing compositions with identities, and simplifying compositions of a morphism with its
  inverse. A particular kind is `rotate_isos n m using rfl`, which tries to solve the goal by
  simplifying the resulting expression in the way described above.
  Note that using a `using` clause will turn `rotate_isos` into a finishing tactic, and will
  throw an error if it fails to close the current goal.
-/
syntax (name := rotate_isos) "rotate_isos "
    ("←" <|> "<-")? ppSpace num ppSpace num ppSpace ("using " term)? (location)? : tactic

elab_rules : tactic |
    `(tactic| rotate_isos $[$rev]? $a:num $b:num $[using $use]? $[$loc]?) => do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := fun h => do
      if use.isSome then throwUnsupportedSyntax
      replaceMainGoal [← rotateIsosAtHyp a.getNat b.getNat rev.isSome h <| ← getMainGoal])
    (atTarget := withMainContext do
      replaceMainGoal [← rotateIsosAtGoal a.getNat b.getNat rev.isSome <| ← getMainGoal]
      if let some t := use then
        -- Needed to make the unusedSimpa linter happy with "using rfl"
        if t.raw.matchesIdent `rfl then
          evalTactic <| ← `(tactic|
            simp only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_symm_eq, IsIso.inv_inv,
              Functor.mapIso_symm, Category.assoc, Category.id_comp, Category.comp_id,
              Iso.trans_refl, Iso.refl_trans]; done)
        else
          evalTactic <| ← `(tactic|
            simpa only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_symm_eq, IsIso.inv_inv,
              Functor.mapIso_symm, Category.assoc, Category.id_comp, Category.comp_id,
              Iso.trans_refl, Iso.refl_trans] using $t))
    (failed := fun _ => throwError "rotate_isos failed")

end Tactic.CategoryTheory.RotateIsos
