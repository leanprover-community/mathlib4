/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Tactic.Cases
import Mathlib.Tactic.PermuteGoals
import Mathlib.Init.Data.Int.Order

/-!
# lift tactic

This file defines the `lift` tactic, allowing the user to lift elements from one type to another
under a specified condition.

## Tags

lift, tactic
-/

--open Lean.TSyntax.Compat

/-- A class specifying that you can lift elements from `α` to `β` assuming `cond` is true.
  Used by the tactic `lift`. -/
class CanLift (α β : Sort _) (coe : outParam <| β → α) (cond : outParam <| α → Prop) where
  /-- An element of `α` that satisfies `cond` belongs to the range of `coe`. -/
  prf : ∀ x : α, cond x → ∃ y : β, coe y = x
#align can_lift CanLift

instance : CanLift ℤ ℕ (fun n : ℕ ↦ n) (0 ≤ ·) :=
  ⟨fun n hn ↦ ⟨n.natAbs, Int.natAbs_of_nonneg hn⟩⟩

/-- Enable automatic handling of pi types in `can_lift`. -/
instance Pi.canLift (ι : Sort _) (α β : ι → Sort _) (coe : ∀ i, β i → α i) (P : ∀ i, α i → Prop)
    [∀ i, CanLift (α i) (β i) (coe i) (P i)] :
    CanLift (∀ i, α i) (∀ i, β i) (fun f i ↦ coe i (f i)) fun f ↦ ∀ i, P i (f i) where
  prf f hf := ⟨fun i => Classical.choose (CanLift.prf (f i) (hf i)),
    funext fun i => Classical.choose_spec (CanLift.prf (f i) (hf i))⟩
#align pi.can_lift Pi.canLift

theorem Subtype.exists_pi_extension {ι : Sort _} {α : ι → Sort _} [ne : ∀ i, Nonempty (α i)]
    {p : ι → Prop} (f : ∀ i : Subtype p, α i) :
    ∃ g : ∀ i : ι, α i, (fun i : Subtype p => g i) = f := by
  haveI : DecidablePred p := fun i ↦ Classical.propDecidable (p i)
  exact ⟨fun i => if hi : p i then f ⟨i, hi⟩ else Classical.choice (ne i),
    funext fun i ↦ dif_pos i.2⟩
#align subtype.exists_pi_extension Subtype.exists_pi_extension

instance PiSubtype.canLift (ι : Sort _) (α : ι → Sort _) [∀ i, Nonempty (α i)] (p : ι → Prop) :
    CanLift (∀ i : Subtype p, α i) (∀ i, α i) (fun f i => f i) fun _ => True where
  prf f _ := Subtype.exists_pi_extension f
#align pi_subtype.can_lift PiSubtype.canLift

-- TODO: test if we need this instance in Lean 4
instance PiSubtype.canLift' (ι : Sort _) (α : Sort _) [Nonempty α] (p : ι → Prop) :
    CanLift (Subtype p → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι (fun _ => α) p
#align pi_subtype.can_lift' PiSubtype.canLift'

instance Subtype.canLift {α : Sort _} (p : α → Prop) :
    CanLift α { x // p x } Subtype.val p where prf a ha :=
  ⟨⟨a, ha⟩, rfl⟩
#align subtype.can_lift Subtype.canLift

namespace Mathlib.Tactic

open Lean Parser Tactic Elab Tactic Meta

/-- Lift an expression to another type.
* Usage: `'lift' expr 'to' expr ('using' expr)? ('with' id (id id?)?)?`.
* If `n : ℤ` and `hn : n ≥ 0` then the tactic `lift n to ℕ using hn` creates a new
  constant of type `ℕ`, also named `n` and replaces all occurrences of the old variable `(n : ℤ)`
  with `↑n` (where `n` in the new variable). It will remove `n` and `hn` from the context.
  + So for example the tactic `lift n to ℕ using hn` transforms the goal
    `n : ℤ, hn : n ≥ 0, h : P n ⊢ n = 3` to `n : ℕ, h : P ↑n ⊢ ↑n = 3`
    (here `P` is some term of type `ℤ → Prop`).
* The argument `using hn` is optional, the tactic `lift n to ℕ` does the same, but also creates a
  new subgoal that `n ≥ 0` (where `n` is the old variable).
  This subgoal will be placed at the top of the goal list.
  + So for example the tactic `lift n to ℕ` transforms the goal
    `n : ℤ, h : P n ⊢ n = 3` to two goals
    `n : ℤ, h : P n ⊢ n ≥ 0` and `n : ℕ, h : P ↑n ⊢ ↑n = 3`.
* You can also use `lift n to ℕ using e` where `e` is any expression of type `n ≥ 0`.
* Use `lift n to ℕ with k` to specify the name of the new variable.
* Use `lift n to ℕ with k hk` to also specify the name of the equality `↑k = n`. In this case, `n`
  will remain in the context. You can use `rfl` for the name of `hk` to substitute `n` away
  (i.e. the default behavior).
* You can also use `lift e to ℕ with k hk` where `e` is any expression of type `ℤ`.
  In this case, the `hk` will always stay in the context, but it will be used to rewrite `e` in
  all hypotheses and the target.
  + So for example the tactic `lift n + 3 to ℕ using hn with k hk` transforms the goal
    `n : ℤ, hn : n + 3 ≥ 0, h : P (n + 3) ⊢ n + 3 = 2 * n` to the goal
    `n : ℤ, k : ℕ, hk : ↑k = n + 3, h : P ↑k ⊢ ↑k = 2 * n`.
* The tactic `lift n to ℕ using h` will remove `h` from the context. If you want to keep it,
  specify it again as the third argument to `with`, like this: `lift n to ℕ using h with n rfl h`.
* More generally, this can lift an expression from `α` to `β` assuming that there is an instance
  of `can_lift α β`. In this case the proof obligation is specified by `can_lift.cond`.
* Given an instance `can_lift β γ`, it can also lift `α → β` to `α → γ`; more generally, given
  `β : Π a : α, Type*`, `γ : Π a : α, Type*`, and `[Π a : α, can_lift (β a) (γ a)]`, it
  automatically generates an instance `can_lift (Π a, β a) (Π a, γ a)`.

`lift` is in some sense dual to the `zify` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.
-/
syntax (name := lift) "lift " term " to " term (" using " term)?
  (" with " ident (colGt ident)? (colGt ident)?)? : tactic

/-- Generate instance for the `lift` tactic. -/
def Lift.getInst (old_tp new_tp : Expr) : MetaM (Expr × Expr × Expr) := do
  let coe ← mkFreshExprMVar (some $ .forallE `a new_tp old_tp .default)
  let p ← mkFreshExprMVar (some $ .forallE `a old_tp (.sort .zero) .default)
  let inst_type ← mkAppM ``CanLift #[old_tp, new_tp, coe, p]
  let inst ← synthInstance inst_type -- TODO: catch error
  return (← instantiateMVars p, ← instantiateMVars coe, ← instantiateMVars inst)

def Lift.mkSimpOnlyContext (hyps : List Name) (inv : Bool) : MetaM Simp.Context := do
  let hyps := hyps ++ Lean.Elab.Tactic.simpOnlyBuiltins
  let simpThms ← hyps.foldlM (·.addConst · (inv := inv)) ({} : SimpTheorems)
  return { config := {},
           simpTheorems := #[simpThms],
           congrTheorems := (← getSimpCongrTheorems) }

elab_rules : tactic | `(tactic| lift $e to $t $[using $h]?) => withMainContext do
  let e ← elabTerm e none
  let goal ← getMainGoal
  if !(← inferType (← goal.getType)).isProp then throwError
    "lift tactic failed. Tactic is only applicable when the target is a proposition."
  if !e.isFVar then throwError
    ("lift tactic failed. To lift an expression, provide explicit names for the new variable" ++
    " and the assumption.")
  let (p, coe, inst) ← Lift.getInst (← inferType e) (← Term.elabType t)
  let prf ←  match h with
    | some h => elabTermEnsuringType h (p.betaRev #[e])
    | none => mkFreshExprMVar (some (p.betaRev #[e]))
  let varName ← e.fvarId!.getUserName
  --let eqName := (eqName.map Syntax.getId).getD `rfl
  let prf_ex ← mkAppOptM ``CanLift.prf #[none, none, coe, p, inst, e, prf]
  let prf_ex ← instantiateMVars prf_ex
  let prfSyn ← prf_ex.toSyntax
  replaceMainGoal (← Std.Tactic.RCases.rcases #[(none, prfSyn)]
    (.tuple Syntax.missing <| [varName, `rfl].map (.one Syntax.missing)) goal)
  match prf with
  | .fvar prf => do
      let name ← prf.getUserName
      let g ← getMainGoal
      g.withContext do
        let decl ← getLocalDeclFromUserName name
        replaceMainGoal [(← g.clear decl.fvarId)]
  | _ => pure ()
  if h.isNone then setGoals (prf.mvarId! :: (← getGoals))



elab_rules : tactic | `(tactic| lift $e to $t $[using $h]?
    with $varName $eqName $[$prfName]?) => withMainContext do
  let e ← elabTerm e none
  let goal ← getMainGoal
  if !(← inferType (← goal.getType)).isProp then throwError
    "lift tactic failed. Tactic is only applicable when the target is a proposition."
  let (p, coe, inst) ← Lift.getInst (← inferType e) (← Term.elabType t)
  let prf ←  match h with
    | some h => elabTermEnsuringType h (p.betaRev #[e])
    | none => mkFreshExprMVar (some (p.betaRev #[e]))
  let varName := varName.getId
  let eqName := eqName.getId
  let prf_ex ← mkAppOptM ``CanLift.prf #[none, none, coe, p, inst, e, prf]
  let prf_ex ← instantiateMVars prf_ex
  let prfSyn ← prf_ex.toSyntax
  replaceMainGoal (← Std.Tactic.RCases.rcases #[(none, prfSyn)]
    (.tuple Syntax.missing <| [varName, eqName].map (.one Syntax.missing)) goal)
  if eqName ≠ `rfl then
    let eqIdent := mkIdent eqName
    for decl in ←getLCtx do
      if decl.userName != eqName then
        let declIdent := mkIdent decl.userName
        -- The line below fails if $declIdent is there only once.
        evalTactic (← `(tactic| simp only [← $eqIdent] at $declIdent $declIdent))
    evalTactic (← `(tactic| simp only [← $eqIdent]))
  match prf with
  | .fvar prf => do
      let name ← prf.getUserName
      let g ← getMainGoal
      g.withContext do
        let decl ← getLocalDeclFromUserName name
        if prfName.map Syntax.getId ≠ some name then replaceMainGoal [(← g.clear decl.fvarId)]
  | _ => pure ()
  if h.isNone then setGoals (prf.mvarId! :: (← getGoals))

end Mathlib.Tactic
