/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Tactic.Basic
import Batteries.Lean.Expr
import Batteries.Lean.Meta.UnusedNames

/-!
# lift tactic

This file defines the `lift` tactic, allowing the user to lift elements from one type to another
under a specified condition.

## Tags

lift, tactic
-/

/-- A class specifying that you can lift elements from `α` to `β` assuming `cond` is true.
  Used by the tactic `lift`. -/
class CanLift (α β : Sort*) (coe : outParam <| β → α) (cond : outParam <| α → Prop) : Prop where
  /-- An element of `α` that satisfies `cond` belongs to the range of `coe`. -/
  prf : ∀ x : α, cond x → ∃ y : β, coe y = x

/-- The recursor provided by `CanLift`. -/
@[elab_as_elim]
theorem CanLift.cases
    {α : Sort*} {β : Sort*} {coe : β → α} {cond : α → Prop} [inst : CanLift α β coe cond]
    {motive : ∀ x : α, cond x → Prop} (coe : ∀ y h, motive (coe y) h) (a h) : motive a h := by
  obtain ⟨y, rfl⟩ := CanLift.prf (β := β) a h
  exact coe _ _

instance : CanLift Int Nat (fun n : Nat ↦ n) (0 ≤ ·) :=
  ⟨fun n hn ↦ ⟨n.natAbs, Int.natAbs_of_nonneg hn⟩⟩

/-- Enable automatic handling of pi types in `CanLift`. -/
instance Pi.canLift (ι : Sort*) (α β : ι → Sort*) (coe : ∀ i, β i → α i) (P : ∀ i, α i → Prop)
    [∀ i, CanLift (α i) (β i) (coe i) (P i)] :
    CanLift (∀ i, α i) (∀ i, β i) (fun f i ↦ coe i (f i)) fun f ↦ ∀ i, P i (f i) where
  prf f hf := ⟨fun i => Classical.choose (CanLift.prf (f i) (hf i)),
    funext fun i => Classical.choose_spec (CanLift.prf (f i) (hf i))⟩

theorem Subtype.exists_pi_extension {ι : Sort*} {α : ι → Sort*} [ne : ∀ i, Nonempty (α i)]
    {p : ι → Prop} (f : ∀ i : Subtype p, α i) :
    ∃ g : ∀ i : ι, α i, (fun i : Subtype p => g i) = f := by
  haveI : DecidablePred p := fun i ↦ Classical.propDecidable (p i)
  exact ⟨fun i => if hi : p i then f ⟨i, hi⟩ else Classical.choice (ne i),
    funext fun i ↦ dif_pos i.2⟩

instance PiSubtype.canLift (ι : Sort*) (α : ι → Sort*) [∀ i, Nonempty (α i)] (p : ι → Prop) :
    CanLift (∀ i : Subtype p, α i) (∀ i, α i) (fun f i => f i) fun _ => True where
  prf f _ := Subtype.exists_pi_extension f

-- TODO: test if we need this instance in Lean 4
instance PiSubtype.canLift' (ι : Sort*) (α : Sort*) [Nonempty α] (p : ι → Prop) :
    CanLift (Subtype p → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι (fun _ => α) p

instance Subtype.canLift {α : Sort*} (p : α → Prop) :
    CanLift α { x // p x } Subtype.val p where prf a ha :=
  ⟨⟨a, ha⟩, rfl⟩

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
  of `CanLift α β`. In this case the proof obligation is specified by `CanLift.prf`.
* Given an instance `CanLift β γ`, it can also lift `α → β` to `α → γ`; more generally, given
  `β : Π a : α, Type*`, `γ : Π a : α, Type*`, and `[Π a : α, CanLift (β a) (γ a)]`, it
  automatically generates an instance `CanLift (Π a, β a) (Π a, γ a)`.

`lift` is in some sense dual to the `zify` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.
-/
syntax (name := lift) "lift " term " to " term (" using " term)?
  (" with " ident (ppSpace colGt ident)? (ppSpace colGt ident)?)? : tactic

/-- Generate instance for the `lift` tactic. -/
def Lift.getInst (old_tp new_tp : Expr) : MetaM (Expr × Expr × Expr) := do
  let coe ← mkFreshExprMVar (some <| .forallE `a new_tp old_tp .default)
  let p ← mkFreshExprMVar (some <| .forallE `a old_tp (.sort .zero) .default)
  let inst_type ← mkAppM ``CanLift #[old_tp, new_tp, coe, p]
  let inst ← synthInstance inst_type -- TODO: catch error
  return (← instantiateMVars p, ← instantiateMVars coe, ← instantiateMVars inst)


/-- Main function for the `lift` tactic. -/
def Lift.main (e t : TSyntax `term) (hUsing : Option (TSyntax `term))
    (newVarNameStx newEqNameStx : Option (TSyntax `ident)) (keepUsing : Bool) : TacticM Unit :=
    withMainContext do
  -- Are we using a new variable for the lifted var?
  let isNewVar := !newVarNameStx.isNone
  -- Name of the new hypothesis containing the equality of the lifted variable with the old one
  -- rfl if none is given
  let (newEqNameStx, newEqName) := match newEqNameStx with
    | none => (Syntax.missing, `rfl)
    | some stx => (stx, stx.getId)
  -- Was a new hypothesis given?
  let isNewEq := newEqName != `rfl
  let e ← elabTerm e none
  let goal ← getMainGoal
  if !(← inferType (← instantiateMVars (← goal.getType))).isProp then throwError
    "lift tactic failed. Tactic is only applicable when the target is a proposition."
  if newVarNameStx == none ∧ !e.isFVar then throwError
    "lift tactic failed. When lifting an expression, a new variable name must be given"
  let (p, coe, inst) ← Lift.getInst (← inferType e) (← Term.elabType t)
  let prf ← match hUsing with
    | some h => elabTermEnsuringType h (p.betaRev #[e])
    | none => mkFreshExprMVar (some (p.betaRev #[e]))
  let (newVarNameStx, newVarName) ← match newVarNameStx with
                 | some v => pure (v.raw,  v.getId)
                 | none   => pure (Syntax.missing, ← e.fvarId!.getUserName)
  let prfEx ← mkAppOptM ``CanLift.prf #[none, none, coe, p, inst, e, prf]
  let prfEx ← instantiateMVars prfEx
  let prfSyn ← prfEx.toSyntax
  -- if we have a new variable, but no hypothesis name was provided, we temporarily use a dummy
  -- hypothesis name
  let (newEqNameStx, newEqName) ←
    if isNewVar && !isNewEq then
      pure (.missing, ← withMainContext <| getUnusedUserName `tmpVar)
    else
      pure (newEqNameStx, newEqName)
  let newEqIdent := mkIdent newEqName
  -- Run rcases on the proof of the lift condition
  replaceMainGoal (← Lean.Elab.Tactic.RCases.rcases #[(none, prfSyn)]
    (.tuple Syntax.missing <| [.one newVarNameStx newVarName, .one newEqNameStx newEqName]) goal)
  let newVarFVar ← withMainContext <| getFVarFromUserName newVarName
  -- Clear the "using" hypothesis if it's a variable in the context
  if prf.isFVar && !keepUsing then
    withMainContext do
      replaceMainGoal [← (← getMainGoal).clear prf.fvarId!]
  -- if we use a new variable, then substitute it everywhere
  if isNewVar then
    for decl in ← getLCtx do
      if decl.userName != newEqName then
        let declIdent := mkIdent decl.userName
        evalTactic (← `(tactic| simp -failIfUnchanged only [← $newEqIdent] at $declIdent:ident))
    evalTactic (← `(tactic| simp -failIfUnchanged only [← $newEqIdent]))
  else
    Elab.pushInfoLeaf <|
      .ofFVarAliasInfo { id := newVarFVar.fvarId!, baseId := e.fvarId!, userName := newVarName }
  -- Clear the temporary hypothesis used for the new variable name if applicable
  if isNewVar && !isNewEq then
    evalTactic (← `(tactic| clear $newEqIdent))
  if hUsing.isNone then withMainContext <| setGoals (prf.mvarId! :: (← getGoals))

-- elab_rules : tactic
--   | `(tactic| lift $e to $t $[using $h]?) => withMainContext <| Lift.main e t h none none false

-- elab_rules : tactic | `(tactic| lift $e to $t $[using $h]?
--     with $newVarName) => withMainContext <| Lift.main e t h newVarName none false

-- elab_rules : tactic | `(tactic| lift $e to $t $[using $h]?
--     with $newVarName $newEqName) => withMainContext <| Lift.main e t h newVarName newEqName false

macro_rules
| `(tactic| lift $e to $t $[using $h]? $[with $newVarName $[$newEqName]? $[$newPrfName]?]?) => do
  let h ← match h with
    | none => `(?lift)
    | some h => pure h
  let varName ← match newVarName with
    | none => if let `($e:ident) := e then pure e else
      Macro.throwUnsupported
    | some n => pure n
  let genTac : TSyntax `tactic ← match newEqName with
    | some (some eq) => `(tactic| (generalize $eq : $e = $varName at *; replace $eq := Eq.symm $eq))
    | _ => `(tactic| generalize $e = $varName at *)
  let prfName ← match newPrfName with
    | some (some n) => `(Term.funBinder| $n)
    | _ => `(_)
  `(tactic|
    $genTac;
     refine CanLift.cases (α := Int) (β := $t) (fun $varName $prfName => ?_) $e ?_
    )

#check fun _ => 1

  -- withMainContext do
  --   let ee ← Term.elabTerm e none
  --   let et ← Term.elabType t
  --   let (p, coe, inst) ← Lift.getInst (← inferType ee) et
  --   let prf ← match h with
  --   | some h => elabTermEnsuringType h (p.betaRev #[ee])
  --   | none => mkFreshExprMVar (some (p.betaRev #[ee]))
  --   let prfEx ← mkAppOptM ``CanLift.prf #[none, none, coe, p, inst, ee, prf]
  --   withLocal

  -- match h with
  -- | none => Lift.main e t h newVarName newEqName false
  -- | some h =>
  --   unless h.raw == newPrfName do
  --     throwErrorAt newPrfName "Renaming the `using` hypothesis is not supported"
  --   Lift.main e t h newVarName newEqName true

example (z : Int) (hz : 0 ≤ z + 3) : 0 ≤ (z + 3)^2 := by
  generalize hn : z + 3 = n at *
  refine CanLift.cases (α := Int) (β := Nat) ?_ z ?_
  sorry


example (z : Int) (hz : 0 ≤ z + 3) : 0 ≤ ((⟨z + 3, hz⟩ : {z : Int // 0 ≤ z}).val)^2 := by
  generalize hn : z + 3 = n at *
  induction n, hz using CanLift.cases (α := Int) (β := Nat) with | coe n hz => ?_

theorem foo (z : Int) (hz : 0 ≤ z + 3) : 0 ≤ ((⟨z + 3, hz⟩ : {z : Int // 0 ≤ z}).val)^2 := by
  lift z + 3 to Nat with y hy
  sorry
#print foo

end Mathlib.Tactic
