/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.Sum.Order
public import Mathlib.SetTheory.ZFC.Constructible.DefWellOrder
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryConstructible

/-!
# Postfix stack programs for rudimentary evaluation

Prefix tree codes are useful for structural arguments, but a uniform
first-order evaluator would have to parse arbitrary subtree boundaries.  A
postfix stack program has a local transition semantics instead:

* a variable token pushes its generator value;
* an operation token pops the right and left operands and pushes their value.

The token lists still carry a Shortlex well-order. Hence every value in one
Gödel-definability step has a least evaluating program, and these least
programs give a well-order of that step. The local transition semantics admits
internalization by a finite set-coded execution trace.
-/

@[expose] public section

universe u v

namespace Constructible.Godel

namespace RudimentaryTerm

/-- Tokens of a postfix rudimentary stack program. -/
abbrev StackToken (α : Type u) := α ⊕ Fin 9

/-- Compile a term to postfix stack-machine instructions. -/
def stackProgram {α : Type u} :
    RudimentaryTerm α → List (StackToken α)
  | .var a => [.inl a]
  | .app i left right =>
      stackProgram left ++ stackProgram right ++ [.inr i]

/-- Execute one stack instruction.  The head of the list is the stack top. -/
noncomputable def runStackToken {α : Type u}
    (rho : α → ZFSet.{v}) :
    StackToken α → List ZFSet.{v} → Option (List ZFSet.{v})
  | .inl a, stack => some (rho a :: stack)
  | .inr i, right :: left :: rest =>
      some (op i left right :: rest)
  | .inr _, _ => none

/-- Execute a list of postfix instructions from left to right. -/
noncomputable def runStackProgram {α : Type u}
    (rho : α → ZFSet.{v}) :
    List (StackToken α) → List ZFSet.{v} → Option (List ZFSet.{v})
  | [], stack => some stack
  | token :: program, stack =>
      (runStackToken rho token stack).bind
        (runStackProgram rho program)

@[simp]
theorem runStackProgram_nil {α : Type u} (rho : α → ZFSet.{v})
    (stack : List ZFSet.{v}) :
    runStackProgram rho [] stack = some stack :=
  rfl

@[simp]
theorem runStackProgram_append {α : Type u} (rho : α → ZFSet.{v})
    (first second : List (StackToken α)) (stack : List ZFSet.{v}) :
    runStackProgram rho (first ++ second) stack =
      (runStackProgram rho first stack).bind
        (runStackProgram rho second) := by
  induction first generalizing stack with
  | nil => rfl
  | cons token first ih =>
      simp only [List.cons_append, runStackProgram]
      cases hstep : runStackToken rho token stack with
      | none => rfl
      | some next =>
          simp only [Option.bind_some]
          exact ih next

/-- Compiled programs push exactly the value of their source term. -/
@[simp]
theorem run_stackProgram {α : Type u} (rho : α → ZFSet.{v})
    (term : RudimentaryTerm α) (stack : List ZFSet.{v}) :
    runStackProgram rho (stackProgram term) stack =
      some (eval rho term :: stack) := by
  induction term generalizing stack with
  | var a =>
      rfl
  | app i left right ihLeft ihRight =>
      rw [stackProgram, runStackProgram_append,
        runStackProgram_append, ihLeft,
        Option.bind_some, ihRight,
        Option.bind_some]
      rfl

/-! ## The structural program well-order -/

/-- Variables precede operation tokens. -/
def stackTokenRel {α : Type u} (r : α → α → Prop) :
    StackToken α → StackToken α → Prop :=
  Sum.Lex r (fun i j : Fin 9 => i < j)

theorem stackTokenRel_isWellOrder {α : Type u}
    (r : α → α → Prop) [IsWellOrder α r] :
    IsWellOrder (StackToken α) (stackTokenRel r) := by
  unfold stackTokenRel
  infer_instance

/-- Shortlex comparison of postfix instruction lists. -/
def stackProgramRel {α : Type u} (r : α → α → Prop) :
    List (StackToken α) → List (StackToken α) → Prop :=
  List.Shortlex (stackTokenRel r)

theorem stackProgramRel_isWellOrder {α : Type u}
    (r : α → α → Prop) [IsWellOrder α r] :
    IsWellOrder (List (StackToken α)) (stackProgramRel r) := by
  letI : IsWellOrder (StackToken α) (stackTokenRel r) :=
    stackTokenRel_isWellOrder r
  letI : Std.Trichotomous (stackTokenRel r) :=
    { trichotomous :=
        (stackTokenRel_isWellOrder r).trichotomous }
  exact
    { wf := List.Shortlex.wf
        (IsWellFounded.wf : WellFounded (stackTokenRel r))
      trichotomous := fun first second =>
        (inferInstance :
          Std.Trichotomous (List.Shortlex (stackTokenRel r))).trichotomous
            first second }

/-! ## Least programs representing definable values -/

/-- Postfix programs which evaluate from the empty stack to the singleton `z`. -/
def representingStackPrograms (U z : ZFSet.{u}) :
    Set (List (StackToken (Option (Constructible.ZFCarrier U)))) :=
  {program |
    runStackProgram (rudimentaryGenerator U) program [] = some [z]}

theorem representingStackPrograms_nonempty {U z : ZFSet.{u}}
    (hz : z ∈ godelDef U) :
    (representingStackPrograms U z).Nonempty := by
  rcases (mem_godelDef_iff_exists_rudimentaryTerm.mp hz).2 with
    ⟨term, hterm⟩
  refine ⟨stackProgram term, ?_⟩
  simp only [representingStackPrograms, Set.mem_ofPred_eq,
    run_stackProgram]
  change eval (rudimentaryGenerator U) term = z at hterm
  simp only [hterm]

/-- The Shortlex-least postfix program evaluating to `z`. -/
noncomputable def leastStackProgram (U z : ZFSet.{u})
    (hz : z ∈ godelDef U)
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    List (StackToken (Option (Constructible.ZFCarrier U))) :=
  letI : IsWellOrder
      (List (StackToken (Option (Constructible.ZFCarrier U))))
      (stackProgramRel r) := stackProgramRel_isWellOrder r
  (IsWellFounded.wf : WellFounded (stackProgramRel r)).min
    (representingStackPrograms U z)
    (representingStackPrograms_nonempty hz)

@[simp]
theorem run_leastStackProgram (U z : ZFSet.{u})
    (hz : z ∈ godelDef U)
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    runStackProgram (rudimentaryGenerator U)
      (leastStackProgram U z hz r) [] = some [z] := by
  letI : IsWellOrder
      (List (StackToken (Option (Constructible.ZFCarrier U))))
      (stackProgramRel r) := stackProgramRel_isWellOrder r
  exact (IsWellFounded.wf : WellFounded (stackProgramRel r)).min_mem
    (representingStackPrograms U z)
    (representingStackPrograms_nonempty hz)

/-- The least-program map from one definability step to instruction lists. -/
noncomputable def leastStackProgramMap (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    DefCarrier U →
      List (StackToken (Option (Constructible.ZFCarrier U))) :=
  fun z => leastStackProgram U z.1 z.2 r

/-- Distinct definable values have distinct least evaluating programs. -/
theorem leastStackProgramMap_injective (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    Function.Injective (leastStackProgramMap U r) := by
  intro x y hxy
  apply Subtype.ext
  have hrun := congrArg
    (fun program =>
      runStackProgram (rudimentaryGenerator U) program []) hxy
  change
    runStackProgram (rudimentaryGenerator U)
        (leastStackProgram U x.1 x.2 r) [] =
      runStackProgram (rudimentaryGenerator U)
        (leastStackProgram U y.1 y.2 r) [] at hrun
  rw [run_leastStackProgram, run_leastStackProgram] at hrun
  exact (List.cons.inj (Option.some.inj hrun)).1

/-- Compare definable values by their least postfix programs. -/
noncomputable def defCarrierStackRel (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    DefCarrier U → DefCarrier U → Prop :=
  InvImage (stackProgramRel r) (leastStackProgramMap U r)

/-- The least postfix-program order well-orders one Gödel-definability step. -/
theorem defCarrierStackRel_isWellOrder (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    IsWellOrder (DefCarrier U) (defCarrierStackRel U r) := by
  letI : IsWellOrder
      (List (StackToken (Option (Constructible.ZFCarrier U))))
      (stackProgramRel r) := stackProgramRel_isWellOrder r
  exact
    { wf := InvImage.wf (leastStackProgramMap U r)
        (IsWellFounded.wf : WellFounded (stackProgramRel r))
      trichotomous :=
        (InvImage.trichotomous (r := stackProgramRel r)
          (leastStackProgramMap_injective U r)).trichotomous }

end RudimentaryTerm

end Constructible.Godel
