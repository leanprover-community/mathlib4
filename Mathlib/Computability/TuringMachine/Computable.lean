/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Computability.Encoding
public import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Computable functions

This file contains the definition of a Turing machine with some finiteness conditions
(bundling the definition of TM2 in `StackTuringMachine.lean`), a definition of when a TM gives
a certain output (in a certain time), and the definition of computability (in polynomial time or
any time function) of a function between two types that have an encoding (as in `Encoding.lean`).

## Main theorems

- `idComputableInPolyTime` : a TM + a proof it computes the identity on a type in polytime.
- `idComputable`           : a TM + a proof it computes the identity on a type.
- `TM2ComputableInPolyTime.length_le` : the output of a polytime TM has polynomial length.

## Implementation notes

To count the execution time of a Turing machine, we have decided to count the number of times the
`step` function is used. Each step executes a statement (of type `Stmt`); this is a function, and
generally contains multiple "fundamental" steps (pushing, popping, and so on).
However, as functions only contain a finite number of executions and each one is executed at most
once, this execution time is up to multiplication by a constant the amount of fundamental steps.
-/

@[expose] public section



open Computability StateTransition


namespace Turing

/-- A bundled TM2 (an equivalent of the classical Turing machine, defined starting from
the namespace `Turing.TM2` in `StackTuringMachine.lean`), with an input and output stack,
a main function, an initial state and some finiteness guarantees. -/
structure FinTM2 where
  /-- index type of stacks -/
  {K : Type} [kDecidableEq : DecidableEq K]
  /-- A TM2 machine has finitely many stacks. -/
  [kFin : Fintype K]
  /-- input resp. output stack -/
  (k₀ k₁ : K)
  /-- type of stack elements -/
  (Γ : K → Type)
  /-- type of function labels -/
  (Λ : Type)
  /-- a main function: the initial function that is executed, given by its label -/
  (main : Λ)
  /-- A TM2 machine has finitely many function labels. -/
  [ΛFin : Fintype Λ]
  /-- type of states of the machine -/
  (σ : Type)
  /-- the initial state of the machine -/
  (initialState : σ)
  /-- a TM2 machine has finitely many internal states. -/
  [σFin : Fintype σ]
  /-- Each internal stack is finite. -/
  [Γk₀Fin : Fintype (Γ k₀)]
  /-- the program itself, i.e. one function for every function label -/
  (m : Λ → Turing.TM2.Stmt Γ Λ σ)

attribute [nolint docBlame] FinTM2.kDecidableEq

namespace FinTM2

section

variable (tm : FinTM2)

instance decidableEqK : DecidableEq tm.K :=
  tm.kDecidableEq

instance inhabitedσ : Inhabited tm.σ :=
  ⟨tm.initialState⟩

/-- The type of statements (functions) corresponding to this TM. -/
def Stmt : Type :=
  Turing.TM2.Stmt tm.Γ tm.Λ tm.σ

instance inhabitedStmt : Inhabited (Stmt tm) :=
  inferInstanceAs (Inhabited (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ))

/-- The type of configurations (functions) corresponding to this TM. -/
def Cfg : Type :=
  Turing.TM2.Cfg tm.Γ tm.Λ tm.σ

instance inhabitedCfg : Inhabited (Cfg tm) :=
  Turing.TM2.Cfg.inhabited _ _ _

/-- The step function corresponding to this TM. -/
@[simp]
def step : tm.Cfg → Option tm.Cfg :=
  Turing.TM2.step tm.m

/-- The largest number of `push` instructions in a statement of this TM. -/
def maxPushes : ℕ :=
  letI := tm.ΛFin
  Finset.univ.sup fun l ↦ (tm.m l).pushes

theorem pushes_le_maxPushes (l : tm.Λ) : (tm.m l).pushes ≤ tm.maxPushes :=
  letI := tm.ΛFin
  Finset.le_sup (f := fun l ↦ (tm.m l).pushes) (Finset.mem_univ l)

end

end FinTM2

/-- The initial configuration corresponding to a list in the input alphabet. -/
def initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : tm.Cfg where
  l := Option.some tm.main
  var := tm.initialState
  stk := Function.update (fun _ ↦ []) tm.k₀ s

/-- The final configuration corresponding to a list in the output alphabet. -/
def haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : tm.Cfg where
  l := Option.none
  var := tm.initialState
  stk := Function.update (fun _ ↦ []) tm.k₁ s

@[deprecated (since := "2026-03-06")] protected alias EvalsTo :=
  StateTransition.EvalsTo
@[deprecated (since := "2026-03-06")] protected alias EvalsToInTime :=
  StateTransition.EvalsToInTime

/-- A proof of tm outputting l' when given l. -/
def TM2Outputs (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) :=
  EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def TM2OutputsInTime (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁)))
    (m : ℕ) :=
  EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m

/-- The forgetful map, forgetting the upper bound on the number of steps. -/
def TM2OutputsInTime.toTM2Outputs {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ} (h : TM2OutputsInTime tm l l' m) :
    TM2Outputs tm l l' :=
  h.toEvalsTo

/-- The output is at most as long as the input plus `tm.maxPushes` letters per step. -/
theorem TM2Outputs.length_le {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {l' : List (tm.Γ tm.k₁)}
    (h : TM2Outputs tm l (some l')) : l'.length ≤ l.length + tm.maxPushes * h.steps := by
  have := TM2.length_stk_le_of_evalsTo tm.pushes_le_maxPushes (b := haltList tm l') h tm.k₁
  simp only [haltList, initList, Function.update_self] at this
  refine this.trans (Nat.add_le_add_right ?_ _)
  by_cases hk : tm.k₁ = tm.k₀
  · rw [hk, Function.update_self]
  · simp [Function.update_of_ne hk]

/-- A (bundled TM2) Turing machine
with input alphabet equivalent to `Γ₀` and output alphabet equivalent to `Γ₁`. -/
structure TM2ComputableAux (Γ₀ Γ₁ : Type) where
  /-- the underlying bundled TM2 -/
  tm : FinTM2
  /-- the input alphabet is equivalent to `Γ₀` -/
  inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
  /-- the output alphabet is equivalent to `Γ₁` -/
  outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁

/-- A Turing machine + a proof it outputs `f`. -/
structure TM2Computable {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) extends
  TM2ComputableAux αΓ βΓ where
  /-- a proof this machine outputs `f` -/
  outputsFun :
    ∀ a,
      TM2Outputs tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))

/-- A Turing machine + a time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure TM2ComputableInTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
  (f : α → β) extends TM2ComputableAux αΓ βΓ where
  /-- a time function -/
  time : ℕ → ℕ
  /-- proof this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))
        (time (ea a).length)

/-- A Turing machine + a polynomial time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure TM2ComputableInPolyTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
  (f : α → β) extends TM2ComputableAux αΓ βΓ where
  /-- a polynomial time function -/
  time : Polynomial ℕ
  /-- proof that this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))
        (time.eval (ea a).length)

/-- A forgetful map, forgetting the time bound on the number of steps. -/
def TM2ComputableInTime.toTM2Computable {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (h : TM2ComputableInTime ea eb f) : TM2Computable ea eb f :=
  ⟨h.toTM2ComputableAux, fun a => TM2OutputsInTime.toTM2Outputs (h.outputsFun a)⟩

/-- A forgetful map, forgetting that the time function is polynomial. -/
def TM2ComputableInPolyTime.toTM2ComputableInTime {α β αΓ βΓ : Type} {ea : α → List αΓ}
    {eb : β → List βΓ} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInTime ea eb f :=
  ⟨h.toTM2ComputableAux, fun n => h.time.eval n, h.outputsFun⟩

/-- The output of a polynomial-time machine has polynomial length. -/
theorem TM2ComputableInPolyTime.length_le {α β αΓ βΓ : Type} {ea : α → List αΓ}
    {eb : β → List βΓ} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (Polynomial.X + Polynomial.C h.tm.maxPushes * h.time).eval (ea a).length := by
  have := (h.outputsFun a).toTM2Outputs.length_le
  rw [List.length_map, List.length_map] at this
  simpa using this.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (h.outputsFun a).steps_le_m) _)

open Turing.TM2.Stmt

/-- A Turing machine computing the identity on α. -/
def idComputer (αΓ : Type) [Fintype αΓ] : FinTM2 where
  K := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := αΓ
  Λ := Unit
  main := ⟨⟩
  σ := Unit
  initialState := ⟨⟩
  m _ := halt

instance inhabitedFinTM2 : Inhabited FinTM2 :=
  ⟨idComputer Bool⟩

noncomputable section

/-- A proof that the identity map on α is computable in polytime. -/
def idComputableInPolyTime {α αΓ : Type} [Fintype αΓ] (ea : α → List αΓ) :
    @TM2ComputableInPolyTime α α αΓ αΓ ea ea id where
  tm := idComputer αΓ
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 1
  outputsFun _ :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := by simp only [Polynomial.eval_one, le_refl] }

instance inhabitedTM2ComputableInPolyTime :
    Inhabited (TM2ComputableInPolyTime encodeBool encodeBool id) :=
  ⟨idComputableInPolyTime encodeBool⟩

instance inhabitedTM2OutputsInTime :
    Inhabited
      (TM2OutputsInTime (idComputer Bool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false])) (Polynomial.eval 1 1)) :=
  ⟨(idComputableInPolyTime encodeBool).outputsFun false⟩

instance inhabitedTM2Outputs :
    Inhabited
      (TM2Outputs (idComputer Bool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false]))) :=
  ⟨TM2OutputsInTime.toTM2Outputs Turing.inhabitedTM2OutputsInTime.default⟩

instance inhabitedEvalsToInTime :
    Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
  ⟨EvalsToInTime.refl _ _⟩

instance inhabitedTM2EvalsTo : Inhabited (EvalsTo (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
  ⟨EvalsTo.refl _ _⟩

/-- A proof that the identity map on α is computable in time. -/
def idComputableInTime {α αΓ : Type} [Fintype αΓ] (ea : α → List αΓ) :
    @TM2ComputableInTime α α αΓ αΓ ea ea id :=
  TM2ComputableInPolyTime.toTM2ComputableInTime <| idComputableInPolyTime ea

instance inhabitedTM2ComputableInTime :
    Inhabited (TM2ComputableInTime encodeBool encodeBool id) :=
  ⟨idComputableInTime encodeBool⟩

/-- A proof that the identity map on α is computable. -/
def idComputable {α αΓ : Type} [Fintype αΓ] (ea : α → List αΓ) :
    @TM2Computable α α αΓ αΓ ea ea id :=
  TM2ComputableInTime.toTM2Computable <| idComputableInTime ea

instance inhabitedTM2Computable :
    Inhabited (TM2Computable encodeBool encodeBool id) :=
  ⟨idComputable encodeBool⟩

instance inhabitedTM2ComputableAux : Inhabited (TM2ComputableAux Bool Bool) :=
  ⟨(default : TM2Computable encodeBool encodeBool id).toTM2ComputableAux⟩

end

end Turing
