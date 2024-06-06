/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine

#align_import computability.tm_computable from "leanprover-community/mathlib"@"6f9cb03e8a39ea345796a13c6639cb330e50869b"

/-!
# Computable functions

This file contains the definition of a Turing machine with some finiteness conditions
(bundling the definition of TM2 in `TuringMachine.lean`), a definition of when a TM gives a certain
output (in a certain time), and the definition of computability (in polynomial time or
any time function) of a function between two types that have an encoding (as in `Encoding.lean`).

## Main theorems

- `idComputableInPolyTime` : a TM + a proof it computes the identity on a type in polytime.
- `idComputable`           : a TM + a proof it computes the identity on a type.

## Implementation notes

To count the execution time of a Turing machine, we have decided to count the number of times the
`step` function is used. Each step executes a statement (of type `Stmt`); this is a function, and
generally contains multiple "fundamental" steps (pushing, popping, and so on).
However, as functions only contain a finite number of executions and each one is executed at most
once, this execution time is up to multiplication by a constant the amount of fundamental steps.
-/


set_option linter.uppercaseLean3 false

open Computability

namespace Turing

/-- A bundled TM2 (an equivalent of the classical Turing machine, defined starting from
the namespace `Turing.TM2` in `TuringMachine.lean`), with an input and output stack,
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
#align turing.fin_tm2 Turing.FinTM2

attribute [nolint docBlame] FinTM2.kDecidableEq

namespace FinTM2

section

variable (tm : FinTM2)

instance decidableEqK : DecidableEq tm.K :=
  tm.kDecidableEq
#align turing.fin_tm2.K.decidable_eq Turing.FinTM2.decidableEqK

instance inhabitedσ : Inhabited tm.σ :=
  ⟨tm.initialState⟩
#align turing.fin_tm2.σ.inhabited Turing.FinTM2.inhabitedσ

/-- The type of statements (functions) corresponding to this TM. -/
def Stmt : Type :=
  Turing.TM2.Stmt tm.Γ tm.Λ tm.σ
#align turing.fin_tm2.stmt Turing.FinTM2.Stmt

-- Porting note: The `deriving Inhabited` handler couldn't derive this.
instance inhabitedStmt : Inhabited (Stmt tm) :=
  inferInstanceAs (Inhabited (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ))
#align turing.fin_tm2.stmt.inhabited Turing.FinTM2.inhabitedStmt

/-- The type of configurations (functions) corresponding to this TM. -/
def Cfg : Type :=
  Turing.TM2.Cfg tm.Γ tm.Λ tm.σ
#align turing.fin_tm2.cfg Turing.FinTM2.Cfg

instance inhabitedCfg : Inhabited (Cfg tm) :=
  Turing.TM2.Cfg.inhabited _ _ _
#align turing.fin_tm2.inhabited_cfg Turing.FinTM2.inhabitedCfg

/-- The step function corresponding to this TM. -/
@[simp]
def step : tm.Cfg → Option tm.Cfg :=
  Turing.TM2.step tm.m
#align turing.fin_tm2.step Turing.FinTM2.step

end

end FinTM2

/-- The initial configuration corresponding to a list in the input alphabet. -/
def initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : tm.Cfg where
  l := Option.some tm.main
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀) (fun h => by rw [h]; exact s)
      fun _ => []
#align turing.init_list Turing.initList

/-- The final configuration corresponding to a list in the output alphabet. -/
def haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : tm.Cfg where
  l := Option.none
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁) (fun h => by rw [h]; exact s)
      fun _ => []
#align turing.halt_list Turing.haltList

/-- A "proof" of the fact that `f` eventually reaches `b` when repeatedly evaluated on `a`,
remembering the number of steps it takes. -/
structure EvalsTo {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) where
  /-- number of steps taken -/
  steps : ℕ
  evals_in_steps : (flip bind f)^[steps] a = b
#align turing.evals_to Turing.EvalsTo

-- note: this cannot currently be used in `calc`, as the last two arguments must be `a` and `b`.
-- If this is desired, this argument order can be changed, but this spelling is I think the most
-- natural, so there is a trade-off that needs to be made here. A notation can get around this.
/-- A "proof" of the fact that `f` eventually reaches `b` in at most `m` steps when repeatedly
evaluated on `a`, remembering the number of steps it takes. -/
structure EvalsToInTime {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) extends
  EvalsTo f a b where
  steps_le_m : steps ≤ m
#align turing.evals_to_in_time Turing.EvalsToInTime

/-- Reflexivity of `EvalsTo` in 0 steps. -/
-- @[refl] -- Porting note: `@[refl]` attribute only applies to lemmas proving `x ∼ x` in Lean4.
def EvalsTo.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsTo f a a :=
  ⟨0, rfl⟩
#align turing.evals_to.refl Turing.EvalsTo.refl

/-- Transitivity of `EvalsTo` in the sum of the numbers of steps. -/
@[trans]
def EvalsTo.trans {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ)
    (h₁ : EvalsTo f a b) (h₂ : EvalsTo f b c) : EvalsTo f a c :=
  ⟨h₂.steps + h₁.steps, by rw [Function.iterate_add_apply, h₁.evals_in_steps, h₂.evals_in_steps]⟩
#align turing.evals_to.trans Turing.EvalsTo.trans

/-- Reflexivity of `EvalsToInTime` in 0 steps. -/
-- @[refl] -- Porting note: `@[refl]` attribute only applies to lemmas proving `x ∼ x` in Lean4.
def EvalsToInTime.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsToInTime f a a 0 :=
  ⟨EvalsTo.refl f a, le_refl 0⟩
#align turing.evals_to_in_time.refl Turing.EvalsToInTime.refl

/-- Transitivity of `EvalsToInTime` in the sum of the numbers of steps. -/
@[trans]
def EvalsToInTime.trans {σ : Type*} (f : σ → Option σ) (m₁ : ℕ) (m₂ : ℕ) (a : σ) (b : σ)
    (c : Option σ) (h₁ : EvalsToInTime f a b m₁) (h₂ : EvalsToInTime f b c m₂) :
    EvalsToInTime f a c (m₂ + m₁) :=
  ⟨EvalsTo.trans f a b c h₁.toEvalsTo h₂.toEvalsTo, add_le_add h₂.steps_le_m h₁.steps_le_m⟩
#align turing.evals_to_in_time.trans Turing.EvalsToInTime.trans

/-- A proof of tm outputting l' when given l. -/
def TM2Outputs (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) :=
  EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')
#align turing.tm2_outputs Turing.TM2Outputs

/-- A proof of tm outputting l' when given l in at most m steps. -/
def TM2OutputsInTime (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁)))
    (m : ℕ) :=
  EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m
#align turing.tm2_outputs_in_time Turing.TM2OutputsInTime

/-- The forgetful map, forgetting the upper bound on the number of steps. -/
def TM2OutputsInTime.toTM2Outputs {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ} (h : TM2OutputsInTime tm l l' m) :
    TM2Outputs tm l l' :=
  h.toEvalsTo
#align turing.tm2_outputs_in_time.to_tm2_outputs Turing.TM2OutputsInTime.toTM2Outputs

/-- A (bundled TM2) Turing machine
with input alphabet equivalent to `Γ₀` and output alphabet equivalent to `Γ₁`. -/
structure TM2ComputableAux (Γ₀ Γ₁ : Type) where
  /-- the underlying bundled TM2 -/
  tm : FinTM2
  /-- the input alphabet is equivalent to `Γ₀` -/
  inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
  /-- the output alphabet is equivalent to `Γ₁` -/
  outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁
#align turing.tm2_computable_aux Turing.TM2ComputableAux

/-- A Turing machine + a proof it outputs `f`. -/
structure TM2Computable {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) extends
  TM2ComputableAux ea.Γ eb.Γ where
  /-- a proof this machine outputs `f` -/
  outputsFun :
    ∀ a,
      TM2Outputs tm (List.map inputAlphabet.invFun (ea.encode a))
        (Option.some ((List.map outputAlphabet.invFun) (eb.encode (f a))))
#align turing.tm2_computable Turing.TM2Computable

/-- A Turing machine + a time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure TM2ComputableInTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
  (f : α → β) extends TM2ComputableAux ea.Γ eb.Γ where
  /-- a time function -/
  time : ℕ → ℕ
  /-- proof this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea.encode a))
        (Option.some ((List.map outputAlphabet.invFun) (eb.encode (f a))))
        (time (ea.encode a).length)
#align turing.tm2_computable_in_time Turing.TM2ComputableInTime

/-- A Turing machine + a polynomial time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure TM2ComputableInPolyTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
  (f : α → β) extends TM2ComputableAux ea.Γ eb.Γ where
  /-- a polynomial time function -/
  time : Polynomial ℕ
  /-- proof that this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea.encode a))
        (Option.some ((List.map outputAlphabet.invFun) (eb.encode (f a))))
        (time.eval (ea.encode a).length)
#align turing.tm2_computable_in_poly_time Turing.TM2ComputableInPolyTime

/-- A forgetful map, forgetting the time bound on the number of steps. -/
def TM2ComputableInTime.toTM2Computable {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β}
    {f : α → β} (h : TM2ComputableInTime ea eb f) : TM2Computable ea eb f :=
  ⟨h.toTM2ComputableAux, fun a => TM2OutputsInTime.toTM2Outputs (h.outputsFun a)⟩
#align turing.tm2_computable_in_time.to_tm2_computable Turing.TM2ComputableInTime.toTM2Computable

/-- A forgetful map, forgetting that the time function is polynomial. -/
def TM2ComputableInPolyTime.toTM2ComputableInTime {α β : Type} {ea : FinEncoding α}
    {eb : FinEncoding β} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInTime ea eb f :=
  ⟨h.toTM2ComputableAux, fun n => h.time.eval n, h.outputsFun⟩
#align turing.tm2_computable_in_poly_time.to_tm2_computable_in_time Turing.TM2ComputableInPolyTime.toTM2ComputableInTime

open Turing.TM2.Stmt

/-- A Turing machine computing the identity on α. -/
def idComputer {α : Type} (ea : FinEncoding α) : FinTM2 where
  K := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := ea.Γ
  Λ := Unit
  main := ⟨⟩
  σ := Unit
  initialState := ⟨⟩
  Γk₀Fin := ea.ΓFin
  m _ := halt
#align turing.id_computer Turing.idComputer

instance inhabitedFinTM2 : Inhabited FinTM2 :=
  ⟨idComputer Computability.inhabitedFinEncoding.default⟩
#align turing.inhabited_fin_tm2 Turing.inhabitedFinTM2

noncomputable section

/-- A proof that the identity map on α is computable in polytime. -/
def idComputableInPolyTime {α : Type} (ea : FinEncoding α) :
    @TM2ComputableInPolyTime α α ea ea id where
  tm := idComputer ea
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 1
  outputsFun _ :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := by simp only [Polynomial.eval_one, le_refl] }
#align turing.id_computable_in_poly_time Turing.idComputableInPolyTime

instance inhabitedTM2ComputableInPolyTime :
    Inhabited (TM2ComputableInPolyTime (default : FinEncoding Bool) default id) :=
  ⟨idComputableInPolyTime Computability.inhabitedFinEncoding.default⟩
#align turing.inhabited_tm2_computable_in_poly_time Turing.inhabitedTM2ComputableInPolyTime

instance inhabitedTM2OutputsInTime :
    Inhabited
      (TM2OutputsInTime (idComputer finEncodingBoolBool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false])) (Polynomial.eval 1 1)) :=
  ⟨(idComputableInPolyTime finEncodingBoolBool).outputsFun false⟩
#align turing.inhabited_tm2_outputs_in_time Turing.inhabitedTM2OutputsInTime

instance inhabitedTM2Outputs :
    Inhabited
      (TM2Outputs (idComputer finEncodingBoolBool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false]))) :=
  ⟨TM2OutputsInTime.toTM2Outputs Turing.inhabitedTM2OutputsInTime.default⟩
#align turing.inhabited_tm2_outputs Turing.inhabitedTM2Outputs

instance inhabitedEvalsToInTime :
    Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
  ⟨EvalsToInTime.refl _ _⟩
#align turing.inhabited_evals_to_in_time Turing.inhabitedEvalsToInTime

instance inhabitedTM2EvalsTo : Inhabited (EvalsTo (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
  ⟨EvalsTo.refl _ _⟩
#align turing.inhabited_tm2_evals_to Turing.inhabitedTM2EvalsTo

/-- A proof that the identity map on α is computable in time. -/
def idComputableInTime {α : Type} (ea : FinEncoding α) : @TM2ComputableInTime α α ea ea id :=
  TM2ComputableInPolyTime.toTM2ComputableInTime <| idComputableInPolyTime ea
#align turing.id_computable_in_time Turing.idComputableInTime

instance inhabitedTM2ComputableInTime :
    Inhabited (TM2ComputableInTime finEncodingBoolBool finEncodingBoolBool id) :=
  ⟨idComputableInTime Computability.inhabitedFinEncoding.default⟩
#align turing.inhabited_tm2_computable_in_time Turing.inhabitedTM2ComputableInTime

/-- A proof that the identity map on α is computable. -/
def idComputable {α : Type} (ea : FinEncoding α) : @TM2Computable α α ea ea id :=
  TM2ComputableInTime.toTM2Computable <| idComputableInTime ea
#align turing.id_computable Turing.idComputable

instance inhabitedTM2Computable :
    Inhabited (TM2Computable finEncodingBoolBool finEncodingBoolBool id) :=
  ⟨idComputable Computability.inhabitedFinEncoding.default⟩
#align turing.inhabited_tm2_computable Turing.inhabitedTM2Computable

instance inhabitedTM2ComputableAux : Inhabited (TM2ComputableAux Bool Bool) :=
  ⟨(default : TM2Computable finEncodingBoolBool finEncodingBoolBool id).toTM2ComputableAux⟩
#align turing.inhabited_tm2_computable_aux Turing.inhabitedTM2ComputableAux

end

end Turing
