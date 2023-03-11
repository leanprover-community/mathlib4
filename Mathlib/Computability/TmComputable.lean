/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent

! This file was ported from Lean 3 source module computability.tm_computable
! leanprover-community/mathlib commit 6f9cb03e8a39ea345796a13c6639cb330e50869b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Computability.Encoding
import Mathbin.Computability.TuringMachine
import Mathbin.Data.Polynomial.Basic
import Mathbin.Data.Polynomial.Eval

/-!
# Computable functions

This file contains the definition of a Turing machine with some finiteness conditions
(bundling the definition of TM2 in turing_machine.lean), a definition of when a TM gives a certain
output (in a certain time), and the definition of computability (in polytime or any time function)
of a function between two types that have an encoding (as in encoding.lean).

## Main theorems

- `id_computable_in_poly_time` : a TM + a proof it computes the identity on a type in polytime.
- `id_computable`              : a TM + a proof it computes the identity on a type.

## Implementation notes

To count the execution time of a Turing machine, we have decided to count the number of times the
`step` function is used. Each step executes a statement (of type stmt); this is a function, and
generally contains multiple "fundamental" steps (pushing, popping, so on). However, as functions
only contain a finite number of executions and each one is executed at most once, this execution
time is up to multiplication by a constant the amount of fundamental steps.
-/


open Computability

namespace Turing

/-- A bundled TM2 (an equivalent of the classical Turing machine, defined starting from
the namespace `turing.TM2` in `turing_machine.lean`), with an input and output stack,
 a main function, an initial state and some finiteness guarantees. -/
structure FinTm2 where
  {K : Type}
  [kDecidableEq : DecidableEq K]
  [kFin : Fintype K]
  -- index type of stacks
  (k₀ k₁ : K)
  -- input and output stack
  Γ : K → Type
  -- type of stack elements
  Λ : Type
  main : Λ
  [ΛFin : Fintype Λ]
  -- type of function labels
  σ : Type
  initialState : σ
  -- type of states of the machine
  [σFin : Fintype σ]
  [Γk₀Fin : Fintype (Γ k₀)]
  m : Λ → Turing.TM2.Stmt Γ Λ σ
#align turing.fin_tm2 Turing.FinTm2

-- the program itself, i.e. one function for every function label
namespace FinTm2

section

variable (tm : FinTm2)

instance : DecidableEq tm.K :=
  tm.kDecidableEq

instance : Inhabited tm.σ :=
  ⟨tm.initialState⟩

/-- The type of statements (functions) corresponding to this TM. -/
def Stmt : Type :=
  Turing.TM2.Stmt tm.Γ tm.Λ tm.σ deriving Inhabited
#align turing.fin_tm2.stmt Turing.FinTm2.Stmt

/-- The type of configurations (functions) corresponding to this TM. -/
def Cfg : Type :=
  Turing.TM2.Cfg tm.Γ tm.Λ tm.σ
#align turing.fin_tm2.cfg Turing.FinTm2.Cfg

instance inhabitedCfg : Inhabited (Cfg tm) :=
  Turing.TM2.Cfg.inhabited _ _ _
#align turing.fin_tm2.inhabited_cfg Turing.FinTm2.inhabitedCfg

/-- The step function corresponding to this TM. -/
@[simp]
def step : tm.Cfg → Option tm.Cfg :=
  Turing.TM2.step tm.m
#align turing.fin_tm2.step Turing.FinTm2.step

end

end FinTm2

/-- The initial configuration corresponding to a list in the input alphabet. -/
def initList (tm : FinTm2) (s : List (tm.Γ tm.k₀)) : tm.Cfg
    where
  l := Option.some tm.main
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀) (fun h => by rw [h]; exact s)
      fun _ => []
#align turing.init_list Turing.initList

/-- The final configuration corresponding to a list in the output alphabet. -/
def haltList (tm : FinTm2) (s : List (tm.Γ tm.k₁)) : tm.Cfg
    where
  l := Option.none
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁) (fun h => by rw [h]; exact s)
      fun _ => []
#align turing.halt_list Turing.haltList

/-- A "proof" of the fact that f eventually reaches b when repeatedly evaluated on a,
remembering the number of steps it takes. -/
structure EvalsTo {σ : Type _} (f : σ → Option σ) (a : σ) (b : Option σ) where
  steps : ℕ
  evals_in_steps : (flip bind f^[steps]) a = b
#align turing.evals_to Turing.EvalsTo

-- note: this cannot currently be used in `calc`, as the last two arguments must be `a` and `b`.
-- If this is desired, this argument order can be changed, but this spelling is I think the most
-- natural, so there is a trade-off that needs to be made here. A notation can get around this.
/-- A "proof" of the fact that `f` eventually reaches `b` in at most `m` steps when repeatedly
evaluated on `a`, remembering the number of steps it takes. -/
structure EvalsToInTime {σ : Type _} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) extends
  EvalsTo f a b where
  steps_le_m : steps ≤ m
#align turing.evals_to_in_time Turing.EvalsToInTime

/-- Reflexivity of `evals_to` in 0 steps. -/
@[refl]
def EvalsTo.refl {σ : Type _} (f : σ → Option σ) (a : σ) : EvalsTo f a a :=
  ⟨0, rfl⟩
#align turing.evals_to.refl Turing.EvalsTo.refl

/-- Transitivity of `evals_to` in the sum of the numbers of steps. -/
@[trans]
def EvalsTo.trans {σ : Type _} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ)
    (h₁ : EvalsTo f a b) (h₂ : EvalsTo f b c) : EvalsTo f a c :=
  ⟨h₂.steps + h₁.steps, by rw [Function.iterate_add_apply, h₁.evals_in_steps, h₂.evals_in_steps]⟩
#align turing.evals_to.trans Turing.EvalsTo.trans

/-- Reflexivity of `evals_to_in_time` in 0 steps. -/
@[refl]
def EvalsToInTime.refl {σ : Type _} (f : σ → Option σ) (a : σ) : EvalsToInTime f a a 0 :=
  ⟨EvalsTo.refl f a, le_refl 0⟩
#align turing.evals_to_in_time.refl Turing.EvalsToInTime.refl

/-- Transitivity of `evals_to_in_time` in the sum of the numbers of steps. -/
@[trans]
def EvalsToInTime.trans {σ : Type _} (f : σ → Option σ) (m₁ : ℕ) (m₂ : ℕ) (a : σ) (b : σ)
    (c : Option σ) (h₁ : EvalsToInTime f a b m₁) (h₂ : EvalsToInTime f b c m₂) :
    EvalsToInTime f a c (m₂ + m₁) :=
  ⟨EvalsTo.trans f a b c h₁.toEvalsTo h₂.toEvalsTo, add_le_add h₂.steps_le_m h₁.steps_le_m⟩
#align turing.evals_to_in_time.trans Turing.EvalsToInTime.trans

/-- A proof of tm outputting l' when given l. -/
def Tm2Outputs (tm : FinTm2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) :=
  EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')
#align turing.tm2_outputs Turing.Tm2Outputs

/-- A proof of tm outputting l' when given l in at most m steps. -/
def Tm2OutputsInTime (tm : FinTm2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁)))
    (m : ℕ) :=
  EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m
#align turing.tm2_outputs_in_time Turing.Tm2OutputsInTime

/-- The forgetful map, forgetting the upper bound on the number of steps. -/
def Tm2OutputsInTime.toTm2Outputs {tm : FinTm2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ} (h : Tm2OutputsInTime tm l l' m) :
    Tm2Outputs tm l l' :=
  h.toEvalsTo
#align turing.tm2_outputs_in_time.to_tm2_outputs Turing.Tm2OutputsInTime.toTm2Outputs

/-- A Turing machine with input alphabet equivalent to Γ₀ and output alphabet equivalent to Γ₁. -/
structure Tm2ComputableAux (Γ₀ Γ₁ : Type) where
  tm : FinTm2
  inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
  outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁
#align turing.tm2_computable_aux Turing.Tm2ComputableAux

/-- A Turing machine + a proof it outputs f. -/
structure Tm2Computable {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) extends
  Tm2ComputableAux ea.Γ eb.Γ where
  outputsFun :
    ∀ a,
      Tm2Outputs tm (List.map input_alphabet.invFun (ea.encode a))
        (Option.some ((List.map output_alphabet.invFun) (eb.encode (f a))))
#align turing.tm2_computable Turing.Tm2Computable

/-- A Turing machine + a time function + a proof it outputs f in at most time(len(input)) steps. -/
structure Tm2ComputableInTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
  (f : α → β) extends Tm2ComputableAux ea.Γ eb.Γ where
  time : ℕ → ℕ
  outputsFun :
    ∀ a,
      Tm2OutputsInTime tm (List.map input_alphabet.invFun (ea.encode a))
        (Option.some ((List.map output_alphabet.invFun) (eb.encode (f a))))
        (time (ea.encode a).length)
#align turing.tm2_computable_in_time Turing.Tm2ComputableInTime

/-- A Turing machine + a polynomial time function + a proof it outputs f in at most time(len(input))
steps. -/
structure Tm2ComputableInPolyTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
  (f : α → β) extends Tm2ComputableAux ea.Γ eb.Γ where
  time : Polynomial ℕ
  outputsFun :
    ∀ a,
      Tm2OutputsInTime tm (List.map input_alphabet.invFun (ea.encode a))
        (Option.some ((List.map output_alphabet.invFun) (eb.encode (f a))))
        (time.eval (ea.encode a).length)
#align turing.tm2_computable_in_poly_time Turing.Tm2ComputableInPolyTime

/-- A forgetful map, forgetting the time bound on the number of steps. -/
def Tm2ComputableInTime.toTm2Computable {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β}
    {f : α → β} (h : Tm2ComputableInTime ea eb f) : Tm2Computable ea eb f :=
  ⟨h.toTm2ComputableAux, fun a => Tm2OutputsInTime.toTm2Outputs (h.outputsFun a)⟩
#align turing.tm2_computable_in_time.to_tm2_computable Turing.Tm2ComputableInTime.toTm2Computable

/-- A forgetful map, forgetting that the time function is polynomial. -/
def Tm2ComputableInPolyTime.toTm2ComputableInTime {α β : Type} {ea : FinEncoding α}
    {eb : FinEncoding β} {f : α → β} (h : Tm2ComputableInPolyTime ea eb f) :
    Tm2ComputableInTime ea eb f :=
  ⟨h.toTm2ComputableAux, fun n => h.time.eval n, h.outputsFun⟩
#align turing.tm2_computable_in_poly_time.to_tm2_computable_in_time Turing.Tm2ComputableInPolyTime.toTm2ComputableInTime

open Turing.TM2.Stmt

/-- A Turing machine computing the identity on α. -/
def idComputer {α : Type} (ea : FinEncoding α) : FinTm2
    where
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

instance inhabitedFinTm2 : Inhabited FinTm2 :=
  ⟨idComputer Computability.inhabitedFinEncoding.default⟩
#align turing.inhabited_fin_tm2 Turing.inhabitedFinTm2

noncomputable section

/-- A proof that the identity map on α is computable in polytime. -/
def idComputableInPolyTime {α : Type} (ea : FinEncoding α) : @Tm2ComputableInPolyTime α α ea ea id
    where
  tm := idComputer ea
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 1
  outputsFun _ :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := by simp only [Polynomial.eval_one] }
#align turing.id_computable_in_poly_time Turing.idComputableInPolyTime

instance inhabitedTm2ComputableInPolyTime :
    Inhabited (Tm2ComputableInPolyTime (default : FinEncoding Bool) default id) :=
  ⟨idComputableInPolyTime Computability.inhabitedFinEncoding.default⟩
#align turing.inhabited_tm2_computable_in_poly_time Turing.inhabitedTm2ComputableInPolyTime

instance inhabitedTm2OutputsInTime :
    Inhabited
      (Tm2OutputsInTime (idComputer finEncodingBoolBool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false])) _) :=
  ⟨(idComputableInPolyTime finEncodingBoolBool).outputsFun false⟩
#align turing.inhabited_tm2_outputs_in_time Turing.inhabitedTm2OutputsInTime

instance inhabitedTm2Outputs :
    Inhabited
      (Tm2Outputs (idComputer finEncodingBoolBool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false]))) :=
  ⟨Tm2OutputsInTime.toTm2Outputs Turing.inhabitedTm2OutputsInTime.default⟩
#align turing.inhabited_tm2_outputs Turing.inhabitedTm2Outputs

instance inhabitedEvalsToInTime :
    Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
  ⟨EvalsToInTime.refl _ _⟩
#align turing.inhabited_evals_to_in_time Turing.inhabitedEvalsToInTime

instance inhabitedTm2EvalsTo : Inhabited (EvalsTo (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
  ⟨EvalsTo.refl _ _⟩
#align turing.inhabited_tm2_evals_to Turing.inhabitedTm2EvalsTo

/-- A proof that the identity map on α is computable in time. -/
def idComputableInTime {α : Type} (ea : FinEncoding α) : @Tm2ComputableInTime α α ea ea id :=
  Tm2ComputableInPolyTime.toTm2ComputableInTime <| idComputableInPolyTime ea
#align turing.id_computable_in_time Turing.idComputableInTime

instance inhabitedTm2ComputableInTime :
    Inhabited (Tm2ComputableInTime finEncodingBoolBool finEncodingBoolBool id) :=
  ⟨idComputableInTime Computability.inhabitedFinEncoding.default⟩
#align turing.inhabited_tm2_computable_in_time Turing.inhabitedTm2ComputableInTime

/-- A proof that the identity map on α is computable. -/
def idComputable {α : Type} (ea : FinEncoding α) : @Tm2Computable α α ea ea id :=
  Tm2ComputableInTime.toTm2Computable <| idComputableInTime ea
#align turing.id_computable Turing.idComputable

instance inhabitedTm2Computable :
    Inhabited (Tm2Computable finEncodingBoolBool finEncodingBoolBool id) :=
  ⟨idComputable Computability.inhabitedFinEncoding.default⟩
#align turing.inhabited_tm2_computable Turing.inhabitedTm2Computable

instance inhabitedTm2ComputableAux : Inhabited (Tm2ComputableAux Bool Bool) :=
  ⟨(default : Tm2Computable finEncodingBoolBool finEncodingBoolBool id).toTm2ComputableAux⟩
#align turing.inhabited_tm2_computable_aux Turing.inhabitedTm2ComputableAux

end Turing

