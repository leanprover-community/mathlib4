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
- `TM2ComputableInPolyTime.comp` : the composition of two functions computable in polynomial
  time is computable in polynomial time.

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

/-! ### Composition -/

namespace TM2Compose

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (tm₁ tm₂ : FinTM2)

/-- Stacks of the composed machine: those of both machines and one more. -/
abbrev K' : Type := tm₁.K ⊕ tm₂.K ⊕ Unit

/-- Letters of the stacks of the composed machine; the extra stack holds input letters of
`tm₂`. -/
abbrev Γ' : K' tm₁ tm₂ → Type
  | .inl k => tm₁.Γ k
  | .inr (.inl k) => tm₂.Γ k
  | .inr (.inr _) => tm₂.Γ tm₂.k₀

/-- Labels of the composed machine: those of both machines and, for each of the two transfers `b`,
a loop label `(b, none)` and a label `(b, some x)` pushing the letter `x`. -/
abbrev Λ' : Type := tm₁.Λ ⊕ tm₂.Λ ⊕ Bool × Option (tm₂.Γ tm₂.k₀)

/-- States of the composed machine: those of both machines and a one-letter buffer. -/
abbrev σ' : Type := tm₁.σ × tm₂.σ × Option (tm₂.Γ tm₂.k₀)

/-- Stacks of the composed machine from stacks of both machines and the extra stack. -/
@[simp] def combine (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) : ∀ k, List (Γ' tm₁ tm₂ k)
  | .inl k => S₁ k
  | .inr (.inl k) => S₂ k
  | .inr (.inr _) => t

variable {tm₁ tm₂}

theorem update_combine_inl (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (k : tm₁.K) (x : List (tm₁.Γ k)) :
    Function.update (combine tm₁ tm₂ S₁ S₂ t) (.inl k) x =
      combine tm₁ tm₂ (Function.update S₁ k x) S₂ t := by
  funext k'; rcases k' with k' | k' | u <;> simp [Function.update_of_ne]

theorem update_combine_inr_inl (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (k : tm₂.K) (x : List (tm₂.Γ k)) :
    Function.update (combine tm₁ tm₂ S₁ S₂ t) (.inr (.inl k)) x =
      combine tm₁ tm₂ S₁ (Function.update S₂ k x) t := by
  funext k'; rcases k' with k' | k' | u <;> simp [Function.update_of_ne]

theorem update_combine_inr_inr (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (u : Unit) (x : List (tm₂.Γ tm₂.k₀)) :
    Function.update (combine tm₁ tm₂ S₁ S₂ t) (.inr (.inr u)) x = combine tm₁ tm₂ S₁ S₂ x := by
  funext k'; rcases k' with k' | k' | u <;> simp [Function.update_of_ne]

/-- A statement of `tm₁` as one of the composed machine; `halt` starts the first transfer. -/
def lift₁ : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ → TM2.Stmt (Γ' tm₁ tm₂) (Λ' tm₁ tm₂) (σ' tm₁ tm₂)
  | .push k f q => .push (.inl k) (fun s ↦ f s.1) (lift₁ q)
  | .peek k f q => .peek (.inl k) (fun s o ↦ (f s.1 o, s.2)) (lift₁ q)
  | .pop k f q => .pop (.inl k) (fun s o ↦ (f s.1 o, s.2)) (lift₁ q)
  | .load f q => .load (fun s ↦ (f s.1, s.2)) (lift₁ q)
  | .branch f q₁ q₂ => .branch (fun s ↦ f s.1) (lift₁ q₁) (lift₁ q₂)
  | .goto f => .goto fun s ↦ .inl (f s.1)
  | .halt => .goto fun _ ↦ .inr (.inr (false, none))

/-- A statement of `tm₂` as one of the composed machine. -/
def lift₂ : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ → TM2.Stmt (Γ' tm₁ tm₂) (Λ' tm₁ tm₂) (σ' tm₁ tm₂)
  | .push k f q => .push (.inr (.inl k)) (fun s ↦ f s.2.1) (lift₂ q)
  | .peek k f q => .peek (.inr (.inl k)) (fun s o ↦ (s.1, f s.2.1 o, s.2.2)) (lift₂ q)
  | .pop k f q => .pop (.inr (.inl k)) (fun s o ↦ (s.1, f s.2.1 o, s.2.2)) (lift₂ q)
  | .load f q => .load (fun s ↦ (s.1, f s.2.1, s.2.2)) (lift₂ q)
  | .branch f q₁ q₂ => .branch (fun s ↦ f s.2.1) (lift₂ q₁) (lift₂ q₂)
  | .goto f => .goto fun s ↦ .inr (.inl (f s.2.1))
  | .halt => .halt

/-- A configuration of `tm₁` as one of the composed machine; halting starts the first transfer. -/
def emb₁ (w : tm₂.σ × Option (tm₂.Γ tm₂.k₀)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (c : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) :
    TM2.Cfg (Γ' tm₁ tm₂) (Λ' tm₁ tm₂) (σ' tm₁ tm₂) :=
  ⟨some (c.l.elim (.inr (.inr (false, none))) .inl), (c.var, w), combine tm₁ tm₂ c.stk S₂ t⟩

/-- A configuration of `tm₂` as one of the composed machine. -/
def emb₂ (v₁ : tm₁.σ) (r : Option (tm₂.Γ tm₂.k₀)) (S₁ : ∀ k, List (tm₁.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (c : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) :
    TM2.Cfg (Γ' tm₁ tm₂) (Λ' tm₁ tm₂) (σ' tm₁ tm₂) :=
  ⟨c.l.map fun l ↦ .inr (.inl l), (v₁, c.var, r), combine tm₁ tm₂ S₁ c.stk t⟩

theorem stepAux_lift₁ (q : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ) (v : tm₁.σ)
    (w : tm₂.σ × Option (tm₂.Γ tm₂.k₀)) (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (lift₁ q) (v, w) (combine tm₁ tm₂ S₁ S₂ t) =
      emb₁ w S₂ t (TM2.stepAux q v S₁) := by
  induction q generalizing v S₁ with
  | branch f q₁ q₂ ih₁ ih₂ => simp [lift₁, ih₁, ih₂, apply_ite (emb₁ w S₂ t)]
  | _ => simp_all [lift₁, emb₁, update_combine_inl]

theorem stepAux_lift₂ (q : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ) (v₁ : tm₁.σ) (v : tm₂.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (lift₂ q) (v₁, v, r) (combine tm₁ tm₂ S₁ S₂ t) =
      emb₂ v₁ r S₁ t (TM2.stepAux q v S₂) := by
  induction q generalizing v S₂ with
  | branch f q₁ q₂ ih₁ ih₂ => simp [lift₂, ih₁, ih₂, apply_ite (emb₂ v₁ r S₁ t)]
  | _ => simp_all [lift₂, emb₂, update_combine_inr_inl]

variable (e : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)

/-- The program of the composed machine. The first transfer pops the output stack of `tm₁` onto
the extra stack, translating letters by `e`; the second pops the extra stack onto the input stack
of `tm₂`. A popped letter `x` is pushed by the label `(b, some x)`. -/
def prog : Λ' tm₁ tm₂ → TM2.Stmt (Γ' tm₁ tm₂) (Λ' tm₁ tm₂) (σ' tm₁ tm₂)
  | .inl l => lift₁ (tm₁.m l)
  | .inr (.inl l) => lift₂ (tm₂.m l)
  | .inr (.inr (false, none)) => .pop (.inl tm₁.k₁) (fun s o ↦ (s.1, s.2.1, o.map e))
      (.goto fun s ↦ s.2.2.elim (.inr (.inr (true, none))) fun x ↦ .inr (.inr (false, some x)))
  | .inr (.inr (false, some x)) =>
      .push (.inr (.inr ())) (fun _ ↦ x) (.goto fun _ ↦ .inr (.inr (false, none)))
  | .inr (.inr (true, none)) => .pop (.inr (.inr ())) (fun s o ↦ (s.1, s.2.1, o))
      (.goto fun s ↦ s.2.2.elim (.inr (.inl tm₂.main)) fun x ↦ .inr (.inr (true, some x)))
  | .inr (.inr (true, some x)) =>
      .push (.inr (.inl tm₂.k₀)) (fun _ ↦ x) (.goto fun _ ↦ .inr (.inr (true, none)))

theorem step_emb₁ (w : tm₂.σ × Option (tm₂.Γ tm₂.k₀)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (c c' : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ)
    (h : TM2.step tm₁.m c = some c') :
    TM2.step (prog e) (emb₁ w S₂ t c) = some (emb₁ w S₂ t c') := by
  obtain ⟨_ | l, v, S⟩ := c <;> cases h
  exact congrArg some (stepAux_lift₁ (tm₁.m l) v w S S₂ t)

theorem step_emb₂ (v₁ : tm₁.σ) (r : Option (tm₂.Γ tm₂.k₀)) (S₁ : ∀ k, List (tm₁.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (c c' : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ)
    (h : TM2.step tm₂.m c = some c') :
    TM2.step (prog e) (emb₂ v₁ r S₁ t c) = some (emb₂ v₁ r S₁ t c') := by
  obtain ⟨_ | l, v, S⟩ := c <;> cases h
  exact congrArg some (stepAux_lift₂ (tm₂.m l) v₁ v r S₁ S t)

/-- A transfer pops the stack `k₁` letter by letter into the state and pushes each letter, from
the label `P` of its value, onto the stack `k₂`; it takes two steps per letter and one more. -/
theorem iterate_transfer {K Λ σ T : Type*} {Γ : K → Type*} [DecidableEq K]
    (m : Λ → TM2.Stmt Γ Λ σ) {k₁ k₂ : K} (hk : k₁ ≠ k₂) {get : Γ k₁ → T} {put : T → Γ k₂}
    {rd : σ → Option T} {w : σ → Option (Γ k₁) → σ} {L L' : Λ} {P : T → Λ}
    (hL : m L = .pop k₁ w (.goto fun s ↦ (rd s).elim L' P))
    (hP : ∀ x, m (P x) = .push k₂ (fun _ ↦ put x) (.goto fun _ ↦ L))
    (hrd : ∀ s o, rd (w s o) = o.map get) (hw : ∀ s o o', w (w s o) o' = w s o')
    (S : ∀ k, List (Γ k)) (s : σ) :
    (flip bind (TM2.step m))^[2 * (S k₁).length + 1] (some ⟨some L, s, S⟩) =
      some ⟨some L', w s none, Function.update (Function.update S k₁ []) k₂
        (((S k₁).map (put ∘ get)).reverse ++ S k₂)⟩ := by
  generalize hl : S k₁ = l
  induction l generalizing S s with
  | nil =>
    have hS : Function.update S k₁ [] = S := Function.update_eq_self_iff.2 hl.symm
    simp [flip, hL, hl, hrd, hS]
  | cons x l ih =>
    have h₂ : (flip bind (TM2.step m))^[2] (some ⟨some L, s, S⟩) = some ⟨some L, w s (some x),
        Function.update (Function.update S k₁ l) k₂ (put (get x) :: S k₂)⟩ := by
      simp [flip, hL, hP, hl, hrd, Function.update_of_ne hk.symm]
    rw [show 2 * (x :: l).length + 1 = 2 * l.length + 1 + 2 by rw [List.length_cons]; omega,
      Function.iterate_add_apply, h₂, ih _ _ (by simp [Function.update_of_ne hk])]
    simp [hw, Function.update_comm hk.symm]

/-- The composed machine: it runs `tm₁`, moves its output onto the input stack of `tm₂` through
the extra stack, translating letters by `e`, and runs `tm₂`. -/
abbrev machine : FinTM2 where
  K := K' tm₁ tm₂
  k₀ := .inl tm₁.k₀
  k₁ := .inr (.inl tm₂.k₁)
  Γ := Γ' tm₁ tm₂
  Λ := Λ' tm₁ tm₂
  main := .inl tm₁.main
  σ := σ' tm₁ tm₂
  initialState := (tm₁.initialState, tm₂.initialState, none)
  m := prog e

theorem initList_machine (l : List (tm₁.Γ tm₁.k₀)) :
    initList (machine e) l =
      emb₁ (tm₂.initialState, none) (fun _ ↦ []) [] (initList tm₁ l) := by
  simp only [initList, emb₁]
  congr 1
  funext k; rcases k with k | k | u <;> simp [Function.update_of_ne]

theorem emb₂_haltList (l : List (tm₂.Γ tm₂.k₁)) :
    emb₂ tm₁.initialState none (fun _ ↦ []) [] (haltList tm₂ l) = haltList (machine e) l := by
  simp only [haltList, emb₂]
  congr 1
  funext k; rcases k with k | k | u <;> simp [Function.update_of_ne]

/-- The two transfers take the output `y` of `tm₁` to the input `y.map e` of `tm₂` in
`4 * y.length + 2` steps. -/
theorem iterate_transfers (y : List (tm₁.Γ tm₁.k₁)) :
    (flip bind (machine e).step)^[4 * y.length + 2]
      (some (emb₁ (tm₂.initialState, none) (fun _ ↦ []) [] (haltList tm₁ y))) =
      some (emb₂ tm₁.initialState none (fun _ ↦ []) [] (initList tm₂ (y.map e))) := by
  have h₁ := iterate_transfer (prog e) (k₁ := .inl tm₁.k₁) (k₂ := .inr (.inr ())) (get := e)
    (put := id) (rd := (·.2.2)) (w := fun s o ↦ (s.1, s.2.1, o.map e))
    (L := .inr (.inr (false, none))) (L' := .inr (.inr (true, none)))
    (P := fun x ↦ .inr (.inr (false, some x))) (by simp) rfl (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ _ ↦ rfl) (combine tm₁ tm₂ (Function.update (fun _ ↦ []) tm₁.k₁ y) (fun _ ↦ []) [])
    (tm₁.initialState, tm₂.initialState, none)
  have h₂ := iterate_transfer (prog e) (k₁ := .inr (.inr ())) (k₂ := .inr (.inl tm₂.k₀))
    (get := id) (put := id) (rd := (·.2.2)) (w := fun s o ↦ (s.1, s.2.1, o))
    (L := .inr (.inr (true, none))) (L' := .inr (.inl tm₂.main))
    (P := fun x ↦ .inr (.inr (true, some x))) (by simp) rfl (fun _ ↦ rfl) (fun _ _ ↦ by simp)
    (fun _ _ _ ↦ rfl) (combine tm₁ tm₂ (fun _ ↦ []) (fun _ ↦ []) (y.map e).reverse)
    (tm₁.initialState, tm₂.initialState, none)
  simp only [combine, Function.update_self, update_combine_inl, update_combine_inr_inl,
    update_combine_inr_inr, Function.update_idem, Function.update_eq_self, List.map_reverse,
    List.length_reverse, List.length_map, List.append_nil, List.reverse_reverse, Function.id_comp,
    List.map_id, Option.map_none] at h₁ h₂
  rw [show 4 * y.length + 2 = 2 * y.length + 1 + (2 * y.length + 1) by omega,
    Function.iterate_add_apply]
  simp only [emb₁, emb₂, haltList, initList, FinTM2.step]
  dsimp only [Option.elim, Option.map]
  exact (congrArg (flip bind (TM2.step (prog e)))^[2 * y.length + 1] h₁).trans h₂

end TM2Compose

open TM2Compose in
/-- If `f` and `g` are computable in polynomial time by TM2 machines, so is `g ∘ f`. -/
noncomputable def TM2ComputableInPolyTime.comp {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ}
    {eβ : β → List βΓ} {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h1 : TM2ComputableInPolyTime eα eβ f) (h2 : TM2ComputableInPolyTime eβ eγ g) :
    TM2ComputableInPolyTime eα eγ (g ∘ f) :=
  let e : h1.tm.Γ h1.tm.k₁ → h2.tm.Γ h2.tm.k₀ := h2.inputAlphabet.symm ∘ h1.outputAlphabet
  let q : Polynomial ℕ := .X + .C h1.tm.maxPushes * h1.time
  { tm := machine e
    inputAlphabet := h1.inputAlphabet
    outputAlphabet := h2.outputAlphabet
    time := h1.time + 4 * q + 2 + h2.time.comp q
    outputsFun a :=
      { steps := (h2.outputsFun (f a)).steps +
          (4 * (eβ (f a)).length + 2 + (h1.outputsFun a).steps)
        evals_in_steps := by
          have H₁ : (flip bind (machine e).step)^[(h1.outputsFun a).steps]
              (some (emb₁ (h2.tm.initialState, none) (fun _ ↦ []) []
                (initList h1.tm ((eα a).map h1.inputAlphabet.invFun)))) = _ :=
            ((h1.outputsFun a).toEvalsTo.map _ (step_emb₁ e _ _ _)).evals_in_steps
          have H₂ := ((h2.outputsFun (f a)).toEvalsTo.map _
            (step_emb₂ e h1.tm.initialState none (fun _ ↦ []) [])).evals_in_steps
          have hm : ((eβ (f a)).map h1.outputAlphabet.invFun).map e =
              (eβ (f a)).map h2.inputAlphabet.invFun := by
            simp [e, Function.comp_def]
          have T := iterate_transfers e ((eβ (f a)).map h1.outputAlphabet.invFun)
          rw [hm, List.length_map] at T
          rw [Function.iterate_add_apply, Function.iterate_add_apply, initList_machine, H₁]
          exact (congrArg _ T).trans (H₂.trans (congrArg some (emb₂_haltList e _)))
        steps_le_m := by
          have mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
            induction p using Polynomial.induction_on' with
            | add p₁ p₂ hp₁ hp₂ => simpa using Nat.add_le_add hp₁ hp₂
            | monomial k c => simpa using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)
          have hq : (eβ (f a)).length ≤ q.eval (eα a).length := h1.length_le a
          have h₁ := (h1.outputsFun a).steps_le_m
          have h₂ := ((h2.outputsFun (f a)).steps_le_m).trans (mono h2.time hq)
          simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_ofNat] at h₂ hq ⊢
          omega } }

end Turing
