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
- `idComputable` : a TM + a proof it computes the identity on a type.
- `TM2ComputableInPolyTime.length_le` : the output of a polytime TM has polynomial length.
- `TM2ComputableInPolyTime.comp` : a TM + a proof it computes `g ∘ f` in polytime, given such for
  `f` and `g`.

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

attribute [local instance] ΛFin

/-- The largest number of `push` instructions in a statement of this TM. -/
def maxPushes : ℕ :=
  Finset.univ.sup fun l ↦ (tm.m l).pushes

/-- Every statement of this TM has at most `tm.maxPushes` `push` instructions. -/
theorem pushes_le_maxPushes (l : tm.Λ) : (tm.m l).pushes ≤ tm.maxPushes :=
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

/-- If `h` is a run of `tm` from `l` to `l'`, then `l'` is at most `tm.maxPushes * h.steps`
letters longer than `l`. -/
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

/-- The output of a polynomial-time machine has polynomial length: the encoding of `f a` is at most
`h.tm.maxPushes * h.time.eval n` letters longer than the encoding of `a`, of length `n`. -/
theorem TM2ComputableInPolyTime.length_le {α β αΓ βΓ : Type} {ea : α → List αΓ}
    {eb : β → List βΓ} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length + h.tm.maxPushes * h.time.eval (ea a).length := by
  have := (h.outputsFun a).toTM2Outputs.length_le
  simp only [List.length_map] at this
  exact this.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (h.outputsFun a).steps_le_m) _)

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

/-!
### Composition

Given machines `tm₁` and `tm₂` and a translation `e : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀` of the output
letters of `tm₁` into the input letters of `tm₂`, the composed machine `TM2Compose.machine e` has
the stacks of both machines and one extra stack; its state is a state of each machine and a
one-letter buffer. It runs `tm₁` on the stacks of `tm₁` (`trStmt₁`); when `tm₁` halts, it pops
the output stack of `tm₁` letter by letter onto the extra stack, translating by `e`, then pops the
extra stack onto the input stack of `tm₂`, which restores the order of the letters; then it runs
`tm₂` on the stacks of `tm₂` (`trStmt₂`) and halts when `tm₂` halts.

A popped letter is carried by a label `(b, some x)` that pushes it, since `push` takes a total
function of the state and the alphabets need not be inhabited. The buffer and these labels range
over the input alphabet of `tm₂`, the only alphabet a `FinTM2` is required to make finite. Each
transfer of `n` letters takes `2 * n + 1` steps (`TM2.iterate_transfer`). As `haltList` and
`initList` both empty every other stack and use the initial state, the transfers lead from the
halting configuration of `tm₁` to the initial configuration of `tm₂` (`transfers`), and a run of
`tm₁` followed by a run of `tm₂` is a run of the composed machine (`TM2Outputs.comp`).
-/

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

/-- Labels of the composed machine: those of both machines and, for each transfer `b : Bool`
(`false`: from the output stack of `tm₁` to the extra stack; `true`: from the extra stack to the
input stack of `tm₂`), a loop label `(b, none)` that pops a letter and a label `(b, some x)` that
pushes the letter `x`. -/
abbrev Λ' : Type := tm₁.Λ ⊕ tm₂.Λ ⊕ Bool × Option (tm₂.Γ tm₂.k₀)

/-- States of the composed machine: those of both machines and a one-letter buffer. -/
abbrev σ' : Type := tm₁.σ × tm₂.σ × Option (tm₂.Γ tm₂.k₀)

variable {tm₁ tm₂}

/-- Stacks of the composed machine from stacks of both machines and the extra stack. -/
@[simp]
def combine (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k)) (t : List (tm₂.Γ tm₂.k₀)) :
    ∀ k, List (Γ' tm₁ tm₂ k)
  | .inl k => S₁ k
  | .inr (.inl k) => S₂ k
  | .inr (.inr _) => t

@[simp]
theorem update_combine_inl (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (k : tm₁.K) (x : List (tm₁.Γ k)) :
    Function.update (combine S₁ S₂ t) (.inl k) x = combine (Function.update S₁ k x) S₂ t := by
  funext k'; rcases k' with k' | k' | _ <;> simp [Function.update_of_ne]

@[simp]
theorem update_combine_inr_inl (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (k : tm₂.K) (x : List (tm₂.Γ k)) :
    Function.update (combine S₁ S₂ t) (.inr (.inl k)) x =
      combine S₁ (Function.update S₂ k x) t := by
  funext k'; rcases k' with k' | k' | _ <;> simp [Function.update_of_ne]

@[simp]
theorem update_combine_inr_inr (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t x : List (tm₂.Γ tm₂.k₀)) :
    Function.update (combine S₁ S₂ t) (.inr (.inr ())) x = combine S₁ S₂ x := by
  funext k'; rcases k' with k' | k' | _ <;> simp [Function.update_of_ne]

/-- A statement of `tm₁` as one of the composed machine; `halt` starts the first transfer. -/
def trStmt₁ : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ → TM2.Stmt (Γ' tm₁ tm₂) (Λ' tm₁ tm₂) (σ' tm₁ tm₂)
  | .push k f q => .push (.inl k) (fun s ↦ f s.1) (trStmt₁ q)
  | .peek k f q => .peek (.inl k) (fun s o ↦ (f s.1 o, s.2)) (trStmt₁ q)
  | .pop k f q => .pop (.inl k) (fun s o ↦ (f s.1 o, s.2)) (trStmt₁ q)
  | .load f q => .load (fun s ↦ (f s.1, s.2)) (trStmt₁ q)
  | .branch f q₁ q₂ => .branch (fun s ↦ f s.1) (trStmt₁ q₁) (trStmt₁ q₂)
  | .goto f => .goto fun s ↦ .inl (f s.1)
  | .halt => .goto fun _ ↦ .inr (.inr (false, none))

/-- A statement of `tm₂` as one of the composed machine. -/
def trStmt₂ : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ → TM2.Stmt (Γ' tm₁ tm₂) (Λ' tm₁ tm₂) (σ' tm₁ tm₂)
  | .push k f q => .push (.inr (.inl k)) (fun s ↦ f s.2.1) (trStmt₂ q)
  | .peek k f q => .peek (.inr (.inl k)) (fun s o ↦ (s.1, f s.2.1 o, s.2.2)) (trStmt₂ q)
  | .pop k f q => .pop (.inr (.inl k)) (fun s o ↦ (s.1, f s.2.1 o, s.2.2)) (trStmt₂ q)
  | .load f q => .load (fun s ↦ (s.1, f s.2.1, s.2.2)) (trStmt₂ q)
  | .branch f q₁ q₂ => .branch (fun s ↦ f s.2.1) (trStmt₂ q₁) (trStmt₂ q₂)
  | .goto f => .goto fun s ↦ .inr (.inl (f s.2.1))
  | .halt => .halt

/-- A configuration of `tm₁` as one of the composed machine, given the state `w` of `tm₂` with
the buffer, the stacks `S₂` of `tm₂` and the extra stack `t`; a halted configuration is sent to
the loop label of the first transfer. -/
def trCfg₁ (w : tm₂.σ × Option (tm₂.Γ tm₂.k₀)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (c : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) :
    TM2.Cfg (Γ' tm₁ tm₂) (Λ' tm₁ tm₂) (σ' tm₁ tm₂) :=
  ⟨some (c.l.elim (.inr (.inr (false, none))) .inl), (c.var, w), combine c.stk S₂ t⟩

/-- A configuration of `tm₂` as one of the composed machine, given the state `v₁` of `tm₁`, the
buffer `r`, the stacks `S₁` of `tm₁` and the extra stack `t`. -/
def trCfg₂ (v₁ : tm₁.σ) (r : Option (tm₂.Γ tm₂.k₀)) (S₁ : ∀ k, List (tm₁.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (c : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) :
    TM2.Cfg (Γ' tm₁ tm₂) (Λ' tm₁ tm₂) (σ' tm₁ tm₂) :=
  ⟨c.l.map fun l ↦ .inr (.inl l), (v₁, c.var, r), combine S₁ c.stk t⟩

theorem stepAux_trStmt₁ (q : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ) (v : tm₁.σ)
    (w : tm₂.σ × Option (tm₂.Γ tm₂.k₀)) (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (trStmt₁ q) (v, w) (combine S₁ S₂ t) = trCfg₁ w S₂ t (TM2.stepAux q v S₁) := by
  induction q generalizing v S₁ with
  | branch f q₁ q₂ ih₁ ih₂ => simp [trStmt₁, ih₁, ih₂, apply_ite (trCfg₁ w S₂ t)]
  | _ => simp_all [trStmt₁, trCfg₁]

theorem stepAux_trStmt₂ (q : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ) (v₁ : tm₁.σ) (v : tm₂.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (S₁ : ∀ k, List (tm₁.Γ k)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (trStmt₂ q) (v₁, v, r) (combine S₁ S₂ t) =
      trCfg₂ v₁ r S₁ t (TM2.stepAux q v S₂) := by
  induction q generalizing v S₂ with
  | branch f q₁ q₂ ih₁ ih₂ => simp [trStmt₂, ih₁, ih₂, apply_ite (trCfg₂ v₁ r S₁ t)]
  | _ => simp_all [trStmt₂, trCfg₂]

variable (e : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)

/-- The program of the composed machine; the transfer labels are described in the section
comment. -/
def tr : Λ' tm₁ tm₂ → TM2.Stmt (Γ' tm₁ tm₂) (Λ' tm₁ tm₂) (σ' tm₁ tm₂)
  | .inl l => trStmt₁ (tm₁.m l)
  | .inr (.inl l) => trStmt₂ (tm₂.m l)
  | .inr (.inr (false, none)) =>
      .pop (.inl tm₁.k₁) (fun s o ↦ (s.1, s.2.1, o.map e))
        (.goto fun s ↦ s.2.2.elim (.inr (.inr (true, none))) fun x ↦ .inr (.inr (false, some x)))
  | .inr (.inr (false, some x)) =>
      .push (.inr (.inr ())) (fun _ ↦ x) (.goto fun _ ↦ .inr (.inr (false, none)))
  | .inr (.inr (true, none)) =>
      .pop (.inr (.inr ())) (fun s o ↦ (s.1, s.2.1, o))
        (.goto fun s ↦ s.2.2.elim (.inr (.inl tm₂.main)) fun x ↦ .inr (.inr (true, some x)))
  | .inr (.inr (true, some x)) =>
      .push (.inr (.inl tm₂.k₀)) (fun _ ↦ x) (.goto fun _ ↦ .inr (.inr (true, none)))

/-- The composed machine: it runs `tm₁`, moves its output onto the input stack of `tm₂`,
translating letters by `e`, and runs `tm₂`. It is reducible, like `K'`, `Γ'`, `Λ'` and `σ'`, so
that its finiteness instances are inferred from those of `tm₁` and `tm₂`, and its fields unfold
in the proofs below. -/
abbrev machine : FinTM2 where
  K := K' tm₁ tm₂
  k₀ := .inl tm₁.k₀
  k₁ := .inr (.inl tm₂.k₁)
  Γ := Γ' tm₁ tm₂
  Λ := Λ' tm₁ tm₂
  main := .inl tm₁.main
  σ := σ' tm₁ tm₂
  initialState := (tm₁.initialState, tm₂.initialState, none)
  m := tr e

/-- A step of `tm₁` is a step of the composed machine. -/
theorem step_trCfg₁ (w : tm₂.σ × Option (tm₂.Γ tm₂.k₀)) (S₂ : ∀ k, List (tm₂.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (c c' : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) (h : TM2.step tm₁.m c = some c') :
    (machine e).step (trCfg₁ w S₂ t c) = some (trCfg₁ w S₂ t c') := by
  obtain ⟨_ | l, v, S⟩ := c <;> cases h
  exact congrArg some (stepAux_trStmt₁ (tm₁.m l) v w S S₂ t)

/-- A step of `tm₂` is a step of the composed machine. -/
theorem step_trCfg₂ (v₁ : tm₁.σ) (r : Option (tm₂.Γ tm₂.k₀)) (S₁ : ∀ k, List (tm₁.Γ k))
    (t : List (tm₂.Γ tm₂.k₀)) (c c' : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) (h : TM2.step tm₂.m c = some c') :
    (machine e).step (trCfg₂ v₁ r S₁ t c) = some (trCfg₂ v₁ r S₁ t c') := by
  obtain ⟨_ | l, v, S⟩ := c <;> cases h
  exact congrArg some (stepAux_trStmt₂ (tm₂.m l) v₁ v r S₁ S t)

/-- The initial configuration of the composed machine is that of `tm₁`, translated. -/
theorem initList_machine (l : List (tm₁.Γ tm₁.k₀)) :
    initList (machine e) l = trCfg₁ (tm₂.initialState, none) (fun _ ↦ []) [] (initList tm₁ l) := by
  simp only [initList, trCfg₁]
  congr 1
  funext k; rcases k with k | k | _ <;> simp [Function.update_of_ne]

/-- The halting configuration of the composed machine is that of `tm₂`, translated. -/
theorem haltList_machine (l : List (tm₂.Γ tm₂.k₁)) :
    haltList (machine e) l = trCfg₂ tm₁.initialState none (fun _ ↦ []) [] (haltList tm₂ l) := by
  simp only [haltList, trCfg₂]
  congr 1
  funext k; rcases k with k | k | _ <;> simp [Function.update_of_ne]

/-- The two transfers lead from the halting configuration of `tm₁` with output `y` to the initial
configuration of `tm₂` with input `y.map e`, in `4 * y.length + 2` steps. -/
def transfers (y : List (tm₁.Γ tm₁.k₁)) :
    EvalsTo (machine e).step (trCfg₁ (tm₂.initialState, none) (fun _ ↦ []) [] (haltList tm₁ y))
      (some (trCfg₂ tm₁.initialState none (fun _ ↦ []) [] (initList tm₂ (y.map e)))) where
  steps := 4 * y.length + 2
  evals_in_steps := by
    have h₁ : (flip bind (TM2.step (tr e)))^[2 * y.length + 1]
        (some (trCfg₁ (tm₂.initialState, none) (fun _ ↦ []) [] (haltList tm₁ y))) =
        some ⟨some (.inr (.inr (true, none))), (tm₁.initialState, tm₂.initialState, none),
          combine (fun _ ↦ []) (fun _ ↦ []) (y.map e).reverse⟩ := by
      simpa [trCfg₁, haltList] using TM2.iterate_transfer (tr e) (k₁ := .inl tm₁.k₁)
        (k₂ := .inr (.inr ())) (get := e) (rd := (·.2.2)) (w := fun s o ↦ (s.1, s.2.1, o.map e))
        (L := .inr (.inr (false, none))) (L' := .inr (.inr (true, none)))
        (P := fun x ↦ .inr (.inr (false, some x))) (by simp) rfl (fun _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun _ _ _ ↦ rfl) (combine (Function.update (fun _ ↦ []) tm₁.k₁ y) (fun _ ↦ []) [])
        (tm₁.initialState, tm₂.initialState, none)
    have h₂ : (flip bind (TM2.step (tr e)))^[2 * y.length + 1]
        (some ⟨some (.inr (.inr (true, none))), (tm₁.initialState, tm₂.initialState, none),
          combine (fun _ ↦ []) (fun _ ↦ []) (y.map e).reverse⟩) =
        some (trCfg₂ tm₁.initialState none (fun _ ↦ []) [] (initList tm₂ (y.map e))) := by
      simpa [trCfg₂, initList] using TM2.iterate_transfer (tr e) (k₁ := .inr (.inr ()))
        (k₂ := .inr (.inl tm₂.k₀)) (get := id) (rd := (·.2.2)) (w := fun s o ↦ (s.1, s.2.1, o))
        (L := .inr (.inr (true, none))) (L' := .inr (.inl tm₂.main))
        (P := fun x ↦ .inr (.inr (true, some x))) (by simp) rfl (fun _ ↦ rfl) (fun _ _ ↦ by simp)
        (fun _ _ _ ↦ rfl) (combine (fun _ ↦ []) (fun _ ↦ []) (y.map e).reverse)
        (tm₁.initialState, tm₂.initialState, none)
    rw [show 4 * y.length + 2 = 2 * y.length + 1 + (2 * y.length + 1) by omega,
      Function.iterate_add_apply]
    exact (congrArg (flip bind (machine e).step)^[2 * y.length + 1] h₁).trans h₂

end TM2Compose

open TM2Compose in
/-- A run of `tm₂` from `y.map e` to `z` after a run of `tm₁` from `l` to `y` gives a run of the
composed machine `TM2Compose.machine e` from `l` to `z`, which takes `4 * y.length + 2` more
steps. -/
def TM2Outputs.comp {tm₁ tm₂ : FinTM2} (e : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀) {l : List (tm₁.Γ tm₁.k₀)}
    {y : List (tm₁.Γ tm₁.k₁)} {l₂ : List (tm₂.Γ tm₂.k₀)} {z : List (tm₂.Γ tm₂.k₁)}
    (h₂ : TM2Outputs tm₂ l₂ (some z)) (hy : y.map e = l₂) (h₁ : TM2Outputs tm₁ l (some y)) :
    TM2Outputs (machine e) l (some z) where
  steps := h₂.steps + (4 * y.length + 2 + h₁.steps)
  evals_in_steps := by
    subst hy
    rw [initList_machine, Option.map_some _ (haltList (machine e)), haltList_machine]
    exact (((h₁.map _ (step_trCfg₁ e _ _ _)).trans _ _ _ _ (transfers e y)).trans _ _ _ _
      (h₂.map _ (step_trCfg₂ e _ _ _ _))).evals_in_steps

@[simp]
theorem TM2Outputs.comp_steps {tm₁ tm₂ : FinTM2} (e : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    {l : List (tm₁.Γ tm₁.k₀)} {y : List (tm₁.Γ tm₁.k₁)} {l₂ : List (tm₂.Γ tm₂.k₀)}
    {z : List (tm₂.Γ tm₂.k₁)} (h₂ : TM2Outputs tm₂ l₂ (some z)) (hy : y.map e = l₂)
    (h₁ : TM2Outputs tm₁ l (some y)) :
    (h₂.comp e hy h₁).steps = h₂.steps + (4 * y.length + 2 + h₁.steps) :=
  rfl

/-- Evaluating a polynomial with natural coefficients is monotone. Private, pending a general
version in `Mathlib/Algebra/Polynomial/`. -/
private theorem _root_.Polynomial.eval_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) :
    p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ => simpa using Nat.add_le_add hp₁ hp₂
  | monomial k c => simpa using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

/-- A machine computing `g ∘ f` in polynomial time, from machines computing `f` and `g` in
polynomial time: it runs the machine for `f`, moves the output onto the input stack of the machine
for `g`, and runs that machine (`TM2Compose.machine`). Its time bound is
`hf.time + 4 * q + 2 + hg.time.comp q`, where `q = X + C hf.tm.maxPushes * hf.time` bounds the
length of the intermediate output (`TM2ComputableInPolyTime.length_le`). -/
noncomputable def TM2ComputableInPolyTime.comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ}
    {eb : β → List βΓ} {ec : γ → List γΓ} {g : β → γ} {f : α → β}
    (hg : TM2ComputableInPolyTime eb ec g) (hf : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInPolyTime ea ec (g ∘ f) :=
  let e : hf.tm.Γ hf.tm.k₁ → hg.tm.Γ hg.tm.k₀ := hg.inputAlphabet.symm ∘ hf.outputAlphabet
  let q : Polynomial ℕ := .X + .C hf.tm.maxPushes * hf.time
  { tm := TM2Compose.machine e
    inputAlphabet := hf.inputAlphabet
    outputAlphabet := hg.outputAlphabet
    time := hf.time + 4 * q + 2 + hg.time.comp q
    outputsFun a :=
      { toEvalsTo := (hg.outputsFun (f a)).toTM2Outputs.comp e (by simp [e, Function.comp_def])
          (hf.outputsFun a).toTM2Outputs
        steps_le_m := by
          have hq := hf.length_le a
          have h₁ := (hf.outputsFun a).steps_le_m
          have h₂ := (hg.outputsFun (f a)).steps_le_m.trans (Polynomial.eval_mono hg.time hq)
          rw [TM2Outputs.comp_steps]
          simp only [q, TM2OutputsInTime.toTM2Outputs, List.length_map, Polynomial.eval_add,
            Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp,
            Polynomial.eval_ofNat]
          omega } }

end Turing
