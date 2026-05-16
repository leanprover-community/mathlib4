
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Computability.PostTuringMachine
public import Mathlib.Computability.BinEncoding
public import Mathlib.Computability.TuringMachine

/-!

This file is meant to develop the theory of time complexity for single-tape Turing machines.

Related is `TMComputable.lean`, which develops this for (a kind of) multi-tape Turing machines.

This file tries to fix the alphabet to computability on functions from lists of booleans to lists of booleans
with tape of Option Bool (none is the blank symbol),


-/


@[expose] public section


open Computability

namespace Turing

def Tape.move? {α} [Inhabited α] : Turing.Tape α → Option Dir → Turing.Tape α
  | t, none => t
  | t, some d => t.move d

open Classical in
/--
-/
noncomputable def ListBlank.space_used {α} [Inhabited α] (l : ListBlank α) : ℕ :=
  Nat.find (p := fun n => ∀ i > n, l.nth i = default)
    (by sorry)

/--
The space used by a tape is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the tape
-/
noncomputable def Tape.space_used {α} [Inhabited α] (t : Turing.Tape α) : ℕ :=
  1 + t.left.space_used + t.right.space_used

lemma Tape.space_used_write {α} [Inhabited α] (t : Turing.Tape α) (a : α) :
    (t.write a).space_used = t.space_used := by
  sorry

lemma Tape.space_used_move {α} [Inhabited α] (t : Turing.Tape α) (d : Dir) :
    (t.move d).space_used ≤ t.space_used + 1 := by
  sorry

namespace BinTM0

/-- A Turing machine "statement" is just a command to move
  left or right, and write a symbol on the tape. -/
def Stmt := (Option Bool) × Option (Dir)
deriving Inhabited

end BinTM0

/-- A TM0 over the alphabet of Option Bool (none is blank tape symbol). -/
structure BinTM0 where
  /-- type of state labels -/
  (Λ : Type)
  /-- finiteness of the state type -/
  [FintypeΛ : Fintype Λ]
  /-- Initial state -/
  (q₀ : Λ)
  /-- Transition function, mapping a state and a head symbol
  to a Stmt to invoke, and optionally a new state (none for halt) -/
  (M : Λ → (Option Bool) → (Turing.BinTM0.Stmt × Option Λ))

namespace BinTM0

section

variable (tm : BinTM0)

instance : Inhabited tm.Λ :=
  ⟨tm.q₀⟩

instance : Fintype tm.Λ :=
  tm.FintypeΛ

instance inhabitedStmt : Inhabited (Stmt) := inferInstance

/-- The type of configurations (functions) corresponding to this TM. -/
structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.Λ
  /-- the tape contents, which -/
  tape : Tape (Option Bool)
deriving Inhabited

/-- The step function corresponding to this TM. -/
@[simp]
def step : tm.Cfg → Option tm.Cfg :=
  fun ⟨q, t⟩ =>
    match q with
    -- If in the halting state, there is no next configuration
    | none => none
    -- If in state q'
    | some q' =>
      -- Look up the transition function
      match tm.M q' t.head with
      | ⟨(wr, dir), q''⟩ =>
          -- enter a new configuration
          some ⟨
            -- With state q'' (or none for halting)
            q'',
            -- And tape updated according to the Stmt
            (t.write wr).move? dir⟩
end

/-- The initial configuration corresponding to a list in the input alphabet. -/
def initCfg (tm : BinTM0) (s : List Bool) : tm.Cfg := ⟨some tm.q₀, Tape.mk₁ s⟩

/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
def haltList (tm : BinTM0) (s : List (Bool)) : tm.Cfg := ⟨none, Tape.mk₁ s⟩

/-- `f` eventually reaches `b` when repeatedly evaluated on `a`, in exactly `steps` steps. -/
def EvalsToInTime {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) (steps : ℕ) : Prop :=
  (· >>= f)^[steps] a = b

/-- Reflexivity of `EvalsTo` in 0 steps. -/
lemma EvalsToInTime.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsToInTime f a (some a) 0 :=
  rfl

/-- Transitivity of `EvalsTo` in the sum of the numbers of steps. -/
@[trans]
lemma EvalsToInTime.trans {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ)
    (steps₁ steps₂ : ℕ)
    (h₁ : EvalsToInTime f a b steps₁)
    (h₂ : EvalsToInTime f b c steps₂) :
    EvalsToInTime f a c (steps₂ + steps₁) := by
  simp_all only [EvalsToInTime, Option.bind_eq_bind]
  rw [Function.iterate_add_apply, h₁, h₂]

/-- If we evaluate to some state in n+1 steps, there is an intermediate state
    that we reach in n steps, and then one more step reaches the final state. -/
lemma EvalsToInTime.succ_decompose {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ)
    (n : ℕ) (h : EvalsToInTime f a (some b) (n + 1)) :
    ∃ c : σ, EvalsToInTime f a (some c) n ∧ f c = some b := by
  set c' := (· >>= f)^[n] (some a) with hc'
  simp only [EvalsToInTime, Option.bind_eq_bind] at h hc' ⊢
  rw [Function.iterate_succ_apply'] at h
  -- h : (· >>= f) ((· >>= f)^[n] (some a)) = some b
  -- This means (· >>= f)^[n] (some a) >>= f = some b
  -- So (· >>= f)^[n] (some a) = some c for some c with f c = some b
  rw [<-hc'] at h
  revert h hc'
  cases c' with
  | none =>
    grind
  | some c =>
    intros h hc'
    use c
    grind

lemma EvalsToInTime.succ_iff {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ)
    (n : ℕ) :
    EvalsToInTime f a (some b) (n + 1) ↔
      ∃ c : σ, EvalsToInTime f a (some c) n ∧ f c = some b := by
  constructor
  · exact EvalsToInTime.succ_decompose f a b n
  · intro ⟨c, hc_eval, hc_step⟩
    simp only [EvalsToInTime, Option.bind_eq_bind, Function.iterate_succ_apply'] at hc_eval ⊢
    simp only [hc_eval, Option.bind_some, hc_step]

theorem Turing.BinTM0.EvalsToInTime.congr.extracted_1_2.{u_2, u_1}
    {σ : Type u_1} {σ' : Type u_2} (f : σ → Option σ)
    (f' : σ' → Option σ') (g : σ → σ')
    (hg : ∀ (x : σ), Option.map g (f x) = f' (g x)) (n : ℕ) (a : σ) :
    (Option.map g ((flip Option.bind f)^[n] (some a))).bind f' =
      ((flip Option.bind f)^[n] (some a)).bind fun a ↦ f' (g a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply, flip, Option.bind_some, <- hg] at ih ⊢
    grind





/--
If `f` is homomorphic to `f'` via `g`, then if `f` evals to `b` from `a` in `steps` steps,
then `f'` evals to `g b` from `g a` in `steps` steps.
-/
lemma EvalsToInTime.map {σ σ' : Type*} (f : σ → Option σ) (f' : σ' → Option σ')
    (g : σ → σ') (hg : ∀ x, Option.map g (f x) = f' (g x))
    (a : σ) (b : Option σ)
    (steps : ℕ)
    (h : EvalsToInTime f a b steps) : EvalsToInTime f' (g a) (Option.map g b) steps := by
  induction steps generalizing a b with
  | zero =>
    simp only [EvalsToInTime, Option.bind_eq_bind, Function.iterate_zero, id_eq] at h ⊢
    subst h
    rfl
  | succ n ih =>
    simp only [EvalsToInTime, Option.bind_eq_bind, Function.iterate_succ_apply',
      forall_eq'] at h ih ⊢
    subst h
    rw [ih]
    clear ih
    simp only [Option.map_bind, Function.comp_apply, hg]
    exact Turing.BinTM0.EvalsToInTime.congr.extracted_1_2 f f' g hg n a

/--
If `h : σ → ℕ` increases by at most 1 on each step of `f`,
then the value of `h` at the output after `steps` steps is at most `h` at the input plus `steps`.
-/
lemma EvalsToInTime.small_change {σ : Type*} (f : σ → Option σ) (h : σ → ℕ)
    (h_step : ∀ a b, f a = some b → h b ≤ h a + 1)
    (a : σ) (b : Option σ)
    (steps : ℕ)
    (hevals : EvalsToInTime f a b steps) :
    ∀ b' : σ, b = some b' → h b' ≤ h a + steps := by
  sorry

-- m -> step_bound
/-- `f` eventually reaches `b` in at most `m` steps when repeatedly
evaluated on `a`. -/
def EvalsToWithinTime {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ steps ≤ m, EvalsToInTime f a b steps

/-- Reflexivity of `EvalsToWithinTime` in 0 steps. -/
def EvalsToWithinTime.refl {σ : Type*} (f : σ → Option σ) (a : σ) :
    EvalsToWithinTime f a (some a) 0 := by
  use 0
  exact if_false_right.mp rfl

/-- Transitivity of `EvalsToWithinTime` in the sum of the numbers of steps. -/
@[trans]
def EvalsToWithinTime.trans {σ : Type*} (f : σ → Option σ) (m₁ : ℕ) (m₂ : ℕ) (a : σ) (b : σ)
    (c : Option σ) (h₁ : EvalsToWithinTime f a b m₁) (h₂ : EvalsToWithinTime f b c m₂) :
    EvalsToWithinTime f a c (m₂ + m₁) := by
  obtain ⟨steps₁, hsteps₁, hevals₁⟩ := h₁
  obtain ⟨steps₂, hsteps₂, hevals₂⟩ := h₂
  use steps₂ + steps₁
  constructor
  · omega
  · exact EvalsToInTime.trans f a b c steps₁ steps₂ hevals₁ hevals₂

def EvalsToWithinTime.map {σ σ' : Type*} (f : σ → Option σ) (f' : σ' → Option σ')
    (g : σ → σ') (hg : ∀ x, Option.map g (f x) = f' (g x))
    (a : σ) (b : Option σ)
    (m : ℕ)
    (h : EvalsToWithinTime f a b m) : EvalsToWithinTime f' (g a) (Option.map g b) m := by
  obtain ⟨steps, hsteps, hevals⟩ := h
  use steps
  constructor
  · exact hsteps
  · exact EvalsToInTime.map f f' g hg a b steps hevals

/--
Monotonicity of `EvalsToWithinTime` in the time bound.
-/
def EvalsToWithinTime.mono_time {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ)
    {m₁ m₂ : ℕ} (h : EvalsToWithinTime f a b m₁) (hm : m₁ ≤ m₂) : EvalsToWithinTime f a b m₂ := by
  obtain ⟨steps, hsteps, hevals⟩ := h
  use steps
  simp_all only
  simp
  omega

/-- A proof of tm outputting l' when given l. -/
def OutputsInTime (tm : BinTM0) (l : List (Bool)) (l' : Option (List (Bool))) :=
  EvalsToInTime tm.step (initCfg tm l) ((Option.map (haltList tm)) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def OutputsWithinTime (tm : BinTM0) (l : List (Bool)) (l' : Option (List (Bool)))
    (m : ℕ) :=
  EvalsToWithinTime tm.step (initCfg tm l) ((Option.map (haltList tm)) l') m

-- /-- A (bundled TM0) Turing machine
-- with input alphabet equivalent to `Γ₀` and output alphabet equivalent to `Γ₁`.
-- TODO this is something of a holdover, might get rid
-- -/
-- structure ComputableAux (Γ₀ Γ₁ : Type) where
--   /-- the underlying bundled TM0 -/
--   tm : BinTM0
--   /-- the input alphabet is equivalent to `Γ₀` -/
--   inputAlphabet : Bool ≃ Γ₀
--   /-- the output alphabet is equivalent to `Γ₁` -/
--   outputAlphabet : Bool ≃ Γ₁

/-- A Turing machine + a proof it outputsInTime `f`. -/
structure Computable {α β : Type} (ea : BinEncoding α) (eb : BinEncoding β) (f : α → β) where
  /-- the underlying bundled TM0 -/
  tm : BinTM0
  steps : ℕ
  /-- a proof this machine outputsInTime `f` -/
  outputsFun :
    ∀ a,
      OutputsInTime tm ((ea.encode a))
        (Option.some ((eb.encode (f a))))
        steps

/-- A Turing machine + a time function +
a proof it outputsInTime `f` in at most `time(input.length)` steps. -/
structure ComputableInTime {α β : Type} (ea : BinEncoding α) (eb : BinEncoding β)
  (f : α → β) where
  /-- the underlying bundled TM0 -/
  tm : BinTM0
  /-- a time function -/
  time : ℕ → ℕ
  /-- proof this machine outputsInTime `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      tm.OutputsWithinTime
        ((ea.encode a))
        (Option.some ((eb.encode (f a))))
        (time (ea.encode a).length)

/-- A Turing machine + a polynomial time function +
a proof it outputsInTime `f` in at most `time(input.length)` steps. -/
structure ComputableInPolyTime {α β : Type} (ea : BinEncoding α) (eb : BinEncoding β)
  (f : α → β) where
  /-- the underlying bundled TM0 -/
  tm : BinTM0
  /-- a polynomial time function -/
  time : Polynomial ℕ
  /-- proof that this machine outputsInTime `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      OutputsWithinTime tm ((ea.encode a))
        (Option.some ((eb.encode (f a))))
        (time.eval (ea.encode a).length)

-- /-- A forgetful map, forgetting the time bound on the number of steps. -/
-- def ComputableInTime.toComputable {α β : Type} {ea : BinEncoding α} {eb : BinEncoding β}
--     {f : α → β} (h : ComputableInTime ea eb f) : Computable ea eb f :=
--   ⟨h.tm, fun a => OutputsWithinTime.toOutputsInTime (h.outputsFun a)⟩

/-- A forgetful map, forgetting that the time function is polynomial. -/
def ComputableInPolyTime.toComputableInTime {α β : Type} {ea : BinEncoding α}
    {eb : BinEncoding β} {f : α → β} (h : ComputableInPolyTime ea eb f) :
    ComputableInTime ea eb f :=
  ⟨h.tm, fun n => h.time.eval n, h.outputsFun⟩

open Turing.TM0.Stmt

/-- A Turing machine computing the identity. -/
def idComputer : BinTM0 where
  Λ := PUnit
  q₀ := PUnit.unit
  M := fun _ b => ⟨(b, none), none⟩

noncomputable section

/-- A proof that the identity map on α is computable in polytime. -/
def ComputableInPolyTime.id {α : Type} (ea : BinEncoding α) :
    @ComputableInPolyTime α α ea ea id where
  tm := idComputer
  time := 1
  outputsFun x := by
    use 1
    simp only [Polynomial.eval_one, le_refl, id_eq, Option.map_some, true_and]
    simp only [EvalsToInTime, initCfg, haltList, idComputer,
      Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    congr 1


    -- { steps := 1
    --   evals_in_steps := rfl
    --   steps_le_m := by simp only [Polynomial.eval_one, le_refl] }

-- instance inhabitedComputableInPolyTime :
--     Inhabited (ComputableInPolyTime (default : BinEncoding Bool) default id) :=
--   ⟨idComputableInPolyTime Computability.inhabitedBinEncoding.default⟩

-- instance inhabitedOutputsWithinTime :
--     Inhabited
--       (OutputsWithinTime (idComputer finEncodingBoolBool)
--         (List.map (Equiv.cast rfl).invFun [false])
--         (some (List.map (Equiv.cast rfl).invFun [false])) (Polynomial.eval 1 1)) :=
--   ⟨(idComputableInPolyTime finEncodingBoolBool).outputsFun false⟩

-- instance inhabitedOutputsInTime :
--     Inhabited
--       (OutputsInTime (idComputer finEncodingBoolBool) (List.map (Equiv.cast rfl).invFun [false])
--         (some (List.map (Equiv.cast rfl).invFun [false]))) :=
--   ⟨OutputsWithinTime.toOutputsInTime Turing.inhabitedOutputsWithinTime.default⟩

-- instance inhabitedEvalsToWithinTime :
--     Inhabited (EvalsToWithinTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
--   ⟨EvalsToWithinTime.refl _ _⟩

-- instance inhabitedTM0EvalsToInTime :
--     Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
--   ⟨EvalsTo.refl _ _⟩

/-- A proof that the identity map on α is computable in time. -/
def ComputableInTime.id {α : Type} (ea : BinEncoding α) :
    @ComputableInTime α α ea ea id :=
  ComputableInPolyTime.toComputableInTime <| ComputableInPolyTime.id ea

-- instance inhabitedComputableInTime :
--     Inhabited (ComputableInTime finEncodingBoolBool finEncodingBoolBool id) :=
--   ⟨idComputableInTime Computability.inhabitedBinEncoding.default⟩

-- /-- A proof that the identity map on α is computable. -/
-- def idComputable {α : Type} (ea : BinEncoding α) : @Computable α α ea ea id :=
--   ComputableInTime.toComputable <| ComputableInTime.id ea

-- instance inhabitedComputable :
--     Inhabited (Computable finEncodingBoolBool finEncodingBoolBool id) :=
--   ⟨idComputable Computability.inhabitedBinEncoding.default⟩

-- instance inhabitedComputableAux : Inhabited (ComputableAux Bool Bool) :=
--   ⟨(default : Computable finEncodingBoolBool finEncodingBoolBool id).toComputableAux⟩

def compComputer {α β γ : Type} {eα : BinEncoding α} {eβ : BinEncoding β}
    {eγ : BinEncoding γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f)
    (hg : ComputableInTime eβ eγ g) :
    BinTM0 :=
  {
    Λ := hf.tm.Λ ⊕ hg.tm.Λ
    q₀ := Sum.inl hf.tm.q₀
    M := fun q h =>
      match q with
      -- If we are in the first machine's states, run that machine
      | Sum.inl ql => match hf.tm.M ql (h) with
        -- The action should be the same, and the state should either be the corresponding state
        -- in the first machine, or transition to the start state of the second machine if halting
        | (ql', stmt) => (ql',
            match stmt with
            -- If it halts, transition to the start state of the second machine
            | none => some (Sum.inr hg.tm.q₀)
            -- Otherwise continue as normal
            | _ => Option.map Sum.inl stmt)
      -- If we are in the second machine's states, run that machine
      | Sum.inr qr =>
        match hg.tm.M qr (h) with
        -- The action should be the same, and the state should be the corresponding state
        -- in the second machine, or halting if the second machine halts
        | (qr', stmt) => (qr',
            match stmt with
            -- If it halts, transition to the halting state
            | none => none
            -- Otherwise continue as normal
            | _ => Option.map Sum.inr stmt)
  }

lemma compComputer_q₀_eq {α β γ : Type} {eα : BinEncoding α} {eβ : BinEncoding β}
    {eγ : BinEncoding γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f)
    (hg : ComputableInTime eβ eγ g) :
    (compComputer hf hg).q₀ = Sum.inl hf.tm.q₀ :=
  rfl

/-- Lift a config over a tm to a config over the comp -/
def liftCompCfg_left {α β γ : Type} {eα : BinEncoding α} {eβ : BinEncoding β}
    {eγ : BinEncoding γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f)
    (hg : ComputableInTime eβ eγ g)
    (cfg : hf.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  {
    state := Option.map Sum.inl cfg.state
    tape := cfg.tape
  }

def liftCompCfg_right {α β γ : Type} {eα : BinEncoding α} {eβ : BinEncoding β}
    {eγ : BinEncoding γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f)
    (hg : ComputableInTime eβ eγ g)
    (cfg : hg.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  {
    state := Option.map Sum.inr cfg.state
    tape := cfg.tape
  }

theorem map_liftCompCfg_left_step
    {α β γ : Type} {eα : BinEncoding α} {eβ : BinEncoding β} {eγ : BinEncoding γ}
    {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f) (hg : ComputableInTime eβ eγ g)
    (x : hf.tm.Cfg)
    (hx : ∀ cfg, hf.tm.step x = some cfg → cfg.state.isSome) :
    Option.map (liftCompCfg_left hf hg) (hf.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_left hf hg x) := by
  cases x with
  | mk state tape =>
    cases state with
    | none =>
      -- x is already in halting state, step returns none on both sides
      simp only [step, liftCompCfg_left, Option.map_none, compComputer]
    | some q =>
      simp only [step, liftCompCfg_left, compComputer, Option.map_some]
      -- Get the transition result
      generalize hM : hf.tm.M q tape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      simp only
      -- Case on whether the next state is none (halting) or some
      cases nextState with
      | none =>
        -- The first machine halts, but hx says the result has state.isSome
        simp only [step, hM] at hx
        have := hx ⟨none, (tape.write wr).move? dir⟩ rfl
        simp at this
      | some q' =>
        -- Normal step case - both sides produce the lifted config
        simp only [hM, Option.map_some, liftCompCfg_left]

/-- Helper lemma: liftCompCfg_right commutes with step for the second machine -/
theorem map_liftCompCfg_right_step
    {α β γ : Type} {eα : BinEncoding α} {eβ : BinEncoding β} {eγ : BinEncoding γ}
    {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f) (hg : ComputableInTime eβ eγ g)
    (x : hg.tm.Cfg) :
    Option.map (liftCompCfg_right hf hg) (hg.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_right hf hg x) := by
  cases x with
  | mk state tape =>
    cases state with
    | none =>
      simp only [step, liftCompCfg_right, Option.map_none, compComputer]
    | some q =>
      simp only [step, liftCompCfg_right, compComputer, Option.map_some]
      generalize hM : hg.tm.M q tape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState with
      | none => simp only [hM, Option.map_some, liftCompCfg_right, Option.map_none]
      | some q' => simp only [hM, Option.map_some, liftCompCfg_right]

/-- When the first machine would halt, the composed machine transitions to the second machine -/
theorem comp_transition_to_right {α β γ : Type}
    {eα : BinEncoding α} {eβ : BinEncoding β} {eγ : BinEncoding γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f) (hg : ComputableInTime eβ eγ g)
    (tape : Tape (Option Bool))
    (q : hf.tm.Λ)
    (hM : (hf.tm.M q tape.head).2 = none) :
    (compComputer hf hg).step { state := some (Sum.inl q), tape := tape } =
      some { state := some (Sum.inr hg.tm.q₀),
             tape := (tape.write (hf.tm.M q tape.head).1.1).move? (hf.tm.M q tape.head).1.2 } := by
  simp only [step, compComputer, hM]
  generalize hfM_eq : hf.tm.M q tape.head = result
  obtain ⟨⟨wr, dir⟩, nextState⟩ := result
  simp only [hfM_eq]

/-- Helper: lifting to Sum.inl and transitioning to Sum.inr on halt -/
def liftCompCfg_left_or_right {α β γ : Type} {eα : BinEncoding α} {eβ : BinEncoding β}
    {eγ : BinEncoding γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f)
    (hg : ComputableInTime eβ eγ g)
    (cfg : hf.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  match cfg.state with
  | some q => { state := some (Sum.inl q), tape := cfg.tape }
  | none => { state := some (Sum.inr hg.tm.q₀), tape := cfg.tape }

/-- The lifting function commutes with step, converting halt to transition -/
theorem map_liftCompCfg_left_or_right_step
    {α β γ : Type} {eα : BinEncoding α} {eβ : BinEncoding β} {eγ : BinEncoding γ}
    {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f) (hg : ComputableInTime eβ eγ g)
    (x : hf.tm.Cfg)
    (hx : x.state.isSome) :
    Option.map (liftCompCfg_left_or_right hf hg) (hf.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_left_or_right hf hg x) := by
  cases x with
  | mk state tape =>
    cases state with
    | none => simp at hx
    | some q =>
      simp only [step, liftCompCfg_left_or_right, compComputer]
      generalize hM : hf.tm.M q tape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState with
      | none => simp only [hM, Option.map_some, liftCompCfg_left_or_right]
      | some q' => simp only [hM, Option.map_some, liftCompCfg_left_or_right]

/-- General simulation: if the first machine goes from cfg to halt, the composed machine
    goes from lifted cfg to Sum.inr hg.tm.q₀ -/
theorem comp_left_simulation_general {α β γ : Type}
    {eα : BinEncoding α} {eβ : BinEncoding β} {eγ : BinEncoding γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f) (hg : ComputableInTime eβ eγ g)
    (cfg : hf.tm.Cfg)
    (hcfg : cfg.state.isSome)
    (haltCfg : hf.tm.Cfg)
    -- (haltCfg_state : haltCfg.state = none)
    (steps : ℕ)
    (h : EvalsToInTime hf.tm.step cfg (some haltCfg) steps) :
    EvalsToInTime (compComputer hf hg).step
      (liftCompCfg_left_or_right hf hg cfg)
      (some (liftCompCfg_left_or_right hf hg haltCfg))
      steps := by
  -- Proof by induction on steps.
  -- Key insight: liftCompCfg_left_or_right maps:
  --   { state := some q, tape } -> { state := some (Sum.inl q), tape }
  --   { state := none, tape }   -> { state := some (Sum.inr hg.tm.q₀), tape }
  -- For non-halting configs, the composed machine simulates exactly.
  -- When the first machine halts, the composed machine transitions to Sum.inr hg.tm.q₀.
  induction steps generalizing cfg haltCfg with
  | zero =>
    simp only [EvalsToInTime, Option.bind_eq_bind, step, Function.iterate_zero, id_eq,
      Option.some.injEq] at h ⊢
    rw [h]
  | succ n ih =>
    -- Use the decomposition lemma: cfg evals to some intermediate c in n steps,
    -- and then c steps to haltCfg
    -- obtain ⟨c, hc_n, hc_step⟩ := EvalsToInTime.succ_decompose hf.tm.step cfg haltCfg n h
    rw [EvalsToInTime.succ_iff] at h ⊢
    obtain ⟨c, hc_n, hc_step⟩ := h
    use liftCompCfg_left_or_right hf hg c
    constructor
    · apply ih
      · exact hcfg
      · exact hc_n
    · cases c with
      | mk state tape =>
        cases state with
        | none =>
          simp_all
        | some q =>
          rw [← map_liftCompCfg_left_or_right_step hf hg ⟨some q, tape⟩ (by simp)]
          simp only [hc_step, Option.map_some]


/--
Simulation for the first phase of the composed computer.
When the first machine runs from start to halt, the composed machine
runs from start (with Sum.inl state) to Sum.inr hg.tm.q₀ (the start of the second phase).
This takes the same number of steps because the halt transition becomes a transition to the
second machine.
-/
theorem comp_left_simulation {α β γ : Type}
    {eα : BinEncoding α} {eβ : BinEncoding β} {eγ : BinEncoding γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f) (hg : ComputableInTime eβ eγ g)
    (a : α)
    (hf_outputsFun :
      EvalsToWithinTime hf.tm.step
        { state := some hf.tm.q₀, tape := Tape.mk₁ (eα.encode a) }
        (some { state := none, tape := Tape.mk₁ (eβ.encode (f a)) })
        (hf.time (eα.encode a).length)) :
    EvalsToWithinTime (compComputer hf hg).step
      { state := some (Sum.inl hf.tm.q₀), tape := Tape.mk₁ (eα.encode a) }
      (some { state := some (Sum.inr hg.tm.q₀), tape := Tape.mk₁ (eβ.encode (f a)) })
      (hf.time (eα.encode a).length) := by
  obtain ⟨steps, hsteps_le, hsteps_eval⟩ := hf_outputsFun
  use steps
  constructor
  · exact hsteps_le
  · have := comp_left_simulation_general hf hg
      { state := some hf.tm.q₀, tape := Tape.mk₁ (eα.encode a) }
      (by simp)
      { state := none, tape := Tape.mk₁ (eβ.encode (f a)) }
      steps
      hsteps_eval
    simp only [liftCompCfg_left_or_right] at this
    exact this

/-- Simulation lemma for the second machine in the composed computer -/
theorem comp_right_simulation {α β γ : Type}
    {eα : BinEncoding α} {eβ : BinEncoding β} {eγ : BinEncoding γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f) (hg : ComputableInTime eβ eγ g)
    (x : hg.tm.Cfg) (y : Option hg.tm.Cfg) (m : ℕ)
    (h : EvalsToWithinTime hg.tm.step x y m) :
    EvalsToWithinTime (compComputer hf hg).step
      (liftCompCfg_right hf hg x)
      (Option.map (liftCompCfg_right hf hg) y)
      m := by
  exact EvalsToWithinTime.map hg.tm.step (compComputer hf hg).step
    (liftCompCfg_right hf hg) (map_liftCompCfg_right_step hf hg) x y m h




lemma output_length_le_input_length_add_time (tm : BinTM0) (l l' : List Bool) (t : ℕ)
    (h : tm.OutputsWithinTime l (some l') t) :
    l'.length ≤ l.length + t := by
  unfold OutputsWithinTime EvalsToWithinTime at h

  obtain ⟨steps, hsteps_le, hevals⟩ := h
  -- have := EvalsToInTime.small_change
  --
  sorry

/--
A composition for ComputableInTime.

If f and g are computed by turing machines M₁ and M₂
then we can construct a turing machine M which computes g ∘ f by first running M₁
and then, when M₁ halts, transitioning to the start state of M₂ and running M₂.

This results in time bounded by the amount of time taken by M₁ plus the maximum time taken by M₂ on
inputs of length of the maximum output length of M₁ for that input size (which is itself bounded by
the time taken by M₁).

Note that we require the time function of the second machine to be monotone;
this is to ensure that if the first machine returns an output
which is shorter than the maximum possible length of output for that input size,
then the time bound for the second machine still holds for that shorter input to the second machine.

TODO refactor out the definition of the composed TM.
Prove separately that it
evals to the intermediate state from the start state and
then from the intermediate state to the final state.
-/
def ComputableInTime.comp
    {α β γ : Type} {eα : BinEncoding α} {eβ : BinEncoding β}
    {eγ : BinEncoding γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f)
    (hg : ComputableInTime eβ eγ g)
    (h_mono : Monotone hg.time) :
    (ComputableInTime eα eγ (g ∘ f)) where
  tm := compComputer hf hg
  time l := hf.time l + hg.time (l + hf.time l)
  outputsFun a := by
    have hf_outputsFun := hf.outputsFun a
    have hg_outputsFun := hg.outputsFun (f a)
    simp only [OutputsWithinTime, initCfg, compComputer_q₀_eq, Function.comp_apply,
      Option.map_some, haltList] at hg_outputsFun hf_outputsFun ⊢
    -- The computer evals a to f a in time hf.time (eα.encode a)
    have h_a_evalsTo_f_a :
        EvalsToWithinTime (compComputer hf hg).step
          { state := some (Sum.inl hf.tm.q₀), tape := Tape.mk₁ (eα.encode a) }
          (some { state := some (Sum.inr hg.tm.q₀), tape := Tape.mk₁ (eβ.encode ((f a))) })
          (hf.time (eα.encode a).length) :=
      comp_left_simulation hf hg a hf_outputsFun
    have h_f_a_evalsTo_g_f_a :
        EvalsToWithinTime (compComputer hf hg).step
          { state := some (Sum.inr hg.tm.q₀), tape := Tape.mk₁ (eβ.encode ((f a))) }
          (some { state := none, tape := Tape.mk₁ (eγ.encode ((g (f a)))) })
          (hg.time (eβ.encode ((f a))).length) := by
      -- Use the simulation lemma for the second machine
      have := comp_right_simulation hf hg
        { state := some hg.tm.q₀, tape := Tape.mk₁ (eβ.encode (f a)) }
        (some { state := none, tape := Tape.mk₁ (eγ.encode (g (f a))) })
        (hg.time (eβ.encode (f a)).length)
        hg_outputsFun
      simp only [liftCompCfg_right, Option.map_some] at this
      exact this
    have h_a_evalsTo_g_f_a :=
      EvalsToWithinTime.trans
        (compComputer hf hg).step _ _ _ _ _ h_a_evalsTo_f_a h_f_a_evalsTo_g_f_a
    apply EvalsToWithinTime.mono_time _ _ _ h_a_evalsTo_g_f_a
    nth_rw 1 [← add_comm]
    apply add_le_add
    · exact le_refl _
    · apply h_mono
      -- Use the lemma about output length being bounded by input length + time
      exact output_length_le_input_length_add_time hf.tm _ _ _ (hf.outputsFun a)

end

end BinTM0

end Turing
