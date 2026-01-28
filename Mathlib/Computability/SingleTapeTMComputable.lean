
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Computability.PostTuringMachine
public import Mathlib.Computability.EncodingTo
public import Mathlib.Computability.TuringMachine

/-!

This file is meant to develop the theory of time complexity for single-tape Turing machines.

Related is `TMComputable.lean`, which develops this for (a kind of) multi-tape Turing machines.

-/


@[expose] public section


open Computability



namespace Turing

namespace FinTM0

-- type of tape symbols
variable (Γ : Type*)

/-- A Turing machine "statement" is just a command to either move
  left or right, or write a symbol on the tape. -/
inductive Stmt
  | null : Stmt
  | move : Dir → Stmt
  | write : Γ → Stmt
deriving Inhabited

/--
Map a Stmt over an equivalence of alphabets.
-/
def Stmt.mapEquiv {Γ₁ Γ₂ : Type} (e : Γ₁ ≃ Γ₂) (s : Stmt Γ₁) :
    Stmt Γ₂ :=
  match s with
  | null => null
  | move d => move d
  | write a => write (e.toFun a)

end FinTM0

/-- A bundled TM0 with finiteness guarantees. -/
structure FinTM0 where
  /-- type of tape symbols -/
  (Γ : Type)
  [InhabitedΓ : Inhabited Γ]
  [FintypeΓ : Fintype Γ]
  /-- type of state labels -/
  (Λ : Type)
  /-- Initial state -/
  (q₀ : Λ)
  [FintypeΛ : Fintype Λ]
  /-- Transition function, mapping a state and a head symbol
  `Option`ally to a new state and Stmt to invoke, or else `none` to represent halting -/
  (M : Λ → Γ → Option (Λ × (Turing.FinTM0.Stmt Γ)))

namespace FinTM0

section

variable (tm : FinTM0)

instance : Inhabited tm.Γ :=
  tm.InhabitedΓ

instance : Fintype tm.Γ :=
  tm.FintypeΓ

instance : Inhabited tm.Λ :=
  ⟨tm.q₀⟩

instance : Fintype tm.Λ :=
  tm.FintypeΛ

instance inhabitedStmt : Inhabited (Stmt tm.Γ) := inferInstance

/-- The type of configurations (functions) corresponding to this TM. -/
structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.Λ
  /-- the tape contents -/
  tape : Tape tm.Γ
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
      -- If it is none, the TM halts by entering a halting configuration with tape t
      | none => some ⟨none, t⟩
      -- If it is some ⟨q'', a⟩,
      | some ⟨q'', a⟩ =>
        -- enter a new configuration
        some ⟨
          -- With state q''
          some q'',
          -- And tape updated according to the Stmt
          match a with -- TODO let this be its own `def`
          | Turing.FinTM0.Stmt.null => t
          | Turing.FinTM0.Stmt.move d => t.move d
          | Turing.FinTM0.Stmt.write a => t.write a⟩
end

/-- The initial configuration corresponding to a list in the input alphabet. -/
def initList (tm : FinTM0) (s : List tm.Γ) : tm.Cfg := ⟨some tm.q₀, Tape.mk₁ s⟩

/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
def haltList (tm : FinTM0) (s : List (tm.Γ)) : tm.Cfg := ⟨none, Tape.mk₁ s⟩

/-- A "proof" of the fact that `f` eventually reaches `b` when repeatedly evaluated on `a`,
remembering the number of steps it takes. -/
structure EvalsTo {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) where
  /-- number of steps taken -/
  steps : ℕ
  evals_in_steps : (flip bind f)^[steps] a = b

-- note: this cannot currently be used in `calc`, as the last two arguments must be `a` and `b`.
-- If this is desired, this argument order can be changed, but this spelling is I think the most
-- natural, so there is a trade-off that needs to be made here. A notation can get around this.
/-- A "proof" of the fact that `f` eventually reaches `b` in at most `m` steps when repeatedly
evaluated on `a`, remembering the number of steps it takes. -/
structure EvalsToInTime {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) extends
  EvalsTo f a b where
  steps_le_m : steps ≤ m

/-- Reflexivity of `EvalsTo` in 0 steps. -/
def EvalsTo.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsTo f a (some a) :=
  ⟨0, rfl⟩

/-- Transitivity of `EvalsTo` in the sum of the numbers of steps. -/
@[trans]
def EvalsTo.trans {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ)
    (h₁ : EvalsTo f a b) (h₂ : EvalsTo f b c) : EvalsTo f a c :=
  ⟨h₂.steps + h₁.steps, by rw [Function.iterate_add_apply, h₁.evals_in_steps, h₂.evals_in_steps]⟩

/-- Reflexivity of `EvalsToInTime` in 0 steps. -/
def EvalsToInTime.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsToInTime f a (some a) 0 :=
  ⟨EvalsTo.refl f a, le_refl 0⟩

/-- Transitivity of `EvalsToInTime` in the sum of the numbers of steps. -/
@[trans]
def EvalsToInTime.trans {σ : Type*} (f : σ → Option σ) (m₁ : ℕ) (m₂ : ℕ) (a : σ) (b : σ)
    (c : Option σ) (h₁ : EvalsToInTime f a b m₁) (h₂ : EvalsToInTime f b c m₂) :
    EvalsToInTime f a c (m₂ + m₁) :=
  ⟨EvalsTo.trans f a b c h₁.toEvalsTo h₂.toEvalsTo, add_le_add h₂.steps_le_m h₁.steps_le_m⟩

/-- A proof of tm outputting l' when given l. -/
def Outputs (tm : FinTM0) (l : List (tm.Γ)) (l' : Option (List (tm.Γ))) :=
  EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def OutputsInTime (tm : FinTM0) (l : List (tm.Γ)) (l' : Option (List (tm.Γ)))
    (m : ℕ) :=
  EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m

/-- The forgetful map, forgetting the upper bound on the number of steps. -/
def OutputsInTime.toOutputs {tm : FinTM0} {l : List (tm.Γ)}
    {l' : Option (List (tm.Γ))} {m : ℕ} (h : OutputsInTime tm l l' m) :
    Outputs tm l l' :=
  h.toEvalsTo

-- /-- A (bundled TM0) Turing machine
-- with input alphabet equivalent to `Γ₀` and output alphabet equivalent to `Γ₁`.
-- TODO this is something of a holdover, might get rid
-- -/
-- structure ComputableAux (Γ₀ Γ₁ : Type) where
--   /-- the underlying bundled TM0 -/
--   tm : FinTM0
--   /-- the input alphabet is equivalent to `Γ₀` -/
--   inputAlphabet : tm.Γ ≃ Γ₀
--   /-- the output alphabet is equivalent to `Γ₁` -/
--   outputAlphabet : tm.Γ ≃ Γ₁

/-- A Turing machine + a proof it outputs `f`. -/
structure Computable {α β Γ : Type} (ea : FinEncodingTo α Γ) (eb : FinEncodingTo β Γ) (f : α → β) where
  /-- the underlying bundled TM0 -/
  tm : FinTM0
  /-- the alphabet is equivalent to `Γ` -/
  equivAlphabet : tm.Γ ≃ Γ
  /-- a proof this machine outputs `f` -/
  outputsFun :
    ∀ a,
      Outputs tm ((List.map equivAlphabet.invFun) (ea.encode a))
        (Option.some ((List.map equivAlphabet.invFun) (eb.encode (f a))))

/-- A Turing machine + a time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure ComputableInTime {α β Γ : Type} (ea : FinEncodingTo α Γ) (eb : FinEncodingTo β Γ)
  (f : α → β) where
  /-- the underlying bundled TM0 -/
  tm : FinTM0
  /-- the alphabet is equivalent to `Γ` -/
  equivAlphabet : tm.Γ ≃ Γ
  /-- a time function -/
  time : ℕ → ℕ
  /-- proof this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      tm.OutputsInTime
        (List.map equivAlphabet.invFun (ea.encode a))
        (Option.some ((List.map equivAlphabet.invFun) (eb.encode (f a))))
        (time (ea.encode a).length)

/-- A Turing machine + a polynomial time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure ComputableInPolyTime {α β Γ : Type} (ea : FinEncodingTo α Γ) (eb : FinEncodingTo β Γ)
  (f : α → β) where
  /-- the underlying bundled TM0 -/
  tm : FinTM0
  /-- the alphabet is equivalent to `Γ` -/
  equivAlphabet : tm.Γ ≃ Γ
  /-- a polynomial time function -/
  time : Polynomial ℕ
  /-- proof that this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      OutputsInTime tm (List.map equivAlphabet.invFun (ea.encode a))
        (Option.some ((List.map equivAlphabet.invFun) (eb.encode (f a))))
        (time.eval (ea.encode a).length)

/-- A forgetful map, forgetting the time bound on the number of steps. -/
def ComputableInTime.toComputable {α β Γ : Type} {ea : FinEncodingTo α Γ} {eb : FinEncodingTo β Γ}
    {f : α → β} (h : ComputableInTime ea eb f) : Computable ea eb f :=
  ⟨h.tm, _, fun a => OutputsInTime.toOutputs (h.outputsFun a)⟩

/-- A forgetful map, forgetting that the time function is polynomial. -/
def ComputableInPolyTime.toComputableInTime {α β Γ : Type} {ea : FinEncodingTo α Γ}
    {eb : FinEncodingTo β Γ} {f : α → β} (h : ComputableInPolyTime ea eb f) :
    ComputableInTime ea eb f :=
  ⟨h.tm, _, fun n => h.time.eval n, h.outputsFun⟩

open Turing.TM0.Stmt

/-- A Turing machine computing the identity on lists over Γ. -/
def idComputer {Γ : Type} [Inhabited Γ] [Fintype Γ] : FinTM0 where
  Γ := Γ
  Λ := PUnit
  q₀ := PUnit.unit
  M := fun _ _ => none


-- instance inhabitedFinTM0 : Inhabited FinTM0 :=
--   ⟨idComputer Computability.inhabitedFinEncodingTo.default⟩

noncomputable section

/-- A proof that the identity map on α is computable in polytime. -/
def ComputableInPolyTime.id {α Γ : Type} (ea : FinEncodingTo α Γ) [Inhabited Γ] [Fintype Γ] :
    @ComputableInPolyTime α α Γ ea ea id where
  tm := idComputer
  equivAlphabet := Equiv.cast rfl
  time := 1
  outputsFun _ :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := by simp only [Polynomial.eval_one, le_refl] }

-- instance inhabitedComputableInPolyTime :
--     Inhabited (ComputableInPolyTime (default : FinEncodingTo Bool) default id) :=
--   ⟨idComputableInPolyTime Computability.inhabitedFinEncodingTo.default⟩

-- instance inhabitedOutputsInTime :
--     Inhabited
--       (OutputsInTime (idComputer finEncodingBoolBool) (List.map (Equiv.cast rfl).invFun [false])
--         (some (List.map (Equiv.cast rfl).invFun [false])) (Polynomial.eval 1 1)) :=
--   ⟨(idComputableInPolyTime finEncodingBoolBool).outputsFun false⟩

-- instance inhabitedOutputs :
--     Inhabited
--       (Outputs (idComputer finEncodingBoolBool) (List.map (Equiv.cast rfl).invFun [false])
--         (some (List.map (Equiv.cast rfl).invFun [false]))) :=
--   ⟨OutputsInTime.toOutputs Turing.inhabitedOutputsInTime.default⟩

-- instance inhabitedEvalsToInTime :
--     Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
--   ⟨EvalsToInTime.refl _ _⟩

-- instance inhabitedTM0EvalsTo : Inhabited (EvalsTo (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
--   ⟨EvalsTo.refl _ _⟩

/-- A proof that the identity map on α is computable in time. -/
def ComputableInTime.id {α Γ : Type} (ea : FinEncodingTo α Γ) [Inhabited Γ] [Fintype Γ] :
    @ComputableInTime α α Γ ea ea id :=
  ComputableInPolyTime.toComputableInTime <| ComputableInPolyTime.id ea

-- instance inhabitedComputableInTime :
--     Inhabited (ComputableInTime finEncodingBoolBool finEncodingBoolBool id) :=
--   ⟨idComputableInTime Computability.inhabitedFinEncodingTo.default⟩

/-- A proof that the identity map on α is computable. -/
def idComputable {α Γ : Type} (ea : FinEncodingTo α Γ) [Inhabited Γ] [Fintype Γ] : @Computable α α Γ ea ea id :=
  ComputableInTime.toComputable <| ComputableInTime.id ea

-- instance inhabitedComputable :
--     Inhabited (Computable finEncodingBoolBool finEncodingBoolBool id) :=
--   ⟨idComputable Computability.inhabitedFinEncodingTo.default⟩

-- instance inhabitedComputableAux : Inhabited (ComputableAux Bool Bool) :=
--   ⟨(default : Computable finEncodingBoolBool finEncodingBoolBool id).toComputableAux⟩

def compComputer {α β γ Γ : Type} {eα : FinEncodingTo α Γ} {eβ : FinEncodingTo β Γ}
    {eγ : FinEncodingTo γ Γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f)
    (hg : ComputableInTime eβ eγ g)
    (h_mono : Monotone hg.time) :
    FinTM0 :=
  {
    Γ := Γ
    InhabitedΓ := sorry
    FintypeΓ := sorry
    Λ := hf.tm.Λ ⊕ hg.tm.Λ
    q₀ := Sum.inl hf.tm.q₀
    M := fun q h =>
      match q with
      -- If we are in the first machine's states, run that machine
      | Sum.inl ql => match hf.tm.M ql (hf.equivAlphabet.invFun h) with
        -- If it halts, transition to the second machine's start state, take null action on tape
        | none => some ⟨Sum.inr hg.tm.q₀, Stmt.null⟩
        -- Otherwise continue as normal
        | some (ql', stmt) => some (Sum.inl ql', stmt.mapEquiv (hf.equivAlphabet))
      -- If we are in the second machine's states, run that machine
      | Sum.inr qr =>
        match hg.tm.M qr (hg.equivAlphabet.invFun h) with
        -- If it halts, halt
        | none => none
        -- Otherwise continue as normal
        | some (qr', stmt) => some (Sum.inr qr', stmt.mapEquiv (hg.equivAlphabet))
  }

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
    {α β γ Γ : Type} {eα : FinEncodingTo α Γ} {eβ : FinEncodingTo β Γ}
    {eγ : FinEncodingTo γ Γ} {f : α → β} {g : β → γ}
    (hf : ComputableInTime eα eβ f)
    (hg : ComputableInTime eβ eγ g)
    (h_mono : Monotone hg.time) :
    (ComputableInTime eα eγ (g ∘ f)) where
  tm := compComputer hf hg h_mono
  equivAlphabet := Equiv.refl Γ
  time l := hf.time l + 1 + hg.time (l + hf.time l)
  outputsFun a := by
    simp [OutputsInTime, initList, haltList]
    -- The computer evals a to f a in time hf.time (eα.encode a)
    have :
        EvalsToInTime (compComputer hf hg h_mono).step
          { state := some (compComputer hf hg h_mono).q₀, tape := Tape.mk₁ (List.map (⇑(Equiv.refl Γ).symm) (eα.encode a)) }
          (some { state := none, tape := Tape.mk₁ (List.map (⇑(Equiv.refl Γ).symm) (eγ.encode (g (f a)))) })
          (hf.time (eα.encode a).length + 1 + hg.time ((eα.encode a).length + hf.time (eα.encode a).length)) := by
      sorry

    sorry


end

end FinTM0

end Turing
