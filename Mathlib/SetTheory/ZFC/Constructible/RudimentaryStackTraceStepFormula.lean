/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.FiniteOrdinalSuccessorFormula
public import Mathlib.SetTheory.ZFC.Constructible.IndexedSequenceLookup
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackStepFormula

/-!
# One indexed transition of a rudimentary stack trace

The outer assignment layout is

`[U, varTag, appTag, empty, op0, ..., op8, program, trace, index]`.

The formula appends witnesses `token`, `input`, `succ`, and `output`.  It reads
the token and input state at `index`, verifies that `succ` is the finite
ordinal successor of `index`, reads the output state at `succ`, and applies
`stackStepFormula` to the decoded transition.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

/-! ## Fixed coordinates and renamings -/

/-- The program coordinate in the trace-step layout. -/
def traceStepProgramIndex : Fin 16 := 13
/-- The trace coordinate in the trace-step layout. -/
def traceStepTraceIndex : Fin 16 := 14
/-- The current-index coordinate in the trace-step layout. -/
def traceStepIndexIndex : Fin 16 := 15

/-- Read `[program,index,token]` in the four-witness context. -/
def traceStepProgramValueRename : Fin 3 -> Fin 20 :=
  ![(13 : Fin 20), (15 : Fin 20), (16 : Fin 20)]

/-- Read `[trace,index,input]` in the four-witness context. -/
def traceStepInputValueRename : Fin 3 -> Fin 20 :=
  ![(14 : Fin 20), (15 : Fin 20), (17 : Fin 20)]

/-- Read `[trace,succ,output]` in the four-witness context. -/
def traceStepOutputValueRename : Fin 3 -> Fin 20 :=
  ![(14 : Fin 20), (18 : Fin 20), (19 : Fin 20)]

/--
Supply the thirteen fixed stack-step parameters followed by
`[token,input,output]`.
-/
def traceStepStackStepRename : Fin 16 -> Fin 20 :=
  Fin.lastCases (19 : Fin 20)
    (fun i15 => Fin.lastCases (17 : Fin 20)
      (fun i14 => Fin.lastCases (16 : Fin 20)
        (fun i13 =>
          i13.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        i14) i15)

/-! ## Formula -/

/-- The four-witness body in context indices zero through nineteen. -/
def traceStepBody : FOFormula 20 :=
  .conj
    (FOFormula.rename traceStepProgramValueRename
      Constructible.IndexedSequenceZF.valueAtFormula)
    (.conj
      (FOFormula.rename traceStepInputValueRename
        Constructible.IndexedSequenceZF.valueAtFormula)
      (.conj
        (Delta0Formula.successorFOAt (18 : Fin 20) (15 : Fin 20))
        (.conj
          (FOFormula.rename traceStepOutputValueRename
            Constructible.IndexedSequenceZF.valueAtFormula)
          (FOFormula.rename traceStepStackStepRename stackStepFormula))))

/-- One local transition of an indexed postfix-program execution trace. -/
def traceStepFormula : FOFormula 16 :=
  .ex (.ex (.ex (.ex traceStepBody)))

/-- The intended assignment to the fixed outer context. -/
noncomputable def traceStepAssignment
    (U program trace index : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  stackStepAssignment U program trace index

theorem comp_traceStepProgramValueRename
    (U program trace index token input succ output : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
        token) input) succ) output (traceStepProgramValueRename i)) =
      ![program, index, token] := by
  funext i
  fin_cases i <;> rfl

theorem comp_traceStepInputValueRename
    (U program trace index token input succ output : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
        token) input) succ) output (traceStepInputValueRename i)) =
      ![trace, index, input] := by
  funext i
  fin_cases i <;> rfl

theorem comp_traceStepOutputValueRename
    (U program trace index token input succ output : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
        token) input) succ) output (traceStepOutputValueRename i)) =
      ![trace, succ, output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem traceStepWitnessSucc
    (U program trace index token input succ output : ZFSet.{u}) :
    snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
      token) input) succ) output (18 : Fin 20) = succ :=
  rfl

@[simp]
theorem traceStepWitnessIndex
    (U program trace index token input succ output : ZFSet.{u}) :
    snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
    token) input) succ) output (15 : Fin 20) = index :=
  rfl

set_option maxHeartbeats 1200000 in
-- The nested `snoc` assignment has sixteen coordinates; the proof below
-- reduces it by three explicit `Fin.lastCases` layers.
theorem comp_traceStepStackStepRename
    (U program trace index token input succ output : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
        token) input) succ) output (traceStepStackStepRename i)) =
      stackStepAssignment U token input output := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rfl
      · simp [traceStepAssignment, stackStepAssignment,
          traceStepStackStepRename]

/-! ## Raw semantics -/

/-- Semantic decomposition into the four constituent checks. -/
@[simp]
theorem satisfies_traceStepFormula_components
    (U program trace index : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
        (traceStepAssignment U program trace index) <->
      exists token input succ output : ZFSet.{u},
        FOFormula.Satisfies Delta0Formula.ZFMem
            Constructible.IndexedSequenceZF.valueAtFormula
            ![program, index, token] /\
        FOFormula.Satisfies Delta0Formula.ZFMem
            Constructible.IndexedSequenceZF.valueAtFormula
            ![trace, index, input] /\
        succ = insert index index /\
        FOFormula.Satisfies Delta0Formula.ZFMem
            Constructible.IndexedSequenceZF.valueAtFormula
            ![trace, succ, output] /\
        FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
          (stackStepAssignment U token input output) := by
  simp only [traceStepFormula, traceStepBody, FOFormula.Satisfies,
    FOFormula.satisfies_rename,
    Delta0Formula.satisfies_successorFOAt_ambient,
    comp_traceStepProgramValueRename,
    comp_traceStepInputValueRename,
    comp_traceStepOutputValueRename,
    traceStepWitnessSucc, traceStepWitnessIndex,
    comp_traceStepStackStepRename]

/-- Complete raw `ZFSet` normal form of one trace transition. -/
theorem satisfies_traceStepFormula
    (U program trace index : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
        (traceStepAssignment U program trace index) <->
      exists token input succ output : ZFSet.{u},
        (exists programLength programGraph : ZFSet.{u},
          program = ZFSet.pair programLength programGraph /\
            index ∈ programLength /\
            ZFSet.pair token index ∈ programGraph) /\
        (exists traceLength traceGraph : ZFSet.{u},
          trace = ZFSet.pair traceLength traceGraph /\
            index ∈ traceLength /\
            ZFSet.pair input index ∈ traceGraph) /\
        succ = insert index index /\
        (exists traceLength traceGraph : ZFSet.{u},
          trace = ZFSet.pair traceLength traceGraph /\
            succ ∈ traceLength /\
            ZFSet.pair output succ ∈ traceGraph) /\
        ((exists generator : ZFSet.{u},
            token = triple varTag generator ∅ /\
              (generator = U \/ generator ∈ U) /\
              output = ZFSet.pair generator input) \/
          (exists i : Fin 9,
            exists right left rest result : ZFSet.{u},
              token = triple appTag (operationCode i) ∅ /\
                input = ZFSet.pair right (ZFSet.pair left rest) /\
                output = ZFSet.pair result rest /\
                result = op i left right)) := by
  rw [satisfies_traceStepFormula_components]
  simp only [Constructible.IndexedSequenceZF.satisfies_valueAtFormula,
    satisfies_stackStepFormula]

/-! ## Genuine indexed sequence codes -/

/--
On actual sequence codes, the trace-step formula selects the entries at `k`
and `k + 1` and applies exactly one raw stack-step formula.
-/
theorem satisfies_traceStepFormula_sequenceCodes_iff
    (U : ZFSet.{u}) (program trace : List ZFSet.{u}) (k : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
        (traceStepAssignment U
          (Constructible.IndexedSequenceZF.sequenceCode program)
          (Constructible.IndexedSequenceZF.sequenceCode trace)
          (FiniteSequenceZF.natCode k)) <->
      exists hp : k < program.length,
        exists hi : k < trace.length,
          exists ho : k + 1 < trace.length,
            FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
              (stackStepAssignment U
                (program.get ⟨k, hp⟩)
                (trace.get ⟨k, hi⟩)
                (trace.get ⟨k + 1, ho⟩)) := by
  rw [satisfies_traceStepFormula_components]
  constructor
  · rintro ⟨token, input, succ, output,
      htoken, hinput, hsucc, houtput, hstep⟩
    rcases
        (Constructible.IndexedSequenceZF.satisfies_valueAtFormula_sequenceCode_iff
          program k token).mp
          htoken with
      ⟨hp, htoken⟩
    rcases
        (Constructible.IndexedSequenceZF.satisfies_valueAtFormula_sequenceCode_iff
          trace k input).mp
          hinput with
      ⟨hi, hinput⟩
    have hsuccCode : succ = FiniteSequenceZF.natCode (k + 1) :=
      hsucc.trans (FiniteSequenceZF.natCode_succ_eq_insert k).symm
    rw [hsuccCode] at houtput
    rcases
        (Constructible.IndexedSequenceZF.satisfies_valueAtFormula_sequenceCode_iff
          trace (k + 1) output).mp
          houtput with
      ⟨ho, houtput⟩
    refine ⟨hp, hi, ho, ?_⟩
    subst token
    subst input
    subst output
    exact hstep
  · rintro ⟨hp, hi, ho, hstep⟩
    refine ⟨program.get ⟨k, hp⟩, trace.get ⟨k, hi⟩,
      FiniteSequenceZF.natCode (k + 1), trace.get ⟨k + 1, ho⟩,
      ?_, ?_, ?_, ?_, hstep⟩
    · exact
        (Constructible.IndexedSequenceZF.satisfies_valueAtFormula_sequenceCode_iff
          program k _).mpr
          ⟨hp, rfl⟩
    · exact
        (Constructible.IndexedSequenceZF.satisfies_valueAtFormula_sequenceCode_iff
          trace k _).mpr
          ⟨hi, rfl⟩
    · exact FiniteSequenceZF.natCode_succ_eq_insert k
    · exact
        (Constructible.IndexedSequenceZF.satisfies_valueAtFormula_sequenceCode_iff
          trace (k + 1) _).mpr
          ⟨ho, rfl⟩

/-- Fixed-bound form of `satisfies_traceStepFormula_sequenceCodes_iff`. -/
theorem satisfies_traceStepFormula_sequenceCodes_iff_at
    (U : ZFSet.{u}) (program trace : List ZFSet.{u}) (k : Nat)
    (hp : k < program.length) (hi : k < trace.length)
    (ho : k + 1 < trace.length) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
        (traceStepAssignment U
          (Constructible.IndexedSequenceZF.sequenceCode program)
          (Constructible.IndexedSequenceZF.sequenceCode trace)
          (FiniteSequenceZF.natCode k)) <->
      FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U
          (program.get ⟨k, hp⟩)
          (trace.get ⟨k, hi⟩)
          (trace.get ⟨k + 1, ho⟩)) := by
  rw [satisfies_traceStepFormula_sequenceCodes_iff]
  constructor
  · rintro ⟨hp', hi', ho', hstep⟩
    simpa using hstep
  · intro hstep
    exact ⟨hp, hi, ho, hstep⟩

/-- The same local-step semantics for arbitrary valid sequence representations. -/
theorem satisfies_traceStepFormula_represents_iff
    (U : ZFSet.{u})
    {programCode traceCode : ZFSet.{u}}
    {program trace : List ZFSet.{u}}
    (hprogram : Constructible.IndexedSequenceZF.Represents
      programCode program)
    (htrace : Constructible.IndexedSequenceZF.Represents traceCode trace)
    (k : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
        (traceStepAssignment U programCode traceCode
          (FiniteSequenceZF.natCode k)) ↔
      ∃ hp : k < program.length,
        ∃ hi : k < trace.length,
          ∃ ho : k + 1 < trace.length,
            FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
              (stackStepAssignment U
                (program.get ⟨k, hp⟩)
                (trace.get ⟨k, hi⟩)
                (trace.get ⟨k + 1, ho⟩)) := by
  rw [satisfies_traceStepFormula_components]
  constructor
  · rintro ⟨token, input, succ, output,
      htoken, hinput, hsucc, houtput, hstep⟩
    rcases
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          hprogram k token).mp htoken with
      ⟨hp, htoken⟩
    rcases
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          htrace k input).mp hinput with
      ⟨hi, hinput⟩
    have hsuccCode : succ = FiniteSequenceZF.natCode (k + 1) :=
      hsucc.trans (FiniteSequenceZF.natCode_succ_eq_insert k).symm
    rw [hsuccCode] at houtput
    rcases
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          htrace (k + 1) output).mp houtput with
      ⟨ho, houtput⟩
    refine ⟨hp, hi, ho, ?_⟩
    subst token
    subst input
    subst output
    exact hstep
  · rintro ⟨hp, hi, ho, hstep⟩
    refine ⟨program.get ⟨k, hp⟩, trace.get ⟨k, hi⟩,
      FiniteSequenceZF.natCode (k + 1), trace.get ⟨k + 1, ho⟩,
      ?_, ?_, ?_, ?_, hstep⟩
    · exact
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          hprogram k _).mpr ⟨hp, rfl⟩
    · exact
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          htrace k _).mpr ⟨hi, rfl⟩
    · exact FiniteSequenceZF.natCode_succ_eq_insert k
    · exact
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          htrace (k + 1) _).mpr ⟨ho, rfl⟩

end Constructible.Godel.RudimentaryTerm
