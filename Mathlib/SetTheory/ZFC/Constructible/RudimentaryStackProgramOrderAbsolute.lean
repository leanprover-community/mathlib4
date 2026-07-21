/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.InternalWellOrder
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderFormula

/-!
# Absoluteness of the postfix-program order on genuine codes

`stackProgramLtFormula` contains unrestricted witnesses for decoded lengths,
graphs, entries, and token payloads.  Consequently it is not a bounded formula
and no blanket absoluteness theorem applies.  This file supplies constructible
witnesses for genuine program codes and proves the restricted semantics
directly.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open IndexedSequenceZF
open FiniteSequenceZF

/-- Every entry in the encoded-token list of a genuine program is in `L`. -/
theorem stackTokenCodes_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (program : List (StackToken (Option (Constructible.ZFCarrier U)))) :
    ∀ code ∈ program.map (stackTokenZFCode U), code ∈ L := by
  intro code hcode
  rcases List.mem_map.mp hcode with ⟨token, _htoken, rfl⟩
  exact stackTokenZFCode_mem_L hU token

/-- The indexed graph underlying a genuine program code is constructible. -/
theorem stackProgramGraph_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (program : List (StackToken (Option (Constructible.ZFCarrier U)))) :
    IndexedSequenceZF.graph
        (program.map (stackTokenZFCode U)) ∈ L := by
  exact IndexedSequenceZF.graphFrom_mem_L
    (stackTokenCodes_mem_L hU program) 0

/-- All eight free coordinates of the program comparison, packaged in `L`. -/
def stackProgramLtLAssignment (U relation : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    Tuple Model.LCarrier.{u} 8 :=
  ![⟨U, hU⟩,
    ⟨relation, hrelation⟩,
    ⟨varTag, varTag_mem_L⟩,
    ⟨appTag, appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩,
    ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩,
    ⟨stackProgramZFCode U left, stackProgramZFCode_mem_L hU left⟩,
    ⟨stackProgramZFCode U right, stackProgramZFCode_mem_L hU right⟩]

theorem stackProgramLtLAssignment_val (U relation : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    (fun i =>
      (stackProgramLtLAssignment U relation hU hrelation left right i).1) =
      stackProgramLtAssignment U relation left right := by
  funext i
  fin_cases i <;> rfl

/-! ## Component formulas over `LCarrier` -/

local notation "LMem" => Model.lCarrierMem

theorem satisfies_kuratowskiPairEqAt_lCarrier {n : Nat}
    (pair left right : Fin n) (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.kuratowskiPairEqAt pair left right).toFO s ↔
      (s pair).1 = ZFSet.pair (s left).1 (s right).1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]

@[simp]
theorem satisfies_functionGraphValueAt_lCarrier {n : Nat}
    (graph value index : Fin n) (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (IndexedSequenceZF.functionGraphValueAt graph value index) s ↔
      ZFSet.pair (s value).1 (s index).1 ∈ (s graph).1 := by
  rw [IndexedSequenceZF.functionGraphValueAt,
    Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO]
  simp only [Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hq
    exact ⟨ZFSet.pair (s value).1 (s index).1, hq, rfl⟩

@[simp]
theorem satisfies_valueAtFormula_lCarrier_iff
    (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ L)
    (k : Nat) (value : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            IndexedSequenceZF.sequenceCode_mem_L hxs⟩,
          ⟨natCode k, natCode_mem_L k⟩, value] ↔
      ∃ hk : k < xs.length, value.1 = xs.get ⟨k, hk⟩ := by
  rw [IndexedSequenceZF.valueAtFormula,
    Delta0Formula.satisfies_toFO_lCarrier_absolute]
  have hval :
      (fun i =>
        (![⟨IndexedSequenceZF.sequenceCode xs,
              IndexedSequenceZF.sequenceCode_mem_L hxs⟩,
            ⟨natCode k, natCode_mem_L k⟩, value] i).1) =
        ![IndexedSequenceZF.sequenceCode xs, natCode k, value.1] := by
    funext i
    fin_cases i <;> rfl
  rw [hval]
  exact IndexedSequenceZF.satisfies_valueAt_sequenceCode_iff xs k value.1

@[simp]
theorem satisfies_samePrefixFormula_lCarrier
    (leftSequence rightSequence bound : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.samePrefixFormula
        ![leftSequence, rightSequence, bound] ↔
      ∀ index : Model.LCarrier.{u}, index.1 ∈ bound.1 →
        ∃ value : Model.LCarrier.{u},
          FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
              ![leftSequence, index, value] ∧
            FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
              ![rightSequence, index, value] := by
  simp only [IndexedSequenceZF.samePrefixFormula,
    FOFormula.satisfies_boundedAll, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  constructor
  · intro h index hindex
    rcases h index hindex with ⟨value, hleft, hright⟩
    refine ⟨value, ?_, ?_⟩
    · change FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
        ![leftSequence, index, value] at hleft
      exact hleft
    · change FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
        ![rightSequence, index, value] at hright
      exact hright
  · intro h index hindex
    rcases h index hindex with ⟨value, hleft, hright⟩
    refine ⟨value, ?_, ?_⟩
    · change FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
        (fun i => snoc (snoc ![leftSequence, rightSequence, bound] index) value
          (![0, 3, 4] i))
      exact hleft
    · change FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
        (fun i => snoc (snoc ![leftSequence, rightSequence, bound] index) value
          (![1, 3, 4] i))
      exact hright

theorem satisfies_samePrefix_sequenceCode_lCarrier_iff
    (xs ys : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ L) (hys : ∀ y ∈ ys, y ∈ L)
    (k : Nat) :
    FOFormula.Satisfies LMem IndexedSequenceZF.samePrefixFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            IndexedSequenceZF.sequenceCode_mem_L hxs⟩,
          ⟨IndexedSequenceZF.sequenceCode ys,
            IndexedSequenceZF.sequenceCode_mem_L hys⟩,
          ⟨natCode k, natCode_mem_L k⟩] ↔
      ∀ j : Nat, j < k →
        ∃ hx : j < xs.length, ∃ hy : j < ys.length,
          xs.get ⟨j, hx⟩ = ys.get ⟨j, hy⟩ := by
  rw [satisfies_samePrefixFormula_lCarrier]
  constructor
  · intro h j hj
    let index : Model.LCarrier.{u} := ⟨natCode j, natCode_mem_L j⟩
    rcases h index ((mem_natCode_iff _ _).mpr ⟨j, hj, rfl⟩) with
      ⟨value, hleft, hright⟩
    rcases (satisfies_valueAtFormula_lCarrier_iff xs hxs j value).mp
        (by simpa only [index] using hleft) with ⟨hx, hvalueX⟩
    rcases (satisfies_valueAtFormula_lCarrier_iff ys hys j value).mp
        (by simpa only [index] using hright) with ⟨hy, hvalueY⟩
    exact ⟨hx, hy, hvalueX.symm.trans hvalueY⟩
  · intro h index hindex
    rcases (mem_natCode_iff index.1 k).mp hindex with ⟨j, hj, hindexEq⟩
    rcases h j hj with ⟨hx, hy, hxy⟩
    let indexJ : Model.LCarrier.{u} := ⟨natCode j, natCode_mem_L j⟩
    have hindexCarrier : index = indexJ := Subtype.ext hindexEq
    have hvalueL : xs.get ⟨j, hx⟩ ∈ L :=
      hxs _ (List.get_mem xs ⟨j, hx⟩)
    let value : Model.LCarrier.{u} := ⟨xs.get ⟨j, hx⟩, hvalueL⟩
    refine ⟨value, ?_, ?_⟩
    · have hleft :=
        (satisfies_valueAtFormula_lCarrier_iff xs hxs j value).mpr
          ⟨hx, rfl⟩
      simpa only [hindexCarrier, indexJ] using hleft
    · have hright :=
        (satisfies_valueAtFormula_lCarrier_iff ys hys j value).mpr
          ⟨hy, hxy⟩
      simpa only [hindexCarrier, indexJ, value] using hright

@[simp]
theorem satisfies_hasLengthFormula_lCarrier_iff
    (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ L)
    (length : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.hasLengthFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            IndexedSequenceZF.sequenceCode_mem_L hxs⟩, length] ↔
      length.1 = natCode xs.length := by
  simp only [IndexedSequenceZF.hasLengthFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨graph, hpair⟩
    have hpairRaw :=
      (satisfies_kuratowskiPairEqAt_lCarrier
        (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
        (snoc ![⟨IndexedSequenceZF.sequenceCode xs,
          IndexedSequenceZF.sequenceCode_mem_L hxs⟩, length] graph)).mp hpair
    exact (ZFSet.pair_inj.mp hpairRaw).1.symm
  · intro hlength
    let graph : Model.LCarrier.{u} :=
      ⟨IndexedSequenceZF.graph xs,
        IndexedSequenceZF.graphFrom_mem_L hxs 0⟩
    refine ⟨graph, ?_⟩
    apply (satisfies_kuratowskiPairEqAt_lCarrier
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
      (snoc ![⟨IndexedSequenceZF.sequenceCode xs,
        IndexedSequenceZF.sequenceCode_mem_L hxs⟩, length] graph)).mpr
    change IndexedSequenceZF.sequenceCode xs =
      ZFSet.pair length.1 (IndexedSequenceZF.graph xs)
    rw [hlength]
    rfl

@[simp]
theorem satisfies_uniqueValueAtBody_lCarrier
    (omega sequence length graph index value : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.uniqueValueAtBody
        ![omega, sequence, length, graph, index, value] ↔
      ZFSet.pair value.1 index.1 ∈ graph.1 ∧
        ∀ other : Model.LCarrier.{u},
          ZFSet.pair other.1 index.1 ∈ graph.1 → other.1 = value.1 := by
  simp [IndexedSequenceZF.uniqueValueAtBody,
    IndexedSequenceZF.satisfies_formulaImp,
    satisfies_functionGraphValueAt_lCarrier, Subtype.ext_iff,
    Model.snoc_eq_finSnoc]

@[simp]
theorem satisfies_totalFunctionalBody_lCarrier
    (omega sequence length graph index : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.totalFunctionalBody
        ![omega, sequence, length, graph, index] ↔
      (index.1 ∈ length.1 →
        ∃ value : Model.LCarrier.{u},
          ZFSet.pair value.1 index.1 ∈ graph.1 ∧
            ∀ other : Model.LCarrier.{u},
              ZFSet.pair other.1 index.1 ∈ graph.1 →
                other.1 = value.1) := by
  simp [IndexedSequenceZF.totalFunctionalBody,
    IndexedSequenceZF.satisfies_formulaImp,
    satisfies_uniqueValueAtBody_lCarrier, Model.snoc_eq_finSnoc]

@[simp]
theorem satisfies_sequenceValidityFormula_lCarrier
    (omega sequence : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
        ![omega, sequence] ↔
      ∃ length graph : Model.LCarrier.{u},
        sequence.1 = ZFSet.pair length.1 graph.1 ∧
          length.1 ∈ omega.1 ∧
          ∀ index : Model.LCarrier.{u}, index.1 ∈ length.1 →
            ∃ value : Model.LCarrier.{u},
              ZFSet.pair value.1 index.1 ∈ graph.1 ∧
                ∀ other : Model.LCarrier.{u},
                  ZFSet.pair other.1 index.1 ∈ graph.1 →
                    other.1 = value.1 := by
  simp only [IndexedSequenceZF.sequenceValidityFormula,
    FOFormula.Satisfies, FOFormula.satisfies_all]
  constructor
  · rintro ⟨length, graph, hpair, hlength, htotal⟩
    refine ⟨length, graph, ?_, hlength, ?_⟩
    · have hpairRaw :=
        (satisfies_kuratowskiPairEqAt_lCarrier
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (snoc (snoc ![omega, sequence] length) graph)).mp hpair
      change sequence.1 = ZFSet.pair length.1 graph.1 at hpairRaw
      exact hpairRaw
    · intro index hindex
      have hbody := htotal index
      exact
        ((satisfies_totalFunctionalBody_lCarrier
          omega sequence length graph index).mp
            (by
              change FOFormula.Satisfies LMem
                IndexedSequenceZF.totalFunctionalBody
                ![omega, sequence, length, graph, index] at hbody
              exact hbody)) hindex
  · rintro ⟨length, graph, hpair, hlength, htotal⟩
    refine ⟨length, graph, ?_, hlength, ?_⟩
    · apply (satisfies_kuratowskiPairEqAt_lCarrier
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
        (snoc (snoc ![omega, sequence] length) graph)).mpr
      change sequence.1 = ZFSet.pair length.1 graph.1
      exact hpair
    · intro index
      have hbody :=
        (satisfies_totalFunctionalBody_lCarrier
          omega sequence length graph index).mpr (htotal index)
      change FOFormula.Satisfies LMem
        IndexedSequenceZF.totalFunctionalBody
        ![omega, sequence, length, graph, index]
      exact hbody

/-- Every genuine indexed code is valid even with all quantifiers restricted to `L`. -/
theorem satisfies_sequenceValidity_sequenceCode_lCarrier
    (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ L) :
    FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
      ![⟨Ordinal.omega0.toZFSet, omega_mem_L⟩,
        ⟨IndexedSequenceZF.sequenceCode xs,
          IndexedSequenceZF.sequenceCode_mem_L hxs⟩] := by
  rw [satisfies_sequenceValidityFormula_lCarrier]
  let length : Model.LCarrier.{u} :=
    ⟨natCode xs.length, natCode_mem_L xs.length⟩
  let graph : Model.LCarrier.{u} :=
    ⟨IndexedSequenceZF.graph xs,
      IndexedSequenceZF.graphFrom_mem_L hxs 0⟩
  refine ⟨length, graph, rfl, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 xs.length)
  · intro index hindex
    rcases (mem_natCode_iff index.1 xs.length).mp hindex with
      ⟨k, hk, hindexEq⟩
    have hvalueL : xs.get ⟨k, hk⟩ ∈ L :=
      hxs _ (List.get_mem xs ⟨k, hk⟩)
    let value : Model.LCarrier.{u} := ⟨xs.get ⟨k, hk⟩, hvalueL⟩
    refine ⟨value, ?_, ?_⟩
    · apply (IndexedSequenceZF.mem_graph_iff xs _).mpr
      exact ⟨⟨k, hk⟩, by simp only [hindexEq, value]⟩
    · intro other hother
      rcases (IndexedSequenceZF.mem_graph_iff xs _).mp hother with
        ⟨j, hpair⟩
      have hparts := ZFSet.pair_inj.mp hpair
      have hkj : k = j.1 := by
        apply natCode_injective
        exact hindexEq.symm.trans hparts.2
      simpa only [value, hkj] using hparts.1

/-! ## Token comparison over `LCarrier` -/

/-- The seven-coordinate token comparison assignment, with all entries in `L`. -/
def stackTokenLtLAssignment (U relation : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : StackToken (Option (Constructible.ZFCarrier U))) :
    Tuple Model.LCarrier.{u} 7 :=
  ![⟨U, hU⟩, ⟨relation, hrelation⟩,
    ⟨varTag, varTag_mem_L⟩, ⟨appTag, appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩,
    ⟨stackTokenZFCode U left, stackTokenZFCode_mem_L hU left⟩,
    ⟨stackTokenZFCode U right, stackTokenZFCode_mem_L hU right⟩]

theorem stackTokenLtLAssignment_val (U relation : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : StackToken (Option (Constructible.ZFCarrier U))) :
    (fun i =>
      (stackTokenLtLAssignment U relation hU hrelation left right i).1) =
      stackTokenLtAssignment U relation
        (stackTokenZFCode U left) (stackTokenZFCode U right) := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_stackTokenLtFormula_lCarrier_normal
    (s : Tuple Model.LCarrier.{u} 7) :
    FOFormula.Satisfies LMem stackTokenLtFormula s ↔
      ∃ x y : Model.LCarrier.{u},
        ((s 5).1 = triple (s 2).1 x.1 (s 4).1 ∧
          (s 6).1 = triple (s 2).1 y.1 (s 4).1 ∧
          ((x.1 = (s 0).1 ∧ y.1 ∈ (s 0).1) ∨
            (x.1 ∈ (s 0).1 ∧ y.1 ∈ (s 0).1 ∧
              ZFSet.pair x.1 y.1 ∈ (s 1).1))) ∨
        ((s 5).1 = triple (s 2).1 x.1 (s 4).1 ∧
          (s 6).1 = triple (s 3).1 y.1 (s 4).1) ∨
        ((s 5).1 = triple (s 3).1 x.1 (s 4).1 ∧
          (s 6).1 = triple (s 3).1 y.1 (s 4).1 ∧ x.1 ∈ y.1) := by
  simp only [stackTokenLtFormula, FOFormula.Satisfies]
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute]
  simp only [Delta0Formula.satisfies_toFO,
    stackTokenLtBody, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_disj,
    Delta0Formula.satisfies_tripleEqAt, satisfies_pairMemAt,
    Model.subtypeVal_snoc]
  rw [stackTokenLtWitnessAssignment]
  rfl

/-- Exact token-order semantics with the two payload witnesses restricted to `L`. -/
theorem satisfies_stackTokenLtFormula_lCarrier_tokenCodes
    (U relation : ZFSet.{u}) (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : StackToken (Option (Constructible.ZFCarrier U))) :
    FOFormula.Satisfies LMem stackTokenLtFormula
        (stackTokenLtLAssignment U relation hU hrelation left right) ↔
      stackTokenRel (generatorTokenRel U relation) left right := by
  constructor
  · intro h
    rw [satisfies_stackTokenLtFormula_lCarrier_normal] at h
    rcases h with ⟨x, y, hbody⟩
    apply (satisfies_stackTokenLtFormula_tokenCodes U relation left right).mp
    apply (satisfies_stackTokenLtFormula
      (stackTokenLtAssignment U relation
        (stackTokenZFCode U left) (stackTokenZFCode U right))).mpr
    simpa [stackTokenLtLAssignment] using ⟨x.1, y.1, hbody⟩
  · intro h
    rw [satisfies_stackTokenLtFormula_lCarrier_normal]
    cases left with
    | inl leftGenerator =>
        let leftPayload : Model.LCarrier.{u} :=
          ⟨rudimentaryGenerator U leftGenerator,
            rudimentaryGenerator_mem_L hU leftGenerator⟩
        cases right with
        | inl rightGenerator =>
            let rightPayload : Model.LCarrier.{u} :=
              ⟨rudimentaryGenerator U rightGenerator,
                rudimentaryGenerator_mem_L hU rightGenerator⟩
            refine ⟨leftPayload, rightPayload, Or.inl ⟨rfl, rfl, ?_⟩⟩
            exact (generatorPayloadLt_iff U relation
              leftGenerator rightGenerator).mpr (by
                cases h with
                | inl hgenerator => exact hgenerator)
        | inr rightOperation =>
            let rightPayload : Model.LCarrier.{u} :=
              ⟨operationCode rightOperation,
                operationCode_mem_L rightOperation⟩
            exact ⟨leftPayload, rightPayload,
              Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | inr leftOperation =>
        let leftPayload : Model.LCarrier.{u} :=
          ⟨operationCode leftOperation,
            operationCode_mem_L leftOperation⟩
        cases right with
        | inl rightGenerator =>
            cases h
        | inr rightOperation =>
            let rightPayload : Model.LCarrier.{u} :=
              ⟨operationCode rightOperation,
                operationCode_mem_L rightOperation⟩
            refine ⟨leftPayload, rightPayload,
              Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩
            cases h with
            | inr hoperation =>
                exact (operationCode_mem_operationCode_iff
                  leftOperation rightOperation).mpr hoperation

/-! ## Program comparison over `LCarrier` -/

/--
The structural normal form of indexed-sequence shortlex when every unbounded
quantifier ranges over `LCarrier`.  No absoluteness claim is made about the
supplied token formula.
-/
theorem satisfies_shortlexFormula_lCarrier {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple Model.LCarrier.{u} parameterCount)
    (omega leftSequence rightSequence : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem (IndexedSequenceZF.shortlexFormula tokenLt)
        (snoc (snoc (snoc params omega) leftSequence) rightSequence) ↔
      FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
          ![omega, leftSequence] ∧
        FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
          ![omega, rightSequence] ∧
        ∃ leftLength rightLength : Model.LCarrier.{u},
          FOFormula.Satisfies LMem IndexedSequenceZF.hasLengthFormula
              ![leftSequence, leftLength] ∧
            FOFormula.Satisfies LMem IndexedSequenceZF.hasLengthFormula
              ![rightSequence, rightLength] ∧
            (leftLength.1 ∈ rightLength.1 ∨
              leftLength = rightLength ∧
                ∃ index : Model.LCarrier.{u}, index.1 ∈ leftLength.1 ∧
                  FOFormula.Satisfies LMem IndexedSequenceZF.samePrefixFormula
                      ![leftSequence, rightSequence, index] ∧
                    ∃ leftValue rightValue : Model.LCarrier.{u},
                      FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
                          ![leftSequence, index, leftValue] ∧
                        FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
                          ![rightSequence, index, rightValue] ∧
                        FOFormula.Satisfies LMem tokenLt
                          (snoc (snoc params leftValue) rightValue)) := by
  simp only [IndexedSequenceZF.shortlexFormula,
    IndexedSequenceZF.shortlexCore, FOFormula.Satisfies,
    FOFormula.satisfies_rename, FOFormula.satisfies_disj,
    FOFormula.satisfies_boundedEx,
    IndexedSequenceZF.comp_validityLeftRename,
    IndexedSequenceZF.comp_validityRightRename,
    IndexedSequenceZF.comp_leftLengthRename,
    IndexedSequenceZF.comp_rightLengthRename,
    IndexedSequenceZF.comp_prefixRename,
    IndexedSequenceZF.comp_leftValueRename,
    IndexedSequenceZF.comp_rightValueRename,
    IndexedSequenceZF.comp_tokenLtRename, snoc_last, snoc_castSucc]

/--
The relation on raw constructible codes induced by a formula whose witnesses
and quantifiers are interpreted in `LCarrier`.
-/
def lCarrierFormulaRel {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple Model.LCarrier.{u} parameterCount)
    (leftCode rightCode : ZFSet.{u}) : Prop :=
  ∃ leftValue rightValue : Model.LCarrier.{u},
    leftValue.1 = leftCode ∧ rightValue.1 = rightCode ∧
      FOFormula.Satisfies LMem tokenLt
        (snoc (snoc params leftValue) rightValue)

/--
On canonical indexed codes whose entries lie in `L`, restricted shortlex
satisfaction is exactly shortlex for the relation induced on their entries.
-/
theorem satisfies_shortlexFormula_sequenceCode_lCarrier_iff
    {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple Model.LCarrier.{u} parameterCount)
    (xs ys : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ L) (hys : ∀ y ∈ ys, y ∈ L) :
    FOFormula.Satisfies LMem (IndexedSequenceZF.shortlexFormula tokenLt)
        (snoc (snoc
          (snoc params ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
          ⟨IndexedSequenceZF.sequenceCode xs,
            IndexedSequenceZF.sequenceCode_mem_L hxs⟩)
          ⟨IndexedSequenceZF.sequenceCode ys,
            IndexedSequenceZF.sequenceCode_mem_L hys⟩) ↔
      List.Shortlex (lCarrierFormulaRel tokenLt params) xs ys := by
  rw [satisfies_shortlexFormula_lCarrier]
  have hvalidLeft :
      FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
        ![⟨Ordinal.omega0.toZFSet, omega_mem_L⟩,
          ⟨IndexedSequenceZF.sequenceCode xs,
            IndexedSequenceZF.sequenceCode_mem_L hxs⟩] :=
    satisfies_sequenceValidity_sequenceCode_lCarrier xs hxs
  have hvalidRight :
      FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
        ![⟨Ordinal.omega0.toZFSet, omega_mem_L⟩,
          ⟨IndexedSequenceZF.sequenceCode ys,
            IndexedSequenceZF.sequenceCode_mem_L hys⟩] :=
    satisfies_sequenceValidity_sequenceCode_lCarrier ys hys
  constructor
  · rintro ⟨_hvalidLeft, _hvalidRight, leftLength, rightLength,
      hleftLength, hrightLength, hshort⟩
    have hleftLengthEq :=
      (satisfies_hasLengthFormula_lCarrier_iff xs hxs leftLength).mp
        hleftLength
    have hrightLengthEq :=
      (satisfies_hasLengthFormula_lCarrier_iff ys hys rightLength).mp
        hrightLength
    rcases hshort with hlength | ⟨hlengthCarrier, index, hindex,
        hprefix, leftValue, rightValue, hleftValue, hrightValue, hlt⟩
    · apply List.Shortlex.of_length_lt
      apply (natCode_mem_natCode_iff xs.length ys.length).mp
      simpa only [hleftLengthEq, hrightLengthEq] using hlength
    · have hlengthCode : natCode xs.length = natCode ys.length :=
        hleftLengthEq.symm.trans
          ((congrArg Subtype.val hlengthCarrier).trans hrightLengthEq)
      have hlength : xs.length = ys.length := natCode_injective hlengthCode
      have hindexNat : index.1 ∈ natCode xs.length := by
        simpa only [hleftLengthEq] using hindex
      rcases (mem_natCode_iff index.1 xs.length).mp hindexNat with
        ⟨k, hk, hindexEq⟩
      let indexK : Model.LCarrier.{u} :=
        ⟨natCode k, natCode_mem_L k⟩
      have hindexCarrier : index = indexK := Subtype.ext hindexEq
      have hpoint :=
        (satisfies_samePrefix_sequenceCode_lCarrier_iff
          xs ys hxs hys k).mp
          (by simpa only [hindexCarrier, indexK] using hprefix)
      have hkRightLe : k ≤ ys.length := by
        rw [← hlength]
        exact hk.le
      have htake : xs.take k = ys.take k :=
        (IndexedSequenceZF.take_eq_take_iff_pointwise
          xs ys k hk.le hkRightLe).mpr hpoint
      rcases (satisfies_valueAtFormula_lCarrier_iff
          xs hxs k leftValue).mp
          (by simpa only [hindexCarrier, indexK] using hleftValue) with
        ⟨hkx, hleftValueEq⟩
      rcases (satisfies_valueAtFormula_lCarrier_iff
          ys hys k rightValue).mp
          (by simpa only [hindexCarrier, indexK] using hrightValue) with
        ⟨hky, hrightValueEq⟩
      have hrelation :
          lCarrierFormulaRel tokenLt params
            (xs.get ⟨k, hkx⟩) (ys.get ⟨k, hky⟩) :=
        ⟨leftValue, rightValue, hleftValueEq, hrightValueEq, hlt⟩
      apply List.Shortlex.of_lex hlength
      apply (listLex_iff_exists_index hlength).mpr
      exact ⟨k, hkx, hky, htake, hrelation⟩
  · intro hshortlex
    let leftLength : Model.LCarrier.{u} :=
      ⟨natCode xs.length, natCode_mem_L xs.length⟩
    let rightLength : Model.LCarrier.{u} :=
      ⟨natCode ys.length, natCode_mem_L ys.length⟩
    refine ⟨hvalidLeft, hvalidRight, leftLength, rightLength, ?_, ?_, ?_⟩
    · exact (satisfies_hasLengthFormula_lCarrier_iff
        xs hxs leftLength).mpr (by rfl)
    · exact (satisfies_hasLengthFormula_lCarrier_iff
        ys hys rightLength).mpr (by rfl)
    · rcases List.shortlex_def.mp hshortlex with
        hlength | ⟨hlength, hlex⟩
      · apply Or.inl
        simpa only [leftLength, rightLength] using
          ((natCode_mem_natCode_iff xs.length ys.length).mpr hlength)
      · apply Or.inr
        refine ⟨Subtype.ext (congrArg natCode hlength), ?_⟩
        rcases (listLex_iff_exists_index hlength).mp hlex with
          ⟨k, hkx, hky, htake, hrelation⟩
        rcases hrelation with
          ⟨leftValue, rightValue, hleftValueEq, hrightValueEq, hlt⟩
        let index : Model.LCarrier.{u} :=
          ⟨natCode k, natCode_mem_L k⟩
        refine ⟨index, ?_, ?_, leftValue, rightValue, ?_, ?_, hlt⟩
        · simpa only [index, leftLength] using
            ((natCode_mem_natCode_iff k xs.length).mpr hkx)
        · apply (satisfies_samePrefix_sequenceCode_lCarrier_iff
            xs ys hxs hys k).mpr
          exact (IndexedSequenceZF.take_eq_take_iff_pointwise
            xs ys k hkx.le hky.le).mp htake
        · exact (satisfies_valueAtFormula_lCarrier_iff
            xs hxs k leftValue).mpr ⟨hkx, hleftValueEq⟩
        · exact (satisfies_valueAtFormula_lCarrier_iff
            ys hys k rightValue).mpr ⟨hky, hrightValueEq⟩

/--
The program-order formula has its intended structural semantics when all
quantifiers are restricted to `L` and both programs are genuine codes.
-/
@[simp]
theorem satisfies_stackProgramLtFormula_lCarrier
    (U relation : ZFSet.{u}) (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    FOFormula.Satisfies LMem stackProgramLtFormula
        (stackProgramLtLAssignment U relation hU hrelation left right) ↔
      stackProgramRel (generatorTokenRel U relation) left right := by
  let params : Tuple Model.LCarrier.{u} 5 :=
    ![⟨U, hU⟩, ⟨relation, hrelation⟩,
      ⟨varTag, varTag_mem_L⟩, ⟨appTag, appTag_mem_L⟩,
      ⟨∅, empty_mem_L⟩]
  let xs : List ZFSet.{u} := left.map (stackTokenZFCode U)
  let ys : List ZFSet.{u} := right.map (stackTokenZFCode U)
  have hxs : ∀ code ∈ xs, code ∈ L := by
    simpa only [xs] using stackTokenCodes_mem_L hU left
  have hys : ∀ code ∈ ys, code ∈ L := by
    simpa only [ys] using stackTokenCodes_mem_L hU right
  have hshort :=
    satisfies_shortlexFormula_sequenceCode_lCarrier_iff
      stackTokenLtFormula params xs ys hxs hys
  have htoken : ∀ leftToken rightToken : StackToken
      (Option (Constructible.ZFCarrier U)),
      lCarrierFormulaRel stackTokenLtFormula params
          (stackTokenZFCode U leftToken)
          (stackTokenZFCode U rightToken) ↔
        stackTokenRel (generatorTokenRel U relation)
          leftToken rightToken := by
    intro leftToken rightToken
    constructor
    · rintro ⟨leftValue, rightValue,
        hleftValue, hrightValue, hlt⟩
      let leftCode : Model.LCarrier.{u} :=
        ⟨stackTokenZFCode U leftToken,
          stackTokenZFCode_mem_L hU leftToken⟩
      let rightCode : Model.LCarrier.{u} :=
        ⟨stackTokenZFCode U rightToken,
          stackTokenZFCode_mem_L hU rightToken⟩
      have hleftCarrier : leftValue = leftCode := Subtype.ext hleftValue
      have hrightCarrier : rightValue = rightCode := Subtype.ext hrightValue
      apply (satisfies_stackTokenLtFormula_lCarrier_tokenCodes
        U relation hU hrelation leftToken rightToken).mp
      rw [hleftCarrier, hrightCarrier] at hlt
      change FOFormula.Satisfies LMem stackTokenLtFormula
        (stackTokenLtLAssignment U relation hU hrelation leftToken rightToken) at hlt
      exact hlt
    · intro hlt
      let leftValue : Model.LCarrier.{u} :=
        ⟨stackTokenZFCode U leftToken,
          stackTokenZFCode_mem_L hU leftToken⟩
      let rightValue : Model.LCarrier.{u} :=
        ⟨stackTokenZFCode U rightToken,
          stackTokenZFCode_mem_L hU rightToken⟩
      refine ⟨leftValue, rightValue, rfl, rfl, ?_⟩
      have hrestricted :=
        (satisfies_stackTokenLtFormula_lCarrier_tokenCodes
          U relation hU hrelation leftToken rightToken).mpr hlt
      change FOFormula.Satisfies LMem stackTokenLtFormula
        (snoc (snoc params leftValue) rightValue) at hrestricted
      exact hrestricted
  have hmap :
      List.Shortlex (lCarrierFormulaRel stackTokenLtFormula params) xs ys ↔
        stackProgramRel (generatorTokenRel U relation) left right := by
    simpa only [xs, ys, stackProgramRel] using
      (listShortlex_map_iff (stackTokenZFCode U)
        (stackTokenZFCode_injective U) htoken left right)
  have hformula :
      FOFormula.Satisfies LMem stackProgramLtFormula
          (stackProgramLtLAssignment U relation hU hrelation left right) ↔
        List.Shortlex (lCarrierFormulaRel stackTokenLtFormula params)
          xs ys := by
    change FOFormula.Satisfies LMem stackProgramLtFormula
        (stackProgramLtLAssignment U relation hU hrelation left right) ↔
      List.Shortlex (lCarrierFormulaRel stackTokenLtFormula params) xs ys at hshort
    exact hshort
  exact hformula.trans hmap

/-- Raw-assignment presentation of restricted satisfaction in `L`. -/
@[simp]
theorem satisfiesIn_L_stackProgramLtFormula
    (U relation : ZFSet.{u}) (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    Model.SatisfiesIn L stackProgramLtFormula
        (stackProgramLtAssignment U relation left right) ↔
      stackProgramRel (generatorTokenRel U relation) left right := by
  rw [← stackProgramLtLAssignment_val U relation hU hrelation left right]
  rw [← Model.satisfies_lCarrier_iff_satisfiesIn_L
    stackProgramLtFormula
    (stackProgramLtLAssignment U relation hU hrelation left right)]
  exact satisfies_stackProgramLtFormula_lCarrier
    U relation hU hrelation left right

end

end Constructible.Godel.RudimentaryTerm
