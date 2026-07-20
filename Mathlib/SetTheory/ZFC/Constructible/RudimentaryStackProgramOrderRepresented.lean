/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderAbsolute
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackTraceDecode

/-!
# Program order on arbitrary valid indexed representations

The first-order order formula compares the finite sequence represented by a
code.  It must therefore be insensitive to harmless extra graph entries in a
valid code, rather than being correct only for `sequenceCode` itself.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open IndexedSequenceZF
open FiniteSequenceZF

local notation "LMem" => Model.lCarrierMem

/-- The fixed program-order layout with arbitrary sequence codes. -/
def stackProgramLtCodeAssignment (U relation leftCode rightCode : ZFSet.{u}) :
    Tuple ZFSet.{u} 8 :=
  ![U, relation, varTag, appTag, ∅, Ordinal.omega0.toZFSet,
    leftCode, rightCode]

/-- Ambient Shortlex semantics is independent of the representing graphs. -/
@[simp]
theorem satisfies_stackProgramLtFormula_represents_iff
    (U relation leftCode rightCode : ZFSet.{u})
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (hleft : Represents leftCode (encodedStackProgram U left))
    (hright : Represents rightCode (encodedStackProgram U right)) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramLtFormula
        (stackProgramLtCodeAssignment U relation leftCode rightCode) ↔
      stackProgramRel (generatorTokenRel U relation) left right := by
  let params : Tuple ZFSet.{u} 5 :=
    ![U, relation, varTag, appTag, ∅]
  let rawTokenRel : ZFSet.{u} → ZFSet.{u} → Prop := fun x y =>
    FOFormula.Satisfies Delta0Formula.ZFMem stackTokenLtFormula
      (snoc (snoc params x) y)
  have hshort := satisfies_shortlexFormula_represents_iff
    stackTokenLtFormula params rawTokenRel hleft hright
      (fun _ _ => Iff.rfl)
  have htoken : ∀ x y : StackToken
      (Option (Constructible.ZFCarrier U)),
      rawTokenRel (stackTokenZFCode U x) (stackTokenZFCode U y) ↔
        stackTokenRel (generatorTokenRel U relation) x y := by
    intro x y
    have htokenCode :=
      satisfies_stackTokenLtFormula_tokenCodes U relation x y
    change FOFormula.Satisfies Delta0Formula.ZFMem stackTokenLtFormula
        (snoc (snoc params (stackTokenZFCode U x)) (stackTokenZFCode U y)) ↔
      stackTokenRel (generatorTokenRel U relation) x y at htokenCode
    exact htokenCode
  have hmap := listShortlex_map_iff (stackTokenZFCode U)
    (stackTokenZFCode_injective U) htoken left right
  have hformula :
      FOFormula.Satisfies Delta0Formula.ZFMem stackProgramLtFormula
          (stackProgramLtCodeAssignment U relation leftCode rightCode) ↔
        List.Shortlex rawTokenRel
          (encodedStackProgram U left) (encodedStackProgram U right) := by
    change FOFormula.Satisfies Delta0Formula.ZFMem stackProgramLtFormula
        (stackProgramLtCodeAssignment U relation leftCode rightCode) ↔
      List.Shortlex rawTokenRel
        (encodedStackProgram U left) (encodedStackProgram U right) at hshort
    exact hshort
  exact hformula.trans hmap

/-! ## Constructible witnesses for represented sequences -/

private theorem pairRight_mem_L_of_pair_eq
    {sequence length graph : ZFSet.{u}} (hsequence : sequence ∈ L)
    (hcode : sequence = ZFSet.pair length graph) : graph ∈ L := by
  have hpairMem :
      ZFSet.pair length graph ∈ ({sequence} : ZFSet.{u}) := by
    simp only [ZFSet.mem_singleton]
    exact hcode.symm
  exact mem_L_of_mem (pair_right_mem_pairField hpairMem)
    (pairField_mem_L (singleton_mem_L hsequence))

/-- The graph component of a constructible represented code is constructible. -/
theorem representedGraph_mem_L
    {sequence : ZFSet.{u}} (hsequence : sequence ∈ L)
    {xs : List ZFSet.{u}} (hrep : Represents sequence xs) :
    ∃ graph : ZFSet.{u},
      sequence = ZFSet.pair (natCode xs.length) graph ∧
        (∀ k : Fin xs.length,
          ZFSet.pair (xs.get k) (natCode k.1) ∈ graph ∧
            ∀ value : ZFSet.{u},
              ZFSet.pair value (natCode k.1) ∈ graph →
                value = xs.get k) ∧
        graph ∈ L := by
  rcases hrep with ⟨graph, hcode, hgraph⟩
  exact ⟨graph, hcode, hgraph,
    pairRight_mem_L_of_pair_eq hsequence hcode⟩

private theorem representedLength_eq
    {sequence length graph : ZFSet.{u}} {xs : List ZFSet.{u}}
    (hrep : Represents sequence xs)
    (hpair : sequence = ZFSet.pair length graph) :
    length = natCode xs.length := by
  rcases hrep with ⟨representedGraph, hcode, _hgraph⟩
  have hpairs :
      ZFSet.pair (natCode xs.length) representedGraph =
        ZFSet.pair length graph := hcode.symm.trans hpair
  exact (ZFSet.pair_inj.mp hpairs).1.symm

/-- Any constructible representation with constructible entries is valid in `L`. -/
theorem satisfies_sequenceValidity_represents_lCarrier
    (sequence : Model.LCarrier.{u}) {xs : List ZFSet.{u}}
    (hrep : Represents sequence.1 xs) (hxs : ∀ x ∈ xs, x ∈ L) :
    FOFormula.Satisfies LMem sequenceValidityFormula
      ![⟨Ordinal.omega0.toZFSet, omega_mem_L⟩, sequence] := by
  rw [satisfies_sequenceValidityFormula_lCarrier]
  rcases representedGraph_mem_L sequence.2 hrep with
    ⟨graph, hcode, hgraph, hgraphL⟩
  let length : Model.LCarrier.{u} :=
    ⟨natCode xs.length, natCode_mem_L xs.length⟩
  let graphCarrier : Model.LCarrier.{u} := ⟨graph, hgraphL⟩
  refine ⟨length, graphCarrier, hcode, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 xs.length)
  · intro index hindex
    rcases (mem_natCode_iff index.1 xs.length).mp hindex with
      ⟨k, hk, hindexEq⟩
    let i : Fin xs.length := ⟨k, hk⟩
    have hvalueL : xs.get i ∈ L := hxs _ (List.get_mem xs i)
    let value : Model.LCarrier.{u} := ⟨xs.get i, hvalueL⟩
    refine ⟨value, ?_, ?_⟩
    · simpa only [i, hindexEq, value, graphCarrier] using (hgraph i).1
    · intro other hother
      have hunique := (hgraph i).2 other.1
        (by simpa only [i, hindexEq, graphCarrier] using hother)
      simpa only [value] using hunique

set_option maxHeartbeats 250000 in
-- Kernel checking of the three-coordinate subtype assignment needs a small
-- margin above the default budget; the proof itself is finite-case.
@[simp]
theorem satisfies_valueAtFormula_represents_lCarrier_iff
    (sequence : Model.LCarrier.{u}) {xs : List ZFSet.{u}}
    (hrep : Represents sequence.1 xs) (k : Nat)
    (value : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem valueAtFormula
        ![sequence, ⟨natCode k, natCode_mem_L k⟩, value] ↔
      ∃ hk : k < xs.length, value.1 = xs.get ⟨k, hk⟩ := by
  rw [valueAtFormula, Delta0Formula.satisfies_toFO_lCarrier_absolute]
  have hvals :
      (fun i =>
        (![sequence, ⟨natCode k, natCode_mem_L k⟩, value] i).1) =
        ![sequence.1, natCode k, value.1] := by
    funext i
    fin_cases i <;> rfl
  rw [hvals, Delta0Formula.satisfies_toFO]
  exact satisfies_valueAt_represents_iff hrep k value.1

private theorem satisfies_hasLengthFormula_represents_lCarrier_sound
    (sequence : Model.LCarrier.{u}) {xs : List ZFSet.{u}}
    (hrep : Represents sequence.1 xs)
    (length : Model.LCarrier.{u})
    (h : FOFormula.Satisfies LMem hasLengthFormula ![sequence, length]) :
    length.1 = natCode xs.length := by
  simp only [hasLengthFormula, FOFormula.Satisfies] at h
  rcases h with ⟨graphCarrier, hpair⟩
  have hpairRaw :=
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.kuratowskiPairEqAt 0 1 2)
      (snoc ![sequence, length] graphCarrier)).mp hpair
  rw [Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt] at hpairRaw
  have hpairRaw' :
      sequence.1 = ZFSet.pair length.1 graphCarrier.1 := by
    change sequence.1 = ZFSet.pair length.1 graphCarrier.1 at hpairRaw
    exact hpairRaw
  exact representedLength_eq hrep hpairRaw'

private theorem representedLengthGraphCarrier
    (sequence : Model.LCarrier.{u}) {xs : List ZFSet.{u}}
    (hrep : Represents sequence.1 xs)
    (length : Model.LCarrier.{u})
    (hlength : length.1 = natCode xs.length) :
    ∃ graphCarrier : Model.LCarrier.{u},
      sequence.1 = ZFSet.pair length.1 graphCarrier.1 := by
  rcases hrep with ⟨graph, hcode, _hgraph⟩
  have hgraphL : graph ∈ L :=
    pairRight_mem_L_of_pair_eq sequence.2 hcode
  let graphCarrier : Model.LCarrier.{u} := ⟨graph, hgraphL⟩
  refine ⟨graphCarrier, ?_⟩
  simpa only [graphCarrier, hlength] using hcode

@[simp]
theorem satisfies_hasLengthFormula_represents_lCarrier_iff
    (sequence : Model.LCarrier.{u}) {xs : List ZFSet.{u}}
    (hrep : Represents sequence.1 xs)
    (length : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem hasLengthFormula ![sequence, length] ↔
      length.1 = natCode xs.length := by
  constructor
  · exact satisfies_hasLengthFormula_represents_lCarrier_sound
      sequence hrep length
  · intro hlength
    rcases representedLengthGraphCarrier sequence hrep length hlength with
      ⟨graphCarrier, hpair⟩
    simp only [hasLengthFormula, FOFormula.Satisfies]
    refine ⟨graphCarrier, ?_⟩
    apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.kuratowskiPairEqAt 0 1 2)
      (snoc ![sequence, length] graphCarrier)).mpr
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_kuratowskiPairEqAt]
    change sequence.1 = ZFSet.pair length.1 graphCarrier.1
    exact hpair

@[simp]
theorem satisfies_samePrefix_represents_lCarrier_iff
    (leftSequence rightSequence : Model.LCarrier.{u})
    {xs ys : List ZFSet.{u}}
    (hleft : Represents leftSequence.1 xs)
    (hright : Represents rightSequence.1 ys)
    (hxs : ∀ x ∈ xs, x ∈ L) (_hys : ∀ y ∈ ys, y ∈ L)
    (k : Nat) :
    FOFormula.Satisfies LMem samePrefixFormula
        ![leftSequence, rightSequence,
          ⟨natCode k, natCode_mem_L k⟩] ↔
      ∀ j : Nat, j < k →
        ∃ hx : j < xs.length, ∃ hy : j < ys.length,
          xs.get ⟨j, hx⟩ = ys.get ⟨j, hy⟩ := by
  constructor
  · intro h
    have hnormal :=
      (satisfies_samePrefixFormula_lCarrier leftSequence rightSequence
        ⟨natCode k, natCode_mem_L k⟩).mp h
    intro j hj
    let index : Model.LCarrier.{u} := ⟨natCode j, natCode_mem_L j⟩
    rcases hnormal index ((mem_natCode_iff _ _).mpr ⟨j, hj, rfl⟩) with
      ⟨value, hleftValue, hrightValue⟩
    rcases (satisfies_valueAtFormula_represents_lCarrier_iff
      leftSequence hleft j value).mp
        (by simpa only [index] using hleftValue) with
      ⟨hx, hvalueX⟩
    rcases (satisfies_valueAtFormula_represents_lCarrier_iff
      rightSequence hright j value).mp
        (by simpa only [index] using hrightValue) with
      ⟨hy, hvalueY⟩
    exact ⟨hx, hy, hvalueX.symm.trans hvalueY⟩
  · intro h
    apply (satisfies_samePrefixFormula_lCarrier leftSequence rightSequence
      ⟨natCode k, natCode_mem_L k⟩).mpr
    intro index hindex
    rcases (mem_natCode_iff index.1 k).mp hindex with
      ⟨j, hj, hindexEq⟩
    rcases h j hj with ⟨hx, hy, hxy⟩
    let indexJ : Model.LCarrier.{u} := ⟨natCode j, natCode_mem_L j⟩
    have hindexCarrier : index = indexJ := Subtype.ext hindexEq
    have hvalueL : xs.get ⟨j, hx⟩ ∈ L :=
      hxs _ (List.get_mem xs ⟨j, hx⟩)
    let value : Model.LCarrier.{u} := ⟨xs.get ⟨j, hx⟩, hvalueL⟩
    refine ⟨value, ?_, ?_⟩
    · have hvalue :=
        (satisfies_valueAtFormula_represents_lCarrier_iff
          leftSequence hleft j value).mpr ⟨hx, rfl⟩
      simpa only [hindexCarrier, indexJ] using hvalue
    · have hvalue :=
        (satisfies_valueAtFormula_represents_lCarrier_iff
          rightSequence hright j value).mpr ⟨hy, hxy⟩
      simpa only [hindexCarrier, indexJ, value] using hvalue

/-! ## Restricted Shortlex on arbitrary representations -/

/-- Arbitrary constructible program-code assignments over `LCarrier`. -/
def stackProgramLtCodeLAssignment
    (U relation leftCode rightCode : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (hleftCode : leftCode ∈ L) (hrightCode : rightCode ∈ L) :
    Tuple Model.LCarrier.{u} 8 :=
  ![⟨U, hU⟩, ⟨relation, hrelation⟩,
    ⟨varTag, varTag_mem_L⟩, ⟨appTag, appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩, ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩,
    ⟨leftCode, hleftCode⟩, ⟨rightCode, hrightCode⟩]

theorem stackProgramLtCodeLAssignment_val
    (U relation leftCode rightCode : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (hleftCode : leftCode ∈ L) (hrightCode : rightCode ∈ L) :
    (fun i => (stackProgramLtCodeLAssignment U relation leftCode rightCode
      hU hrelation hleftCode hrightCode i).1) =
      stackProgramLtCodeAssignment U relation leftCode rightCode := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_stackProgramLtFormula_represents_lCarrier_iff
    (U relation leftCode rightCode : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (hleftCode : leftCode ∈ L) (hrightCode : rightCode ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (hleft : Represents leftCode (encodedStackProgram U left))
    (hright : Represents rightCode (encodedStackProgram U right)) :
    FOFormula.Satisfies LMem stackProgramLtFormula
        (stackProgramLtCodeLAssignment U relation leftCode rightCode
          hU hrelation hleftCode hrightCode) ↔
      stackProgramRel (generatorTokenRel U relation) left right := by
  let params : Tuple Model.LCarrier.{u} 5 :=
    ![⟨U, hU⟩, ⟨relation, hrelation⟩,
      ⟨varTag, varTag_mem_L⟩, ⟨appTag, appTag_mem_L⟩,
      ⟨∅, empty_mem_L⟩]
  let xs := encodedStackProgram U left
  let ys := encodedStackProgram U right
  have hxs : ∀ x ∈ xs, x ∈ L := by
    simpa only [xs, encodedStackProgram] using stackTokenCodes_mem_L hU left
  have hys : ∀ y ∈ ys, y ∈ L := by
    simpa only [ys, encodedStackProgram] using stackTokenCodes_mem_L hU right
  let leftCarrier : Model.LCarrier.{u} := ⟨leftCode, hleftCode⟩
  let rightCarrier : Model.LCarrier.{u} := ⟨rightCode, hrightCode⟩
  have hassignment :
      stackProgramLtCodeLAssignment U relation leftCode rightCode
          hU hrelation hleftCode hrightCode =
        snoc (snoc
          (snoc params ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
          leftCarrier) rightCarrier := by
    funext i
    fin_cases i <;> rfl
  rw [stackProgramLtFormula]
  rw [hassignment]
  rw [satisfies_shortlexFormula_lCarrier]
  have hvalidLeft := satisfies_sequenceValidity_represents_lCarrier
    leftCarrier hleft hxs
  have hvalidRight := satisfies_sequenceValidity_represents_lCarrier
    rightCarrier hright hys
  constructor
  · rintro ⟨_hvl, _hvr, leftLength, rightLength,
      hleftLength, hrightLength, hshort⟩
    have hleftLengthEq :=
      (satisfies_hasLengthFormula_represents_lCarrier_iff
        leftCarrier hleft leftLength).mp
        (by simpa only [params, leftCarrier, rightCarrier,
          stackProgramLtCodeLAssignment] using hleftLength)
    have hrightLengthEq :=
      (satisfies_hasLengthFormula_represents_lCarrier_iff
        rightCarrier hright rightLength).mp
        (by simpa only [params, leftCarrier, rightCarrier,
          stackProgramLtCodeLAssignment] using hrightLength)
    have hshortlex : List.Shortlex
        (lCarrierFormulaRel stackTokenLtFormula params) xs ys := by
      rcases hshort with hlen | ⟨hlengthCarrier, index, hindex,
          hprefix, leftValue, rightValue, hleftValue,
          hrightValue, hlt⟩
      · apply List.Shortlex.of_length_lt
        apply (natCode_mem_natCode_iff xs.length ys.length).mp
        simpa only [hleftLengthEq, hrightLengthEq] using hlen
      · have hlengthCode : natCode xs.length = natCode ys.length :=
          hleftLengthEq.symm.trans
            ((congrArg Subtype.val hlengthCarrier).trans hrightLengthEq)
        have hlength : xs.length = ys.length := natCode_injective hlengthCode
        rcases (mem_natCode_iff index.1 xs.length).mp
            (by simpa only [hleftLengthEq] using hindex) with
          ⟨k, hk, hindexEq⟩
        let indexK : Model.LCarrier.{u} := ⟨natCode k, natCode_mem_L k⟩
        have hindexCarrier : index = indexK := Subtype.ext hindexEq
        have hpoint :=
          (satisfies_samePrefix_represents_lCarrier_iff
            leftCarrier rightCarrier hleft hright hxs hys k).mp
            (by simpa only [params, leftCarrier, rightCarrier,
              hindexCarrier, indexK, stackProgramLtCodeLAssignment]
              using hprefix)
        have htake : xs.take k = ys.take k :=
          (take_eq_take_iff_pointwise xs ys k hk.le
            (by rw [← hlength]; exact hk.le)).mpr hpoint
        rcases (satisfies_valueAtFormula_represents_lCarrier_iff
          leftCarrier hleft k leftValue).mp
            (by simpa only [params, leftCarrier, rightCarrier,
              hindexCarrier, indexK, stackProgramLtCodeLAssignment]
              using hleftValue) with
          ⟨hkx, hleftValueEq⟩
        rcases (satisfies_valueAtFormula_represents_lCarrier_iff
          rightCarrier hright k rightValue).mp
            (by simpa only [params, leftCarrier, rightCarrier,
              hindexCarrier, indexK, stackProgramLtCodeLAssignment]
              using hrightValue) with
          ⟨hky, hrightValueEq⟩
        apply List.Shortlex.of_lex hlength
        apply (listLex_iff_exists_index hlength).mpr
        exact ⟨k, hkx, hky, htake,
          ⟨leftValue, rightValue, hleftValueEq, hrightValueEq,
            by simpa only [params, stackProgramLtCodeLAssignment]
              using hlt⟩⟩
    have htoken : ∀ leftToken rightToken : StackToken
        (Option (Constructible.ZFCarrier U)),
        lCarrierFormulaRel stackTokenLtFormula params
            (stackTokenZFCode U leftToken) (stackTokenZFCode U rightToken) ↔
          stackTokenRel (generatorTokenRel U relation)
            leftToken rightToken := by
      intro leftToken rightToken
      constructor
      · rintro ⟨leftValue, rightValue, hl, hr, hlt⟩
        have hrestricted :=
          (satisfies_stackTokenLtFormula_lCarrier_tokenCodes
            U relation hU hrelation leftToken rightToken).mp
            (by
              have hlc : leftValue =
                  ⟨stackTokenZFCode U leftToken,
                    stackTokenZFCode_mem_L hU leftToken⟩ := Subtype.ext hl
              have hrc : rightValue =
                  ⟨stackTokenZFCode U rightToken,
                    stackTokenZFCode_mem_L hU rightToken⟩ := Subtype.ext hr
              rw [hlc, hrc] at hlt
              change FOFormula.Satisfies LMem stackTokenLtFormula
                (stackTokenLtLAssignment U relation hU hrelation
                  leftToken rightToken) at hlt
              exact hlt)
        exact hrestricted
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
    simpa only [xs, ys, stackProgramRel] using
      (listShortlex_map_iff (stackTokenZFCode U)
        (stackTokenZFCode_injective U) htoken left right).mp hshortlex
  · intro hprogramLt
    have htoken : ∀ leftToken rightToken : StackToken
        (Option (Constructible.ZFCarrier U)),
        lCarrierFormulaRel stackTokenLtFormula params
            (stackTokenZFCode U leftToken) (stackTokenZFCode U rightToken) ↔
          stackTokenRel (generatorTokenRel U relation)
            leftToken rightToken := by
      intro leftToken rightToken
      constructor
      · rintro ⟨leftValue, rightValue, hl, hr, hlt⟩
        apply (satisfies_stackTokenLtFormula_lCarrier_tokenCodes
          U relation hU hrelation leftToken rightToken).mp
        have hlc : leftValue =
            ⟨stackTokenZFCode U leftToken,
              stackTokenZFCode_mem_L hU leftToken⟩ := Subtype.ext hl
        have hrc : rightValue =
            ⟨stackTokenZFCode U rightToken,
              stackTokenZFCode_mem_L hU rightToken⟩ := Subtype.ext hr
        rw [hlc, hrc] at hlt
        change FOFormula.Satisfies LMem stackTokenLtFormula
          (stackTokenLtLAssignment U relation hU hrelation
            leftToken rightToken) at hlt
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
    have hshortlex :
        List.Shortlex (lCarrierFormulaRel stackTokenLtFormula params) xs ys := by
      apply (listShortlex_map_iff (stackTokenZFCode U)
        (stackTokenZFCode_injective U) htoken left right).mpr
      exact hprogramLt
    refine ⟨?_, ?_,
      ⟨natCode xs.length, natCode_mem_L xs.length⟩,
      ⟨natCode ys.length, natCode_mem_L ys.length⟩, ?_, ?_, ?_⟩
    · simpa only [params, leftCarrier, stackProgramLtCodeLAssignment] using
        hvalidLeft
    · simpa only [params, rightCarrier, stackProgramLtCodeLAssignment] using
        hvalidRight
    · have hlen :=
        (satisfies_hasLengthFormula_represents_lCarrier_iff
          leftCarrier hleft
          ⟨natCode xs.length, natCode_mem_L xs.length⟩).mpr rfl
      simpa only [params, leftCarrier, rightCarrier,
        stackProgramLtCodeLAssignment] using hlen
    · have hlen :=
        (satisfies_hasLengthFormula_represents_lCarrier_iff
          rightCarrier hright
          ⟨natCode ys.length, natCode_mem_L ys.length⟩).mpr rfl
      simpa only [params, leftCarrier, rightCarrier,
        stackProgramLtCodeLAssignment] using hlen
    · rcases List.shortlex_def.mp hshortlex with hlen | ⟨hlen, hlex⟩
      · apply Or.inl
        exact (natCode_mem_natCode_iff xs.length ys.length).mpr hlen
      · apply Or.inr
        refine ⟨Subtype.ext (congrArg natCode hlen), ?_⟩
        rcases (listLex_iff_exists_index hlen).mp hlex with
          ⟨k, hkx, hky, htake, hrelationAt⟩
        rcases hrelationAt with
          ⟨leftValue, rightValue, hleftValueEq, hrightValueEq, hlt⟩
        let index : Model.LCarrier.{u} := ⟨natCode k, natCode_mem_L k⟩
        refine ⟨index, (mem_natCode_iff _ _).mpr ⟨k, hkx, rfl⟩,
          ?_, leftValue, rightValue, ?_, ?_, ?_⟩
        · have hprefix :=
            (satisfies_samePrefix_represents_lCarrier_iff
              leftCarrier rightCarrier hleft hright hxs hys k).mpr
              ((take_eq_take_iff_pointwise xs ys k hkx.le hky.le).mp htake)
          simpa only [params, leftCarrier, rightCarrier, index,
            stackProgramLtCodeLAssignment] using hprefix
        · have hvalue :=
            (satisfies_valueAtFormula_represents_lCarrier_iff
              leftCarrier hleft k leftValue).mpr
              ⟨hkx, hleftValueEq⟩
          simpa only [params, leftCarrier, rightCarrier, index,
            stackProgramLtCodeLAssignment] using hvalue
        · have hvalue :=
            (satisfies_valueAtFormula_represents_lCarrier_iff
              rightCarrier hright k rightValue).mpr
              ⟨hky, hrightValueEq⟩
          simpa only [params, leftCarrier, rightCarrier, index,
            stackProgramLtCodeLAssignment] using hvalue
        · simpa only [params, stackProgramLtCodeLAssignment] using hlt

/-- Raw-domain presentation of represented-code program comparison in `L`. -/
@[simp]
theorem satisfiesIn_L_stackProgramLtFormula_represents_iff
    (U relation leftCode rightCode : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (hleftCode : leftCode ∈ L) (hrightCode : rightCode ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (hleft : Represents leftCode (encodedStackProgram U left))
    (hright : Represents rightCode (encodedStackProgram U right)) :
    Model.SatisfiesIn L stackProgramLtFormula
        (stackProgramLtCodeAssignment U relation leftCode rightCode) ↔
      stackProgramRel (generatorTokenRel U relation) left right := by
  rw [← stackProgramLtCodeLAssignment_val U relation leftCode rightCode
    hU hrelation hleftCode hrightCode]
  rw [← Model.satisfies_lCarrier_iff_satisfiesIn_L
    stackProgramLtFormula
    (stackProgramLtCodeLAssignment U relation leftCode rightCode
      hU hrelation hleftCode hrightCode)]
  exact satisfies_stackProgramLtFormula_represents_lCarrier_iff
    U relation leftCode rightCode hU hrelation hleftCode hrightCode
      left right hleft hright

end

end Constructible.Godel.RudimentaryTerm
