/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Delta0Godel
public import Mathlib.SetTheory.ZFC.Constructible.FiniteSequenceZF
public import Mathlib.SetTheory.ZFC.Constructible.Model
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryCode
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryTermZFCode

/-!
# Bounded comparison formulas for finite-sequence codes

The von Neumann codes used for lengths are ordered by membership, so their
strict comparison has a fixed atomic formula.  We also package the
lexicographic comparison of an operation token's three numeric components.

The equal-length branch of shortlex for `FiniteSequenceZF.sequenceCode` is
handled by the indexed-sequence validity and lookup infrastructure developed
in the companion modules.  The formulas below provide the reusable numeric
and lexicographic components used by those constructions.
-/

@[expose] public section

universe u

namespace Constructible

namespace FiniteSequenceZF

/-! ## Natural-number codes -/

/--
Strict comparison of two von Neumann natural-number codes.

The assignment layout is `[left,right]`; membership is strict ordinal order.
-/
def natCodeLtDelta0 : Delta0Formula 2 :=
  .mem 0 1

/-- The same comparison in the unrestricted syntax used by model semantics. -/
def natCodeLtFormula : FOFormula 2 :=
  natCodeLtDelta0.toFO

@[simp]
theorem natCode_mem_natCode_iff (m n : Nat) :
    (natCode m : ZFSet.{u}) ∈ natCode n ↔ m < n := by
  change (m : Ordinal.{u}).toZFSet ∈ (n : Ordinal.{u}).toZFSet ↔ m < n
  rw [Ordinal.toZFSet_mem_toZFSet_iff]
  exact_mod_cast Iff.rfl

@[simp]
theorem satisfies_natCodeLtDelta0 (m n : Nat) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natCodeLtDelta0
        ![(natCode m : ZFSet.{u}), natCode n] ↔
      m < n := by
  simp [natCodeLtDelta0]

@[simp]
theorem satisfies_natCodeLtFormula (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem natCodeLtFormula
        ![(natCode m : ZFSet.{u}), natCode n] ↔
      m < n := by
  rw [natCodeLtFormula, Delta0Formula.satisfies_toFO,
    satisfies_natCodeLtDelta0]

/-- A natural-number code bundled as an element of the constructible carrier. -/
noncomputable def natCodeLCarrier (n : Nat) : Model.LCarrier.{u} :=
  ⟨natCode n, natCode_mem_L n⟩

@[simp]
theorem satisfies_natCodeLtFormula_lCarrier (m n : Nat) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        natCodeLtFormula ![natCodeLCarrier m, natCodeLCarrier n] ↔
      m < n := by
  change (natCode m : ZFSet.{u}) ∈ natCode n ↔ m < n
  exact natCode_mem_natCode_iff m n

end FiniteSequenceZF

namespace Godel.RudimentaryTerm

/-! ## Numeric operation-token payloads -/

/-- Operation indices, like sequence lengths, are finite ordinal codes. -/
@[simp]
theorem operationCode_mem_operationCode_iff (i j : Fin 9) :
    (operationCode i : ZFSet.{u}) ∈ operationCode j ↔ i < j := by
  change (i.1 : Ordinal.{u}).toZFSet ∈
      (j.1 : Ordinal.{u}).toZFSet ↔ i < j
  rw [Ordinal.toZFSet_mem_toZFSet_iff]
  exact_mod_cast Iff.rfl

@[simp]
theorem operationCode_inj_iff (i j : Fin 9) :
    (operationCode i : ZFSet.{u}) = operationCode j ↔ i = j :=
  operationCode_injective.eq_iff

/--
Lexicographic comparison of two operation-token numeric payloads.

The assignment layout is
`[op,leftLength,rightLength,op',leftLength',rightLength']`.
-/
def operationTupleLexDelta0 : Delta0Formula 6 :=
  .disj
    (.mem 0 3)
    (.conj
      (.eq 0 3)
      (.disj
        (.mem 1 4)
        (.conj (.eq 1 4) (.mem 2 5))))

/-- The operation-token payload comparison in unrestricted syntax. -/
def operationTupleLexFormula : FOFormula 6 :=
  operationTupleLexDelta0.toFO

@[simp]
theorem satisfies_operationTupleLexDelta0
    (i j : Fin 9) (left right left' right' : Nat) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem operationTupleLexDelta0
        ![(operationCode i : ZFSet.{u}),
          FiniteSequenceZF.natCode left,
          FiniteSequenceZF.natCode right,
          operationCode j,
          FiniteSequenceZF.natCode left',
          FiniteSequenceZF.natCode right'] ↔
      operationTokenRel (i, left, right) (j, left', right') := by
  simp [operationTupleLexDelta0, operationTokenRel, Prod.lex_def]

@[simp]
theorem satisfies_operationTupleLexFormula
    (i j : Fin 9) (left right left' right' : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem operationTupleLexFormula
        ![(operationCode i : ZFSet.{u}),
          FiniteSequenceZF.natCode left,
          FiniteSequenceZF.natCode right,
          operationCode j,
          FiniteSequenceZF.natCode left',
          FiniteSequenceZF.natCode right'] ↔
      operationTokenRel (i, left, right) (j, left', right') := by
  rw [operationTupleLexFormula, Delta0Formula.satisfies_toFO,
    satisfies_operationTupleLexDelta0]

end Godel.RudimentaryTerm

end Constructible
