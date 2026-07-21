/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.FiniteSequenceComparison
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramZFCode
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryTokenOrderFormula

/-!
# A first-order formula for the postfix stack-token order

The free-variable layout of `stackTokenLtFormula` is

`[U, r, varTag, appTag, empty, leftCode, rightCode]`.

Two unrestricted witnesses decode the payloads of the two token codes.  The
bounded body is the disjunction of the three possible strict-order branches:

* two variable tokens, ordered by `generatorTokenRel U r`;
* a variable token followed by an operation token;
* two operation tokens, ordered by membership of their finite ordinal codes.

There is deliberately no operation-variable branch.  On genuine
`stackTokenZFCode`s, the formula is exactly `stackTokenRel
(generatorTokenRel U r)`.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

/-! ## Formula -/

/--
The bounded body after decoding payloads `x` and `y`.  Its context is
`[U, r, varTag, appTag, empty, leftCode, rightCode, x, y]`.
-/
def stackTokenLtBody : Delta0Formula 9 :=
  .disj
    (.conj
      (Delta0Formula.tripleEqAt 5 2 7 4)
      (.conj
        (Delta0Formula.tripleEqAt 6 2 8 4)
        (.disj
          (.conj (.eq 7 0) (.mem 8 0))
          (.conj (.mem 7 0)
            (.conj (.mem 8 0) (pairMemAt 1 7 8))))))
    (.disj
      (.conj
        (Delta0Formula.tripleEqAt 5 2 7 4)
        (Delta0Formula.tripleEqAt 6 3 8 4))
      (.conj
        (Delta0Formula.tripleEqAt 5 3 7 4)
        (.conj
          (Delta0Formula.tripleEqAt 6 3 8 4)
          (.mem 7 8))))

/-- The complete strict-order formula for postfix stack-token codes. -/
def stackTokenLtFormula : FOFormula 7 :=
  .ex (.ex stackTokenLtBody.toFO)

/-- The intended assignment for comparing two internal stack-token codes. -/
def stackTokenLtAssignment (U r leftCode rightCode : ZFSet.{u}) :
    Tuple ZFSet.{u} 7 :=
  ![U, r, varTag, appTag, ∅, leftCode, rightCode]

@[simp]
theorem stackTokenLtWitnessAssignment {A : Type u}
    (s : Tuple A 7) (x y : A) :
    snoc (snoc s x) y =
      ![s 0, s 1, s 2, s 3, s 4, s 5, s 6, x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_stackTokenLtFormula (s : Tuple ZFSet.{u} 7) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackTokenLtFormula s <->
      exists x y : ZFSet.{u},
        ((s 5 = triple (s 2) x (s 4) /\
            s 6 = triple (s 2) y (s 4) /\
            ((x = s 0 /\ y ∈ s 0) \/
              (x ∈ s 0 /\ y ∈ s 0 /\ ZFSet.pair x y ∈ s 1))) \/
          (s 5 = triple (s 2) x (s 4) /\
            s 6 = triple (s 3) y (s 4)) \/
          (s 5 = triple (s 3) x (s 4) /\
            s 6 = triple (s 3) y (s 4) /\ x ∈ y)) := by
  simp only [stackTokenLtFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO, stackTokenLtBody,
    Delta0Formula.Satisfies, Delta0Formula.satisfies_disj,
    Delta0Formula.satisfies_tripleEqAt, satisfies_pairMemAt]
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  rw [stackTokenLtWitnessAssignment]
  rfl

/-! ## Exact semantics on genuine token codes -/

/-- The payload condition used by the variable-variable branch. -/
@[simp]
theorem generatorPayloadLt_iff
    (U r : ZFSet.{u})
    (left right : Option (Constructible.ZFCarrier U)) :
    ((rudimentaryGenerator U left = U /\
        rudimentaryGenerator U right ∈ U) \/
      (rudimentaryGenerator U left ∈ U /\
        rudimentaryGenerator U right ∈ U /\
        ZFSet.pair (rudimentaryGenerator U left)
          (rudimentaryGenerator U right) ∈ r)) <->
      generatorTokenRel U r left right := by
  cases left with
  | none =>
      cases right with
      | none =>
          simp [rudimentaryGenerator, generatorTokenRel,
            ZFSet.mem_irrefl]
      | some y =>
          simp [rudimentaryGenerator, generatorTokenRel,
            y.2, ZFSet.mem_irrefl]
  | some x =>
      have hxne : x.1 ≠ U := carrier_value_ne_universe x
      cases right with
      | none =>
          simp [rudimentaryGenerator, generatorTokenRel,
            x.2, hxne, ZFSet.mem_irrefl]
      | some y =>
          simp [rudimentaryGenerator, generatorTokenRel,
            generatorPairRel, x.2, y.2, hxne]

/--
The internal formula agrees exactly with the external structural order on
all genuine postfix stack-token codes.
-/
theorem satisfies_stackTokenLtFormula_tokenCodes
    (U r : ZFSet.{u})
    (left right : StackToken (Option (Constructible.ZFCarrier U))) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackTokenLtFormula
        (stackTokenLtAssignment U r
          (stackTokenZFCode U left) (stackTokenZFCode U right)) <->
      stackTokenRel (generatorTokenRel U r) left right := by
  rw [satisfies_stackTokenLtFormula]
  have hempty_ne_appTag : (∅ : ZFSet.{u}) ≠ appTag := by
    intro h
    apply (varTag_ne_appTag : (varTag : ZFSet.{u}) ≠ appTag)
    rw [varTag_eq_empty]
    exact h
  have happTag_ne_empty : (appTag : ZFSet.{u}) ≠ ∅ :=
    Ne.symm hempty_ne_appTag
  cases left with
  | inl leftGenerator =>
      cases right with
      | inl rightGenerator =>
          simp [stackTokenLtAssignment, stackTokenZFCode,
            stackTokenRel, triple, ZFSet.pair_inj,
            hempty_ne_appTag]
      | inr rightOperation =>
          simp [stackTokenLtAssignment, stackTokenZFCode,
            stackTokenRel, triple, ZFSet.pair_inj,
            hempty_ne_appTag, happTag_ne_empty]
  | inr leftOperation =>
      cases right with
      | inl rightGenerator =>
          simp [stackTokenLtAssignment, stackTokenZFCode,
            stackTokenRel, triple, ZFSet.pair_inj,
            hempty_ne_appTag, happTag_ne_empty]
      | inr rightOperation =>
          simp [stackTokenLtAssignment, stackTokenZFCode,
            stackTokenRel, triple, ZFSet.pair_inj,
            happTag_ne_empty]

end

end Constructible.Godel.RudimentaryTerm
