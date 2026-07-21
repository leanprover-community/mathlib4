/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Delta0Godel
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryPrefixZFCode

/-!
# A formula for the generator-token order

This file internalizes the variable-token branch of
`RudimentaryTerm.codeTokenRel`, where the distinguished generator `U` comes
first and ordinary generators are compared by membership of their Kuratowski
pair in an internal relation graph `r`.

The free-variable layout of `generatorTokenLtFormula` is

`[U, r, zeroTag, leftCode, rightCode]`.

The formula uses two unrestricted witnesses for the decoded generator
payloads.  All structural checks on those witnesses are bounded formulas.
For actual variable tokens, `zeroTag` is instantiated by the empty set, which
is both `varTag` and the third component of the token code.

`RudimentaryStackTokenOrderFormula` combines this branch with operation-token
and mixed-token comparisons to obtain the full token order.
-/

@[expose] public section

universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section

/-- The raw relation represented by a Kuratowski-pair graph. -/
def generatorPairRel {U : ZFSet.{u}} (r : ZFSet.{u})
    (x y : Constructible.ZFCarrier U) : Prop :=
  ZFSet.pair x.1 y.1 ∈ r

/--
The generator order used by prefix tokens: `none`, representing `U`, is
strictly before every `some x`; ordinary generators use the graph `r`.
-/
def generatorTokenRel (U r : ZFSet.{u}) :
    Option (Constructible.ZFCarrier U) ->
      Option (Constructible.ZFCarrier U) -> Prop
  | none, none => False
  | none, some _ => True
  | some _, none => False
  | some x, some y => generatorPairRel r x y

/-- With assignment `[r,x,y]`, assert that `pair x y` belongs to `r`. -/
def pairMemAt {n : Nat} (relation x y : Fin n) : Delta0Formula n :=
  .boundedEx relation
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) x.castSucc y.castSucc)

@[simp]
theorem satisfies_pairMemAt {n : Nat} (relation x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (pairMemAt relation x y) s <->
      ZFSet.pair (s x) (s y) ∈ s relation := by
  simp only [pairMemAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, hpair⟩
    simpa only [hpair] using hq
  · intro hpair
    exact ⟨ZFSet.pair (s x) (s y), hpair, rfl⟩

/--
The bounded body after decoding payloads `x` and `y`.  Its context is
`[U, r, zeroTag, leftCode, rightCode, x, y]`.
-/
def generatorTokenLtBody : Delta0Formula 7 :=
  .conj
    (Delta0Formula.tripleEqAt 3 2 5 2)
    (.conj
      (Delta0Formula.tripleEqAt 4 2 6 2)
      (.disj
        (.conj (.eq 5 0) (.mem 6 0))
        (.conj (.mem 5 0)
          (.conj (.mem 6 0) (pairMemAt 1 5 6)))))

/--
The variable-token strict-order formula in context
`[U, r, zeroTag, leftCode, rightCode]`.
-/
def generatorTokenLtFormula : FOFormula 5 :=
  .ex (.ex generatorTokenLtBody.toFO)

/-- The two decoded witnesses occupy coordinates five and six. -/
@[simp]
theorem generatorTokenWitnessAssignment {A : Type u}
    (s : Tuple A 5) (x y : A) :
    snoc (snoc s x) y = ![s 0, s 1, s 2, s 3, s 4, x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_generatorTokenLtFormula (s : Tuple ZFSet.{u} 5) :
    FOFormula.Satisfies Delta0Formula.ZFMem generatorTokenLtFormula s <->
      exists x y : ZFSet.{u},
        s 3 = triple (s 2) x (s 2) /\
        s 4 = triple (s 2) y (s 2) /\
          ((x = s 0 /\ y ∈ s 0) \/
            (x ∈ s 0 /\ y ∈ s 0 /\ ZFSet.pair x y ∈ s 1)) := by
  simp only [generatorTokenLtFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO, generatorTokenLtBody,
    Delta0Formula.Satisfies, Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_disj, satisfies_pairMemAt]
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  rw [generatorTokenWitnessAssignment]
  rfl

@[simp]
theorem varTag_eq_empty : (varTag : ZFSet.{u}) = ∅ := by
  simp [varTag]

/-- No member of `U` is equal to `U`. -/
theorem carrier_value_ne_universe {U : ZFSet.{u}}
    (x : Constructible.ZFCarrier U) : x.1 ≠ U := by
  intro h
  have hself : U ∈ U := by
    simpa only [h] using x.2
  exact ZFSet.mem_irrefl U hself

/-- Exact semantics of the generator-token formula on actual token codes. -/
theorem satisfies_generatorTokenLtFormula_tokenCodes
    (U r : ZFSet.{u})
    (left right : Option (Constructible.ZFCarrier U)) :
    FOFormula.Satisfies Delta0Formula.ZFMem generatorTokenLtFormula
        ![U, r, (∅ : ZFSet.{u}),
          tokenZFCode U (.inl left), tokenZFCode U (.inl right)] <->
      generatorTokenRel U r left right := by
  rw [satisfies_generatorTokenLtFormula]
  cases left with
  | none =>
      cases right with
      | none =>
          simp [tokenZFCode, rudimentaryGenerator, generatorTokenRel,
            triple, ZFSet.mem_irrefl]
      | some y =>
          simp [tokenZFCode, rudimentaryGenerator, generatorTokenRel,
            triple, y.2, ZFSet.mem_irrefl]
  | some x =>
      have hxne : x.1 ≠ U := carrier_value_ne_universe x
      cases right with
      | none =>
          simp [tokenZFCode, rudimentaryGenerator, generatorTokenRel,
            triple, ZFSet.mem_irrefl]
      | some y =>
          simp [tokenZFCode, rudimentaryGenerator, generatorTokenRel,
            generatorPairRel, triple, x.2, y.2, hxne]

/--
On two variable tokens, the formula is exactly the corresponding branch of
the external structural token order.
-/
theorem satisfies_generatorTokenLtFormula_codeTokenRel
    (U r : ZFSet.{u})
    (left right : Option (Constructible.ZFCarrier U)) :
    FOFormula.Satisfies Delta0Formula.ZFMem generatorTokenLtFormula
        ![U, r, (∅ : ZFSet.{u}),
          tokenZFCode U (.inl left), tokenZFCode U (.inl right)] <->
      codeTokenRel (generatorTokenRel U r)
        (Sum.inl left) (Sum.inl right) := by
  rw [satisfies_generatorTokenLtFormula_tokenCodes]
  constructor
  · exact Sum.Lex.inl
  · intro h
    cases h with
    | inl hleft => exact hleft

end


end RudimentaryTerm

end Constructible.Godel
