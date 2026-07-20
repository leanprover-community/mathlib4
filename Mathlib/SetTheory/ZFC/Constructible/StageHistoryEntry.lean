/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.DefinableRelationGraph
public import Mathlib.SetTheory.ZFC.Constructible.Delta0GodelGraph

/-!
# Constructible codes for stage-history entries

A stage history records triples `(index, stage, relation)`.  This file gives
the constructible triple code and a four-variable first-order lookup formula
whose semantics is exact in `LCarrier`.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-- A right-associated Kuratowski triple packaged as an element of `L`. -/
def tripleLCarrier (x y z : LCarrier.{u}) : LCarrier.{u} :=
  orderedPairLCarrier x (orderedPairLCarrier y z)

@[simp]
theorem tripleLCarrier_val (x y z : LCarrier.{u}) :
    (tripleLCarrier x y z).1 = Godel.triple x.1 y.1 z.1 :=
  rfl

/-- Right-associated Kuratowski triples are injective in all coordinates. -/
theorem triple_injective {a b c a' b' c' : ZFSet.{u}}
    (h : Godel.triple a b c = Godel.triple a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  rcases ZFSet.pair_inj.mp h with ⟨ha, htail⟩
  rcases ZFSet.pair_inj.mp htail with ⟨hb, hc⟩
  exact ⟨ha, hb, hc⟩

/-!
The free-variable layout of `historyEntryFormula` is
`(history, index, stage, relation)`.  The existentially bound last variable
is the encoded triple itself.
-/

/-- In an arbitrary context, the selected history contains the triple made
from the other three selected coordinates. -/
def historyEntryAt {n : Nat}
    (history index stage relation : Fin n) : FOFormula n :=
  .ex (.conj
    (.mem (Fin.last n) history.castSucc)
    (Delta0Formula.tripleEqAt
      (Fin.last n) index.castSucc stage.castSucc relation.castSucc).toFO)

/-- A history contains the triple `(index, stage, relation)`. -/
def historyEntryFormula : FOFormula 4 :=
  historyEntryAt (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)

/-- The direct four-coordinate assignment for a history lookup. -/
def historyEntryAssignment
    (history index stage relation : LCarrier.{u}) :
    Tuple LCarrier.{u} 4 :=
  ![history, index, stage, relation]

@[simp]
theorem satisfies_historyEntryAt_components {n : Nat}
    (history index stage relation : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (historyEntryAt history index stage relation) s ↔
      ∃ entry : LCarrier.{u},
        entry.1 ∈ (s history).1 ∧
          entry.1 = Godel.triple
            (s index).1 (s stage).1 (s relation).1 := by
  simp only [historyEntryAt, FOFormula.Satisfies,
    snoc_last, snoc_castSucc]
  apply exists_congr
  intro entry
  apply and_congr_right
  intro _hentry
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_tripleEqAt]
  simp only [snoc_last, snoc_castSucc]

/-- Exact arbitrary-context semantics of a history lookup. -/
theorem satisfies_historyEntryAt_iff {n : Nat}
    (history index stage relation : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (historyEntryAt history index stage relation) s ↔
      Godel.triple (s index).1 (s stage).1 (s relation).1 ∈
        (s history).1 := by
  rw [satisfies_historyEntryAt_components]
  constructor
  · rintro ⟨entry, hentry, heq⟩
    simpa only [heq] using hentry
  · intro hentry
    exact
      ⟨tripleLCarrier (s index) (s stage) (s relation),
        by simpa only [tripleLCarrier_val] using hentry,
        tripleLCarrier_val (s index) (s stage) (s relation)⟩

@[simp]
theorem satisfies_historyEntryFormula_components
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyEntryFormula
        (historyEntryAssignment history index stage relation) ↔
      ∃ entry : LCarrier.{u},
        entry.1 ∈ history.1 ∧
          entry.1 = Godel.triple index.1 stage.1 relation.1 := by
  simp only [historyEntryFormula, historyEntryAt, historyEntryAssignment,
    FOFormula.Satisfies, Matrix.cons_val_zero, snoc_last, snoc_castSucc]
  apply exists_congr
  intro entry
  apply and_congr_right
  intro _hentry
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_tripleEqAt]
  rfl

/-- Lookup satisfaction is exactly membership of the canonical triple. -/
theorem satisfies_historyEntryFormula_iff
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyEntryFormula
        (historyEntryAssignment history index stage relation) ↔
      Godel.triple index.1 stage.1 relation.1 ∈ history.1 := by
  rw [satisfies_historyEntryFormula_components]
  constructor
  · rintro ⟨entry, hentry, heq⟩
    simpa only [heq] using hentry
  · intro hentry
    exact
      ⟨tripleLCarrier index stage relation,
        by simpa only [tripleLCarrier_val] using hentry,
        tripleLCarrier_val index stage relation⟩

/-- The external predicate denoted by `historyEntryFormula`. -/
def HistoryEntry
    (history index stage relation : LCarrier.{u}) : Prop :=
  Godel.triple index.1 stage.1 relation.1 ∈ history.1

theorem satisfies_historyEntryFormula_iff_historyEntry
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyEntryFormula
        (historyEntryAssignment history index stage relation) ↔
      HistoryEntry history index stage relation :=
  satisfies_historyEntryFormula_iff history index stage relation

end

end Constructible.Model
