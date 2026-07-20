/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryEntry

/-!
# Internal operations on constructible stage histories

A history is an actual member of `L`, not an external Lean set.  This file
constructs the internal operation which adjoins one canonical triple and
records its exact lookup behavior.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The constructible singleton containing `x`. -/
def singletonLCarrier (x : LCarrier.{u}) : LCarrier.{u} :=
  pairLCarrier x x

@[simp]
theorem mem_singletonLCarrier_iff (x z : LCarrier.{u}) :
    z.1 ∈ (singletonLCarrier x).1 ↔ z = x := by
  simp only [singletonLCarrier, mem_pairLCarrier_iff, or_self]

/-- Binary union, constructed internally from Pairing and Union. -/
def unionLCarrier (x y : LCarrier.{u}) : LCarrier.{u} :=
  sUnionLCarrier (pairLCarrier x y)

@[simp]
theorem mem_unionLCarrier_iff (x y z : LCarrier.{u}) :
    z.1 ∈ (unionLCarrier x y).1 ↔ z.1 ∈ x.1 ∨ z.1 ∈ y.1 := by
  rw [unionLCarrier, mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨member, hmember, hz⟩
    rcases (mem_pairLCarrier_iff x y member).mp hmember with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨x, (mem_pairLCarrier_iff x y x).mpr (Or.inl rfl), hz⟩
    · exact ⟨y, (mem_pairLCarrier_iff x y y).mpr (Or.inr rfl), hz⟩

/-- Adjoin the canonical code of one state to an internal history. -/
def addHistoryEntry
    (history index stage relation : LCarrier.{u}) : LCarrier.{u} :=
  unionLCarrier history
    (singletonLCarrier (tripleLCarrier index stage relation))

@[simp]
theorem mem_addHistoryEntry_iff
    (history index stage relation entry : LCarrier.{u}) :
    entry.1 ∈ (addHistoryEntry history index stage relation).1 ↔
      entry.1 ∈ history.1 ∨
        entry = tripleLCarrier index stage relation := by
  simp only [addHistoryEntry, mem_unionLCarrier_iff,
    mem_singletonLCarrier_iff]

/-- Looking up an extended history either finds an old state or exactly the
newly adjoined state. -/
@[simp]
theorem historyEntry_addHistoryEntry_iff
    (history index stage relation queryIndex queryStage queryRelation :
      LCarrier.{u}) :
    HistoryEntry (addHistoryEntry history index stage relation)
        queryIndex queryStage queryRelation ↔
      HistoryEntry history queryIndex queryStage queryRelation ∨
        (queryIndex = index ∧ queryStage = stage ∧
          queryRelation = relation) := by
  change
    Godel.triple queryIndex.1 queryStage.1 queryRelation.1 ∈
        (addHistoryEntry history index stage relation).1 ↔ _
  let queryEntry := tripleLCarrier queryIndex queryStage queryRelation
  have hquery :
      queryEntry.1 =
        Godel.triple queryIndex.1 queryStage.1 queryRelation.1 :=
    tripleLCarrier_val queryIndex queryStage queryRelation
  rw [← hquery, mem_addHistoryEntry_iff]
  constructor
  · rintro (hold | hnew)
    · exact Or.inl hold
    · right
      have hcoordinates := triple_injective
        (congrArg Subtype.val hnew)
      exact
        ⟨Subtype.ext hcoordinates.1,
          Subtype.ext hcoordinates.2.1,
          Subtype.ext hcoordinates.2.2⟩
  · rintro (hold | ⟨rfl, rfl, rfl⟩)
    · exact Or.inl hold
    · exact Or.inr rfl

end

end Constructible.Model
