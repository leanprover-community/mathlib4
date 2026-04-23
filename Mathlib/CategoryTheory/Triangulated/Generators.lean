/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.ObjectProperty.ClosureShift
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.StacksAttribute

/-!
# Generators in triangulated categories

We define the notions of strong and classical generators in (pre)triangulated categories.
This is not to be confused with `ObjectProperty.IsStrongGenerator` defined in
`CategoryTheory/Generator`.

## Main definitions

- `ObjectProperty.triangEnvelopeIter P n`: The object property of all objects reachable from `P`
  by shifts, binary products, retracts and at most `n` extensions.
- `ObjectProperty.triangEnvelope P`: The triangulated envelope of `P`, i.e., the object property
  of all objects reachable from `P` by shifts, binary products, retracts and extensions. This is
  the smallest triangulated object property closed under retracts that contains `P`, see
  `ObjectProperty.triangEnvelope_le_iff`.
- `ObjectProperty.IsStrongTriangulatedGenerator P`: `P` is a strong triangulated generator if
  there exists `n` such that every object is in `P.triangEnvelopeIter n`.
- `ObjectProperty.IsClassicalTriangulatedGenerator P`: `P` is a classical triangulated generator
  if every object is in `P.triangEnvelope`.

## Main results

- `ObjectProperty.triangEnvelope_le_iff`: The universal property of `P.triangEnvelope`: it is
  the smallest triangulated object property closed under retracts that contains `P`.
- `ObjectProperty.IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator`: A strong
  triangulated generator is a classical triangulated generator.

## TODO

* Prove that if `C` has a strong generator and `P` is a classical generator, then `P` is a
  strong generator (stacks 0FXA).

## References

* [Bondal and Van den Bergh, *Generators and representability of functors in commutative and
  noncommutative geometry*][bondal_vandenbergh_2003]
* [Stacks 09SJ](https://stacks.math.columbia.edu/tag/09SJ)

-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

/-- All objects that can be reached by shifts, binary products, retracts and at most `n`
extensions from objects in `P`. -/
abbrev triangEnvelopeIter (n : ℕ) : ObjectProperty C :=
  ((P.shiftClosure ℤ).binaryProductsClosure.retractClosure.extensionProductIter n).retractClosure

@[simp]
lemma triangEnvelopeIter_zero :
    P.triangEnvelopeIter 0 = (P.shiftClosure ℤ).binaryProductsClosure.retractClosure := by
  rw [triangEnvelopeIter, extensionProductIter_zero, retractClosure_eq_self]

lemma triangEnvelopeIter_succ (n : ℕ) :
    P.triangEnvelopeIter (n + 1) =
      (extensionProduct (P.shiftClosure ℤ).binaryProductsClosure.retractClosure
         (P.triangEnvelopeIter n)).retractClosure := by
  rw [triangEnvelopeIter, extensionProductIter_succ,
    ← retractClosure_extensionProduct_retractClosure_retractClosure]
  simp

lemma triangEnvelopeIter_succ' [IsTriangulated C] (n : ℕ) :
    P.triangEnvelopeIter (n + 1) =
      (extensionProduct (P.triangEnvelopeIter n)
        (P.shiftClosure ℤ).binaryProductsClosure.retractClosure).retractClosure := by
  rw [triangEnvelopeIter, extensionProductIter_succ',
    ← retractClosure_extensionProduct_retractClosure_retractClosure]
  simp

lemma triangEnvelopeIter_add [IsTriangulated C] {n m n' : ℕ} (h : n = n' + 1 := by lia) :
    P.triangEnvelopeIter (n + m) =
      (extensionProduct (P.triangEnvelopeIter n') (P.triangEnvelopeIter m)).retractClosure := by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add _ h]

lemma triangEnvelopeIter_add' [IsTriangulated C] {n m m' : ℕ} (h : m = m' + 1 := by lia) :
    P.triangEnvelopeIter (n + m) =
      (extensionProduct (P.triangEnvelopeIter n) (P.triangEnvelopeIter m')).retractClosure := by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add' _ h]

variable {P} in
lemma monotone_triangEnvelopeIter {Q : ObjectProperty C} (hPQ : P ≤ Q) (n : ℕ) :
    P.triangEnvelopeIter n ≤ Q.triangEnvelopeIter n :=
  monotone_retractClosure <| monotone_extensionProductIter
    (monotone_retractClosure <| limitsClosure_monotone _ <| monotone_shiftClosure hPQ) n

lemma monotone'_triangEnvelopeIter {n m : ℕ} (h : n ≤ m := by lia) :
    P.triangEnvelopeIter n ≤ P.triangEnvelopeIter m := by
  apply monotone_retractClosure
  by_cases! hP : P.Nonempty
  · exact monotone'_extensionProductIter _ h
  · simp [hP]

lemma le_triangEnvelopeIter (n : ℕ) : P ≤ P.triangEnvelopeIter n :=
  calc
    P ≤ P.shiftClosure ℤ := le_shiftClosure _
    _ ≤ (P.shiftClosure ℤ).binaryProductsClosure := le_limitsClosure _ _
    _ ≤ (P.shiftClosure ℤ).binaryProductsClosure.retractClosure := le_retractClosure _
    _ ≤ P.triangEnvelopeIter n := by
      rw [← triangEnvelopeIter_zero]
      exact P.monotone'_triangEnvelopeIter (Nat.zero_le n)

/-- An object property `P` is called a strong triangulated generator, if every object
can be reached from objects in `P` by shifts, binary products, retracts and at most `n`
extensions, for some fixed `n`. -/
@[stacks 09SJ "(2)"]
def IsStrongTriangulatedGenerator : Prop := ∃ n, P.triangEnvelopeIter n = ⊤

lemma isStrongTriangulatedGenerator_iff :
    P.IsStrongTriangulatedGenerator ↔ ∃ n, P.triangEnvelopeIter n = ⊤ := Iff.rfl

/-- All objects that can be reached by shifts, binary products, retracts and extensions
from objects in `P`. This is the smallest triangulated object property closed under retracts
that contains `P`, see `ObjectProperty.triangEnvelope_le_iff`. -/
def triangEnvelope : ObjectProperty C := ⨆ n, P.triangEnvelopeIter n

lemma prop_triangEnvelope_iff (X : C) : P.triangEnvelope X ↔ ∃ n, P.triangEnvelopeIter n X :=
  prop_iSup_iff _ X

lemma triangEnvelopeIter_le_triangEnvelope (n : ℕ) : P.triangEnvelopeIter n ≤ P.triangEnvelope :=
  le_iSup _ _

lemma le_triangEnvelope : P ≤ P.triangEnvelope :=
  (P.le_triangEnvelopeIter 0).trans (P.triangEnvelopeIter_le_triangEnvelope 0)

instance [P.Nonempty] : P.triangEnvelope.Nonempty :=
  .mono P.le_triangEnvelope

variable {P} in
lemma monotone_triangEnvelope {Q : ObjectProperty C} (h : P ≤ Q) :
    P.triangEnvelope ≤ Q.triangEnvelope :=
  iSup_le fun n => (P.monotone_triangEnvelopeIter h n).trans
    (Q.triangEnvelopeIter_le_triangEnvelope n)

instance : P.triangEnvelope.IsStableUnderRetracts where
  of_retract := by
    intro X Y r hY
    rw [prop_triangEnvelope_iff] at hY ⊢
    obtain ⟨n, hn⟩ := hY
    exact ⟨n, IsStableUnderRetracts.of_retract r hn⟩

instance : P.triangEnvelope.IsStableUnderShift ℤ where
  isStableUnderShiftBy a := IsStableUnderShiftBy.mk <| by
    intro X hX
    rw [prop_triangEnvelope_iff] at hX
    obtain ⟨n, hn⟩ := hX
    rw [prop_shift_iff, prop_triangEnvelope_iff]
    exact ⟨n, IsStableUnderShiftBy.le_shift _ hn⟩

instance [IsTriangulated C] : P.triangEnvelope.IsTriangulatedClosed₂ := by
  apply IsTriangulatedClosed₂.mk'
  intro T hT h₁ h₂
  rw [prop_triangEnvelope_iff] at h₁ h₂ ⊢
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  use n + (m + 1)
  rw [triangEnvelopeIter_add' P rfl]
  exact le_retractClosure _ _ ⟨_, _, _, _, _, hT, hn, hm⟩

instance [P.Nonempty] [IsTriangulated C] : P.triangEnvelope.IsTriangulated where

lemma triangEnvelope_le_iff {Q : ObjectProperty C} [Q.IsStableUnderRetracts] [Q.IsTriangulated] :
    P.triangEnvelope ≤ Q ↔ P ≤ Q := by
  refine ⟨fun h ↦ le_trans P.le_triangEnvelope h, fun h ↦ ?_⟩
  rw [triangEnvelope, iSup_le_iff]
  intro n
  rw [triangEnvelopeIter, retractClosure_le_iff]
  apply extensionProductIter_le_of_isTriangulatedClosed₂
  rwa [retractClosure_le_iff, binaryProductsClosure_le_iff, shiftClosure_le_iff]

/-- An object property `P` is called a classical generator, if every object can be reached
from objects in `P` by shifts, binary products, retracts and extensions. -/
@[stacks 09SJ "(1)"]
def IsClassicalTriangulatedGenerator : Prop := P.triangEnvelope = ⊤

lemma isClassicalTriangulatedGenerator_iff :
    P.IsClassicalTriangulatedGenerator ↔ P.triangEnvelope = ⊤ := Iff.rfl

lemma IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator
    (h : P.IsStrongTriangulatedGenerator) : P.IsClassicalTriangulatedGenerator := by
  obtain ⟨n, hn⟩ := h
  rw [isClassicalTriangulatedGenerator_iff, eq_top_iff]
  exact hn ▸ (P.triangEnvelopeIter_le_triangEnvelope n)

end CategoryTheory.ObjectProperty
