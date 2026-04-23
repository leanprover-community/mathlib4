/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.Init
import Mathlib.RingTheory.Etale.Field
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!

# Smooth algebras over fields

We show that separably generated extensions of fields are smooth.
In particular finitely generated field extensions over perfect fields are smooth.

-/

@[expose] public section

variable {K L ι : Type*} [Field L] [Field K] [Algebra K L]

open scoped IntermediateField.algebraAdjoinAdjoin in
lemma Algebra.FormallySmooth.adjoin_of_algebraicIndependent {v : ι → L}
    (hb : AlgebraicIndependent K v) :
    Algebra.FormallySmooth K (IntermediateField.adjoin K (Set.range v)) := by
  have : Algebra.FormallySmooth K (adjoin K (Set.range v)) :=
    .of_equiv hb.aevalEquiv
  have : Algebra.FormallySmooth (adjoin K (Set.range v))
      (IntermediateField.adjoin K (Set.range v)) :=
    .of_isLocalization (nonZeroDivisors _)
  exact .comp _ (adjoin K (Set.range v)) _

/-- Purely transcendental extensions are formally smooth. -/
lemma Algebra.FormallySmooth.of_algebraicIndependent {v : ι → L}
    (hb : AlgebraicIndependent K v) (hb' : IntermediateField.adjoin K (Set.range v) = ⊤) :
    Algebra.FormallySmooth K L := by
  have := Algebra.FormallySmooth.adjoin_of_algebraicIndependent hb
  rw [hb'] at this
  exact .of_equiv IntermediateField.topEquiv

/-- Separably generated extensions are formally smooth. -/
lemma Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
    {v : ι → L} (hb : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) L] :
    Algebra.FormallySmooth K L := by
  have := FormallySmooth.adjoin_of_algebraicIndependent hb
  have : FormallyEtale (IntermediateField.adjoin K (Set.range v)) L :=
    Algebra.FormallyEtale.of_isSeparable _ L
  exact .comp _ (IntermediateField.adjoin K (Set.range v)) _

instance (priority := low) Algebra.FormallySmooth.of_perfectField
    [PerfectField K] [Algebra.EssFiniteType K L] : Algebra.FormallySmooth K L := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have : Algebra.IsSeparable (↥(IntermediateField.adjoin K (Set.range ((↑) : s → L)))) L := by
    convert H <;> simp
  exact .of_algebraicIndependent_of_isSeparable hs.1
