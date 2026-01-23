/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.SeparablyGenerated

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
lemma Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable [EssFiniteType K L]
    {v : ι → L} (hb : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) L] :
    Algebra.FormallySmooth K L := by
  have := Algebra.FormallySmooth.adjoin_of_algebraicIndependent hb
  have : EssFiniteType (IntermediateField.adjoin K (Set.range v)) L :=
    .of_comp K _ _
  have : FormallyEtale (IntermediateField.adjoin K (Set.range v)) L :=
    (FormallyEtale.iff_isSeparable _ _).mpr inferInstance
  exact .comp _ (IntermediateField.adjoin K (Set.range v)) _

instance (priority := low) Algebra.FormallySmooth.of_perfectField
    [PerfectField K] [Algebra.EssFiniteType K L] : Algebra.FormallySmooth K L := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have : Algebra.IsSeparable (↥(IntermediateField.adjoin K (Set.range ((↑) : s → L)))) L := by
    convert H <;> simp
  exact .of_algebraicIndependent_of_isSeparable hs.1
