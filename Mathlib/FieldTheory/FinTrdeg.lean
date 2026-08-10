/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Extensions with Finite Transcendence Degree

A field extension L/K has finite transcendence degree if
the transcendence degree of L over K is finite.
Equivalently, if L is an algebraic extension of a finitely generated field extension of K.
-/

public section

open IntermediateField

/-- A field extension L/K is said to have finite transcendence degree if there is some
intermediate extension L/E/K with E/K finitely generated and L/E algebraic. -/
class FinTrdeg (K L : Type*) [Field K] [Field L] [Algebra K L] where
  exists_fg_isAlgebraic (K L) : ∃ E : IntermediateField K L, E.FG ∧ Algebra.IsAlgebraic E L

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (K L) in
instance [Algebra.IsAlgebraic K L] : FinTrdeg K L where
  exists_fg_isAlgebraic := ⟨⊥, IntermediateField.fg_bot, inferInstance⟩

variable (K L) in
instance [Algebra.EssFiniteType K L] : FinTrdeg K L where
  exists_fg_isAlgebraic := ⟨⊤, IntermediateField.fg_top_iff.mpr ‹_›, inferInstance⟩

theorem finTrdeg_iff_trdeg : FinTrdeg K L ↔ Algebra.trdeg K L < .aleph0 := by
  constructor
  · intro ⟨E, fg, alg⟩
    rw [← trdeg_add_eq K E, trdeg_eq_zero_iff.2 alg, add_zero]
    rw [← essFiniteType_iff, Algebra.essFiniteType_iff_exists_subalgebra] at fg
    obtain ⟨S₀, M, fin, islocal⟩ := fg
    rw [← trdeg_add_eq K S₀, trdeg_eq_zero_iff.2 islocal.isAlgebraic, add_zero]
    exact trdeg_lt_aleph0_of_finiteType
  · intro h
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
    have fin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.1 (hs.cardinalMk_eq_trdeg.trans_lt h)
    constructor
    refine ⟨adjoin K s, fg_adjoin_of_finite fin, ?_⟩
    have alg := hs.isAlgebraic_field
    rwa [Subtype.range_coe] at alg

alias ⟨_, FinTrdeg.of_trdeg⟩ := finTrdeg_iff_trdeg

variable (K L) in
theorem trdeg_lt_aleph0 [FinTrdeg K L] : Algebra.trdeg K L < .aleph0 :=
  finTrdeg_iff_trdeg.mp ‹_›

theorem FinTrdeg.trans (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FinTrdeg K E] [FinTrdeg E L] : FinTrdeg K L := by
  rw [finTrdeg_iff_trdeg, ← Cardinal.lift_lt_aleph0, ← lift_trdeg_add_eq K E L,
    Cardinal.add_lt_aleph0_iff, Cardinal.lift_lt_aleph0, Cardinal.lift_lt_aleph0]
  exact ⟨trdeg_lt_aleph0 K E, trdeg_lt_aleph0 E L⟩

theorem finite_of_isTranscendenceBasis [FinTrdeg K L] {ι : Type*} {x : ι → L}
    (hx : IsTranscendenceBasis K x) : Finite ι := by
  rw [← Cardinal.mk_lt_aleph0_iff, ← Cardinal.lift_lt_aleph0,
    hx.lift_cardinalMk_eq_trdeg, Cardinal.lift_lt_aleph0]
  exact trdeg_lt_aleph0 K L

theorem finite_of_algebraicIndependent [FinTrdeg K L] {ι : Type*} {x : ι → L}
    (hx : AlgebraicIndependent K x) : Finite ι := by
  rw [← Cardinal.mk_lt_aleph0_iff, ← Cardinal.lift_lt_aleph0]
  exact hx.lift_cardinalMk_le_trdeg.trans_lt (Cardinal.lift_lt_aleph0.mpr (trdeg_lt_aleph0 K L))

theorem FinTrdeg.of_isTranscendenceBasis {ι : Type*} [Finite ι] {x : ι → L}
    (hx : IsTranscendenceBasis K x) : FinTrdeg K L := by
  rw [finTrdeg_iff_trdeg, ← Cardinal.lift_lt_aleph0,
    ← hx.lift_cardinalMk_eq_trdeg, Cardinal.lift_lt_aleph0]
  exact Cardinal.mk_lt_aleph0

variable (K L) in
theorem exists_finset_isTranscendenceBasis [FinTrdeg K L] :
    ∃ s : Finset L, IsTranscendenceBasis K ((↑) : s → L) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  obtain ⟨s, rfl⟩ := Finset.mem_range_coe_iff.2
    (Set.finite_coe_iff.1 (finite_of_isTranscendenceBasis hs))
  exact ⟨s, hs⟩
