/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.MvRatFunc.Rank
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Cardinality of a transcendence basis

This file concerns the cardinality of a transcendence basis.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## TODO
Define the transcendence degree and show it is independent of the choice of a
transcendence basis.

## Tags
transcendence basis, transcendence degree, transcendence

-/

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u v w

open AlgebraicIndependent

open Cardinal

theorem IsTranscendenceBasis.lift_cardinalMk_eq_max_lift
    {F : Type u} {E : Type v} [CommRing F] [Nontrivial F] [CommRing E] [IsDomain E] [Algebra F E]
    {ι : Type w} {x : ι → E} [Nonempty ι] (hx : IsTranscendenceBasis F x) :
    lift.{max u w} #E = lift.{max v w} #F ⊔ lift.{max u v} #ι ⊔ ℵ₀ := by
  let K := Algebra.adjoin F (Set.range x)
  suffices #E = #K by simp [K, this, ← lift_mk_eq'.2 ⟨hx.1.aevalEquiv.toEquiv⟩]
  haveI : Algebra.IsAlgebraic K E := hx.isAlgebraic
  refine le_antisymm ?_ (mk_le_of_injective Subtype.val_injective)
  haveI : Infinite K := hx.1.aevalEquiv.infinite_iff.1 inferInstance
  simpa only [sup_eq_left.2 (aleph0_le_mk K)] using Algebra.IsAlgebraic.cardinalMk_le_max K E

theorem IsTranscendenceBasis.lift_rank_eq_max_lift
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {ι : Type w} {x : ι → E} [Nonempty ι] (hx : IsTranscendenceBasis F x) :
    lift.{max u w} (Module.rank F E) = lift.{max v w} #F ⊔ lift.{max u v} #ι ⊔ ℵ₀ := by
  let K := IntermediateField.adjoin F (Set.range x)
  haveI : Algebra.IsAlgebraic K E := hx.isAlgebraic_field
  rw [← rank_mul_rank F K E, lift_mul, ← hx.1.aevalEquivField.toLinearEquiv.lift_rank_eq,
    MvRatFunc.rank_eq_max_lift, lift_max, lift_max, lift_lift, lift_lift, lift_aleph0]
  refine mul_eq_left le_sup_right ((lift_le.2 ((rank_le_card K E).trans
    (Algebra.IsAlgebraic.cardinalMk_le_max K E))).trans_eq ?_) (by simp [rank_pos.ne'])
  simp [K, ← lift_mk_eq'.2 ⟨hx.1.aevalEquivField.toEquiv⟩]

theorem Algebra.Transcendental.rank_eq_cardinalMk
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [Algebra.Transcendental F E] :
    Module.rank F E = #E := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' F E
  haveI := hx.nonempty_iff_transcendental.2 ‹_›
  simpa [← hx.lift_cardinalMk_eq_max_lift] using hx.lift_rank_eq_max_lift

theorem IntermediateField.rank_sup_le
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] (A B : IntermediateField F E) :
    Module.rank F ↥(A ⊔ B) ≤ Module.rank F A * Module.rank F B := by
  by_cases hA : Algebra.IsAlgebraic F A
  · exact rank_sup_le_of_isAlgebraic A B (Or.inl hA)
  by_cases hB : Algebra.IsAlgebraic F B
  · exact rank_sup_le_of_isAlgebraic A B (Or.inr hB)
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at hA hB
  haveI : Algebra.Transcendental F ↥(A ⊔ B) := .ringHom_of_comp_eq (RingHom.id F)
    (inclusion le_sup_left) Function.surjective_id (inclusion_injective _) rfl
  haveI := Algebra.Transcendental.infinite F A
  haveI := Algebra.Transcendental.infinite F B
  simp_rw [Algebra.Transcendental.rank_eq_cardinalMk]
  rw [sup_def, mul_mk_eq_max, ← Cardinal.lift_le.{u}]
  refine (lift_cardinalMk_adjoin_le _ _).trans ?_
  calc
    _ ≤ Cardinal.lift.{v} #F ⊔ Cardinal.lift.{u} (#A ⊔ #B) ⊔ ℵ₀ := by
      gcongr
      rw [Cardinal.lift_le]
      exact (mk_union_le _ _).trans_eq (by simp)
    _ = _ := by
      simp [lift_mk_le_lift_mk_of_injective (algebraMap F A).injective]
