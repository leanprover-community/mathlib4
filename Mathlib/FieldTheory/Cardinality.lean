/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Rat.Encodable
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.SetTheory.Cardinal.Divisibility

/-!
# Cardinality of Fields

In this file we show all the possible cardinalities of fields. All infinite cardinals can harbour
a field structure, and so can all types with prime power cardinalities, and this is sharp.

## Main statements

* `Fintype.nonempty_field_iff`: A `Fintype` can be given a field structure iff its cardinality is a
  prime power.
* `Infinite.nonempty_field` : Any infinite type can be endowed a field structure.
* `Field.nonempty_iff` : There is a field structure on type iff its cardinality is a prime power.

-/


local notation "‖" x "‖" => Fintype.card x

open scoped Cardinal nonZeroDivisors

universe u

/-- A finite field has prime power cardinality. -/
theorem Fintype.isPrimePow_card_of_field {α} [Fintype α] [Field α] : IsPrimePow ‖α‖ := by
  -- TODO: `Algebra` version of `CharP.exists`, of type `∀ p, Algebra (ZMod p) α`
  cases' CharP.exists α with p _
  haveI hp := Fact.mk (CharP.char_is_prime α p)
  letI : Algebra (ZMod p) α := ZMod.algebra _ _
  let b := IsNoetherian.finsetBasis (ZMod p) α
  rw [Module.card_fintype b, ZMod.card, isPrimePow_pow_iff]
  · exact hp.1.isPrimePow
  rw [← Module.finrank_eq_card_basis b]
  exact Module.finrank_pos.ne'

/-- A `Fintype` can be given a field structure iff its cardinality is a prime power. -/
theorem Fintype.nonempty_field_iff {α} [Fintype α] : Nonempty (Field α) ↔ IsPrimePow ‖α‖ := by
  refine ⟨fun ⟨h⟩ => Fintype.isPrimePow_card_of_field, ?_⟩
  rintro ⟨p, n, hp, hn, hα⟩
  haveI := Fact.mk hp.nat_prime
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  exact ⟨(Fintype.equivOfCardEq
    (((Fintype.card_eq_nat_card).trans (GaloisField.card p n hn.ne')).trans hα)).symm.field⟩

theorem Fintype.not_isField_of_card_not_prime_pow {α} [Fintype α] [Ring α] :
    ¬IsPrimePow ‖α‖ → ¬IsField α :=
  mt fun h => Fintype.nonempty_field_iff.mp ⟨h.toField⟩

/-- Any infinite type can be endowed a field structure. -/
theorem Infinite.nonempty_field {α : Type u} [Infinite α] : Nonempty (Field α) := by
  suffices #α = #(FractionRing (MvPolynomial α <| ULift.{u} ℚ)) from
    (Cardinal.eq.1 this).map (·.field)
  simp

/-- There is a field structure on type if and only if its cardinality is a prime power. -/
theorem Field.nonempty_iff {α : Type u} : Nonempty (Field α) ↔ IsPrimePow #α := by
  rw [Cardinal.isPrimePow_iff]
  cases' fintypeOrInfinite α with h h
  · simpa only [Cardinal.mk_fintype, Nat.cast_inj, exists_eq_left',
      (Cardinal.nat_lt_aleph0 _).not_le, false_or] using Fintype.nonempty_field_iff
  · simpa only [← Cardinal.infinite_iff, h, true_or, iff_true] using Infinite.nonempty_field
