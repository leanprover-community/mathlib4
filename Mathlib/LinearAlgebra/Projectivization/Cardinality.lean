/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Cardinality of projective spaces

We compute the cardinality of `ℙ k V` if `k` is a finite field.

-/

namespace Projectivization

open scoped LinearAlgebra.Projectivization

section

variable (k V : Type*) [DivisionRing k] [AddCommGroup V] [Module k V]

/-- `ℙ k V` is equivalent to the quotient of the non-zero elements of `V` by `kˣ`. -/
def equivQuotientOrbitRel : ℙ k V ≃ Quotient (MulAction.orbitRel kˣ { v : V // v ≠ 0 }) :=
  Quotient.congr (Equiv.refl _) (fun x y ↦ (Units.orbitRel_nonZero_iff k V x y).symm)

/-- The non-zero elements of `V` are equivalent to the product of `ℙ k V` with the units of `k`. -/
noncomputable def nonZeroEquivProjectivizationProdUnits : { v : V // v ≠ 0 } ≃ ℙ k V × kˣ :=
  let e := MulAction.selfEquivOrbitsQuotientProd <| fun b ↦ by
    rw [(Units.nonZeroSubMul k V).stabilizer_of_subMul,
      Module.stabilizer_units_eq_bot_of_ne_zero k b.property]
  e.trans (Equiv.prodCongrLeft (fun _ ↦ (equivQuotientOrbitRel k V).symm))

/-- If `V` is a finite `k`-module and `k` is finite, `ℙ k V` is finite. -/
instance finite_of_finite [Finite k] [Finite V] : Finite (ℙ k V) :=
  have : Finite (ℙ k V × kˣ) := Finite.of_equiv _ (nonZeroEquivProjectivizationProdUnits k V)
  Finite.prod_left kˣ

/-- Fraction free cardinality formula for the points of `ℙ k V` if `k` and `V` are finite.
See `Projectivization.card'` and `Projectivization.card''` for other spellings of the formula. -/
lemma card [Finite k] [Finite V] :
    Nat.card V - 1 = Nat.card (ℙ k V) * (Nat.card k - 1) := by
  classical
  haveI : Finite V := Module.finite_of_finite k
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (ℙ k V) := Fintype.ofFinite (ℙ k V)
  haveI : Fintype k := Fintype.ofFinite k
  have hV : Fintype.card { v : V // v ≠ 0 } = Fintype.card V - 1 := by simp
  simp_rw [← Fintype.card_eq_nat_card, ← Fintype.card_units (α := k), ← hV]
  rw [Fintype.card_congr (nonZeroEquivProjectivizationProdUnits k V), Fintype.card_prod]

/-- Cardinality formula for the points of `ℙ k V` if `k` and `V` are finite with less
natural subtraction. -/
lemma card' [Finite k] [Finite V] :
    Nat.card V = Nat.card (ℙ k V) * (Nat.card k - 1) + 1 := by
  rw [← card k V]
  have : Nat.card V > 0 := Nat.card_pos
  omega

end

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

/-- Cardinality formula for the points of `ℙ k V` if `k` and `V` are finite expressed
as a fraction. -/
lemma card'' [Finite k] [Finite V] :
    Nat.card (ℙ k V) = (Nat.card V - 1) / (Nat.card k - 1) := by
  haveI : Fintype k := Fintype.ofFinite k
  rw [card k]
  have : 2 ≤ Nat.card k := FiniteField.two_le_card k
  have h : 0 ≠ (Nat.card k - 1) := by omega
  exact Nat.eq_div_of_mul_eq_left (Ne.symm h) rfl

lemma card_of_finrank_two [Finite k] (h : Module.finrank k V = 2) :
    Nat.card (ℙ k V) = Nat.card k + 1 := by
  have : Module.Finite k V := Module.finite_of_finrank_eq_succ h
  have : Finite V := Module.finite_of_finite k
  let e : V ≃ₗ[k] (Fin 2 → k) := LinearEquiv.ofFinrankEq _ _ (by simpa)
  have : Nat.card V = Nat.card k ^ 2 := by
    simp only [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [card'', this, Nat.sq_sub_sq _ 1]
  have : 2 ≤ Nat.card k := FiniteField.two_le_card k
  exact (Nat.eq_div_of_mul_eq_left (by omega) rfl).symm

end Projectivization
