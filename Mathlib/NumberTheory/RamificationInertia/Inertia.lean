/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Finiteness
import Mathlib.Init
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Ramification index and inertia degree

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **inertia degree** `Ideal.inertiaDeg p P` is the degree of the field extension
`(S / P) : (R / p)`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`

We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `f` stands for the inertia degree of `P` over `p`, leaving `p` and `P` implicit.

-/

@[expose] public section


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section DecEq

variable {S₁ : Type*} [CommRing S₁] [Algebra R S₁]

open Classical in
/-- The inertia degree of `P : Ideal S` lying over `p : Ideal R` is the degree of the
extension `(S / P) : (R / p)`.

We do not assume `P` lies over `p` in the definition; we return `0` instead.

See `inertiaDeg_algebraMap` for the common case where `f = algebraMap R S`
and there is an algebra structure `R / p → S / P`.
-/
noncomputable def inertiaDeg : ℕ :=
  if hPp : comap f P = p then
    letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfLEComap hPp.ge
    finrank (R ⧸ p) (S ⧸ P)
  else 0

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp]
theorem inertiaDeg_of_subsingleton [hp : p.IsMaximal] [hQ : Subsingleton (S ⧸ P)] :
    inertiaDeg p P = 0 := by
  have := Ideal.Quotient.subsingleton_iff.mp hQ
  subst this
  exact dif_neg fun h => hp.ne_top <| h.symm.trans comap_top

@[simp]
theorem inertiaDeg_algebraMap [P.LiesOver p] :
    inertiaDeg p P = finrank (R ⧸ p) (S ⧸ P) := by
  rw [inertiaDeg, dif_pos (over_def P p).symm]

theorem inertiaDeg_pos [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] : 0 < inertiaDeg p P :=
  have : Nontrivial (S ⧸ P) := Quotient.nontrivial_of_liesOver_of_isPrime P p
  finrank_pos.trans_eq (inertiaDeg_algebraMap p P).symm

theorem inertiaDeg_ne_zero [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] : inertiaDeg p P ≠ 0 :=
  (Nat.ne_of_lt (inertiaDeg_pos p P)).symm

lemma inertiaDeg_comap_eq (e : S ≃ₐ[R] S₁) (P : Ideal S₁) :
    inertiaDeg p (P.comap e) = inertiaDeg p P := by
  have he : (P.comap e).comap (algebraMap R S) = p ↔ P.comap (algebraMap R S₁) = p := by
    rw [← comap_coe e, comap_comap, ← e.toAlgHom_toRingHom, AlgHom.comp_algebraMap]
  by_cases h : P.LiesOver p
  · rw [inertiaDeg_algebraMap, inertiaDeg_algebraMap]
    exact (Quotient.algEquivOfEqComap p e rfl).toLinearEquiv.finrank_eq
  · rw [inertiaDeg, dif_neg (fun eq => h ⟨(he.mp eq).symm⟩)]
    rw [inertiaDeg, dif_neg (fun eq => h ⟨eq.symm⟩)]

lemma inertiaDeg_map_eq (P : Ideal S)
    {E : Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁] (e : E) :
    inertiaDeg p (P.map e) = inertiaDeg p P := by
  rw [show P.map e = _ from map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.inertiaDeg_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

theorem inertiaDeg_bot [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
    [hP : P.LiesOver (⊥ : Ideal R)] :
    (⊥ : Ideal R).inertiaDeg P = finrank R S := by
  rw [inertiaDeg, dif_pos (over_def P (⊥ : Ideal R)).symm]
  replace hP : P = ⊥ := eq_bot_of_liesOver_bot R P
  rw [Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot R).symm
    ((quotEquivOfEq hP).trans (RingEquiv.quotientBot S)).symm]
  rfl

theorem inertiaDeg_le_inertiaDeg {T : Type*} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Module.Finite R T] (Q : Ideal T) [P.LiesOver p] [Q.LiesOver P]
    [p.IsPrime] : inertiaDeg P Q ≤ inertiaDeg p Q := by
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDeg_algebraMap, inertiaDeg_algebraMap]
  have : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩
    simp [Submodule.Quotient.quot_mk_eq_mk, IsScalarTower.algebraMap_apply R (S ⧸ P) (T ⧸ Q)]
  exact finrank_top_le_finrank_of_isScalarTower ..

end DecEq

section absNorm

lemma absNorm_eq_pow_inertiaDeg_of_liesOver {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [IsDedekindDomain R] [Module.Free ℤ R] [Algebra S R] [Module.Finite S R]
    (P : Ideal R) (p : Ideal S) [P.LiesOver p] (hp : p.IsPrime) (hp_ne_bot : p ≠ ⊥) :
    absNorm P = absNorm p ^ (p.inertiaDeg P) := by
  have : p.IsMaximal := hp.isMaximal hp_ne_bot
  let _ : Field (S ⧸ p) := Quotient.field p
  simpa [absNorm_apply, Submodule.cardQuot_apply] using Module.natCard_eq_pow_finrank (K := S ⧸ p)

set_option backward.isDefEq.respectTransparency false in
/-- The absolute norm of an ideal `P` above a rational prime `p` is
`|p| ^ ((span {p}).inertiaDeg P)`.
See `absNorm_eq_pow_inertiaDeg'` for a version with `p` of type `ℕ`. -/
lemma absNorm_eq_pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℤ}
    (P : Ideal R) [P.LiesOver (span {p})] (hp : Prime p) :
    absNorm P = p.natAbs ^ ((span {p}).inertiaDeg P) := by
  simpa using absNorm_eq_pow_inertiaDeg_of_liesOver P (span {p})
    (by rwa [span_singleton_prime hp.ne_zero]) (by simpa using hp.ne_zero)

/-- The absolute norm of an ideal `P` above a rational (positive) prime `p` is
`p ^ ((span {p}).inertiaDeg P)`.
See `absNorm_eq_pow_inertiaDeg` for a version with `p` of type `ℤ`. -/
lemma absNorm_eq_pow_inertiaDeg' [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℕ}
    (P : Ideal R) [P.LiesOver (span {(p : ℤ)})] (hp : p.Prime) :
    absNorm P = p ^ ((span {(p : ℤ)}).inertiaDeg P) :=
  absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)

end absNorm

section tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Let `T / S / R` be a tower of algebras, `p, P, I` be ideals in `R, S, T`, respectively,
  and `p` and `P` are maximal. If `p = P ∩ S` and `P = I ∩ S`,
  then `f (I | p) = f (P | p) * f (I | P)`. -/
theorem inertiaDeg_algebra_tower (p : Ideal R) (P : Ideal S) (I : Ideal T) [p.IsMaximal]
    [P.IsMaximal] [P.LiesOver p] [I.LiesOver P] : inertiaDeg p I =
    inertiaDeg p P * inertiaDeg P I := by
  have h₁ := P.over_def p
  have h₂ := I.over_def P
  have h₃ := (LiesOver.trans I P p).over
  simp only [inertiaDeg, dif_pos h₁.symm, dif_pos h₂.symm, dif_pos h₃.symm]
  letI : Algebra (R ⧸ p) (S ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap h₁.le
  letI : Algebra (S ⧸ P) (T ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap h₂.le
  letI : Algebra (R ⧸ p) (T ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap h₃.le
  letI : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ I) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩; exact congr_arg _ (IsScalarTower.algebraMap_apply R S T x)
  exact (finrank_mul_finrank (R ⧸ p) (S ⧸ P) (T ⧸ I)).symm

end tower

end Ideal
