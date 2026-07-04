/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Inertia degree

Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined
to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`.

## Main definitions

* `Ideal.inertiaDeg q R`: The inertia degree of `q` over `R`.

## Main statements

* `inertiaDeg'_eq_inertiaDeg`: The inertia degree agrees with the usual definition in the case of
  maximal ideals.
* `inertiaDeg_tower`: Inertia degree is multiplicative in towers.
-/

@[expose] public section

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open Classical in
/-- Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined
to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.inertiaDeg'`. -/
noncomputable def inertiaDeg : ℕ :=
  if _ : q.IsPrime then
    letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    Module.finrank (q.under R).ResidueField q.ResidueField else 0

theorem inertiaDeg_def [hq : q.IsPrime]
    [Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra (q.under R) q] :
    q.inertiaDeg R = Module.finrank (q.under R).ResidueField q.ResidueField := by
  convert! dif_pos hq
  simp [Algebra.algebra_ext_iff, Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_def := inertiaDeg_def

theorem inertiaDeg_of_not_isPrime (hq : ¬ q.IsPrime) : q.inertiaDeg R = 0 :=
  dif_neg hq

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_of_not_isPrime :=
  inertiaDeg_of_not_isPrime

theorem inertiaDeg_pos [hq : q.IsPrime] [Module.Finite R S] : 0 < q.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  rw [inertiaDeg_def]
  apply Module.finrank_pos

end

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) (r : Ideal T)

theorem inertiaDeg_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    q.inertiaDeg R = Module.finrank p.ResidueField q.ResidueField := by
  have := Ideal.over_def q p
  subst this
  exact inertiaDeg_def q R

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_eq := inertiaDeg_eq

theorem inertiaDeg_eq_of_isFractionRing [q.LiesOver p] [p.IsPrime] [q.IsPrime]
    (K L : Type*) [Field K] [Field L]
    [Algebra (R ⧸ p) K] [IsFractionRing (R ⧸ p) K]
    [Algebra (S ⧸ q) L] [IsFractionRing (S ⧸ q) L]
    [Algebra R K] [IsScalarTower R (R ⧸ p) K]
    [Algebra S L] [IsScalarTower S (S ⧸ q) L]
    [Algebra R L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L] :
    q.inertiaDeg R = Module.finrank K L := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  rw [inertiaDeg_eq p q]
  apply Algebra.finrank_eq_of_equiv_equiv
    (IsFractionRing.algEquivOfAlgEquiv (R := R) (A := R ⧸ p) (K := p.ResidueField) (L := K) .refl)
    (IsFractionRing.algEquivOfAlgEquiv (R := S) (A := S ⧸ q) (K := q.ResidueField) (L := L) .refl)
  apply IsFractionRing.ringHom_ext (A := R ⧸ p)
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [← IsScalarTower.algebraMap_apply R p.ResidueField q.ResidueField,
    IsScalarTower.algebraMap_apply R S q.ResidueField,
    ← IsScalarTower.algebraMap_apply R K L, ← IsScalarTower.algebraMap_apply R S L]

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_eq_of_isFractionRing :=
inertiaDeg_eq_of_isFractionRing

theorem inertiaDeg_eq_of_isMaximal [q.LiesOver p] [p.IsMaximal] [q.IsMaximal] :
    q.inertiaDeg R = Module.finrank (R ⧸ p) (S ⧸ q) := by
  let : Field (R ⧸ p) := Quotient.field p
  let : Field (S ⧸ q) := Quotient.field q
  exact inertiaDeg_eq_of_isFractionRing p q (R ⧸ p) (S ⧸ q)

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_eq_of_isMaximal :=
  inertiaDeg_eq_of_isMaximal

theorem inertiaDeg'_eq_inertiaDeg [q.LiesOver p] [p.IsMaximal] [q.IsMaximal] :
    p.inertiaDeg' q = q.inertiaDeg R := by
  rw [inertiaDeg'_algebraMap, inertiaDeg_eq_of_isMaximal p q]

@[deprecated (since := "2026-07-03")] alias inertiaDeg_eq_inertiaDeg' := inertiaDeg'_eq_inertiaDeg

theorem inertiaDeg_tower [r.LiesOver q] :
    r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
    let := Localization.AtPrime.algebraOfLiesOver (r.under R) r
    let := Localization.AtPrime.algebraOfLiesOver (r.under R) q
    let := Localization.AtPrime.algebraOfLiesOver q r
    rw [inertiaDeg_def, inertiaDeg_eq (r.under R), inertiaDeg_eq q, eq_comm]
    apply Module.finrank_mul_finrank
  · rw [inertiaDeg_of_not_isPrime r R hr, inertiaDeg_of_not_isPrime r S hr, mul_zero]

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_tower := inertiaDeg_tower

theorem inertiaDeg_below_dvd [r.LiesOver q] :
    q.inertiaDeg R ∣ r.inertiaDeg R := by
  use r.inertiaDeg S
  rw [← inertiaDeg_tower]

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_below_dvd := inertiaDeg_below_dvd

theorem inertiaDeg_above_dvd [r.LiesOver q] :
    r.inertiaDeg S ∣ r.inertiaDeg R := by
  use q.inertiaDeg R
  rw [mul_comm, ← inertiaDeg_tower]

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_above_dvd := inertiaDeg_above_dvd

theorem inertiaDeg_below_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] :
    q.inertiaDeg R ≤ r.inertiaDeg R :=
  Nat.le_of_dvd (r.inertiaDeg_pos R) (q.inertiaDeg_below_dvd r)

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_below_le := inertiaDeg_below_le

theorem inertiaDeg_above_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] :
    r.inertiaDeg S ≤ r.inertiaDeg R :=
  Nat.le_of_dvd (r.inertiaDeg_pos R) (q.inertiaDeg_above_dvd r)

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_above_le := inertiaDeg_above_le

variable (R) in
open Pointwise in
@[simp]
theorem inertiaDeg_smul {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (g : G) : (g • q).inertiaDeg R = q.inertiaDeg R := by
  by_cases hq : q.IsPrime; swap
  · rw [inertiaDeg_of_not_isPrime, inertiaDeg_of_not_isPrime] <;> simpa
  · let p := q.under R
    let f₀ := MulSemiringAction.toAlgAut G R S g
    let := Localization.AtPrime.algebraOfLiesOver p q
    let := Localization.AtPrime.algebraOfLiesOver p (g • q)
    rw [inertiaDeg_eq p q, inertiaDeg_eq p (g • q)]
    let e₂ := Ideal.residueFieldAlgEquiv' p (g • q) q f₀.symm (comap_symm f₀.toRingEquiv).symm
    exact e₂.toLinearEquiv.finrank_eq

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_smul := inertiaDeg_smul

theorem cardQuot_pow_inertiaDeg [Module.Finite R S] [p.IsMaximal] [q.IsMaximal] [q.LiesOver p] :
    p.cardQuot ^ q.inertiaDeg R = q.cardQuot := by
  let _ : Field (R ⧸ p) := Quotient.field p
  rw [← inertiaDeg'_eq_inertiaDeg p q, inertiaDeg'_algebraMap p q]
  exact Module.natCard_eq_pow_finrank.symm

@[deprecated (since := "2026-07-03")] alias cardQuot_pow_inertiaDeg' := cardQuot_pow_inertiaDeg

theorem absNorm_pow_inertiaDeg [Module.Finite R S] [q.IsPrime] [q.LiesOver p]
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Free ℤ R] [Module.Free ℤ S] :
    p.absNorm ^ q.inertiaDeg R = q.absNorm := by
  by_cases hp : p = ⊥
  · subst hp
    simpa [eq_bot_of_liesOver_bot R q] using (inertiaDeg_pos q R).ne'
  have := isPrime_of_liesOver q p
  have := isMaximal_of_isPrime_of_ne_bot p hp
  have := IsMaximal.of_liesOver_isMaximal q p
  exact cardQuot_pow_inertiaDeg p q

@[deprecated (since := "2026-07-03")] alias absNorm_pow_inertiaDeg' := absNorm_pow_inertiaDeg

theorem natAbs_pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] (p : ℤ)
    (P : Ideal R) [P.IsPrime] [P.LiesOver (span {p})] :
    p.natAbs ^ P.inertiaDeg ℤ = absNorm P := by
  simpa using absNorm_pow_inertiaDeg (span {p}) P

@[deprecated (since := "2026-07-03")] alias natAbs_pow_inertiaDeg' := natAbs_pow_inertiaDeg

theorem pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] (p : ℕ)
    (P : Ideal R) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    p ^ P.inertiaDeg ℤ = absNorm P :=
  natAbs_pow_inertiaDeg p P

end

end Ideal
