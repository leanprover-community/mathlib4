/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Inertia

/-!
# Inertia degree

Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined
to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`.

## Main definitions

* `Ideal.inertiaDeg' q R`: The inertia degree of `q` over `R`.

## Main statements

* `inertiaDeg_eq_inertiaDeg'`: The inertia degree agrees with the usual definition in the case of
  maximal ideals.
* `inertiaDeg'_tower`: Inertia degree is multiplicative in towers.
-/

@[expose] public section

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open Classical in
/-- Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined
to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.inertiaDeg`. -/
noncomputable def inertiaDeg' : ℕ :=
  if _ : q.IsPrime then
    letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    Module.finrank (q.under R).ResidueField q.ResidueField else 0

theorem inertiaDeg'_def [hq : q.IsPrime]
    [Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra (q.under R) q] :
    q.inertiaDeg' R = Module.finrank (q.under R).ResidueField q.ResidueField := by
  convert dif_pos hq
  simp [Algebra.algebra_ext_iff, Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]

theorem inertiaDeg'_of_not_isPrime (hq : ¬ q.IsPrime) : q.inertiaDeg' R = 0 :=
  dif_neg hq

end

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) (r : Ideal T)

theorem inertiaDeg'_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    q.inertiaDeg' R = Module.finrank p.ResidueField q.ResidueField := by
  have := Ideal.over_def q p
  subst this
  exact inertiaDeg'_def q R

theorem inertiaDeg_eq_inertiaDeg' [q.LiesOver p] [p.IsMaximal] [q.IsMaximal] :
    p.inertiaDeg q = q.inertiaDeg' R := by
  let : Field (R ⧸ p) := Quotient.field p
  let : Field (S ⧸ q) := Quotient.field q
  let := Localization.AtPrime.algebraOfLiesOver p q
  rw [inertiaDeg'_eq p q, inertiaDeg_algebraMap]
  let f := (algebraMap (S ⧸ q) q.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ q))
  let g := (algebraMap p.ResidueField q.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField)
  have h : f = g := by ext; simp [f, g, ← IsScalarTower.algebraMap_apply]
  let : Algebra (R ⧸ p) q.ResidueField := f.toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ q) q.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField q.ResidueField := IsScalarTower.of_algebraMap_eq' h
  rw [← mul_one (Module.finrank (R ⧸ p) (S ⧸ q)),
    ← Module.finrank_of_bijective_algebraMap (bijective_algebraMap_quotient_residueField q),
    Module.finrank_mul_finrank, ← Module.finrank_mul_finrank (R ⧸ p) p.ResidueField q.ResidueField,
    Module.finrank_of_bijective_algebraMap (bijective_algebraMap_quotient_residueField p), one_mul]

theorem inertiaDeg'_tower [r.LiesOver q] :
    r.inertiaDeg' R = q.inertiaDeg' R * r.inertiaDeg' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
    let := Localization.AtPrime.algebraOfLiesOver (r.under R) r
    let := Localization.AtPrime.algebraOfLiesOver (r.under R) q
    let := Localization.AtPrime.algebraOfLiesOver q r
    rw [inertiaDeg'_def, inertiaDeg'_eq (r.under R), inertiaDeg'_eq q, eq_comm]
    apply Module.finrank_mul_finrank
  · rw [inertiaDeg'_of_not_isPrime r R hr, inertiaDeg'_of_not_isPrime r S hr, mul_zero]

end

end Ideal
