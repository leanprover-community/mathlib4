/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Inertia degree

Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined
to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`.
-/

@[expose] public section

namespace Ideal

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open Classical in
/-- Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined
to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.inertiaDeg`. -/
noncomputable def inertiaDeg' : ℕ :=
  if _ : q.IsPrime then Module.finrank (q.under R).ResidueField q.ResidueField else 0

theorem inertiaDeg'_def [q.IsPrime] :
    q.inertiaDeg' R = Module.finrank (q.under R).ResidueField q.ResidueField :=
  dif_pos _

theorem inertiaDeg'_of_not_isPrime (hq : ¬ q.IsPrime) : q.inertiaDeg' R = 0 :=
  dif_neg hq

theorem inertiaDeg'_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [h : q.LiesOver p] [q.IsPrime] [p.IsPrime] :
    q.inertiaDeg' R = Module.finrank p.ResidueField q.ResidueField := by
  rw [inertiaDeg'_def]
  convert rfl <;> exact LiesOver.over

theorem inertiaDeg'_tower'
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) (r : Ideal T) [h : r.LiesOver q] :
    r.inertiaDeg' R = q.inertiaDeg' R * r.inertiaDeg' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
    rw [inertiaDeg'_eq (r.under R), inertiaDeg'_eq (r.under R), inertiaDeg'_eq q, eq_comm]
    apply Module.finrank_mul_finrank
  · rw [inertiaDeg'_of_not_isPrime r R hr, inertiaDeg'_of_not_isPrime r S hr, mul_zero]

end Ideal
