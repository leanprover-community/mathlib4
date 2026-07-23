/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib

set_option linter.minImports true

/-!
# Lowest-balanced-face arithmetic for GMC(2)

This module formalizes three finite-dimensional algebraic steps from the
lowest-balanced-face proof of `the lowest-balanced-face theorem`:

* every balanced multiplicity vector supported on one tilted face has the
  same radial height at fixed mass;
* using any positive amount of a strict off-face term makes that height
  strictly larger, hence at least one larger when both heights are integral;
* on a tilted face, charge determines the exact exponent pair, so an exact
  monomial support has no hidden collision after projection to charge.

The number-theoretic Kummer/Lucas/Frobenius layer is deliberately outside
this small kernel.  There are no analytic or asymptotic assumptions here.
-/

open Finset

namespace GMC2FrobeniusFace

variable {ι : Type*}

/-- Charge of the exponent pair `(a i, b i)`.  Integer exponents make the
lemma reusable after embedding the natural polynomial exponents. -/
def charge (a b : ι → ℤ) (i : ι) : ℤ := a i - b i

/-- The affine height exposed by the dual slope `lambda`. -/
def tiltedHeight (a b : ι → ℤ) (lambda : ℚ) (i : ι) : ℚ :=
  (a i : ℚ) - lambda * (charge a b i : ℚ)

/-- Total rational mass of a multiplicity vector on a finite index set. -/
def massQ (F : Finset ι) (r : ι → ℕ) : ℚ :=
  ∑ i ∈ F, (r i : ℚ)

/-- Total charge of a multiplicity vector, viewed in `ℚ`. -/
def totalChargeQ (a b : ι → ℤ) (F : Finset ι) (r : ι → ℕ) : ℚ :=
  ∑ i ∈ F, (r i : ℚ) * (charge a b i : ℚ)

/-- Wick/radial height `sum r_i a_i`, viewed in `ℚ`. -/
def radialHeightQ (a : ι → ℤ) (F : Finset ι) (r : ι → ℕ) : ℚ :=
  ∑ i ∈ F, (r i : ℚ) * (a i : ℚ)

/-- A balanced channel supported on one tilted face has height `delta` times
its mass.  Thus all face channels of a fixed mass have one common Wick height. -/
theorem balanced_height_eq_on_face [DecidableEq ι]
    (a b : ι → ℤ) (lambda delta : ℚ) (F : Finset ι) (r : ι → ℕ)
    (hface : ∀ i ∈ F, tiltedHeight a b lambda i = delta)
    (hbalanced : totalChargeQ a b F r = 0) :
    radialHeightQ a F r = delta * massQ F r := by
  have hterm : ∀ i ∈ F,
      (r i : ℚ) * (a i : ℚ) =
        delta * (r i : ℚ) + lambda * ((r i : ℚ) * (charge a b i : ℚ)) := by
    intro i hi
    have hf := hface i hi
    unfold tiltedHeight at hf
    linear_combination (r i : ℚ) * hf
  calc
    radialHeightQ a F r =
        ∑ i ∈ F, (delta * (r i : ℚ) +
          lambda * ((r i : ℚ) * (charge a b i : ℚ))) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i hi
    _ = delta * massQ F r + lambda * totalChargeQ a b F r := by
          simp only [massQ, totalChargeQ, Finset.sum_add_distrib, Finset.mul_sum]
    _ = delta * massQ F r := by rw [hbalanced]; ring

/-- If every support point lies on or above the tilted face and a channel uses
a positive multiplicity of one strictly off-face point, its balanced radial
height is strictly larger than the face height at the same mass. -/
theorem balanced_height_strict_of_off_face [DecidableEq ι]
    (a b : ι → ℤ) (lambda delta : ℚ) (F : Finset ι) (r : ι → ℕ)
    (hlower : ∀ i ∈ F, delta ≤ tiltedHeight a b lambda i)
    (hbalanced : totalChargeQ a b F r = 0)
    (j : ι) (hj : j ∈ F) (hrj : 0 < r j)
    (hstrict : delta < tiltedHeight a b lambda j) :
    delta * massQ F r < radialHeightQ a F r := by
  have hle : ∀ i ∈ F,
      delta * (r i : ℚ) ≤
        (r i : ℚ) * (a i : ℚ) -
          lambda * ((r i : ℚ) * (charge a b i : ℚ)) := by
    intro i hi
    calc
      delta * (r i : ℚ) ≤ tiltedHeight a b lambda i * (r i : ℚ) :=
        mul_le_mul_of_nonneg_right (hlower i hi) (by positivity)
      _ = (r i : ℚ) * (a i : ℚ) -
          lambda * ((r i : ℚ) * (charge a b i : ℚ)) := by
            unfold tiltedHeight
            ring
  have hlt : delta * (r j : ℚ) <
      (r j : ℚ) * (a j : ℚ) -
        lambda * ((r j : ℚ) * (charge a b j : ℚ)) := by
    calc
      delta * (r j : ℚ) < tiltedHeight a b lambda j * (r j : ℚ) :=
        mul_lt_mul_of_pos_right hstrict (by exact_mod_cast hrj)
      _ = (r j : ℚ) * (a j : ℚ) -
          lambda * ((r j : ℚ) * (charge a b j : ℚ)) := by
            unfold tiltedHeight
            ring
  have hsum :
      (∑ i ∈ F, delta * (r i : ℚ)) <
        ∑ i ∈ F, ((r i : ℚ) * (a i : ℚ) -
          lambda * ((r i : ℚ) * (charge a b i : ℚ))) :=
    Finset.sum_lt_sum hle ⟨j, hj, hlt⟩
  calc
    delta * massQ F r = ∑ i ∈ F, delta * (r i : ℚ) := by
      simp [massQ, Finset.mul_sum]
    _ < ∑ i ∈ F, ((r i : ℚ) * (a i : ℚ) -
          lambda * ((r i : ℚ) * (charge a b i : ℚ))) := hsum
    _ = radialHeightQ a F r - lambda * totalChargeQ a b F r := by
      simp [radialHeightQ, totalChargeQ, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = radialHeightQ a F r := by rw [hbalanced]; ring

/-- The strict rational inequality above becomes the exact integer gap used
in the factorial layer: a strictly larger integral height is at least `A0+1`. -/
theorem integer_gap_of_strict_height {A0 A : ℤ}
    (hstrict : (A0 : ℚ) < (A : ℚ)) : A0 + 1 ≤ A := by
  have : A0 < A := by exact_mod_cast hstrict
  omega

/-- Consumer form of the off-face lemma when the reference and channel
heights have already been identified with integers `A0` and `A`. -/
theorem off_face_integer_gap [DecidableEq ι]
    (a b : ι → ℤ) (lambda delta : ℚ) (F : Finset ι) (r : ι → ℕ)
    (hlower : ∀ i ∈ F, delta ≤ tiltedHeight a b lambda i)
    (hbalanced : totalChargeQ a b F r = 0)
    (j : ι) (hj : j ∈ F) (hrj : 0 < r j)
    (hstrict : delta < tiltedHeight a b lambda j)
    (A0 A : ℤ)
    (hA0 : delta * massQ F r = (A0 : ℚ))
    (hA : radialHeightQ a F r = (A : ℚ)) :
    A0 + 1 ≤ A := by
  apply integer_gap_of_strict_height
  rw [← hA0, ← hA]
  exact balanced_height_strict_of_off_face
    a b lambda delta F r hlower hbalanced j hj hrj hstrict

/-- On one tilted face, equality of charges forces equality of both exact
exponents.  This is the algebraic reason the face Laurent polynomial has no
hidden coefficient collision after projecting exact support to charge. -/
theorem exponent_pair_eq_of_same_charge_on_face
    (a b : ι → ℤ) (lambda delta : ℚ) {i j : ι}
    (hi : tiltedHeight a b lambda i = delta)
    (hj : tiltedHeight a b lambda j = delta)
    (hq : charge a b i = charge a b j) :
    (a i, b i) = (a j, b j) := by
  have hqQ : (charge a b i : ℚ) = (charge a b j : ℚ) := by
    exact_mod_cast hq
  have haQ : (a i : ℚ) = (a j : ℚ) := by
    unfold tiltedHeight at hi hj
    rw [hqQ] at hi
    linarith
  have ha : a i = a j := by exact_mod_cast haQ
  have hb : b i = b j := by
    unfold charge at hq
    omega
  exact Prod.ext ha hb

/-- Collision-free projection statement for an exact monomial support:
restriction of charge to a tilted face is injective. -/
theorem charge_injective_on_face [DecidableEq ι]
    (a b : ι → ℤ) (lambda delta : ℚ) (F : Finset ι)
    (hexact : Function.Injective (fun i => (a i, b i)))
    (hface : ∀ i ∈ F, tiltedHeight a b lambda i = delta) :
    Function.Injective (fun i : {i // i ∈ F} => charge a b i) := by
  intro i j hq
  apply Subtype.ext
  apply hexact
  exact exponent_pair_eq_of_same_charge_on_face a b lambda delta
    (hface i i.property) (hface j j.property) hq

end GMC2FrobeniusFace

