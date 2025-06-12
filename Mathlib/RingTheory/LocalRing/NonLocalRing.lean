/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Prod
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!

# Non-local rings

This file gathers some results about non-local rings.

## Main results

- `not_isLocalRing_of_nontrivial_pi`: for an index type `ι` with at least two elements and
  an indexed family of (semi)rings `R : ι → Type*`, the indexed product (semi)ring
  `Π i, R i` is not local.
- `not_isLocalRing_of_prod_of_nontrivial`: the product of two nontrivial (semi)rings is not
  local.
- `not_isLocalRing_tfae`: the following conditions are equivalent for a commutative (semi)ring `R`:
    * `R` is not local,
    * the maximal spectrum of `R` is nontrivial,
    * `R` has two distinct maximal ideals.
- `exists_surjective_of_not_isLocalRing`: there exists a surjective ring homomorphism from
  a non-local commutative ring onto a product of two fields.

-/

namespace IsLocalRing

/-- If two non-units sum to 1 in a (semi)ring `R` then `R` is not local. -/
theorem not_isLocalRing_def {R : Type*} [Semiring R] {a b : R} (ha : ¬IsUnit a) (hb : ¬IsUnit b)
    (hab : a + b = 1) : ¬IsLocalRing R :=
  fun _ ↦ hb <| (isUnit_or_isUnit_of_add_one hab).resolve_left ha

/-- For an index type `ι` with at least two elements and an indexed family of (semi)rings
`R : ι → Type*`, the indexed product (semi)ring `Π i, R i` is not local. -/
theorem not_isLocalRing_of_nontrivial_pi {ι : Type*} [Nontrivial ι] (R : ι → Type*)
    [∀ i, Semiring (R i)] [∀ i, Nontrivial (R i)] : ¬IsLocalRing (Π i, R i) := by
  classical
  let ⟨i₁, i₂, hi⟩ := exists_pair_ne ι
  have ha : ¬IsUnit (fun i ↦ if i = i₁ then 0 else 1 : Π i, R i) :=
    fun h ↦ not_isUnit_zero (M₀ := R i₁) (by simpa using h.map (Pi.evalRingHom R i₁))
  have hb : ¬IsUnit (fun i ↦ if i = i₁ then 1 else 0 : Π i, R i) :=
    fun h ↦ not_isUnit_zero (M₀ := R i₂) (by simpa [hi.symm] using h.map (Pi.evalRingHom R i₂))
  exact not_isLocalRing_def ha hb (by ext; dsimp; split <;> simp)

/-- The product of two nontrivial (semi)rings is not local. -/
theorem not_isLocalRing_of_prod_of_nontrivial (R₁ R₂ : Type*) [Semiring R₁] [Semiring R₂]
    [Nontrivial R₁] [Nontrivial R₂] : ¬IsLocalRing (R₁ × R₂) :=
  have ha : ¬IsUnit ((1, 0) : R₁ × R₂) :=
    fun h ↦ not_isUnit_zero (M₀ := R₁) (by simpa using h.map (RingHom.snd R₁ R₂))
  have hb : ¬IsUnit ((0, 1) : R₁ × R₂) :=
    fun h ↦ not_isUnit_zero (M₀ := R₂) (by simpa using h.map (RingHom.fst R₁ R₂))
  not_isLocalRing_def ha hb (by simp)

/-- The following conditions are equivalent for a commutative (semi)ring `R`:
    * `R` is not local,
    * the maximal spectrum of `R` is nontrivial,
    * `R` has two distinct maximal ideals.
-/
theorem not_isLocalRing_tfae {R : Type*} [CommSemiring R] [Nontrivial R] :
    List.TFAE [
      ¬IsLocalRing R,
      Nontrivial (MaximalSpectrum R),
      ∃ m₁ m₂ : Ideal R, m₁.IsMaximal ∧ m₂.IsMaximal ∧ m₁ ≠ m₂] := by
  tfae_have 1 → 2
  | h => not_subsingleton_iff_nontrivial.mp fun _ ↦ h of_singleton_maximalSpectrum
  tfae_have 2 → 3
  | ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩, h⟩ => ⟨m₁, m₂, ⟨hm₁, hm₂, fun _ ↦ h (by congr)⟩⟩
  tfae_have 3 → 1
  | ⟨m₁, m₂, ⟨hm₁, hm₂, h⟩⟩ => fun _ ↦ h <| (eq_maximalIdeal hm₁).trans (eq_maximalIdeal hm₂).symm
  tfae_finish

/-- There exists a surjective ring homomorphism from a non-local commutative ring onto a product
of two fields. -/
theorem exists_surjective_of_not_isLocalRing.{u} {R : Type u} [CommRing R] [Nontrivial R]
    (h : ¬IsLocalRing R) :
    ∃ (K₁ K₂ : Type u) (_ : Field K₁) (_ : Field K₂) (f : R →+* K₁ × K₂),
      Function.Surjective f := by
  /- get two different maximal ideals and project on the product of quotients -/
  obtain ⟨m₁, m₂, _, _, hm₁m₂⟩ := (not_isLocalRing_tfae.out 0 2).mp h
  let e := Ideal.quotientInfEquivQuotientProd m₁ m₂ <| Ideal.isCoprime_of_isMaximal hm₁m₂
  let f := e.toRingHom.comp <| Ideal.Quotient.mk (m₁ ⊓ m₂)
  use R ⧸ m₁, R ⧸ m₂, Ideal.Quotient.field m₁, Ideal.Quotient.field m₂, f
  apply Function.Surjective.comp e.surjective Ideal.Quotient.mk_surjective

end IsLocalRing
