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

- `not_isLocalRing_of_nontrivial_pi`: for an index type `ι` with least two elements and
  an indexed family of (semi)rings `R : ι → Type*`, the indexed product (semi)ring
  `Π i, R i` is not local.
- `not_isLocalRing_of_prod_of_nontrivial`: the product of two nontrivial (semi)rings is not
  local.
- `not_isLocalRing_iff_nontrivial_maximalSpectrum`: a commutative (semi)ring is not local iff
  it has nontrivial maximal spectrum.
- `not_isLocalRing_iff_exist_maximal_ne`: a commutative (semi)ring is not local iff it has
  two distinct maximal ideals.
- `exists_surjective_of_not_isLocalRing`: there exists a surjective ring homomorphism from
  a non-local commutative ring onto a product of two fields.

-/

namespace IsLocalRing

theorem not_isLocalRing_def {R : Type*} [Semiring R] {a b : R} (ha : ¬IsUnit a) (hb : ¬IsUnit b)
    (hab : a + b = 1) : ¬IsLocalRing R :=
  fun _ ↦ hb <| (isUnit_or_isUnit_of_add_one hab).resolve_left ha

theorem not_isLocalRing_of_nontrivial_pi {ι : Type*} [Nontrivial ι] [DecidableEq ι] (R : ι → Type*)
    [∀ i, Semiring (R i)] [∀ i, Nontrivial (R i)] : ¬IsLocalRing (Π i, R i) :=
  let ⟨i₁, i₂, hi⟩ := exists_pair_ne ι
  have ha : ¬IsUnit (fun i ↦ if i = i₁ then 0 else 1 : Π i, R i) :=
    fun h ↦ not_isUnit_zero (M₀ := R i₁) (by simpa using h.map (Pi.evalRingHom R i₁))
  have hb : ¬IsUnit (fun i ↦ if i = i₁ then 1 else 0 : Π i, R i) :=
    fun h ↦ not_isUnit_zero (M₀ := R i₂) (by simpa [hi.symm] using h.map (Pi.evalRingHom R i₂))
  not_isLocalRing_def ha hb (by ext; dsimp; split <;> simp)

theorem not_isLocalRing_of_prod_of_nontrivial (R₁ R₂ : Type*) [Semiring R₁] [Semiring R₂]
    [Nontrivial R₁] [Nontrivial R₂] : ¬IsLocalRing (R₁ × R₂) :=
  have ha : ¬IsUnit ((1, 0) : R₁ × R₂) :=
    fun h ↦ not_isUnit_zero (M₀ := R₁) (by simpa using h.map (RingHom.snd R₁ R₂))
  have hb : ¬IsUnit ((0, 1) : R₁ × R₂) :=
    fun h ↦ not_isUnit_zero (M₀ := R₂) (by simpa using h.map (RingHom.fst R₁ R₂))
  not_isLocalRing_def ha hb (by simp)

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- For a non-local, nontrivial, commutative (semi)ring, the maximal spectrum is non-trivial. -/
theorem nontrivial_maximalSpectrum_of_not_isLocalRing [Nontrivial R]
    (h : ¬IsLocalRing R) : Nontrivial (MaximalSpectrum R) :=
  not_subsingleton_iff_nontrivial.mp fun _ ↦ h of_singleton_maximalSpectrum

/-- If the maximal spectrum of a commutative (semi)ring `R` is nontrivial then `R` is not local. -/
theorem not_isLocalRing_of_nontrivial_maximalSpectrum [Nontrivial (MaximalSpectrum R)] :
    ¬IsLocalRing R := fun _ ↦ not_subsingleton_iff_nontrivial.mpr ‹_› inferInstance

/-- A nontrivial commutative (semi)ring is not local if and only if it has a nontrivial
maximal spectrum. -/
theorem not_isLocalRing_iff_nontrivial_maximalSpectrum [Nontrivial R] :
    ¬IsLocalRing R ↔ Nontrivial (MaximalSpectrum R) :=
  ⟨nontrivial_maximalSpectrum_of_not_isLocalRing,
    by apply not_isLocalRing_of_nontrivial_maximalSpectrum⟩

/-- A non-local commutative (semi)ring has two distinct maximal ideals. -/
theorem exist_maximal_ne_of_not_isLocalRing [Nontrivial R] (h : ¬IsLocalRing R) :
    ∃ m₁ m₂ : Ideal R, m₁.IsMaximal ∧ m₂.IsMaximal ∧ m₁ ≠ m₂ :=
  let ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩, hm₁m₂⟩ := nontrivial_maximalSpectrum_of_not_isLocalRing h
  ⟨m₁, m₂, ⟨hm₁, hm₂, by by_contra; apply hm₁m₂; congr⟩⟩

/-- A commutative (semi)ring is not local if it has two distinct maximal ideals. -/
theorem not_isLocalRing_of_exist_maximal_ne {m₁ m₂ : Ideal R}
    [h₁ : m₁.IsMaximal] [h₂ : m₂.IsMaximal] (h : m₁ ≠ m₂) : ¬IsLocalRing R :=
  fun _ ↦ h <| (eq_maximalIdeal h₁).trans (eq_maximalIdeal h₂).symm

/-- A commutative (semi)ring is not local if and only if it has two distinct maximal ideals. -/
theorem not_isLocalRing_iff_exist_maximal_ne [Nontrivial R] :
    ¬IsLocalRing R ↔ ∃ m₁ m₂ : Ideal R, m₁.IsMaximal ∧ m₂.IsMaximal ∧ m₁ ≠ m₂ :=
  ⟨exist_maximal_ne_of_not_isLocalRing, fun ⟨_, _, _, _, h⟩ ↦ not_isLocalRing_of_exist_maximal_ne h⟩

end CommSemiring

/-- There exists a surjective ring homomorphism from a non-local commutative ring onto a product
of two fields. -/
theorem exists_surjective_of_not_isLocalRing.{u} {R : Type u} [CommRing R] [Nontrivial R]
    (h : ¬IsLocalRing R) :
    ∃ (K₁ K₂ : Type u) (_ : Field K₁) (_ : Field K₂) (f : R →+* K₁ × K₂),
      Function.Surjective f := by
  /- get two different maximal ideals and project on the product of quotients -/
  obtain ⟨m₁, m₂, _, _, hm₁m₂⟩ := exist_maximal_ne_of_not_isLocalRing h
  let e := Ideal.quotientInfEquivQuotientProd m₁ m₂ <| Ideal.isCoprime_of_isMaximal hm₁m₂
  let f := e.toRingHom.comp <| Ideal.Quotient.mk (m₁ ⊓ m₂)
  use R ⧸ m₁, R ⧸ m₂, Ideal.Quotient.field m₁, Ideal.Quotient.field m₂, f
  apply Function.Surjective.comp e.surjective Ideal.Quotient.mk_surjective

end IsLocalRing
