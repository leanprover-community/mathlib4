/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!

# Maximal ideal of local rings

We prove basic properties of the maximal ideal of a local ring.

-/

variable {R S K : Type*}
section CommSemiring

variable [CommSemiring R]

namespace IsLocalRing

variable [IsLocalRing R]

@[simp]
theorem mem_maximalIdeal (x) : x ∈ maximalIdeal R ↔ x ∈ nonunits R :=
  Iff.rfl

variable (R)

instance maximalIdeal.isMaximal : (maximalIdeal R).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    apply h
    exact isUnit_one
  · intro I x _ hx H
    rw [mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] at hx
    rcases hx with ⟨u, rfl⟩
    simpa using I.mul_mem_left (↑u⁻¹) H

theorem maximal_ideal_unique : ∃! I : Ideal R, I.IsMaximal :=
  ⟨maximalIdeal R, maximalIdeal.isMaximal R, fun I hI =>
    hI.eq_of_le (maximalIdeal.isMaximal R).1.1 fun _ hx => hI.1.1 ∘ I.eq_top_of_isUnit_mem hx⟩

variable {R}

theorem eq_maximalIdeal {I : Ideal R} (hI : I.IsMaximal) : I = maximalIdeal R :=
  ExistsUnique.unique (maximal_ideal_unique R) hI <| maximalIdeal.isMaximal R

/-- The maximal spectrum of a local ring is a singleton. -/
instance : Unique (MaximalSpectrum R) where
  default := ⟨maximalIdeal R, maximalIdeal.isMaximal R⟩
  uniq := fun I ↦ MaximalSpectrum.ext_iff.mpr <| eq_maximalIdeal I.isMaximal

theorem le_maximalIdeal {J : Ideal R} (hJ : J ≠ ⊤) : J ≤ maximalIdeal R := by
  rcases Ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩
  rwa [← eq_maximalIdeal hM1]

/--
An element `x` of a commutative local semiring is not contained in the maximal ideal
iff it is a unit.
-/
theorem not_mem_maximalIdeal {x : R} : x ∉ maximalIdeal R ↔ IsUnit x := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]

theorem isField_iff_maximalIdeal_eq : IsField R ↔ maximalIdeal R = ⊥ :=
  not_iff_not.mp
    ⟨Ring.ne_bot_of_isMaximal_of_not_isField inferInstance, fun h =>
      Ring.not_isField_iff_exists_prime.mpr ⟨_, h, Ideal.IsMaximal.isPrime' _⟩⟩

end IsLocalRing

@[deprecated (since := "2024-11-11")]
alias LocalRing.maximal_ideal_unique := IsLocalRing.maximal_ideal_unique

@[deprecated (since := "2024-11-11")]
alias LocalRing.eq_maximalIdeal := IsLocalRing.eq_maximalIdeal

@[deprecated (since := "2024-11-11")]
alias LocalRing.le_maximalIdeal := IsLocalRing.le_maximalIdeal

@[deprecated (since := "2024-11-11")]
alias LocalRing.mem_maximalIdeal := IsLocalRing.mem_maximalIdeal

@[deprecated (since := "2024-11-11")]
alias LocalRing.not_mem_maximalIdeal := IsLocalRing.not_mem_maximalIdeal

@[deprecated (since := "2024-11-11")]
alias LocalRing.isField_iff_maximalIdeal_eq := IsLocalRing.isField_iff_maximalIdeal_eq

end CommSemiring

section CommRing

variable [CommRing R]

namespace IsLocalRing

variable [IsLocalRing R]

theorem maximalIdeal_le_jacobson (I : Ideal R) :
    IsLocalRing.maximalIdeal R ≤ I.jacobson :=
  le_sInf fun _ ⟨_, h⟩ => le_of_eq (IsLocalRing.eq_maximalIdeal h).symm

theorem jacobson_eq_maximalIdeal (I : Ideal R) (h : I ≠ ⊤) :
    I.jacobson = IsLocalRing.maximalIdeal R :=
  le_antisymm (sInf_le ⟨le_maximalIdeal h, maximalIdeal.isMaximal R⟩)
              (maximalIdeal_le_jacobson I)

end IsLocalRing

@[deprecated (since := "2024-11-11")]
alias LocalRing.maximalIdeal_le_jacobson := IsLocalRing.maximalIdeal_le_jacobson

@[deprecated (since := "2024-11-11")]
alias LocalRing.jacobson_eq_maximalIdeal := IsLocalRing.jacobson_eq_maximalIdeal

end CommRing

namespace IsLocalRing

section

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

theorem ker_eq_maximalIdeal [Field K] (φ : R →+* K) (hφ : Function.Surjective φ) :
    RingHom.ker φ = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal <| (RingHom.ker_isMaximal_of_surjective φ) hφ

end

end IsLocalRing

theorem IsLocalRing.maximalIdeal_eq_bot {R : Type*} [Field R] : IsLocalRing.maximalIdeal R = ⊥ :=
  IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField R)

@[deprecated (since := "2024-11-09")]
alias LocalRing.ker_eq_maximalIdeal := IsLocalRing.ker_eq_maximalIdeal

@[deprecated (since := "2024-11-09")]
alias LocalRing.maximalIdeal_eq_bot := IsLocalRing.maximalIdeal_eq_bot

section Nilrad_max_localization

open Ideal

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S] {M : Submonoid R}

-- TODO: Make this an `instance`
theorem IsLocalRing.of_nilradical_isMaximal [h : (nilradical R).IsMaximal] :
    IsLocalRing R := by
  refine IsLocalRing.of_unique_max_ideal ⟨nilradical R, h, fun I hI ↦ ?_⟩
  rw [nilradical_eq_sInf] at h ⊢
  exact (IsMaximal.eq_of_le h hI.ne_top (sInf_le hI.isPrime)).symm

@[deprecated (since := "2024-11-09")]
alias LocalRing.of_nilradical_isMaximal := IsLocalRing.of_nilradical_isMaximal

/--
Let `S` be the localization of a commutative semiring `R` at a submonoid `M` that does not
contain 0. If the nilradical of `R` is maximal then there is a `R`-algebra isomorphism between
`R` and `S`. -/
noncomputable def localizationEquivSelfOfNilradicalIsMaximal [h : (nilradical R).IsMaximal]
    (h' : (0 : R) ∉ M) [IsLocalization M S] : R ≃ₐ[R] S := by
  have (m) (hm : m ∈ M) : IsUnit m := by
    haveI := IsLocalRing.of_nilradical_isMaximal (h := h)
    apply IsLocalRing.not_mem_maximalIdeal.mp
    rw [← IsLocalRing.eq_maximalIdeal h]
    rintro ⟨k, hk⟩
    rw [← hk] at h'
    exact h' (Submonoid.pow_mem M hm k)
  exact IsLocalization.atUnits _ _ this

end Nilrad_max_localization
