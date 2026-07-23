/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Jacobson.Ring

set_option linter.minImports true

/-!
# Direct integral specialization for GMC(2)

This module gives the finite-type alternative to choosing primes in a number
field.  A nontrivial finite-type `ℤ`-algebra has a maximal quotient.  Zariski's
lemma over the Jacobson ring `ℤ` makes that quotient finite as a `ℤ`-module;
integrality then rules out characteristic zero.  Its ring characteristic is
therefore prime, and the quotient is a finite field.

The specialization is an actual ring homomorphism from the entire algebra.
Consequently all algebraic zero relations are preserved, while units remain
units (and hence remain nonzero).
-/

open Finset

namespace GMC2.IntegralSpecialization

universe u

/-- The algebraic data of a finite-field specialization of `A`.

The field structure is exposed separately by `ResidueData.fieldStructure`, so the
structure stores only proof data and does not install a global noncomputable
instance. -/
structure ResidueData (A : Type u) [CommRing A] where
  point : MaximalSpectrum A
  p : ℕ
  prime : p.Prime
  charP : CharP (A ⧸ point.asIdeal) p
  finiteOverInt : Module.Finite ℤ (A ⧸ point.asIdeal)
  finiteResidue : Finite (A ⧸ point.asIdeal)

namespace ResidueData

variable {A : Type u} [CommRing A]

/-- The residue type attached to a specialization. -/
abbrev ResidueField (D : ResidueData A) := A ⧸ D.point.asIdeal

/-- The quotient field structure attached to the maximal ideal.  Consumers
may install it locally with `letI := D.fieldStructure`. -/
@[reducible] noncomputable def fieldStructure (D : ResidueData A) : Field D.ResidueField :=
  Ideal.Quotient.field D.point.asIdeal

/-- The specialization homomorphism `A → A/P`. -/
def map (D : ResidueData A) : A →+* D.ResidueField :=
  Ideal.Quotient.mk D.point.asIdeal

/-- Every zero relation is preserved by specialization. -/
theorem map_eq_zero_of_eq_zero (D : ResidueData A) {x : A} (hx : x = 0) :
    D.map x = 0 := by
  rw [hx, map_zero]

/-- Finite sums that vanish before specialization also vanish afterward. -/
theorem map_sum_eq_zero (D : ResidueData A) {ι : Type*} (S : Finset ι) (f : ι → A)
    (h : ∑ i ∈ S, f i = 0) :
    ∑ i ∈ S, D.map (f i) = 0 := by
  rw [← map_sum, h, map_zero]

end ResidueData

/-- The Jacobson radical of the zero ideal of `ℤ` is zero.

For a nonzero integer `x`, choose a rational prime larger than `|x|`.  The
corresponding maximal ideal cannot contain `x`, so `x` is not in the
intersection of all maximal ideals. -/
theorem int_jacobson_bot :
    Ideal.jacobson (⊥ : Ideal ℤ) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  rw [Ideal.mem_bot]
  by_contra hx0
  obtain ⟨p, hpLower, hp⟩ :=
    Nat.exists_infinite_primes (x.natAbs + 1)
  letI : Fact p.Prime := ⟨hp⟩
  have hxSpan : x ∈ Ideal.span {(p : ℤ)} := by
    rw [Ideal.jacobson, Ideal.mem_sInf] at hx
    exact hx ⟨bot_le, inferInstance⟩
  rw [Ideal.mem_span_singleton] at hxSpan
  have hpAbs : p ∣ x.natAbs := Int.natCast_dvd.mp hxSpan
  have hxAbsPos : 0 < x.natAbs := Int.natAbs_pos.mpr hx0
  have hpLe : p ≤ x.natAbs := Nat.le_of_dvd hxAbsPos hpAbs
  have hxLt : x.natAbs < p :=
    (Nat.lt_succ_self x.natAbs).trans_le hpLower
  exact (not_le_of_gt hxLt) hpLe

/-- `ℤ` is Jacobson.  Nonzero prime ideals are maximal because `ℤ` is a PID;
the remaining prime ideal is handled by `int_jacobson_bot`. -/
theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hPbot : P = ⊥
  · simpa [hPbot] using int_jacobson_bot
  · letI : P.IsPrime := hP
    letI : P.IsMaximal := IsPrime.to_maximal_ideal hPbot
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- A finite-type `ℤ`-algebra admits a finite-field specialization preserving
any prescribed finite family of units.

The maximal ideal does not depend on the family: units survive in every
quotient.  The family is retained in the statement because this is the form
needed by the GMC(2) coefficient-specialization consumer. -/
theorem exists_preserving_units
    {A ι : Type*} [CommRing A] [Nontrivial A]
    [Algebra.FiniteType ℤ A]
    (S : Finset ι) (u : ι → A) (hu : ∀ i ∈ S, IsUnit (u i)) :
    ∃ D : ResidueData A,
      (∀ i ∈ S, IsUnit (D.map (u i))) ∧
      ∀ i ∈ S, D.map (u i) ≠ 0 := by
  classical
  obtain ⟨I, hImax⟩ := Ideal.exists_maximal A
  let P : MaximalSpectrum A := ⟨I, hImax⟩
  letI : Field (A ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  letI : IsJacobsonRing ℤ := int_isJacobsonRing
  have hmodule : Module.Finite ℤ (A ⧸ P.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ P.asIdeal)
  letI : Module.Finite ℤ (A ⧸ P.asIdeal) := hmodule
  have hchar : ringChar (A ⧸ P.asIdeal) ≠ 0 := by
    intro hzero
    letI : CharZero (A ⧸ P.asIdeal) :=
      (CharP.ringChar_zero_iff_CharZero
        (R := A ⧸ P.asIdeal)).mp hzero
    haveI : (⊥ : Ideal (A ⧸ P.asIdeal)).IsMaximal :=
      Ideal.bot_isMaximal
    exact Ideal.IsMaximal.ne_bot_of_isIntegral_int
      (⊥ : Ideal (A ⧸ P.asIdeal)) rfl
  have hp : (ringChar (A ⧸ P.asIdeal)).Prime :=
    CharP.char_prime_of_ne_zero (A ⧸ P.asIdeal) hchar
  have htorsionAdd : AddMonoid.IsTorsion (A ⧸ P.asIdeal) := by
    intro x
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨ringChar (A ⧸ P.asIdeal), Nat.pos_of_ne_zero hchar, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul (A ⧸ P.asIdeal)]
    simp
  have htorsion : Module.IsTorsion ℤ (A ⧸ P.asIdeal) :=
    AddMonoid.isTorsion_iff_isTorsion_int.mp htorsionAdd
  have hfinite : Finite (A ⧸ P.asIdeal) :=
    Module.finite_of_fg_torsion (A ⧸ P.asIdeal) htorsion
  let D : ResidueData A :=
    { point := P
      p := ringChar (A ⧸ P.asIdeal)
      prime := hp
      charP := inferInstance
      finiteOverInt := hmodule
      finiteResidue := hfinite }
  refine ⟨D, ?_, ?_⟩
  · intro i hiS
    exact (hu i hiS).map D.map
  · intro i hiS
    exact ((hu i hiS).map D.map).ne_zero

end GMC2.IntegralSpecialization

