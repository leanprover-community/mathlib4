/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Algebraic elements and integral elements

This file relates algebraic and integral elements of an algebra, by proving every integral element
is algebraic and that every algebraic element over a field is integral.

## Main results

* `IsIntegral.isAlgebraic`, `Algebra.IsIntegral.isAlgebraic`: integral implies algebraic.
* `isAlgebraic_iff_isIntegral`, `Algebra.isAlgebraic_iff_isIntegral`: integral iff algebraic
  over a field.
* `IsAlgebraic.of_finite`, `Algebra.IsAlgebraic.of_finite`: finite-dimensional (as module) implies
  algebraic.
* `exists_integral_multiple`: an algebraic element has a multiple which is integral
-/

assert_not_exists LocalRing

universe u v w

open Polynomial

section zero_ne_one

variable {R : Type u} {S : Type*} {A : Type v} [CommRing R]
variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]
variable [IsScalarTower R S A]

/-- An integral element of an algebra is algebraic. -/
theorem IsIntegral.isAlgebraic [Nontrivial R] {x : A} : IsIntegral R x → IsAlgebraic R x :=
  fun ⟨p, hp, hpx⟩ => ⟨p, hp.ne_zero, hpx⟩

instance Algebra.IsIntegral.isAlgebraic [Nontrivial R] [Algebra.IsIntegral R A] :
    Algebra.IsAlgebraic R A := ⟨fun a ↦ (Algebra.IsIntegral.isIntegral a).isAlgebraic⟩

end zero_ne_one

section Field

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral. -/
theorem isAlgebraic_iff_isIntegral {x : A} : IsAlgebraic K x ↔ IsIntegral K x := by
  refine ⟨?_, IsIntegral.isAlgebraic⟩
  rintro ⟨p, hp, hpx⟩
  refine ⟨_, monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [← aeval_def, map_mul, hpx, zero_mul]

protected theorem Algebra.isAlgebraic_iff_isIntegral :
    Algebra.IsAlgebraic K A ↔ Algebra.IsIntegral K A := by
  rw [Algebra.isAlgebraic_def, Algebra.isIntegral_def,
      forall_congr' fun _ ↦ isAlgebraic_iff_isIntegral]

alias ⟨IsAlgebraic.isIntegral, _⟩ := isAlgebraic_iff_isIntegral

/-- This used to be an `alias` of `Algebra.isAlgebraic_iff_isIntegral` but that would make
`Algebra.IsAlgebraic K A` an explicit parameter instead of instance implicit. -/
protected instance Algebra.IsAlgebraic.isIntegral [Algebra.IsAlgebraic K A] :
    Algebra.IsIntegral K A := Algebra.isAlgebraic_iff_isIntegral.mp ‹_›

variable (K) in
theorem Algebra.IsAlgebraic.of_isIntegralClosure (B C : Type*)
    [CommRing B] [CommRing C] [Algebra K B] [Algebra K C] [Algebra B C]
    [IsScalarTower K B C] [IsIntegralClosure B K C] : Algebra.IsAlgebraic K B :=
  Algebra.isAlgebraic_iff_isIntegral.mpr (IsIntegralClosure.isIntegral_algebra K C)

end Field

section

variable (K L : Type*) {R S A : Type*}

section Ring

section Field

variable [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

theorem IsAlgebraic.of_finite (e : A) [FiniteDimensional K A] : IsAlgebraic K e :=
  (IsIntegral.of_finite K e).isAlgebraic

variable (A)

/-- A field extension is algebraic if it is finite. -/
@[stacks 09GG "first part"]
instance Algebra.IsAlgebraic.of_finite [FiniteDimensional K A] : Algebra.IsAlgebraic K A :=
  (IsIntegral.of_finite K A).isAlgebraic

end Field

end Ring

section CommRing

variable {K L} [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
@[stacks 09GJ]
protected theorem Algebra.IsAlgebraic.trans
    [L_alg : Algebra.IsAlgebraic K L] [A_alg : Algebra.IsAlgebraic L A] :
    Algebra.IsAlgebraic K A := by
  rw [Algebra.isAlgebraic_iff_isIntegral] at L_alg A_alg ⊢
  exact Algebra.IsIntegral.trans L

end CommRing

section Field

variable {K L} [Field K] [Ring A] [Algebra K A]

/-- If `K` is a field, `r : A` and `f : K[X]`, then `Polynomial.aeval r f` is
transcendental over `K` if and only if `r` and `f` are both transcendental over `K`.
See also `Transcendental.aeval_of_transcendental` and `Transcendental.of_aeval`. -/
@[simp]
theorem transcendental_aeval_iff {r : A} {f : K[X]} :
    Transcendental K (Polynomial.aeval r f) ↔ Transcendental K r ∧ Transcendental K f := by
  refine ⟨fun h ↦ ⟨?_, h.of_aeval⟩, fun ⟨h1, h2⟩ ↦ h1.aeval_of_transcendental h2⟩
  rw [Transcendental] at h ⊢
  contrapose! h
  rw [isAlgebraic_iff_isIntegral] at h ⊢
  exact .of_mem_of_fg _ h.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)

variable [Field L] [Algebra K L]

theorem AlgHom.bijective [FiniteDimensional K L] (ϕ : L →ₐ[K] L) : Function.Bijective ϕ :=
  (Algebra.IsAlgebraic.of_finite K L).algHom_bijective ϕ

variable (K L) in
/-- Bijection between algebra equivalences and algebra homomorphisms -/
noncomputable abbrev algEquivEquivAlgHom [FiniteDimensional K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) :=
  Algebra.IsAlgebraic.algEquivEquivAlgHom K L

end Field

end

variable {R S : Type*} [CommRing R] [CommRing S]

theorem exists_integral_multiple [Algebra R S] {z : S} (hz : IsAlgebraic R z)
    (inj : ∀ x, algebraMap R S x = 0 → x = 0) :
    ∃ᵉ (x : integralClosure R S) (y ≠ (0 : R)), algebraMap R S y * z = x := by
  rcases hz with ⟨p, p_ne_zero, px⟩
  set a := p.leadingCoeff
  have a_ne_zero : a ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.mp p_ne_zero
  have x_integral : IsIntegral R (algebraMap R S a * z) :=
    ⟨p.integralNormalization, monic_integralNormalization p_ne_zero,
      integralNormalization_aeval_eq_zero px inj⟩
  exact ⟨⟨_, x_integral⟩, a, a_ne_zero, rfl⟩
