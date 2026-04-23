/-
Copyright (c) 2022 Justin Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Thomas
-/
module

public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Init
import Mathlib.RingTheory.Ideal.Lattice
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
# Annihilating Ideal

Given a commutative ring `R` and an `R`-algebra `A`,
every element `a : A` defines
an ideal `Polynomial.annIdeal a ⊆ R[X]`.
Simply put, this is the set of polynomials `p` where
the polynomial evaluation `p(a)` is 0.

## Special case where the ground ring is a field

In the special case that `R` is a field, we use the notation `R = 𝕜`.
Here `𝕜[X]` is a PID, so there is a polynomial `g ∈ Polynomial.annIdeal a`
which generates the ideal. We show that if this generator is
chosen to be monic, then it is the minimal polynomial of `a`,
as defined in `FieldTheory.Minpoly`.

## Special case: endomorphism algebra

Given an `R`-module `M` (`[AddCommGroup M] [Module R M]`)
there are some common specializations which may be more familiar.
* Example 1: `A = M →ₗ[R] M`, the endomorphism algebra of an `R`-module M.
* Example 2: `A = n × n` matrices with entries in `R`.
-/

@[expose] public section


open Polynomial

namespace Polynomial

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (R) in
/-- `annIdeal R a` is the *annihilating ideal* of all `p : R[X]` such that `p(a) = 0`.

The informal notation `p(a)` stands for `Polynomial.aeval a p`.
Again informally, the annihilating ideal of `a` is
`{ p ∈ R[X] | p(a) = 0 }`. This is an ideal in `R[X]`.
The formal definition uses the kernel of the aeval map. -/
noncomputable def annIdeal (a : A) : Ideal R[X] :=
  RingHom.ker ((aeval a).toRingHom : R[X] →+* A)

/-- It is useful to refer to ideal membership sometimes
and the annihilation condition other times. -/
theorem mem_annIdeal_iff_aeval_eq_zero {a : A} {p : R[X]} : p ∈ annIdeal R a ↔ aeval a p = 0 :=
  Iff.rfl

end Semiring

section Field

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
variable (𝕜)

open Submodule

/-- `annIdealGenerator 𝕜 a` is the monic generator of `annIdeal 𝕜 a`
if one exists, otherwise `0`.

Since `𝕜[X]` is a principal ideal domain there is a polynomial `g` such that
`span 𝕜 {g} = annIdeal a`. This picks some generator.
We prefer the monic generator of the ideal. -/
noncomputable def annIdealGenerator (a : A) : 𝕜[X] :=
  let g := IsPrincipal.generator <| annIdeal 𝕜 a
  g * C g.leadingCoeff⁻¹

section

variable {𝕜}

@[simp]
theorem annIdealGenerator_eq_zero_iff {a : A} : annIdealGenerator 𝕜 a = 0 ↔ annIdeal 𝕜 a = ⊥ := by
  simp only [annIdealGenerator, mul_eq_zero, IsPrincipal.eq_bot_iff_generator_eq_zero,
    Polynomial.C_eq_zero, inv_eq_zero, Polynomial.leadingCoeff_eq_zero, or_self_iff]

end

/-- `annIdealGenerator 𝕜 a` is indeed a generator. -/
@[simp]
theorem span_singleton_annIdealGenerator (a : A) :
    Ideal.span {annIdealGenerator 𝕜 a} = annIdeal 𝕜 a := by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, annIdealGenerator_eq_zero_iff.mp h, Set.singleton_zero, Ideal.span_zero]
  · rw [annIdealGenerator, Ideal.span_singleton_mul_right_unit, Ideal.span_singleton_generator]
    apply Polynomial.isUnit_C.mpr
    apply IsUnit.mk0
    apply inv_eq_zero.not.mpr
    apply Polynomial.leadingCoeff_eq_zero.not.mpr
    apply (mul_ne_zero_iff.mp h).1

/-- The annihilating ideal generator is a member of the annihilating ideal. -/
theorem annIdealGenerator_mem (a : A) : annIdealGenerator 𝕜 a ∈ annIdeal 𝕜 a :=
  Ideal.mul_mem_right _ _ (Submodule.IsPrincipal.generator_mem _)

theorem mem_iff_eq_smul_annIdealGenerator {p : 𝕜[X]} (a : A) :
    p ∈ annIdeal 𝕜 a ↔ ∃ s : 𝕜[X], p = s • annIdealGenerator 𝕜 a := by
  simp_rw [@eq_comm _ p, ← mem_span_singleton, ← span_singleton_annIdealGenerator 𝕜 a]

/-- The generator we chose for the annihilating ideal is monic when the ideal is non-zero. -/
theorem monic_annIdealGenerator (a : A) (hg : annIdealGenerator 𝕜 a ≠ 0) :
    Monic (annIdealGenerator 𝕜 a) :=
  monic_mul_leadingCoeff_inv (mul_ne_zero_iff.mp hg).1

/-! We are working toward showing the generator of the annihilating ideal
in the field case is the minimal polynomial. We are going to use a uniqueness
theorem of the minimal polynomial.

This is the first condition: it must annihilate the original element `a : A`. -/


theorem annIdealGenerator_aeval_eq_zero (a : A) : aeval a (annIdealGenerator 𝕜 a) = 0 :=
  mem_annIdeal_iff_aeval_eq_zero.mp (annIdealGenerator_mem 𝕜 a)

variable {𝕜}

theorem mem_iff_annIdealGenerator_dvd {p : 𝕜[X]} {a : A} :
    p ∈ annIdeal 𝕜 a ↔ annIdealGenerator 𝕜 a ∣ p := by
  rw [← Ideal.mem_span_singleton, span_singleton_annIdealGenerator]

/-- The generator of the annihilating ideal has minimal degree among
the non-zero members of the annihilating ideal -/
theorem degree_annIdealGenerator_le_of_mem (a : A) (p : 𝕜[X]) (hp : p ∈ annIdeal 𝕜 a)
    (hpn0 : p ≠ 0) : degree (annIdealGenerator 𝕜 a) ≤ degree p :=
  degree_le_of_dvd (mem_iff_annIdealGenerator_dvd.1 hp) hpn0

variable (𝕜)

/-- The generator of the annihilating ideal is the minimal polynomial. -/
theorem annIdealGenerator_eq_minpoly (a : A) : annIdealGenerator 𝕜 a = minpoly 𝕜 a := by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, minpoly.eq_zero]
    rintro ⟨p, p_monic, hp : aeval a p = 0⟩
    refine p_monic.ne_zero (Ideal.mem_bot.mp ?_)
    simpa only [annIdealGenerator_eq_zero_iff.mp h] using mem_annIdeal_iff_aeval_eq_zero.mpr hp
  · exact minpoly.unique _ _ (monic_annIdealGenerator _ _ h) (annIdealGenerator_aeval_eq_zero _ _)
      fun q q_monic hq =>
        degree_annIdealGenerator_le_of_mem a q (mem_annIdeal_iff_aeval_eq_zero.mpr hq)
          q_monic.ne_zero

/-- If a monic generates the annihilating ideal, it must match our choice
of the annihilating ideal generator. -/
theorem monic_generator_eq_minpoly (a : A) (p : 𝕜[X]) (p_monic : p.Monic)
    (p_gen : Ideal.span {p} = annIdeal 𝕜 a) : annIdealGenerator 𝕜 a = p := by
  by_cases h : p = 0
  · rwa [h, annIdealGenerator_eq_zero_iff, ← p_gen, Ideal.span_singleton_eq_bot.mpr]
  · rw [← span_singleton_annIdealGenerator, Ideal.span_singleton_eq_span_singleton] at p_gen
    rw [eq_comm]
    apply eq_of_monic_of_associated p_monic _ p_gen
    apply monic_annIdealGenerator _ _ ((Associated.ne_zero_iff p_gen).mp h)

theorem span_minpoly_eq_annihilator {M} [AddCommGroup M] [Module 𝕜 M] (f : Module.End 𝕜 M) :
    Ideal.span {minpoly 𝕜 f} = Module.annihilator 𝕜[X] (Module.AEval' f) := by
  rw [← annIdealGenerator_eq_minpoly, span_singleton_annIdealGenerator]; ext
  rw [mem_annIdeal_iff_aeval_eq_zero, DFunLike.ext_iff, Module.mem_annihilator]; rfl

end Field

end Polynomial
