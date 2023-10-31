/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.PowerSeries.Comp
import Mathlib.Data.Polynomial.Derivation

/-!
# Definitions

In this file we define an operation `d⁄dX` (differentiation)
on formal power series in one variable (over an arbitrary commutative semi-ring).

We prove the product rule and the chain rule for differentiation of formal power series.

Under suitable assumptions, we prove that two power series are equal if their derivatives
are equal and their constant terms are equal. This gives us a simple tool for proving
power series identities. For example, one can easily prove the power series identity
`exp ( log (1+X)) = 1+X` by differentiating twice. Several examples of this kind of
identity are contained in "Mathlib.RingTheory.PowerSeries.WellKnown".


## Main results

- `PowerSeries.derivative_mul`  : the product rule (Leibniz' rule) for differentiating.
- `PowerSeries.derivative_comp` : the chain rule for differentiating power series.
- `PowerSeries.derivative.ext`  : two power series are equal if they have the same derivatives
                                    and the same constant terms.

## Notation

- `PowerSeries.D R`     : the formal derivative `R⟦X⟧ → R⟦X⟧`
-/




open Polynomial Finset Derivation Algebra BigOperators


namespace PowerSeries

open Polynomial Nat

section CommutativeSemiring
variable {R} [CommSemiring R]


/--
The formal derivative of a power series in one variable.
This is defined here as a function, but will be packaged as a
derivation `D` on `R⟦X⟧`.
-/
noncomputable def derivativeFun (f : R⟦X⟧) : R⟦X⟧ := mk λ n ↦ coeff R (n + 1) f * (n + 1)

theorem coeff_derivativeFun (f : R⟦X⟧) (n : ℕ) :
    coeff R n f.derivativeFun = coeff R (n + 1) f * (n + 1) := by
  rw [derivativeFun, coeff_mk]

theorem derivativeFun_coe (f : R[X]) : (f : R⟦X⟧).derivativeFun = derivative f := by
  ext
  rw [coeff_derivativeFun, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_derivative]

theorem derivativeFun_add (f g : R⟦X⟧) :
    derivativeFun (f + g) = derivativeFun f + derivativeFun g := by
  ext
  rw [coeff_derivativeFun, map_add, map_add, coeff_derivativeFun, coeff_derivativeFun, add_mul]

theorem derivativeFun_C (r : R) : derivativeFun (C R r) = 0 := by
  ext n
  rw [coeff_derivativeFun, coeff_C]
  split_ifs with h
  · cases succ_ne_zero n h
  · rw [zero_mul, map_zero]

theorem trunc_derivativeFun (f : R⟦X⟧) (n : ℕ) :
    (trunc n f.derivativeFun : R⟦X⟧) = derivativeFun ↑(trunc (n + 1) f) := by
  ext d
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_derivativeFun, coeff_derivativeFun, Polynomial.coeff_coe, coeff_trunc, if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [coeff_derivativeFun, Polynomial.coeff_coe, coeff_trunc, if_neg this, zero_mul]

--A special case of `derivativeFun_mul`, used in its proof.
private theorem derivativeFun_coe_mul_coe (f g : R[X]) : derivativeFun (f * g : R⟦X⟧) =
    f * derivativeFun (g : R⟦X⟧) + g * derivativeFun (f : R⟦X⟧) := by
  rw [←Polynomial.coe_mul, derivativeFun_coe, derivative_mul,
    derivativeFun_coe, derivativeFun_coe, add_comm, mul_comm _ g,
    ←Polynomial.coe_mul, ←Polynomial.coe_mul, Polynomial.coe_add]

/-- Leibniz rule for formal power series.-/
theorem derivativeFun_mul (f g : R⟦X⟧) :
    derivativeFun (f * g) = f • g.derivativeFun + g • f.derivativeFun := by
  ext n
  have h₁ : n < n + 1 := lt_succ_self n
  have h₂ : n < n + 1 + 1 := Nat.lt_add_right _ _ _ h₁
  rw [coeff_derivativeFun, map_add, coeff_mul_eq_coeff_trunc_mul_trunc _ _ (lt_succ_self _),
    smul_eq_mul, smul_eq_mul, coeff_mul_eq_coeff_trunc_mul_trunc₂ g f.derivativeFun h₂ h₁,
    coeff_mul_eq_coeff_trunc_mul_trunc₂ f g.derivativeFun h₂ h₁,
    trunc_derivativeFun, trunc_derivativeFun, ←map_add, ←derivativeFun_coe_mul_coe,
    coeff_derivativeFun]

theorem derivativeFun_one : derivativeFun (1 : R⟦X⟧) = 0 := by
  rw [←map_one (C R), derivativeFun_C (1 : R)]

theorem derivativeFun_smul (r : R) (f : R⟦X⟧) : derivativeFun (r • f) = r • derivativeFun f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, derivativeFun_mul, derivativeFun_C, smul_zero, add_zero,
    smul_eq_mul]

end CommutativeSemiring

/-
Closing and reopening the section, because `R` needs to be an explicit argument of `D`.
-/

/--The formal derivative of a formal power series.-/
noncomputable def derivative (R) [CommSemiring R] : Derivation R R⟦X⟧ R⟦X⟧
where
  toFun             := derivativeFun
  map_add'          := derivativeFun_add
  map_smul'         := derivativeFun_smul
  map_one_eq_zero'  := derivativeFun_one
  leibniz'          := derivativeFun_mul

/--
The formal derivative of a formal power series.
-/
scoped notation "d⁄dX" => derivative

section CommutativeSemiring
variable {R} [CommSemiring R]

/-this can be proved by `simp`.-/
theorem derivative_mul {f g} : d⁄dX R (f * g) = f * d⁄dX R g + g * d⁄dX R f := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

/-`simp` can prove this.-/
theorem derivative_one : d⁄dX R 1 = 0 := derivativeFun_one

@[simp] theorem derivative_C (r : R) : d⁄dX R (C R r) = 0 := derivativeFun_C r

@[simp] theorem coeff_derivative (f : R⟦X⟧) (n : ℕ) :
    coeff R n (d⁄dX R f) = coeff R (n + 1) f * (n + 1) :=
  coeff_derivativeFun f n

theorem derivative_coe (f : R[X]) : d⁄dX R f = Polynomial.derivative f := derivativeFun_coe f

@[simp] theorem derivative_X : d⁄dX R (X : R⟦X⟧) = 1 := by
  ext
  rw [coeff_derivative, coeff_one, coeff_X, boole_mul]
  simp_rw [add_left_eq_self]
  split_ifs with h
  · rw [h, cast_zero, zero_add]
  · rfl

theorem trunc_derivative (f : R⟦X⟧) (n : ℕ) :
    trunc n (d⁄dX R f) = Polynomial.derivative (trunc (n + 1) f) := by
  apply Polynomial.coe_inj.mp
  rw [←derivative_coe]
  apply trunc_derivativeFun

theorem trunc_derivative' (f : R⟦X⟧) (n : ℕ) :
    trunc (n-1) (d⁄dX R f) = Polynomial.derivative (trunc n f) := by
  cases n with
  | zero =>
    simp only [zero_eq, ge_iff_le, tsub_eq_zero_of_le]
    rfl
  | succ n =>
    rw [succ_sub_one, trunc_derivative]

/--
A special case of the "chain rule" for formal power series in one variable:

  `D (f ∘ᶠ g) = (D f) ∘ᶠ g * D g`.

The more general case is `D_comp`.
-/
theorem derivative_coe_comp (f : R[X]) (g : R⟦X⟧) :
    d⁄dX R (f ∘ᶠ g) = (d⁄dX R f) ∘ᶠ g * d⁄dX R g := by
  rw [coe_comp_eq_aeval, Derivation.aeval, derivative_coe, coe_comp_eq_aeval, smul_eq_mul]

open Finset Finset.Nat
/--
The "chain rule" for formal power series in one variable:

  `D (f ∘ᶠ g) = (D f) ∘ᶠ g * D g`.
-/
theorem derivative_comp (f g : R⟦X⟧) (hf : f.HasComp g) (hDf : (d⁄dX R f).HasComp g) :
    d⁄dX R (f ∘ᶠ g) = d⁄dX R f ∘ᶠ g * d⁄dX R g := by
  ext n
  obtain ⟨N₁, hN₁⟩ := uniform_stable_of_HasComp hDf n
  obtain ⟨N₂, hN₂⟩ := hf (n+1)
  set N := max (N₁ + 1) N₂
  rw [coeff_derivative, coeff_comp_of_stable hf (N := N),
    ←coeff_derivative, derivative_coe_comp, coeff_mul, coeff_mul, sum_congr rfl]
  intro _ hxy
  congr 1
  rw [derivative_coe, ←trunc_derivative']
  symm
  apply coeff_comp_of_stable hDf
  · intro _ hm
    rw [tsub_le_iff_right] at hm
    apply hN₁
    exact antidiagonal.fst_le hxy
    have := le_of_max_le_left hm
    rwa [←succ_le_succ_iff]
  · intro _ hm
    apply hN₂
    apply le_of_max_le_right hm

/--
A special case of the "chain rule" for formal power series in one variable:

  `D (f ∘ᶠ g) = (D f) ∘ᶠ g * D g`.

The more general case is `D_comp`.
-/
theorem derivative_comp' {f g : R⟦X⟧} (hg : constantCoeff R g = 0) :
    d⁄dX R (f ∘ᶠ g) = d⁄dX R f ∘ᶠ g * d⁄dX R g := by
  apply derivative_comp <;>
  apply HasComp_of_constantCoeff_eq_zero (hg := hg)


end CommutativeSemiring




/-In the next lemma, we use `smul_right_inj`, which requires not only `no_smul_divisors ℕ R`, but
also cancellation of addition in `R`. For this reason, the next lemma is stated in the case that `R`
is a `CommRing`.-/

/-- If `f` and `g` have the same constant term and derivative, then they are equal.-/
theorem derivative.ext {R} [CommRing R] [NoZeroSMulDivisors ℕ R] {f g} (hD : d⁄dX R f = d⁄dX R g)
    (hc : constantCoeff R f = constantCoeff R g) : f = g := by
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff, hc]
  | succ n =>
    have equ : coeff R n (d⁄dX R f) = coeff R n (d⁄dX R g) := by rw [hD]
    rwa [coeff_derivative, coeff_derivative, ←cast_succ, mul_comm, ←nsmul_eq_mul,
      mul_comm, ←nsmul_eq_mul, smul_right_inj] at equ
    exact n.succ_ne_zero


@[simp] theorem derivative_inv {R} [CommRing R] (f : R⟦X⟧ˣ) :
    d⁄dX R ↑(f⁻¹) = -((f⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ 2 * d⁄dX R f := by
  apply Derivation.leibniz_of_mul_eq_one
  simp only [Units.inv_eq_val_inv, Units.inv_mul]


@[simp] theorem derivative_invOf {R} [CommRing R] (f : R⟦X⟧) [Invertible f] :
    d⁄dX R (⅟ f) = - (⅟ f) ^ 2 * d⁄dX R f := by
  rw [Derivation.leibniz_invOf, smul_eq_mul]

/-
The following theorem is stated only in the case that
`R` is a field. This is because there is currently no
instance of `Inv R⟦X⟧` for more general base rings `R`.
-/
@[simp] theorem derivative_inv' {R} [Field R] (f : R⟦X⟧) : d⁄dX R f⁻¹ = -f⁻¹ ^ 2 * d⁄dX R f := by
  by_cases constantCoeff R f = 0
  · suffices : f⁻¹ = 0
    rw [this, pow_two, zero_mul, neg_zero, zero_mul, map_zero]
    rwa [MvPowerSeries.inv_eq_zero]
  apply Derivation.leibniz_of_mul_eq_one
  exact PowerSeries.inv_mul_cancel (h := h)

end PowerSeries
