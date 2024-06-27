/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPowerSeries.Basic

#align_import ring_theory.power_series.basic from "leanprover-community/mathlib"@"2d5739b61641ee4e7e53eca5688a08f66f2e6a60"

/-!
# Formal power series (in one variable)

This file defines (univariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

Formal power series in one variable are defined from multivariate
power series as `PowerSeries R := MvPowerSeries Unit R`.

The file sets up the (semi)ring structure on univariate power series.

We provide the natural inclusion from polynomials to formal power series.

Additional results can be found in:
* `Mathlib.RingTheory.PowerSeries.Trunc`, truncation of power series;
* `Mathlib.RingTheory.PowerSeries.Inverse`, about inverses of power series,
and the fact that power series over a local ring form a local ring;
* `Mathlib.RingTheory.PowerSeries.Order`, the order of a power series at 0,
and application to the fact that power series over an integral domain
form an integral domain.

## Implementation notes

Because of its definition,
  `PowerSeries R := MvPowerSeries Unit R`.
a lot of proofs and properties from the multivariate case
can be ported to the single variable case.
However, it means that formal power series are indexed by `Unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they were indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.

-/

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

/-- Formal power series over a coefficient type `R` -/
def PowerSeries (R : Type*) :=
  MvPowerSeries Unit R
#align power_series PowerSeries

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section

-- Porting note: not available in Lean 4
-- local reducible PowerSeries


/--
`R⟦X⟧` is notation for `PowerSeries R`,
the semiring of formal power series in one variable over a semiring `R`.
-/
scoped notation:9000 R "⟦X⟧" => PowerSeries R

instance [Inhabited R] : Inhabited R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [Zero R] : Zero R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [AddMonoid R] : AddMonoid R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [AddGroup R] : AddGroup R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [AddCommMonoid R] : AddCommMonoid R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [AddCommGroup R] : AddCommGroup R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [Semiring R] : Semiring R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [CommSemiring R] : CommSemiring R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [Ring R] : Ring R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [CommRing R] : CommRing R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [Nontrivial R] : Nontrivial R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance {A} [Semiring R] [AddCommMonoid A] [Module R A] : Module R A⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance {A S} [Semiring R] [Semiring S] [AddCommMonoid A] [Module R A] [Module S A] [SMul R S]
    [IsScalarTower R S A] : IsScalarTower R S A⟦X⟧ :=
  Pi.isScalarTower

instance {A} [Semiring A] [CommSemiring R] [Algebra R A] : Algebra R A⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

end

section Semiring

variable (R) [Semiring R]

/-- The `n`th coefficient of a formal power series. -/
def coeff (n : ℕ) : R⟦X⟧ →ₗ[R] R :=
  MvPowerSeries.coeff R (single () n)
#align power_series.coeff PowerSeries.coeff

/-- The `n`th monomial with coefficient `a` as formal power series. -/
def monomial (n : ℕ) : R →ₗ[R] R⟦X⟧ :=
  MvPowerSeries.monomial R (single () n)
#align power_series.monomial PowerSeries.monomial

variable {R}

theorem coeff_def {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) : coeff R n = MvPowerSeries.coeff R s := by
  erw [coeff, ← h, ← Finsupp.unique_single s]
#align power_series.coeff_def PowerSeries.coeff_def

/-- Two formal power series are equal if all their coefficients are equal. -/
@[ext]
theorem ext {φ ψ : R⟦X⟧} (h : ∀ n, coeff R n φ = coeff R n ψ) : φ = ψ :=
  MvPowerSeries.ext fun n => by
    rw [← coeff_def]
    · apply h
    rfl
#align power_series.ext PowerSeries.ext

/-- Two formal power series are equal if all their coefficients are equal. -/
theorem ext_iff {φ ψ : R⟦X⟧} : φ = ψ ↔ ∀ n, coeff R n φ = coeff R n ψ :=
  ⟨fun h n => congr_arg (coeff R n) h, ext⟩
#align power_series.ext_iff PowerSeries.ext_iff

instance [Subsingleton R] : Subsingleton R⟦X⟧ := by
  simp only [subsingleton_iff, ext_iff]
  exact fun _ _ _ ↦ (subsingleton_iff).mp (by infer_instance) _ _

/-- Constructor for formal power series. -/
def mk {R} (f : ℕ → R) : R⟦X⟧ := fun s => f (s ())
#align power_series.mk PowerSeries.mk

@[simp]
theorem coeff_mk (n : ℕ) (f : ℕ → R) : coeff R n (mk f) = f n :=
  congr_arg f Finsupp.single_eq_same
#align power_series.coeff_mk PowerSeries.coeff_mk

theorem coeff_monomial (m n : ℕ) (a : R) : coeff R m (monomial R n a) = if m = n then a else 0 :=
  calc
    coeff R m (monomial R n a) = _ := MvPowerSeries.coeff_monomial _ _ _
    _ = if m = n then a else 0 := by simp only [Finsupp.unique_single_eq_iff]

#align power_series.coeff_monomial PowerSeries.coeff_monomial

theorem monomial_eq_mk (n : ℕ) (a : R) : monomial R n a = mk fun m => if m = n then a else 0 :=
  ext fun m => by rw [coeff_monomial, coeff_mk]
#align power_series.monomial_eq_mk PowerSeries.monomial_eq_mk

@[simp]
theorem coeff_monomial_same (n : ℕ) (a : R) : coeff R n (monomial R n a) = a :=
  MvPowerSeries.coeff_monomial_same _ _
#align power_series.coeff_monomial_same PowerSeries.coeff_monomial_same

@[simp]
theorem coeff_comp_monomial (n : ℕ) : (coeff R n).comp (monomial R n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n
#align power_series.coeff_comp_monomial PowerSeries.coeff_comp_monomial

variable (R)

/-- The constant coefficient of a formal power series. -/
def constantCoeff : R⟦X⟧ →+* R :=
  MvPowerSeries.constantCoeff Unit R
#align power_series.constant_coeff PowerSeries.constantCoeff

/-- The constant formal power series. -/
def C : R →+* R⟦X⟧ :=
  MvPowerSeries.C Unit R
set_option linter.uppercaseLean3 false in
#align power_series.C PowerSeries.C

variable {R}

/-- The variable of the formal power series ring. -/
def X : R⟦X⟧ :=
  MvPowerSeries.X ()
set_option linter.uppercaseLean3 false in
#align power_series.X PowerSeries.X

theorem commute_X (φ : R⟦X⟧) : Commute φ X :=
  MvPowerSeries.commute_X _ _
set_option linter.uppercaseLean3 false in
#align power_series.commute_X PowerSeries.commute_X

@[simp]
theorem coeff_zero_eq_constantCoeff : ⇑(coeff R 0) = constantCoeff R := by
  rw [coeff, Finsupp.single_zero]
  rfl
#align power_series.coeff_zero_eq_constant_coeff PowerSeries.coeff_zero_eq_constantCoeff

theorem coeff_zero_eq_constantCoeff_apply (φ : R⟦X⟧) : coeff R 0 φ = constantCoeff R φ := by
  rw [coeff_zero_eq_constantCoeff]
#align power_series.coeff_zero_eq_constant_coeff_apply PowerSeries.coeff_zero_eq_constantCoeff_apply

@[simp]
theorem monomial_zero_eq_C : ⇑(monomial R 0) = C R := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [monomial, Finsupp.single_zero, MvPowerSeries.monomial_zero_eq_C]
set_option linter.uppercaseLean3 false in
#align power_series.monomial_zero_eq_C PowerSeries.monomial_zero_eq_C

theorem monomial_zero_eq_C_apply (a : R) : monomial R 0 a = C R a := by simp
set_option linter.uppercaseLean3 false in
#align power_series.monomial_zero_eq_C_apply PowerSeries.monomial_zero_eq_C_apply

theorem coeff_C (n : ℕ) (a : R) : coeff R n (C R a : R⟦X⟧) = if n = 0 then a else 0 := by
  rw [← monomial_zero_eq_C_apply, coeff_monomial]
set_option linter.uppercaseLean3 false in
#align power_series.coeff_C PowerSeries.coeff_C

@[simp]
theorem coeff_zero_C (a : R) : coeff R 0 (C R a) = a := by
  rw [coeff_C, if_pos rfl]
set_option linter.uppercaseLean3 false in
#align power_series.coeff_zero_C PowerSeries.coeff_zero_C

theorem coeff_ne_zero_C {a : R} {n : ℕ} (h : n ≠ 0) : coeff R n (C R a) = 0 := by
  rw [coeff_C, if_neg h]

@[simp]
theorem coeff_succ_C {a : R} {n : ℕ} : coeff R (n + 1) (C R a) = 0 :=
  coeff_ne_zero_C n.succ_ne_zero

theorem C_injective : Function.Injective (C R) := by
  intro a b H
  have := (ext_iff (φ := C R a) (ψ := C R b)).mp H 0
  rwa [coeff_zero_C, coeff_zero_C] at this

protected theorem subsingleton_iff : Subsingleton R⟦X⟧ ↔ Subsingleton R := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [subsingleton_iff] at h ⊢
  exact fun a b ↦ C_injective (h (C R a) (C R b))

theorem X_eq : (X : R⟦X⟧) = monomial R 1 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align power_series.X_eq PowerSeries.X_eq

theorem coeff_X (n : ℕ) : coeff R n (X : R⟦X⟧) = if n = 1 then 1 else 0 := by
  rw [X_eq, coeff_monomial]
set_option linter.uppercaseLean3 false in
#align power_series.coeff_X PowerSeries.coeff_X

@[simp]
theorem coeff_zero_X : coeff R 0 (X : R⟦X⟧) = 0 := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [coeff, Finsupp.single_zero, X, MvPowerSeries.coeff_zero_X]
set_option linter.uppercaseLean3 false in
#align power_series.coeff_zero_X PowerSeries.coeff_zero_X

@[simp]
theorem coeff_one_X : coeff R 1 (X : R⟦X⟧) = 1 := by rw [coeff_X, if_pos rfl]
set_option linter.uppercaseLean3 false in
#align power_series.coeff_one_X PowerSeries.coeff_one_X

@[simp]
theorem X_ne_zero [Nontrivial R] : (X : R⟦X⟧) ≠ 0 := fun H => by
  simpa only [coeff_one_X, one_ne_zero, map_zero] using congr_arg (coeff R 1) H
set_option linter.uppercaseLean3 false in
#align power_series.X_ne_zero PowerSeries.X_ne_zero

theorem X_pow_eq (n : ℕ) : (X : R⟦X⟧) ^ n = monomial R n 1 :=
  MvPowerSeries.X_pow_eq _ n
set_option linter.uppercaseLean3 false in
#align power_series.X_pow_eq PowerSeries.X_pow_eq

theorem coeff_X_pow (m n : ℕ) : coeff R m ((X : R⟦X⟧) ^ n) = if m = n then 1 else 0 := by
  rw [X_pow_eq, coeff_monomial]
set_option linter.uppercaseLean3 false in
#align power_series.coeff_X_pow PowerSeries.coeff_X_pow

@[simp]
theorem coeff_X_pow_self (n : ℕ) : coeff R n ((X : R⟦X⟧) ^ n) = 1 := by
  rw [coeff_X_pow, if_pos rfl]
set_option linter.uppercaseLean3 false in
#align power_series.coeff_X_pow_self PowerSeries.coeff_X_pow_self

@[simp]
theorem coeff_one (n : ℕ) : coeff R n (1 : R⟦X⟧) = if n = 0 then 1 else 0 :=
  coeff_C n 1
#align power_series.coeff_one PowerSeries.coeff_one

theorem coeff_zero_one : coeff R 0 (1 : R⟦X⟧) = 1 :=
  coeff_zero_C 1
#align power_series.coeff_zero_one PowerSeries.coeff_zero_one

theorem coeff_mul (n : ℕ) (φ ψ : R⟦X⟧) :
    coeff R n (φ * ψ) = ∑ p ∈ antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ := by
  -- `rw` can't see that `PowerSeries = MvPowerSeries Unit`, so use `.trans`
  refine (MvPowerSeries.coeff_mul _ φ ψ).trans ?_
  rw [Finsupp.antidiagonal_single, Finset.sum_map]
  rfl
#align power_series.coeff_mul PowerSeries.coeff_mul

@[simp]
theorem coeff_mul_C (n : ℕ) (φ : R⟦X⟧) (a : R) : coeff R n (φ * C R a) = coeff R n φ * a :=
  MvPowerSeries.coeff_mul_C _ φ a
set_option linter.uppercaseLean3 false in
#align power_series.coeff_mul_C PowerSeries.coeff_mul_C

@[simp]
theorem coeff_C_mul (n : ℕ) (φ : R⟦X⟧) (a : R) : coeff R n (C R a * φ) = a * coeff R n φ :=
  MvPowerSeries.coeff_C_mul _ φ a
set_option linter.uppercaseLean3 false in
#align power_series.coeff_C_mul PowerSeries.coeff_C_mul

@[simp]
theorem coeff_smul {S : Type*} [Semiring S] [Module R S] (n : ℕ) (φ : PowerSeries S) (a : R) :
    coeff S n (a • φ) = a • coeff S n φ :=
  rfl
#align power_series.coeff_smul PowerSeries.coeff_smul

@[simp]
theorem constantCoeff_smul {S : Type*} [Semiring S] [Module R S] (φ : PowerSeries S) (a : R) :
    constantCoeff S (a • φ) = a • constantCoeff S φ :=
  rfl

theorem smul_eq_C_mul (f : R⟦X⟧) (a : R) : a • f = C R a * f := by
  ext
  simp
set_option linter.uppercaseLean3 false in
#align power_series.smul_eq_C_mul PowerSeries.smul_eq_C_mul

@[simp]
theorem coeff_succ_mul_X (n : ℕ) (φ : R⟦X⟧) : coeff R (n + 1) (φ * X) = coeff R n φ := by
  simp only [coeff, Finsupp.single_add]
  convert φ.coeff_add_mul_monomial (single () n) (single () 1) _
  rw [mul_one]; rfl
set_option linter.uppercaseLean3 false in
#align power_series.coeff_succ_mul_X PowerSeries.coeff_succ_mul_X

@[simp]
theorem coeff_succ_X_mul (n : ℕ) (φ : R⟦X⟧) : coeff R (n + 1) (X * φ) = coeff R n φ := by
  simp only [coeff, Finsupp.single_add, add_comm n 1]
  convert φ.coeff_add_monomial_mul (single () 1) (single () n) _
  rw [one_mul]; rfl
set_option linter.uppercaseLean3 false in
#align power_series.coeff_succ_X_mul PowerSeries.coeff_succ_X_mul

@[simp]
theorem constantCoeff_C (a : R) : constantCoeff R (C R a) = a :=
  rfl
set_option linter.uppercaseLean3 false in
#align power_series.constant_coeff_C PowerSeries.constantCoeff_C

@[simp]
theorem constantCoeff_comp_C : (constantCoeff R).comp (C R) = RingHom.id R :=
  rfl
set_option linter.uppercaseLean3 false in
#align power_series.constant_coeff_comp_C PowerSeries.constantCoeff_comp_C

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem constantCoeff_zero : constantCoeff R 0 = 0 :=
  rfl
#align power_series.constant_coeff_zero PowerSeries.constantCoeff_zero

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem constantCoeff_one : constantCoeff R 1 = 1 :=
  rfl
#align power_series.constant_coeff_one PowerSeries.constantCoeff_one

@[simp]
theorem constantCoeff_X : constantCoeff R X = 0 :=
  MvPowerSeries.coeff_zero_X _
set_option linter.uppercaseLean3 false in
#align power_series.constant_coeff_X PowerSeries.constantCoeff_X

@[simp]
theorem constantCoeff_mk {f : ℕ → R} : constantCoeff R (mk f) = f 0 := rfl

theorem coeff_zero_mul_X (φ : R⟦X⟧) : coeff R 0 (φ * X) = 0 := by simp
set_option linter.uppercaseLean3 false in
#align power_series.coeff_zero_mul_X PowerSeries.coeff_zero_mul_X

theorem coeff_zero_X_mul (φ : R⟦X⟧) : coeff R 0 (X * φ) = 0 := by simp
set_option linter.uppercaseLean3 false in
#align power_series.coeff_zero_X_mul PowerSeries.coeff_zero_X_mul

theorem constantCoeff_surj : Function.Surjective (constantCoeff R) :=
  fun r => ⟨(C R) r, constantCoeff_C r⟩

-- The following section duplicates the API of `Data.Polynomial.Coeff` and should attempt to keep
-- up to date with that
section

theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) :
    coeff R n (C R x * X ^ k : R⟦X⟧) = if n = k then x else 0 := by
  simp [X_pow_eq, coeff_monomial]
set_option linter.uppercaseLean3 false in
#align power_series.coeff_C_mul_X_pow PowerSeries.coeff_C_mul_X_pow

@[simp]
theorem coeff_mul_X_pow (p : R⟦X⟧) (n d : ℕ) :
    coeff R (d + n) (p * X ^ n) = coeff R d p := by
  rw [coeff_mul, Finset.sum_eq_single (d, n), coeff_X_pow, if_pos rfl, mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow, if_neg, mul_zero]
    rintro rfl
    apply h2
    rw [mem_antidiagonal, add_right_cancel_iff] at h1
    subst h1
    rfl
  · exact fun h1 => (h1 (mem_antidiagonal.2 rfl)).elim
set_option linter.uppercaseLean3 false in
#align power_series.coeff_mul_X_pow PowerSeries.coeff_mul_X_pow

@[simp]
theorem coeff_X_pow_mul (p : R⟦X⟧) (n d : ℕ) :
    coeff R (d + n) (X ^ n * p) = coeff R d p := by
  rw [coeff_mul, Finset.sum_eq_single (n, d), coeff_X_pow, if_pos rfl, one_mul]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow, if_neg, zero_mul]
    rintro rfl
    apply h2
    rw [mem_antidiagonal, add_comm, add_right_cancel_iff] at h1
    subst h1
    rfl
  · rw [add_comm]
    exact fun h1 => (h1 (mem_antidiagonal.2 rfl)).elim
set_option linter.uppercaseLean3 false in
#align power_series.coeff_X_pow_mul PowerSeries.coeff_X_pow_mul

theorem coeff_mul_X_pow' (p : R⟦X⟧) (n d : ℕ) :
    coeff R d (p * X ^ n) = ite (n ≤ d) (coeff R (d - n) p) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow, if_neg, mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne
set_option linter.uppercaseLean3 false in
#align power_series.coeff_mul_X_pow' PowerSeries.coeff_mul_X_pow'

theorem coeff_X_pow_mul' (p : R⟦X⟧) (n d : ℕ) :
    coeff R d (X ^ n * p) = ite (n ≤ d) (coeff R (d - n) p) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_X_pow_mul]
    simp
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow, if_neg, zero_mul]
    have := mem_antidiagonal.mp hx
    rw [add_comm] at this
    exact ((le_of_add_le_right this.le).trans_lt <| not_le.mp h).ne
set_option linter.uppercaseLean3 false in
#align power_series.coeff_X_pow_mul' PowerSeries.coeff_X_pow_mul'

end

/-- If a formal power series is invertible, then so is its constant coefficient. -/
theorem isUnit_constantCoeff (φ : R⟦X⟧) (h : IsUnit φ) : IsUnit (constantCoeff R φ) :=
  MvPowerSeries.isUnit_constantCoeff φ h
#align power_series.is_unit_constant_coeff PowerSeries.isUnit_constantCoeff

/-- Split off the constant coefficient. -/
theorem eq_shift_mul_X_add_const (φ : R⟦X⟧) :
    φ = (mk fun p => coeff R (p + 1) φ) * X + C R (constantCoeff R φ) := by
  ext (_ | n)
  · simp only [Nat.zero_eq, coeff_zero_eq_constantCoeff, map_add, map_mul, constantCoeff_X,
      mul_zero, coeff_zero_C, zero_add]
  · simp only [coeff_succ_mul_X, coeff_mk, LinearMap.map_add, coeff_C, n.succ_ne_zero, sub_zero,
      if_false, add_zero]
set_option linter.uppercaseLean3 false in
#align power_series.eq_shift_mul_X_add_const PowerSeries.eq_shift_mul_X_add_const

/-- Split off the constant coefficient. -/
theorem eq_X_mul_shift_add_const (φ : R⟦X⟧) :
    φ = (X * mk fun p => coeff R (p + 1) φ) + C R (constantCoeff R φ) := by
  ext (_ | n)
  · simp only [Nat.zero_eq, coeff_zero_eq_constantCoeff, map_add, map_mul, constantCoeff_X,
      zero_mul, coeff_zero_C, zero_add]
  · simp only [coeff_succ_X_mul, coeff_mk, LinearMap.map_add, coeff_C, n.succ_ne_zero, sub_zero,
      if_false, add_zero]
set_option linter.uppercaseLean3 false in
#align power_series.eq_X_mul_shift_add_const PowerSeries.eq_X_mul_shift_add_const

section Map

variable {S : Type*} {T : Type*} [Semiring S] [Semiring T]
variable (f : R →+* S) (g : S →+* T)

/-- The map between formal power series induced by a map on the coefficients. -/
def map : R⟦X⟧ →+* S⟦X⟧ :=
  MvPowerSeries.map _ f
#align power_series.map PowerSeries.map

@[simp]
theorem map_id : (map (RingHom.id R) : R⟦X⟧ → R⟦X⟧) = id :=
  rfl
#align power_series.map_id PowerSeries.map_id

theorem map_comp : map (g.comp f) = (map g).comp (map f) :=
  rfl
#align power_series.map_comp PowerSeries.map_comp

@[simp]
theorem coeff_map (n : ℕ) (φ : R⟦X⟧) : coeff S n (map f φ) = f (coeff R n φ) :=
  rfl
#align power_series.coeff_map PowerSeries.coeff_map

@[simp]
theorem map_C (r : R) : map f (C _ r) = C _ (f r) := by
  ext
  simp [coeff_C, apply_ite f]
set_option linter.uppercaseLean3 false in
#align power_series.map_C PowerSeries.map_C

@[simp]
theorem map_X : map f X = X := by
  ext
  simp [coeff_X, apply_ite f]
set_option linter.uppercaseLean3 false in
#align power_series.map_X PowerSeries.map_X

end Map

theorem X_pow_dvd_iff {n : ℕ} {φ : R⟦X⟧} :
    (X : R⟦X⟧) ^ n ∣ φ ↔ ∀ m, m < n → coeff R m φ = 0 := by
  convert@MvPowerSeries.X_pow_dvd_iff Unit R _ () n φ
  constructor <;> intro h m hm
  · rw [Finsupp.unique_single m]
    convert h _ hm
  · apply h
    simpa only [Finsupp.single_eq_same] using hm
set_option linter.uppercaseLean3 false in
#align power_series.X_pow_dvd_iff PowerSeries.X_pow_dvd_iff

theorem X_dvd_iff {φ : R⟦X⟧} : (X : R⟦X⟧) ∣ φ ↔ constantCoeff R φ = 0 := by
  rw [← pow_one (X : R⟦X⟧), X_pow_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]
  constructor <;> intro h
  · exact h 0 zero_lt_one
  · intro m hm
    rwa [Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hm)]
set_option linter.uppercaseLean3 false in
#align power_series.X_dvd_iff PowerSeries.X_dvd_iff

end Semiring

section CommSemiring

variable [CommSemiring R]

open Finset Nat

/-- The ring homomorphism taking a power series `f(X)` to `f(aX)`. -/
noncomputable def rescale (a : R) : R⟦X⟧ →+* R⟦X⟧ where
  toFun f := PowerSeries.mk fun n => a ^ n * PowerSeries.coeff R n f
  map_zero' := by
    ext
    simp only [LinearMap.map_zero, PowerSeries.coeff_mk, mul_zero]
  map_one' := by
    ext1
    simp only [mul_boole, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with h
    · rw [h, pow_zero a]
    rfl
  map_add' := by
    intros
    ext
    dsimp only
    exact mul_add _ _ _
  map_mul' f g := by
    ext
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.mul_sum]
    apply sum_congr rfl
    simp only [coeff_mk, Prod.forall, mem_antidiagonal]
    intro b c H
    rw [← H, pow_add, mul_mul_mul_comm]
#align power_series.rescale PowerSeries.rescale

@[simp]
theorem coeff_rescale (f : R⟦X⟧) (a : R) (n : ℕ) :
    coeff R n (rescale a f) = a ^ n * coeff R n f :=
  coeff_mk n (fun n ↦ a ^ n * (coeff R n) f)
#align power_series.coeff_rescale PowerSeries.coeff_rescale

@[simp]
theorem rescale_zero : rescale 0 = (C R).comp (constantCoeff R) := by
  ext x n
  simp only [Function.comp_apply, RingHom.coe_comp, rescale, RingHom.coe_mk,
    PowerSeries.coeff_mk _ _, coeff_C]
  split_ifs with h <;> simp [h]
#align power_series.rescale_zero PowerSeries.rescale_zero

theorem rescale_zero_apply : rescale 0 X = C R (constantCoeff R X) := by simp
#align power_series.rescale_zero_apply PowerSeries.rescale_zero_apply

@[simp]
theorem rescale_one : rescale 1 = RingHom.id R⟦X⟧ := by
  ext
  simp only [coeff_rescale, one_pow, one_mul, RingHom.id_apply]
#align power_series.rescale_one PowerSeries.rescale_one

theorem rescale_mk (f : ℕ → R) (a : R) : rescale a (mk f) = mk fun n : ℕ => a ^ n * f n := by
  ext
  rw [coeff_rescale, coeff_mk, coeff_mk]
#align power_series.rescale_mk PowerSeries.rescale_mk

theorem rescale_rescale (f : R⟦X⟧) (a b : R) :
    rescale b (rescale a f) = rescale (a * b) f := by
  ext n
  simp_rw [coeff_rescale]
  rw [mul_pow, mul_comm _ (b ^ n), mul_assoc]
#align power_series.rescale_rescale PowerSeries.rescale_rescale

theorem rescale_mul (a b : R) : rescale (a * b) = (rescale b).comp (rescale a) := by
  ext
  simp [← rescale_rescale]
#align power_series.rescale_mul PowerSeries.rescale_mul

end CommSemiring

section CommSemiring

open Finset.HasAntidiagonal Finset

variable {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]

/-- Coefficients of a product of power series -/
theorem coeff_prod (f : ι → PowerSeries R) (d : ℕ) (s : Finset ι) :
    coeff R d (∏ j ∈ s, f j) = ∑ l ∈ finsuppAntidiag s d, ∏ i ∈ s, coeff R (l i) (f i) := by
  simp only [coeff]
  convert MvPowerSeries.coeff_prod _ _ _
  rw [← AddEquiv.finsuppUnique_symm d, ← mapRange_finsuppAntidiag_eq, sum_map, sum_congr rfl]
  intro x _
  apply prod_congr rfl
  intro i _
  congr 2
  simp only [AddEquiv.toEquiv_eq_coe, Finsupp.mapRange.addEquiv_toEquiv, AddEquiv.toEquiv_symm,
    Equiv.coe_toEmbedding, Finsupp.mapRange.equiv_apply, AddEquiv.coe_toEquiv_symm,
    Finsupp.mapRange_apply, AddEquiv.finsuppUnique_symm]

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A]

theorem not_isField : ¬IsField A⟦X⟧ := by
  by_cases hA : Subsingleton A
  · exact not_isField_of_subsingleton _
  · nontriviality A
    rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
    use Ideal.span {X}
    constructor
    · rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact X_ne_zero
    · rw [lt_top_iff_ne_top, Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton,
        X_dvd_iff, constantCoeff_one]
      exact one_ne_zero

@[simp]
theorem rescale_X (a : A) : rescale a X = C A a * X := by
  ext
  simp only [coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with h <;> simp [h]
set_option linter.uppercaseLean3 false in
#align power_series.rescale_X PowerSeries.rescale_X

theorem rescale_neg_one_X : rescale (-1 : A) X = -X := by
  rw [rescale_X, map_neg, map_one, neg_one_mul]
set_option linter.uppercaseLean3 false in
#align power_series.rescale_neg_one_X PowerSeries.rescale_neg_one_X

/-- The ring homomorphism taking a power series `f(X)` to `f(-X)`. -/
noncomputable def evalNegHom : A⟦X⟧ →+* A⟦X⟧ :=
  rescale (-1 : A)
#align power_series.eval_neg_hom PowerSeries.evalNegHom

@[simp]
theorem evalNegHom_X : evalNegHom (X : A⟦X⟧) = -X :=
  rescale_neg_one_X
set_option linter.uppercaseLean3 false in
#align power_series.eval_neg_hom_X PowerSeries.evalNegHom_X

end CommRing

section Domain

variable [Ring R]

theorem eq_zero_or_eq_zero_of_mul_eq_zero [NoZeroDivisors R] (φ ψ : R⟦X⟧) (h : φ * ψ = 0) :
    φ = 0 ∨ ψ = 0 := by
  classical
  rw [or_iff_not_imp_left]
  intro H
  have ex : ∃ m, coeff R m φ ≠ 0 := by
    contrapose! H
    exact ext H
  let m := Nat.find ex
  have hm₁ : coeff R m φ ≠ 0 := Nat.find_spec ex
  have hm₂ : ∀ k < m, ¬coeff R k φ ≠ 0 := fun k => Nat.find_min ex
  ext n
  rw [(coeff R n).map_zero]
  induction' n using Nat.strong_induction_on with n ih
  replace h := congr_arg (coeff R (m + n)) h
  rw [LinearMap.map_zero, coeff_mul, Finset.sum_eq_single (m, n)] at h
  · replace h := NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h
    rw [or_iff_not_imp_left] at h
    exact h hm₁
  · rintro ⟨i, j⟩ hij hne
    by_cases hj : j < n
    · rw [ih j hj, mul_zero]
    by_cases hi : i < m
    · specialize hm₂ _ hi
      push_neg at hm₂
      rw [hm₂, zero_mul]
    rw [mem_antidiagonal] at hij
    push_neg at hi hj
    suffices m < i by
      have : m + n < i + j := add_lt_add_of_lt_of_le this hj
      exfalso
      exact ne_of_lt this hij.symm
    contrapose! hne
    obtain rfl := le_antisymm hi hne
    simpa [Ne, Prod.mk.inj_iff] using (add_right_inj m).mp hij
  · contrapose!
    intro
    rw [mem_antidiagonal]
#align power_series.eq_zero_or_eq_zero_of_mul_eq_zero PowerSeries.eq_zero_or_eq_zero_of_mul_eq_zero

instance [NoZeroDivisors R] : NoZeroDivisors R⟦X⟧ where
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero _ _

instance [IsDomain R] : IsDomain R⟦X⟧ :=
  NoZeroDivisors.to_isDomain _

end Domain

section IsDomain

variable [CommRing R] [IsDomain R]

/-- The ideal spanned by the variable in the power series ring
 over an integral domain is a prime ideal. -/
theorem span_X_isPrime : (Ideal.span ({X} : Set R⟦X⟧)).IsPrime := by
  suffices Ideal.span ({X} : Set R⟦X⟧) = RingHom.ker (constantCoeff R) by
    rw [this]
    exact RingHom.ker_isPrime _
  apply Ideal.ext
  intro φ
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]
set_option linter.uppercaseLean3 false in
#align power_series.span_X_is_prime PowerSeries.span_X_isPrime

/-- The variable of the power series ring over an integral domain is prime. -/
theorem X_prime : Prime (X : R⟦X⟧) := by
  rw [← Ideal.span_singleton_prime]
  · exact span_X_isPrime
  · intro h
    simpa [map_zero (coeff R 1)] using congr_arg (coeff R 1) h
set_option linter.uppercaseLean3 false in
#align power_series.X_prime PowerSeries.X_prime

/-- The variable of the power series ring over an integral domain is irreducible. -/
theorem X_irreducible : Irreducible (X : R⟦X⟧) := X_prime.irreducible

theorem rescale_injective {a : R} (ha : a ≠ 0) : Function.Injective (rescale a) := by
  intro p q h
  rw [PowerSeries.ext_iff] at *
  intro n
  specialize h n
  rw [coeff_rescale, coeff_rescale, mul_eq_mul_left_iff] at h
  apply h.resolve_right
  intro h'
  exact ha (pow_eq_zero h')
#align power_series.rescale_injective PowerSeries.rescale_injective

end IsDomain

section Algebra

variable {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem C_eq_algebraMap {r : R} : C R r = (algebraMap R R⟦X⟧) r :=
  rfl
set_option linter.uppercaseLean3 false in
#align power_series.C_eq_algebra_map PowerSeries.C_eq_algebraMap

theorem algebraMap_apply {r : R} : algebraMap R A⟦X⟧ r = C A (algebraMap R A r) :=
  MvPowerSeries.algebraMap_apply
#align power_series.algebra_map_apply PowerSeries.algebraMap_apply

instance [Nontrivial R] : Nontrivial (Subalgebra R R⟦X⟧) :=
  { inferInstanceAs <| Nontrivial <| Subalgebra R <| MvPowerSeries Unit R with }

end Algebra

end PowerSeries

namespace Polynomial

open Finsupp Polynomial

variable {σ : Type*} {R : Type*} [CommSemiring R] (φ ψ : R[X])

-- Porting note: added so we can add the `@[coe]` attribute
/-- The natural inclusion from polynomials into formal power series. -/
@[coe]
def ToPowerSeries : R[X] → (PowerSeries R) := fun φ =>
  PowerSeries.mk fun n => coeff φ n

/-- The natural inclusion from polynomials into formal power series. -/
instance coeToPowerSeries : Coe R[X] (PowerSeries R) :=
  ⟨ToPowerSeries⟩
#align polynomial.coe_to_power_series Polynomial.coeToPowerSeries

theorem coe_def : (φ : PowerSeries R) = PowerSeries.mk (coeff φ) :=
  rfl
#align polynomial.coe_def Polynomial.coe_def

@[simp, norm_cast]
theorem coeff_coe (n) : PowerSeries.coeff R n φ = coeff φ n :=
  congr_arg (coeff φ) Finsupp.single_eq_same
#align polynomial.coeff_coe Polynomial.coeff_coe

@[simp, norm_cast]
theorem coe_monomial (n : ℕ) (a : R) :
    (monomial n a : PowerSeries R) = PowerSeries.monomial R n a := by
  ext
  simp [coeff_coe, PowerSeries.coeff_monomial, Polynomial.coeff_monomial, eq_comm]
#align polynomial.coe_monomial Polynomial.coe_monomial

@[simp, norm_cast]
theorem coe_zero : ((0 : R[X]) : PowerSeries R) = 0 :=
  rfl
#align polynomial.coe_zero Polynomial.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : R[X]) : PowerSeries R) = 1 := by
  have := coe_monomial 0 (1 : R)
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this
#align polynomial.coe_one Polynomial.coe_one

@[simp, norm_cast]
theorem coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ := by
  ext
  simp
#align polynomial.coe_add Polynomial.coe_add

@[simp, norm_cast]
theorem coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ :=
  PowerSeries.ext fun n => by simp only [coeff_coe, PowerSeries.coeff_mul, coeff_mul]
#align polynomial.coe_mul Polynomial.coe_mul

@[simp, norm_cast]
theorem coe_C (a : R) : ((C a : R[X]) : PowerSeries R) = PowerSeries.C R a := by
  have := coe_monomial 0 a
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this
set_option linter.uppercaseLean3 false in
#align polynomial.coe_C Polynomial.coe_C


set_option linter.deprecated false in
@[simp, norm_cast]
theorem coe_bit0 : ((bit0 φ : R[X]) : PowerSeries R) = bit0 (φ : PowerSeries R) :=
  coe_add φ φ
#align polynomial.coe_bit0 Polynomial.coe_bit0

set_option linter.deprecated false in
@[simp, norm_cast]
theorem coe_bit1 : ((bit1 φ : R[X]) : PowerSeries R) = bit1 (φ : PowerSeries R) := by
  rw [bit1, bit1, coe_add, coe_one, coe_bit0]
#align polynomial.coe_bit1 Polynomial.coe_bit1

@[simp, norm_cast]
theorem coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X :=
  coe_monomial _ _
set_option linter.uppercaseLean3 false in
#align polynomial.coe_X Polynomial.coe_X

@[simp]
theorem constantCoeff_coe : PowerSeries.constantCoeff R φ = φ.coeff 0 :=
  rfl
#align polynomial.constant_coeff_coe Polynomial.constantCoeff_coe

variable (R)

theorem coe_injective : Function.Injective (Coe.coe : R[X] → PowerSeries R) := fun x y h => by
  ext
  simp_rw [← coeff_coe]
  congr
#align polynomial.coe_injective Polynomial.coe_injective

variable {R φ ψ}

@[simp, norm_cast]
theorem coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ :=
  (coe_injective R).eq_iff
#align polynomial.coe_inj Polynomial.coe_inj

@[simp]
theorem coe_eq_zero_iff : (φ : PowerSeries R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]
#align polynomial.coe_eq_zero_iff Polynomial.coe_eq_zero_iff

@[simp]
theorem coe_eq_one_iff : (φ : PowerSeries R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]
#align polynomial.coe_eq_one_iff Polynomial.coe_eq_one_iff

variable (φ ψ)

/-- The coercion from polynomials to power series
as a ring homomorphism.
-/
def coeToPowerSeries.ringHom : R[X] →+* PowerSeries R where
  toFun := (Coe.coe : R[X] → PowerSeries R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul
#align polynomial.coe_to_power_series.ring_hom Polynomial.coeToPowerSeries.ringHom

@[simp]
theorem coeToPowerSeries.ringHom_apply : coeToPowerSeries.ringHom φ = φ :=
  rfl
#align polynomial.coe_to_power_series.ring_hom_apply Polynomial.coeToPowerSeries.ringHom_apply

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((φ ^ n : R[X]) : PowerSeries R) = (φ : PowerSeries R) ^ n :=
  coeToPowerSeries.ringHom.map_pow _ _
#align polynomial.coe_pow Polynomial.coe_pow

theorem eval₂_C_X_eq_coe : φ.eval₂ (PowerSeries.C R) PowerSeries.X = ↑φ := by
  nth_rw 2 [← eval₂_C_X (p := φ)]
  rw [← coeToPowerSeries.ringHom_apply, eval₂_eq_sum_range, eval₂_eq_sum_range, map_sum]
  apply Finset.sum_congr rfl
  intros
  rw [map_mul, map_pow, coeToPowerSeries.ringHom_apply,
    coeToPowerSeries.ringHom_apply, coe_C, coe_X]

variable (A : Type*) [Semiring A] [Algebra R A]

/-- The coercion from polynomials to power series
as an algebra homomorphism.
-/
def coeToPowerSeries.algHom : R[X] →ₐ[R] PowerSeries A :=
  { (PowerSeries.map (algebraMap R A)).comp coeToPowerSeries.ringHom with
    commutes' := fun r => by simp [algebraMap_apply, PowerSeries.algebraMap_apply] }
#align polynomial.coe_to_power_series.alg_hom Polynomial.coeToPowerSeries.algHom

@[simp]
theorem coeToPowerSeries.algHom_apply :
    coeToPowerSeries.algHom A φ = PowerSeries.map (algebraMap R A) ↑φ :=
  rfl
#align polynomial.coe_to_power_series.alg_hom_apply Polynomial.coeToPowerSeries.algHom_apply

end Polynomial

namespace PowerSeries

section Algebra

open Polynomial

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : R⟦X⟧)

instance algebraPolynomial : Algebra R[X] A⟦X⟧ :=
  RingHom.toAlgebra (Polynomial.coeToPowerSeries.algHom A).toRingHom
#align power_series.algebra_polynomial PowerSeries.algebraPolynomial

instance algebraPowerSeries : Algebra R⟦X⟧ A⟦X⟧ :=
  (map (algebraMap R A)).toAlgebra
#align power_series.algebra_power_series PowerSeries.algebraPowerSeries

-- see Note [lower instance priority]
instance (priority := 100) algebraPolynomial' {A : Type*} [CommSemiring A] [Algebra R A[X]] :
    Algebra R A⟦X⟧ :=
  RingHom.toAlgebra <| Polynomial.coeToPowerSeries.ringHom.comp (algebraMap R A[X])
#align power_series.algebra_polynomial' PowerSeries.algebraPolynomial'

variable (A)

theorem algebraMap_apply' (p : R[X]) : algebraMap R[X] A⟦X⟧ p = map (algebraMap R A) p :=
  rfl
#align power_series.algebra_map_apply' PowerSeries.algebraMap_apply'

theorem algebraMap_apply'' :
    algebraMap R⟦X⟧ A⟦X⟧ f = map (algebraMap R A) f :=
  rfl
#align power_series.algebra_map_apply'' PowerSeries.algebraMap_apply''

end Algebra

end PowerSeries

end
