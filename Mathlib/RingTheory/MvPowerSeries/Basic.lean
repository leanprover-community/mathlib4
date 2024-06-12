/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.PiAntidiagonal
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Linarith

#align_import ring_theory.power_series.basic from "leanprover-community/mathlib"@"2d5739b61641ee4e7e53eca5688a08f66f2e6a60"

/-!
# Formal (multivariate) power series

This file defines multivariate formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from multivariate polynomials to multivariate formal power series.

## Note

This file sets up the (semi)ring structure on multivariate power series:
additional results are in:
* `Mathlib.RingTheory.MvPowerSeries.Inverse` : invertibility,
  formal power series over a local ring form a local ring;
* `Mathlib.RingTheory.MvPowerSeries.Trunc`: truncation of power series.

In `Mathlib.RingTheory.PowerSeries.Basic`, formal power series in one variable
will be obtained as a particular case, defined by
  `PowerSeries R := MvPowerSeries Unit R`.
See that file for a specific description.

## Implementation notes

In this file we define multivariate formal power series with
variables indexed by `σ` and coefficients in `R` as
`MvPowerSeries σ R := (σ →₀ ℕ) → R`.
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

-/


noncomputable section

open Finset (antidiagonal mem_antidiagonal)

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring. -/
def MvPowerSeries (σ : Type*) (R : Type*) :=
  (σ →₀ ℕ) → R
#align mv_power_series MvPowerSeries

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

instance [Inhabited R] : Inhabited (MvPowerSeries σ R) :=
  ⟨fun _ => default⟩

instance [Zero R] : Zero (MvPowerSeries σ R) :=
  Pi.instZero

instance [AddMonoid R] : AddMonoid (MvPowerSeries σ R) :=
  Pi.addMonoid

instance [AddGroup R] : AddGroup (MvPowerSeries σ R) :=
  Pi.addGroup

instance [AddCommMonoid R] : AddCommMonoid (MvPowerSeries σ R) :=
  Pi.addCommMonoid

instance [AddCommGroup R] : AddCommGroup (MvPowerSeries σ R) :=
  Pi.addCommGroup

instance [Nontrivial R] : Nontrivial (MvPowerSeries σ R) :=
  Function.nontrivial

instance {A} [Semiring R] [AddCommMonoid A] [Module R A] : Module R (MvPowerSeries σ A) :=
  Pi.module _ _ _

instance {A S} [Semiring R] [Semiring S] [AddCommMonoid A] [Module R A] [Module S A] [SMul R S]
    [IsScalarTower R S A] : IsScalarTower R S (MvPowerSeries σ A) :=
  Pi.isScalarTower

section Semiring

variable (R) [Semiring R]

/-- The `n`th monomial as multivariate formal power series:
  it is defined as the `R`-linear map from `R` to the semi-ring
  of multivariate formal power series associating to each `a`
  the map sending `n : σ →₀ ℕ` to the value `a`
  and sending all other `x : σ →₀ ℕ` different from `n` to `0`. -/
def monomial (n : σ →₀ ℕ) : R →ₗ[R] MvPowerSeries σ R :=
  letI := Classical.decEq σ
  LinearMap.stdBasis R (fun _ ↦ R) n
#align mv_power_series.monomial MvPowerSeries.monomial

/-- The `n`th coefficient of a multivariate formal power series. -/
def coeff (n : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] R :=
  LinearMap.proj n
#align mv_power_series.coeff MvPowerSeries.coeff

variable {R}

/-- Two multivariate formal power series are equal if all their coefficients are equal. -/
@[ext]
theorem ext {φ ψ} (h : ∀ n : σ →₀ ℕ, coeff R n φ = coeff R n ψ) : φ = ψ :=
  funext h
#align mv_power_series.ext MvPowerSeries.ext

/-- Two multivariate formal power series are equal
 if and only if all their coefficients are equal. -/
theorem ext_iff {φ ψ : MvPowerSeries σ R} : φ = ψ ↔ ∀ n : σ →₀ ℕ, coeff R n φ = coeff R n ψ :=
  Function.funext_iff
#align mv_power_series.ext_iff MvPowerSeries.ext_iff

theorem monomial_def [DecidableEq σ] (n : σ →₀ ℕ) :
    (monomial R n) = LinearMap.stdBasis R (fun _ ↦ R) n := by
  rw [monomial]
  -- unify the `Decidable` arguments
  convert rfl
#align mv_power_series.monomial_def MvPowerSeries.monomial_def

theorem coeff_monomial [DecidableEq σ] (m n : σ →₀ ℕ) (a : R) :
    coeff R m (monomial R n a) = if m = n then a else 0 := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [coeff, monomial_def, LinearMap.proj_apply (i := m)]
  dsimp only
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [LinearMap.stdBasis_apply, Function.update_apply, Pi.zero_apply]
#align mv_power_series.coeff_monomial MvPowerSeries.coeff_monomial

@[simp]
theorem coeff_monomial_same (n : σ →₀ ℕ) (a : R) : coeff R n (monomial R n a) = a := by
  classical
  rw [monomial_def]
  exact LinearMap.stdBasis_same R (fun _ ↦ R) n a
#align mv_power_series.coeff_monomial_same MvPowerSeries.coeff_monomial_same

theorem coeff_monomial_ne {m n : σ →₀ ℕ} (h : m ≠ n) (a : R) : coeff R m (monomial R n a) = 0 := by
  classical
  rw [monomial_def]
  exact LinearMap.stdBasis_ne R (fun _ ↦ R) _ _ h a
#align mv_power_series.coeff_monomial_ne MvPowerSeries.coeff_monomial_ne

theorem eq_of_coeff_monomial_ne_zero {m n : σ →₀ ℕ} {a : R} (h : coeff R m (monomial R n a) ≠ 0) :
    m = n :=
  by_contra fun h' => h <| coeff_monomial_ne h' a
#align mv_power_series.eq_of_coeff_monomial_ne_zero MvPowerSeries.eq_of_coeff_monomial_ne_zero

@[simp]
theorem coeff_comp_monomial (n : σ →₀ ℕ) : (coeff R n).comp (monomial R n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n
#align mv_power_series.coeff_comp_monomial MvPowerSeries.coeff_comp_monomial

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem coeff_zero (n : σ →₀ ℕ) : coeff R n (0 : MvPowerSeries σ R) = 0 :=
  rfl
#align mv_power_series.coeff_zero MvPowerSeries.coeff_zero

variable (m n : σ →₀ ℕ) (φ ψ : MvPowerSeries σ R)

instance : One (MvPowerSeries σ R) :=
  ⟨monomial R (0 : σ →₀ ℕ) 1⟩

theorem coeff_one [DecidableEq σ] : coeff R n (1 : MvPowerSeries σ R) = if n = 0 then 1 else 0 :=
  coeff_monomial _ _ _
#align mv_power_series.coeff_one MvPowerSeries.coeff_one

theorem coeff_zero_one : coeff R (0 : σ →₀ ℕ) 1 = 1 :=
  coeff_monomial_same 0 1
#align mv_power_series.coeff_zero_one MvPowerSeries.coeff_zero_one

theorem monomial_zero_one : monomial R (0 : σ →₀ ℕ) 1 = 1 :=
  rfl
#align mv_power_series.monomial_zero_one MvPowerSeries.monomial_zero_one

instance : AddMonoidWithOne (MvPowerSeries σ R) :=
  { show AddMonoid (MvPowerSeries σ R) by infer_instance with
    natCast := fun n => monomial R 0 n
    natCast_zero := by simp [Nat.cast]
    natCast_succ := by simp [Nat.cast, monomial_zero_one]
    one := 1 }

instance : Mul (MvPowerSeries σ R) :=
  letI := Classical.decEq σ
  ⟨fun φ ψ n => ∑ p ∈ antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ⟩

theorem coeff_mul [DecidableEq σ] :
    coeff R n (φ * ψ) = ∑ p ∈ antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  rw [Subsingleton.elim (Classical.decEq σ) ‹DecidableEq σ›]
#align mv_power_series.coeff_mul MvPowerSeries.coeff_mul

protected theorem zero_mul : (0 : MvPowerSeries σ R) * φ = 0 :=
  ext fun n => by classical simp [coeff_mul]
#align mv_power_series.zero_mul MvPowerSeries.zero_mul

protected theorem mul_zero : φ * 0 = 0 :=
  ext fun n => by classical simp [coeff_mul]
#align mv_power_series.mul_zero MvPowerSeries.mul_zero

theorem coeff_monomial_mul (a : R) :
    coeff R m (monomial R n a * φ) = if n ≤ m then a * coeff R (m - n) φ else 0 := by
  classical
  have :
    ∀ p ∈ antidiagonal m,
      coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 (monomial R n a) * coeff R p.2 φ ≠ 0 → p.1 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, Finset.filter_fst_eq_antidiagonal _ n,
    Finset.sum_ite_index]
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]
#align mv_power_series.coeff_monomial_mul MvPowerSeries.coeff_monomial_mul

theorem coeff_mul_monomial (a : R) :
    coeff R m (φ * monomial R n a) = if n ≤ m then coeff R (m - n) φ * a else 0 := by
  classical
  have :
    ∀ p ∈ antidiagonal m,
      coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 φ * coeff R p.2 (monomial R n a) ≠ 0 → p.2 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, Finset.filter_snd_eq_antidiagonal _ n,
    Finset.sum_ite_index]
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]
#align mv_power_series.coeff_mul_monomial MvPowerSeries.coeff_mul_monomial

theorem coeff_add_monomial_mul (a : R) :
    coeff R (m + n) (monomial R m a * φ) = a * coeff R n φ := by
  rw [coeff_monomial_mul, if_pos, add_tsub_cancel_left]
  exact le_add_right le_rfl
#align mv_power_series.coeff_add_monomial_mul MvPowerSeries.coeff_add_monomial_mul

theorem coeff_add_mul_monomial (a : R) :
    coeff R (m + n) (φ * monomial R n a) = coeff R m φ * a := by
  rw [coeff_mul_monomial, if_pos, add_tsub_cancel_right]
  exact le_add_left le_rfl
#align mv_power_series.coeff_add_mul_monomial MvPowerSeries.coeff_add_mul_monomial

@[simp]
theorem commute_monomial {a : R} {n} :
    Commute φ (monomial R n a) ↔ ∀ m, Commute (coeff R m φ) a := by
  refine ext_iff.trans ⟨fun h m => ?_, fun h m => ?_⟩
  · have := h (m + n)
    rwa [coeff_add_mul_monomial, add_comm, coeff_add_monomial_mul] at this
  · rw [coeff_mul_monomial, coeff_monomial_mul]
    split_ifs <;> [apply h; rfl]
#align mv_power_series.commute_monomial MvPowerSeries.commute_monomial

protected theorem one_mul : (1 : MvPowerSeries σ R) * φ = φ :=
  ext fun n => by simpa using coeff_add_monomial_mul 0 n φ 1
#align mv_power_series.one_mul MvPowerSeries.one_mul

protected theorem mul_one : φ * 1 = φ :=
  ext fun n => by simpa using coeff_add_mul_monomial n 0 φ 1
#align mv_power_series.mul_one MvPowerSeries.mul_one

protected theorem mul_add (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
  ext fun n => by
    classical simp only [coeff_mul, mul_add, Finset.sum_add_distrib, LinearMap.map_add]
#align mv_power_series.mul_add MvPowerSeries.mul_add

protected theorem add_mul (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
  ext fun n => by
    classical simp only [coeff_mul, add_mul, Finset.sum_add_distrib, LinearMap.map_add]
#align mv_power_series.add_mul MvPowerSeries.add_mul

protected theorem mul_assoc (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃) := by
  ext1 n
  classical
  simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc, mul_assoc])
#align mv_power_series.mul_assoc MvPowerSeries.mul_assoc

instance : Semiring (MvPowerSeries σ R) :=
  { inferInstanceAs (AddMonoidWithOne (MvPowerSeries σ R)),
    inferInstanceAs (Mul (MvPowerSeries σ R)),
    inferInstanceAs (AddCommMonoid (MvPowerSeries σ R)) with
    mul_one := MvPowerSeries.mul_one
    one_mul := MvPowerSeries.one_mul
    mul_assoc := MvPowerSeries.mul_assoc
    mul_zero := MvPowerSeries.mul_zero
    zero_mul := MvPowerSeries.zero_mul
    left_distrib := MvPowerSeries.mul_add
    right_distrib := MvPowerSeries.add_mul }

end Semiring

instance [CommSemiring R] : CommSemiring (MvPowerSeries σ R) :=
  { show Semiring (MvPowerSeries σ R) by infer_instance with
    mul_comm := fun φ ψ =>
      ext fun n => by
        classical
        simpa only [coeff_mul, mul_comm] using
          sum_antidiagonal_swap n fun a b => coeff R a φ * coeff R b ψ }

instance [Ring R] : Ring (MvPowerSeries σ R) :=
  { inferInstanceAs (Semiring (MvPowerSeries σ R)),
    inferInstanceAs (AddCommGroup (MvPowerSeries σ R)) with }

instance [CommRing R] : CommRing (MvPowerSeries σ R) :=
  { inferInstanceAs (CommSemiring (MvPowerSeries σ R)),
    inferInstanceAs (AddCommGroup (MvPowerSeries σ R)) with }

section Semiring

variable [Semiring R]

theorem monomial_mul_monomial (m n : σ →₀ ℕ) (a b : R) :
    monomial R m a * monomial R n b = monomial R (m + n) (a * b) := by
  classical
  ext k
  simp only [coeff_mul_monomial, coeff_monomial]
  split_ifs with h₁ h₂ h₃ h₃ h₂ <;> try rfl
  · rw [← h₂, tsub_add_cancel_of_le h₁] at h₃
    exact (h₃ rfl).elim
  · rw [h₃, add_tsub_cancel_right] at h₂
    exact (h₂ rfl).elim
  · exact zero_mul b
  · rw [h₂] at h₁
    exact (h₁ <| le_add_left le_rfl).elim
#align mv_power_series.monomial_mul_monomial MvPowerSeries.monomial_mul_monomial

variable (σ) (R)

/-- The constant multivariate formal power series. -/
def C : R →+* MvPowerSeries σ R :=
  { monomial R (0 : σ →₀ ℕ) with
    map_one' := rfl
    map_mul' := fun a b => (monomial_mul_monomial 0 0 a b).symm
    map_zero' := (monomial R (0 : _)).map_zero }
set_option linter.uppercaseLean3 false in
#align mv_power_series.C MvPowerSeries.C

variable {σ} {R}

@[simp]
theorem monomial_zero_eq_C : ⇑(monomial R (0 : σ →₀ ℕ)) = C σ R :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.monomial_zero_eq_C MvPowerSeries.monomial_zero_eq_C

theorem monomial_zero_eq_C_apply (a : R) : monomial R (0 : σ →₀ ℕ) a = C σ R a :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.monomial_zero_eq_C_apply MvPowerSeries.monomial_zero_eq_C_apply

theorem coeff_C [DecidableEq σ] (n : σ →₀ ℕ) (a : R) :
    coeff R n (C σ R a) = if n = 0 then a else 0 :=
  coeff_monomial _ _ _
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_C MvPowerSeries.coeff_C

theorem coeff_zero_C (a : R) : coeff R (0 : σ →₀ ℕ) (C σ R a) = a :=
  coeff_monomial_same 0 a
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_zero_C MvPowerSeries.coeff_zero_C

/-- The variables of the multivariate formal power series ring. -/
def X (s : σ) : MvPowerSeries σ R :=
  monomial R (single s 1) 1
set_option linter.uppercaseLean3 false in
#align mv_power_series.X MvPowerSeries.X

theorem coeff_X [DecidableEq σ] (n : σ →₀ ℕ) (s : σ) :
    coeff R n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0 :=
  coeff_monomial _ _ _
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_X MvPowerSeries.coeff_X

theorem coeff_index_single_X [DecidableEq σ] (s t : σ) :
    coeff R (single t 1) (X s : MvPowerSeries σ R) = if t = s then 1 else 0 := by
  simp only [coeff_X, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_index_single_X MvPowerSeries.coeff_index_single_X

@[simp]
theorem coeff_index_single_self_X (s : σ) : coeff R (single s 1) (X s : MvPowerSeries σ R) = 1 :=
  coeff_monomial_same _ _
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_index_single_self_X MvPowerSeries.coeff_index_single_self_X

theorem coeff_zero_X (s : σ) : coeff R (0 : σ →₀ ℕ) (X s : MvPowerSeries σ R) = 0 := by
  classical
  rw [coeff_X, if_neg]
  intro h
  exact one_ne_zero (single_eq_zero.mp h.symm)
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_zero_X MvPowerSeries.coeff_zero_X

theorem commute_X (φ : MvPowerSeries σ R) (s : σ) : Commute φ (X s) :=
  φ.commute_monomial.mpr fun _m => Commute.one_right _
set_option linter.uppercaseLean3 false in
#align mv_power_series.commute_X MvPowerSeries.commute_X

theorem X_def (s : σ) : X s = monomial R (single s 1) 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_def MvPowerSeries.X_def

theorem X_pow_eq (s : σ) (n : ℕ) : (X s : MvPowerSeries σ R) ^ n = monomial R (single s n) 1 := by
  induction' n with n ih
  · simp
  · rw [pow_succ, ih, Finsupp.single_add, X, monomial_mul_monomial, one_mul]
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_pow_eq MvPowerSeries.X_pow_eq

theorem coeff_X_pow [DecidableEq σ] (m : σ →₀ ℕ) (s : σ) (n : ℕ) :
    coeff R m ((X s : MvPowerSeries σ R) ^ n) = if m = single s n then 1 else 0 := by
  rw [X_pow_eq s n, coeff_monomial]
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_X_pow MvPowerSeries.coeff_X_pow

@[simp]
theorem coeff_mul_C (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) :
    coeff R n (φ * C σ R a) = coeff R n φ * a := by simpa using coeff_add_mul_monomial n 0 φ a
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_mul_C MvPowerSeries.coeff_mul_C

@[simp]
theorem coeff_C_mul (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) :
    coeff R n (C σ R a * φ) = a * coeff R n φ := by simpa using coeff_add_monomial_mul 0 n φ a
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_C_mul MvPowerSeries.coeff_C_mul

theorem coeff_zero_mul_X (φ : MvPowerSeries σ R) (s : σ) : coeff R (0 : σ →₀ ℕ) (φ * X s) = 0 := by
  have : ¬single s 1 ≤ 0 := fun h => by simpa using h s
  simp only [X, coeff_mul_monomial, if_neg this]
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_zero_mul_X MvPowerSeries.coeff_zero_mul_X

theorem coeff_zero_X_mul (φ : MvPowerSeries σ R) (s : σ) : coeff R (0 : σ →₀ ℕ) (X s * φ) = 0 := by
  rw [← (φ.commute_X s).eq, coeff_zero_mul_X]
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_zero_X_mul MvPowerSeries.coeff_zero_X_mul

variable (σ) (R)

/-- The constant coefficient of a formal power series. -/
def constantCoeff : MvPowerSeries σ R →+* R :=
  { coeff R (0 : σ →₀ ℕ) with
    toFun := coeff R (0 : σ →₀ ℕ)
    map_one' := coeff_zero_one
    map_mul' := fun φ ψ => by classical simp [coeff_mul, support_single_ne_zero]
    map_zero' := LinearMap.map_zero _ }
#align mv_power_series.constant_coeff MvPowerSeries.constantCoeff

variable {σ} {R}

@[simp]
theorem coeff_zero_eq_constantCoeff : ⇑(coeff R (0 : σ →₀ ℕ)) = constantCoeff σ R :=
  rfl
#align mv_power_series.coeff_zero_eq_constant_coeff MvPowerSeries.coeff_zero_eq_constantCoeff

theorem coeff_zero_eq_constantCoeff_apply (φ : MvPowerSeries σ R) :
    coeff R (0 : σ →₀ ℕ) φ = constantCoeff σ R φ :=
  rfl
#align mv_power_series.coeff_zero_eq_constant_coeff_apply MvPowerSeries.coeff_zero_eq_constantCoeff_apply

@[simp]
theorem constantCoeff_C (a : R) : constantCoeff σ R (C σ R a) = a :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.constant_coeff_C MvPowerSeries.constantCoeff_C

@[simp]
theorem constantCoeff_comp_C : (constantCoeff σ R).comp (C σ R) = RingHom.id R :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.constant_coeff_comp_C MvPowerSeries.constantCoeff_comp_C

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem constantCoeff_zero : constantCoeff σ R 0 = 0 :=
  rfl
#align mv_power_series.constant_coeff_zero MvPowerSeries.constantCoeff_zero

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem constantCoeff_one : constantCoeff σ R 1 = 1 :=
  rfl
#align mv_power_series.constant_coeff_one MvPowerSeries.constantCoeff_one

@[simp]
theorem constantCoeff_X (s : σ) : constantCoeff σ R (X s) = 0 :=
  coeff_zero_X s
set_option linter.uppercaseLean3 false in
#align mv_power_series.constant_coeff_X MvPowerSeries.constantCoeff_X

/-- If a multivariate formal power series is invertible,
 then so is its constant coefficient. -/
theorem isUnit_constantCoeff (φ : MvPowerSeries σ R) (h : IsUnit φ) :
    IsUnit (constantCoeff σ R φ) :=
  h.map _
#align mv_power_series.is_unit_constant_coeff MvPowerSeries.isUnit_constantCoeff

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem coeff_smul (f : MvPowerSeries σ R) (n) (a : R) : coeff _ n (a • f) = a * coeff _ n f :=
  rfl
#align mv_power_series.coeff_smul MvPowerSeries.coeff_smul

theorem smul_eq_C_mul (f : MvPowerSeries σ R) (a : R) : a • f = C σ R a * f := by
  ext
  simp
set_option linter.uppercaseLean3 false in
#align mv_power_series.smul_eq_C_mul MvPowerSeries.smul_eq_C_mul

theorem X_inj [Nontrivial R] {s t : σ} : (X s : MvPowerSeries σ R) = X t ↔ s = t :=
  ⟨by
    classical
    intro h
    replace h := congr_arg (coeff R (single s 1)) h
    rw [coeff_X, if_pos rfl, coeff_X] at h
    split_ifs at h with H
    · rw [Finsupp.single_eq_single_iff] at H
      cases' H with H H
      · exact H.1
      · exfalso
        exact one_ne_zero H.1
    · exfalso
      exact one_ne_zero h, congr_arg X⟩
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_inj MvPowerSeries.X_inj

end Semiring

section Map

variable {S T : Type*} [Semiring R] [Semiring S] [Semiring T]
variable (f : R →+* S) (g : S →+* T)
variable (σ)

/-- The map between multivariate formal power series induced by a map on the coefficients. -/
def map : MvPowerSeries σ R →+* MvPowerSeries σ S where
  toFun φ n := f <| coeff R n φ
  map_zero' := ext fun _n => f.map_zero
  map_one' :=
    ext fun n =>
      show f ((coeff R n) 1) = (coeff S n) 1 by
        classical
        rw [coeff_one, coeff_one]
        split_ifs with h
        · simp only [RingHom.map_ite_one_zero, ite_true, map_one, h]
        · simp only [RingHom.map_ite_one_zero, ite_false, map_zero, h]
  map_add' φ ψ :=
    ext fun n => show f ((coeff R n) (φ + ψ)) = f ((coeff R n) φ) + f ((coeff R n) ψ) by simp
  map_mul' φ ψ :=
    ext fun n =>
      show f _ = _ by
        classical
        rw [coeff_mul, map_sum, coeff_mul]
        apply Finset.sum_congr rfl
        rintro ⟨i, j⟩ _; rw [f.map_mul]; rfl
#align mv_power_series.map MvPowerSeries.map

variable {σ}

@[simp]
theorem map_id : map σ (RingHom.id R) = RingHom.id _ :=
  rfl
#align mv_power_series.map_id MvPowerSeries.map_id

theorem map_comp : map σ (g.comp f) = (map σ g).comp (map σ f) :=
  rfl
#align mv_power_series.map_comp MvPowerSeries.map_comp

@[simp]
theorem coeff_map (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) : coeff S n (map σ f φ) = f (coeff R n φ) :=
  rfl
#align mv_power_series.coeff_map MvPowerSeries.coeff_map

@[simp]
theorem constantCoeff_map (φ : MvPowerSeries σ R) :
    constantCoeff σ S (map σ f φ) = f (constantCoeff σ R φ) :=
  rfl
#align mv_power_series.constant_coeff_map MvPowerSeries.constantCoeff_map

@[simp]
theorem map_monomial (n : σ →₀ ℕ) (a : R) : map σ f (monomial R n a) = monomial S n (f a) := by
  classical
  ext m
  simp [coeff_monomial, apply_ite f]
#align mv_power_series.map_monomial MvPowerSeries.map_monomial

@[simp]
theorem map_C (a : R) : map σ f (C σ R a) = C σ S (f a) :=
  map_monomial _ _ _
set_option linter.uppercaseLean3 false in
#align mv_power_series.map_C MvPowerSeries.map_C

@[simp]
theorem map_X (s : σ) : map σ f (X s) = X s := by simp [MvPowerSeries.X]
set_option linter.uppercaseLean3 false in
#align mv_power_series.map_X MvPowerSeries.map_X

end Map

section Semiring

variable [Semiring R]

theorem X_pow_dvd_iff {s : σ} {n : ℕ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ^ n ∣ φ ↔ ∀ m : σ →₀ ℕ, m s < n → coeff R m φ = 0 := by
  classical
  constructor
  · rintro ⟨φ, rfl⟩ m h
    rw [coeff_mul, Finset.sum_eq_zero]
    rintro ⟨i, j⟩ hij
    rw [coeff_X_pow, if_neg, zero_mul]
    contrapose! h
    dsimp at h
    subst i
    rw [mem_antidiagonal] at hij
    rw [← hij, Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_right n _
  · intro h
    refine ⟨fun m => coeff R (m + single s n) φ, ?_⟩
    ext m
    by_cases H : m - single s n + single s n = m
    · rw [coeff_mul, Finset.sum_eq_single (single s n, m - single s n)]
      · rw [coeff_X_pow, if_pos rfl, one_mul]
        simpa using congr_arg (fun m : σ →₀ ℕ => coeff R m φ) H.symm
      · rintro ⟨i, j⟩ hij hne
        rw [mem_antidiagonal] at hij
        rw [coeff_X_pow]
        split_ifs with hi
        · exfalso
          apply hne
          rw [← hij, ← hi, Prod.mk.inj_iff]
          refine ⟨rfl, ?_⟩
          ext t
          simp only [add_tsub_cancel_left, Finsupp.add_apply, Finsupp.tsub_apply]
        · exact zero_mul _
      · intro hni
        exfalso
        apply hni
        rwa [mem_antidiagonal, add_comm]
    · rw [h, coeff_mul, Finset.sum_eq_zero]
      · rintro ⟨i, j⟩ hij
        rw [mem_antidiagonal] at hij
        rw [coeff_X_pow]
        split_ifs with hi
        · exfalso
          apply H
          rw [← hij, hi]
          ext
          rw [coe_add, coe_add, Pi.add_apply, Pi.add_apply, add_tsub_cancel_left, add_comm]
        · exact zero_mul _
      · contrapose! H
        ext t
        by_cases hst : s = t
        · subst t
          simpa using tsub_add_cancel_of_le H
        · simp [Finsupp.single_apply, hst]
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_pow_dvd_iff MvPowerSeries.X_pow_dvd_iff

theorem X_dvd_iff {s : σ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ∣ φ ↔ ∀ m : σ →₀ ℕ, m s = 0 → coeff R m φ = 0 := by
  rw [← pow_one (X s : MvPowerSeries σ R), X_pow_dvd_iff]
  constructor <;> intro h m hm
  · exact h m (hm.symm ▸ zero_lt_one)
  · exact h m (Nat.eq_zero_of_le_zero <| Nat.le_of_succ_le_succ hm)
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_dvd_iff MvPowerSeries.X_dvd_iff

end Semiring

section CommSemiring

open Finset.HasAntidiagonal Finset

variable {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]

/-- Coefficients of a product of power series -/
theorem coeff_prod [DecidableEq σ]
    (f : ι → MvPowerSeries σ R) (d : σ →₀ ℕ) (s : Finset ι) :
    coeff R d (∏ j ∈ s, f j) =
      ∑ l ∈ finsuppAntidiag s d,
        ∏ i ∈ s, coeff R (l i) (f i) := by
  induction s using Finset.induction_on generalizing d with
  | empty =>
    simp only [prod_empty, sum_const, nsmul_eq_mul, mul_one, coeff_one, finsuppAntidiag_empty]
    split_ifs
    · simp only [card_singleton, Nat.cast_one]
    · simp only [card_empty, Nat.cast_zero]
  | @insert a s ha ih =>
    rw [finsuppAntidiag_insert ha, prod_insert ha, coeff_mul, sum_biUnion]
    · apply Finset.sum_congr rfl
      simp only [mem_antidiagonal, sum_map, Function.Embedding.coeFn_mk, coe_update, Prod.forall]
      rintro u v rfl
      rw [ih, Finset.mul_sum, ← Finset.sum_attach]
      apply Finset.sum_congr rfl
      simp only [mem_attach, Finset.prod_insert ha, Function.update_same, forall_true_left,
        Subtype.forall]
      rintro x -
      rw [Finset.prod_congr rfl]
      intro i hi
      rw [Function.update_noteq]
      exact ne_of_mem_of_not_mem hi ha
    · simp only [Set.PairwiseDisjoint, Set.Pairwise, mem_coe, mem_antidiagonal, ne_eq,
        disjoint_left, mem_map, mem_attach, Function.Embedding.coeFn_mk, true_and, Subtype.exists,
        exists_prop, not_exists, not_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        Prod.forall, Prod.mk.injEq]
      rintro u v rfl u' v' huv h k - l - hkl
      obtain rfl : u' = u := by
        simpa only [Finsupp.coe_update, Function.update_same] using DFunLike.congr_fun hkl a
      simp only [add_right_inj] at huv
      exact h rfl huv.symm

end CommSemiring

section Algebra

variable {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

instance : Algebra R (MvPowerSeries σ A) :=
  {
    show Module R (MvPowerSeries σ A) by infer_instance with
    commutes' := fun a φ => by
      ext n
      simp [Algebra.commutes]
    smul_def' := fun a σ => by
      ext n
      simp [(coeff A n).map_smul_of_tower a, Algebra.smul_def]
    toRingHom := (MvPowerSeries.map σ (algebraMap R A)).comp (C σ R) }

theorem c_eq_algebraMap : C σ R = algebraMap R (MvPowerSeries σ R) :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.C_eq_algebra_map MvPowerSeries.c_eq_algebraMap

theorem algebraMap_apply {r : R} :
    algebraMap R (MvPowerSeries σ A) r = C σ A (algebraMap R A r) := by
  change (MvPowerSeries.map σ (algebraMap R A)).comp (C σ R) r = _
  simp
#align mv_power_series.algebra_map_apply MvPowerSeries.algebraMap_apply

instance [Nonempty σ] [Nontrivial R] : Nontrivial (Subalgebra R (MvPowerSeries σ R)) :=
  ⟨⟨⊥, ⊤, by
      classical
      rw [Ne, SetLike.ext_iff, not_forall]
      inhabit σ
      refine ⟨X default, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true_iff, Algebra.mem_top]
      intro x
      rw [ext_iff, not_forall]
      refine ⟨Finsupp.single default 1, ?_⟩
      simp [algebraMap_apply, coeff_C]⟩⟩

end Algebra


end MvPowerSeries

namespace MvPolynomial

open Finsupp

variable {σ : Type*} {R : Type*} [CommSemiring R] (φ ψ : MvPolynomial σ R)

-- Porting note: added so we can add the `@[coe]` attribute
/-- The natural inclusion from multivariate polynomials into multivariate formal power series. -/
@[coe]
def toMvPowerSeries : MvPolynomial σ R → MvPowerSeries σ R :=
  fun φ n => coeff n φ

/-- The natural inclusion from multivariate polynomials into multivariate formal power series. -/
instance coeToMvPowerSeries : Coe (MvPolynomial σ R) (MvPowerSeries σ R) :=
  ⟨toMvPowerSeries⟩
#align mv_polynomial.coe_to_mv_power_series MvPolynomial.coeToMvPowerSeries

theorem coe_def : (φ : MvPowerSeries σ R) = fun n => coeff n φ :=
  rfl
#align mv_polynomial.coe_def MvPolynomial.coe_def

@[simp, norm_cast]
theorem coeff_coe (n : σ →₀ ℕ) : MvPowerSeries.coeff R n ↑φ = coeff n φ :=
  rfl
#align mv_polynomial.coeff_coe MvPolynomial.coeff_coe

@[simp, norm_cast]
theorem coe_monomial (n : σ →₀ ℕ) (a : R) :
    (monomial n a : MvPowerSeries σ R) = MvPowerSeries.monomial R n a :=
  MvPowerSeries.ext fun m => by
    classical
    rw [coeff_coe, coeff_monomial, MvPowerSeries.coeff_monomial]
    split_ifs with h₁ h₂ <;> first |rfl|subst m; contradiction
#align mv_polynomial.coe_monomial MvPolynomial.coe_monomial

@[simp, norm_cast]
theorem coe_zero : ((0 : MvPolynomial σ R) : MvPowerSeries σ R) = 0 :=
  rfl
#align mv_polynomial.coe_zero MvPolynomial.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1 :=
    coe_monomial _ _
#align mv_polynomial.coe_one MvPolynomial.coe_one

@[simp, norm_cast]
theorem coe_add : ((φ + ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ + ψ :=
  rfl
#align mv_polynomial.coe_add MvPolynomial.coe_add

@[simp, norm_cast]
theorem coe_mul : ((φ * ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ * ψ :=
  MvPowerSeries.ext fun n => by
    classical
    simp only [coeff_coe, MvPowerSeries.coeff_mul, coeff_mul]
#align mv_polynomial.coe_mul MvPolynomial.coe_mul

@[simp, norm_cast]
theorem coe_C (a : R) : ((C a : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.C σ R a :=
  coe_monomial _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.coe_C MvPolynomial.coe_C

set_option linter.deprecated false in
@[simp, norm_cast]
theorem coe_bit0 :
    ((bit0 φ : MvPolynomial σ R) : MvPowerSeries σ R) = bit0 (φ : MvPowerSeries σ R) :=
  coe_add _ _
#align mv_polynomial.coe_bit0 MvPolynomial.coe_bit0

set_option linter.deprecated false in
@[simp, norm_cast]
theorem coe_bit1 :
    ((bit1 φ : MvPolynomial σ R) : MvPowerSeries σ R) = bit1 (φ : MvPowerSeries σ R) := by
  rw [bit1, bit1, coe_add, coe_one, coe_bit0]
#align mv_polynomial.coe_bit1 MvPolynomial.coe_bit1

@[simp, norm_cast]
theorem coe_X (s : σ) : ((X s : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.X s :=
  coe_monomial _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.coe_X MvPolynomial.coe_X

variable (σ R)

theorem coe_injective : Function.Injective (Coe.coe : MvPolynomial σ R → MvPowerSeries σ R) :=
    fun x y h => by
  ext
  simp_rw [← coeff_coe]
  congr
#align mv_polynomial.coe_injective MvPolynomial.coe_injective

variable {σ R φ ψ}

@[simp, norm_cast]
theorem coe_inj : (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ :=
  (coe_injective σ R).eq_iff
#align mv_polynomial.coe_inj MvPolynomial.coe_inj

@[simp]
theorem coe_eq_zero_iff : (φ : MvPowerSeries σ R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]
#align mv_polynomial.coe_eq_zero_iff MvPolynomial.coe_eq_zero_iff

@[simp]
theorem coe_eq_one_iff : (φ : MvPowerSeries σ R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]
#align mv_polynomial.coe_eq_one_iff MvPolynomial.coe_eq_one_iff

/-- The coercion from multivariate polynomials to multivariate power series
as a ring homomorphism.
-/
def coeToMvPowerSeries.ringHom : MvPolynomial σ R →+* MvPowerSeries σ R where
  toFun := (Coe.coe : MvPolynomial σ R → MvPowerSeries σ R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul
#align mv_polynomial.coe_to_mv_power_series.ring_hom MvPolynomial.coeToMvPowerSeries.ringHom

@[simp, norm_cast]
theorem coe_pow (n : ℕ) :
    ((φ ^ n : MvPolynomial σ R) : MvPowerSeries σ R) = (φ : MvPowerSeries σ R) ^ n :=
  coeToMvPowerSeries.ringHom.map_pow _ _
#align mv_polynomial.coe_pow MvPolynomial.coe_pow

variable (φ ψ)

@[simp]
theorem coeToMvPowerSeries.ringHom_apply : coeToMvPowerSeries.ringHom φ = φ :=
  rfl
#align mv_polynomial.coe_to_mv_power_series.ring_hom_apply MvPolynomial.coeToMvPowerSeries.ringHom_apply

section Algebra

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- The coercion from multivariate polynomials to multivariate power series
as an algebra homomorphism.
-/
def coeToMvPowerSeries.algHom : MvPolynomial σ R →ₐ[R] MvPowerSeries σ A :=
  { (MvPowerSeries.map σ (algebraMap R A)).comp coeToMvPowerSeries.ringHom with
    commutes' := fun r => by simp [algebraMap_apply, MvPowerSeries.algebraMap_apply] }
#align mv_polynomial.coe_to_mv_power_series.alg_hom MvPolynomial.coeToMvPowerSeries.algHom

@[simp]
theorem coeToMvPowerSeries.algHom_apply :
    coeToMvPowerSeries.algHom A φ = MvPowerSeries.map σ (algebraMap R A) ↑φ :=
  rfl
#align mv_polynomial.coe_to_mv_power_series.alg_hom_apply MvPolynomial.coeToMvPowerSeries.algHom_apply

end Algebra

end MvPolynomial

namespace MvPowerSeries

variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : MvPowerSeries σ R)

instance algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPowerSeries σ A) :=
  RingHom.toAlgebra (MvPolynomial.coeToMvPowerSeries.algHom A).toRingHom
#align mv_power_series.algebra_mv_polynomial MvPowerSeries.algebraMvPolynomial

instance algebraMvPowerSeries : Algebra (MvPowerSeries σ R) (MvPowerSeries σ A) :=
  (map σ (algebraMap R A)).toAlgebra
#align mv_power_series.algebra_mv_power_series MvPowerSeries.algebraMvPowerSeries

variable (A)

theorem algebraMap_apply' (p : MvPolynomial σ R) :
    algebraMap (MvPolynomial σ R) (MvPowerSeries σ A) p = map σ (algebraMap R A) p :=
  rfl
#align mv_power_series.algebra_map_apply' MvPowerSeries.algebraMap_apply'

theorem algebraMap_apply'' :
    algebraMap (MvPowerSeries σ R) (MvPowerSeries σ A) f = map σ (algebraMap R A) f :=
  rfl
#align mv_power_series.algebra_map_apply'' MvPowerSeries.algebraMap_apply''

end MvPowerSeries

end
