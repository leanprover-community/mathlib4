/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Formal (multivariate) power series

This file defines multivariate formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from multivariate polynomials to multivariate formal power series.

## Main definitions

- `MvPowerSeries.C`: constant power series

- `MvPowerSeries.X`: the indeterminates

- `MvPowerSeries.coeff`, `MvPowerSeries.constantCoeff`:
the coefficients of a `MvPowerSeries`, its constant coefficient

- `MvPowerSeries.monomial`: the monomials

- `MvPowerSeries.coeff_mul`: computes the coefficients of the product of two `MvPowerSeries`

- `MvPowerSeries.coeff_prod` : computes the coefficients of products of `MvPowerSeries`

- `MvPowerSeries.coeff_pow` : computes the coefficients of powers of a `MvPowerSeries`

- `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent`: if the constant coefficient
of a `MvPowerSeries` is nilpotent, then some coefficients of its powers are automatically zero

- `MvPowerSeries.map`: apply a `RingHom` to the coefficients of a `MvPowerSeries` (as a `RingHom)

- `MvPowerSeries.X_pow_dvd_iff`, `MvPowerSeries.X_dvd_iff`: equivalent
conditions for (a power of) an indeterminate to divide a `MvPowerSeries`

- `MvPolynomial.toMvPowerSeries`: the canonical coercion from `MvPolynomial` to `MvPowerSeries`


## Note

This file sets up the (semi)ring structure on multivariate power series:
additional results are in:
* `Mathlib/RingTheory/MvPowerSeries/Inverse.lean` : invertibility,
  formal power series over a local ring form a local ring;
* `Mathlib/RingTheory/MvPowerSeries/Trunc.lean`: truncation of power series.

In `Mathlib/RingTheory/PowerSeries/Basic.lean`, formal power series in one variable
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

variable [Semiring R]

/-- The `n`th monomial as multivariate formal power series:
  it is defined as the `R`-linear map from `R` to the semiring
  of multivariate formal power series associating to each `a`
  the map sending `n : σ →₀ ℕ` to the value `a`
  and sending all other `x : σ →₀ ℕ` different from `n` to `0`. -/
def monomial (n : σ →₀ ℕ) : R →ₗ[R] MvPowerSeries σ R :=
  letI := Classical.decEq σ
  LinearMap.single R (fun _ ↦ R) n

/-- The `n`th coefficient of a multivariate formal power series. -/
def coeff (n : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] R :=
  LinearMap.proj n

theorem coeff_apply (f : MvPowerSeries σ R) (d : σ →₀ ℕ) : coeff d f = f d :=
  rfl

/-- Two multivariate formal power series are equal if all their coefficients are equal. -/
@[ext]
theorem ext {φ ψ : MvPowerSeries σ R} (h : ∀ n : σ →₀ ℕ, coeff n φ = coeff n ψ) : φ = ψ :=
  funext h

/-- Two multivariate formal power series are equal
if and only if all their coefficients are equal. -/
add_decl_doc MvPowerSeries.ext_iff

theorem monomial_def [DecidableEq σ] (n : σ →₀ ℕ) :
    monomial n = LinearMap.single R (fun _ ↦ R) n := by
  rw [monomial]
  -- unify the `Decidable` arguments
  convert rfl

theorem coeff_monomial [DecidableEq σ] (m n : σ →₀ ℕ) (a : R) :
    coeff m (monomial n a) = if m = n then a else 0 := by
  dsimp only [coeff, MvPowerSeries]
  rw [monomial_def, LinearMap.proj_apply (i := m), LinearMap.single_apply, Pi.single_apply]

@[simp]
theorem coeff_monomial_same (n : σ →₀ ℕ) (a : R) : coeff n (monomial n a) = a := by
  classical
  rw [monomial_def]
  exact Pi.single_eq_same _ _

theorem coeff_monomial_ne {m n : σ →₀ ℕ} (h : m ≠ n) (a : R) : coeff m (monomial n a) = 0 := by
  classical
  rw [monomial_def]
  exact Pi.single_eq_of_ne h _

theorem eq_of_coeff_monomial_ne_zero {m n : σ →₀ ℕ} {a : R} (h : coeff m (monomial n a) ≠ 0) :
    m = n :=
  by_contra fun h' => h <| coeff_monomial_ne h' a

@[simp]
theorem coeff_comp_monomial (n : σ →₀ ℕ) : (coeff (R := R) n).comp (monomial n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n

@[simp]
theorem coeff_zero (n : σ →₀ ℕ) : coeff n (0 : MvPowerSeries σ R) = 0 :=
  rfl

theorem eq_zero_iff_forall_coeff_zero {f : MvPowerSeries σ R} :
    f = 0 ↔ (∀ d : σ →₀ ℕ, coeff d f = 0) :=
  MvPowerSeries.ext_iff

theorem ne_zero_iff_exists_coeff_ne_zero (f : MvPowerSeries σ R) :
    f ≠ 0 ↔ (∃ d : σ →₀ ℕ, coeff d f ≠ 0) := by
  simp only [MvPowerSeries.ext_iff, ne_eq, coeff_zero, not_forall]

variable (m n : σ →₀ ℕ) (φ ψ : MvPowerSeries σ R)

instance : One (MvPowerSeries σ R) :=
  ⟨monomial (0 : σ →₀ ℕ) 1⟩

theorem coeff_one [DecidableEq σ] : coeff n (1 : MvPowerSeries σ R) = if n = 0 then 1 else 0 :=
  coeff_monomial _ _ _

theorem coeff_zero_one : coeff (R := R) (0 : σ →₀ ℕ) 1 = 1 :=
  coeff_monomial_same 0 1

theorem monomial_zero_one : monomial (R := R) (0 : σ →₀ ℕ) 1 = 1 :=
  rfl

instance : AddMonoidWithOne (MvPowerSeries σ R) :=
  { show AddMonoid (MvPowerSeries σ R) by infer_instance with
    natCast := fun n => monomial 0 n
    natCast_zero := by simp [Nat.cast]
    natCast_succ := by simp [Nat.cast, monomial_zero_one]
    one := 1 }

instance : Mul (MvPowerSeries σ R) :=
  letI := Classical.decEq σ
  ⟨fun φ ψ n => ∑ p ∈ antidiagonal n, coeff p.1 φ * coeff p.2 ψ⟩

theorem coeff_mul [DecidableEq σ] :
    coeff n (φ * ψ) = ∑ p ∈ antidiagonal n, coeff p.1 φ * coeff p.2 ψ := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  rw [Subsingleton.elim (Classical.decEq σ) ‹DecidableEq σ›]

protected theorem zero_mul : (0 : MvPowerSeries σ R) * φ = 0 :=
  ext fun n => by classical simp [coeff_mul]

protected theorem mul_zero : φ * 0 = 0 :=
  ext fun n => by classical simp [coeff_mul]

theorem coeff_monomial_mul (a : R) :
    coeff m (monomial n a * φ) = if n ≤ m then a * coeff (m - n) φ else 0 := by
  classical
  have :
    ∀ p ∈ antidiagonal m,
      coeff (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 (monomial n a) * coeff p.2 φ ≠ 0 → p.1 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, Finset.filter_fst_eq_antidiagonal _ n,
    Finset.sum_ite_index]
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]

theorem coeff_mul_monomial (a : R) :
    coeff m (φ * monomial n a) = if n ≤ m then coeff (m - n) φ * a else 0 := by
  classical
  have :
    ∀ p ∈ antidiagonal m,
      coeff (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 φ * coeff p.2 (monomial n a) ≠ 0 → p.2 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, Finset.filter_snd_eq_antidiagonal _ n,
    Finset.sum_ite_index]
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]

theorem coeff_add_monomial_mul (a : R) :
    coeff (m + n) (monomial m a * φ) = a * coeff n φ := by
  rw [coeff_monomial_mul, if_pos, add_tsub_cancel_left]
  exact le_add_right le_rfl

theorem coeff_add_mul_monomial (a : R) :
    coeff (m + n) (φ * monomial n a) = coeff m φ * a := by
  rw [coeff_mul_monomial, if_pos, add_tsub_cancel_right]
  exact le_add_left le_rfl

@[simp]
theorem commute_monomial {a : R} {n} :
    Commute φ (monomial n a) ↔ ∀ m, Commute (coeff m φ) a := by
  rw [commute_iff_eq, MvPowerSeries.ext_iff]
  refine ⟨fun h m => ?_, fun h m => ?_⟩
  · have := h (m + n)
    rwa [coeff_add_mul_monomial, add_comm, coeff_add_monomial_mul] at this
  · rw [coeff_mul_monomial, coeff_monomial_mul]
    split_ifs <;> [apply h; rfl]

protected theorem one_mul : (1 : MvPowerSeries σ R) * φ = φ :=
  ext fun n => by simpa using coeff_add_monomial_mul 0 n φ 1

protected theorem mul_one : φ * 1 = φ :=
  ext fun n => by simpa using coeff_add_mul_monomial n 0 φ 1

protected theorem mul_add (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
  ext fun n => by
    classical simp only [coeff_mul, mul_add, Finset.sum_add_distrib, LinearMap.map_add]

protected theorem add_mul (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
  ext fun n => by
    classical simp only [coeff_mul, add_mul, Finset.sum_add_distrib, LinearMap.map_add]

protected theorem mul_assoc (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃) := by
  ext1 n
  classical
  simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc, mul_assoc])

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
          sum_antidiagonal_swap n fun a b => coeff a φ * coeff b ψ }

instance [Ring R] : Ring (MvPowerSeries σ R) :=
  { inferInstanceAs (Semiring (MvPowerSeries σ R)),
    inferInstanceAs (AddCommGroup (MvPowerSeries σ R)) with }

instance [CommRing R] : CommRing (MvPowerSeries σ R) :=
  { inferInstanceAs (CommSemiring (MvPowerSeries σ R)),
    inferInstanceAs (AddCommGroup (MvPowerSeries σ R)) with }

section Semiring

variable [Semiring R]

theorem monomial_mul_monomial (m n : σ →₀ ℕ) (a b : R) :
    monomial m a * monomial n b = monomial (m + n) (a * b) := by
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

/-- The constant multivariate formal power series. -/
def C : R →+* MvPowerSeries σ R :=
  { monomial (0 : σ →₀ ℕ) with
    map_one' := rfl
    map_mul' := fun a b => Eq.trans (by simp) (monomial_mul_monomial _ _ a b).symm
    map_zero' := (monomial 0).map_zero }

@[simp]
theorem monomial_zero_eq_C : ⇑(monomial (R := R) (0 : σ →₀ ℕ)) = C :=
  rfl

theorem monomial_zero_eq_C_apply (a : R) : monomial (0 : σ →₀ ℕ) a = C a :=
  rfl

theorem coeff_C [DecidableEq σ] (n : σ →₀ ℕ) (a : R) :
    coeff n (C a) = if n = 0 then a else 0 :=
  coeff_monomial _ _ _

theorem coeff_zero_C (a : R) : coeff (0 : σ →₀ ℕ) (C a) = a :=
  coeff_monomial_same 0 a

/-- The variables of the multivariate formal power series ring. -/
def X (s : σ) : MvPowerSeries σ R :=
  monomial (single s 1) 1

theorem coeff_X [DecidableEq σ] (n : σ →₀ ℕ) (s : σ) :
    coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0 :=
  coeff_monomial _ _ _

theorem coeff_index_single_X [DecidableEq σ] (s t : σ) :
    coeff (single t 1) (X s : MvPowerSeries σ R) = if t = s then 1 else 0 := by
  simp only [coeff_X, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]

@[simp]
theorem coeff_index_single_self_X (s : σ) : coeff (single s 1) (X s : MvPowerSeries σ R) = 1 :=
  coeff_monomial_same _ _

theorem coeff_zero_X (s : σ) : coeff (0 : σ →₀ ℕ) (X s : MvPowerSeries σ R) = 0 := by
  classical
  rw [coeff_X, if_neg]
  intro h
  exact one_ne_zero (single_eq_zero.mp h.symm)

theorem commute_X (φ : MvPowerSeries σ R) (s : σ) : Commute φ (X s) :=
  φ.commute_monomial.mpr fun _m => Commute.one_right _

theorem X_mul {φ : MvPowerSeries σ R} {s : σ} : X s * φ = φ * X s :=
  φ.commute_X s |>.symm.eq

theorem commute_X_pow (φ : MvPowerSeries σ R) (s : σ) (n : ℕ) : Commute φ (X s ^ n) :=
  φ.commute_X s |>.pow_right _

theorem X_pow_mul {φ : MvPowerSeries σ R} {s : σ} {n : ℕ} : X s ^ n * φ = φ * X s ^ n :=
  φ.commute_X_pow s n |>.symm.eq

theorem X_def (s : σ) : X s = monomial (single s 1) 1 :=
  rfl

theorem X_pow_eq (s : σ) (n : ℕ) : (X s : MvPowerSeries σ R) ^ n = monomial (single s n) 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Finsupp.single_add, X, monomial_mul_monomial, one_mul]

theorem coeff_X_pow [DecidableEq σ] (m : σ →₀ ℕ) (s : σ) (n : ℕ) :
    coeff m ((X s : MvPowerSeries σ R) ^ n) = if m = single s n then 1 else 0 := by
  rw [X_pow_eq s n, coeff_monomial]

@[simp]
theorem coeff_mul_C (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) :
    coeff n (φ * C a) = coeff n φ * a := by simpa using coeff_add_mul_monomial n 0 φ a

@[simp]
theorem coeff_C_mul (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) :
    coeff n (C a * φ) = a * coeff n φ := by simpa using coeff_add_monomial_mul 0 n φ a

theorem coeff_zero_mul_X (φ : MvPowerSeries σ R) (s : σ) : coeff (0 : σ →₀ ℕ) (φ * X s) = 0 := by
  have : ¬single s 1 ≤ 0 := fun h => by simpa using h s
  simp only [X, coeff_mul_monomial, if_neg this]

theorem coeff_zero_X_mul (φ : MvPowerSeries σ R) (s : σ) : coeff (0 : σ →₀ ℕ) (X s * φ) = 0 := by
  rw [← (φ.commute_X s).eq, coeff_zero_mul_X]

/-- The constant coefficient of a formal power series. -/
def constantCoeff : MvPowerSeries σ R →+* R :=
  { coeff (0 : σ →₀ ℕ) with
    toFun := coeff (0 : σ →₀ ℕ)
    map_one' := coeff_zero_one
    map_mul' := fun φ ψ => by classical simp [coeff_mul]
    map_zero' := LinearMap.map_zero _ }

@[simp]
theorem coeff_zero_eq_constantCoeff : ⇑(coeff (R := R) (0 : σ →₀ ℕ)) = constantCoeff :=
  rfl

theorem coeff_zero_eq_constantCoeff_apply (φ : MvPowerSeries σ R) :
    coeff (0 : σ →₀ ℕ) φ = constantCoeff φ :=
  rfl

@[simp]
theorem constantCoeff_C (a : R) : constantCoeff (σ := σ) (C a) = a :=
  rfl

@[simp]
theorem constantCoeff_comp_C : (constantCoeff (σ := σ)).comp C = RingHom.id R :=
  rfl

@[simp]
theorem constantCoeff_zero : constantCoeff (0 : MvPowerSeries σ R) = 0 :=
  rfl

@[simp]
theorem constantCoeff_one : constantCoeff (1 : MvPowerSeries σ R) = 1 :=
  rfl

@[simp]
theorem constantCoeff_X (s : σ) : constantCoeff (R := R) (X s) = 0 :=
  coeff_zero_X s

@[simp]
theorem constantCoeff_smul {S : Type*} [Semiring S] [Module R S]
    (φ : MvPowerSeries σ S) (a : R) :
    constantCoeff (a • φ) = a • constantCoeff φ := rfl

/-- If a multivariate formal power series is invertible,
then so is its constant coefficient. -/
theorem isUnit_constantCoeff (φ : MvPowerSeries σ R) (h : IsUnit φ) :
    IsUnit (constantCoeff φ) :=
  h.map _

@[simp]
theorem coeff_smul (f : MvPowerSeries σ R) (n) (a : R) : coeff n (a • f) = a * coeff n f :=
  rfl

theorem smul_eq_C_mul (f : MvPowerSeries σ R) (a : R) : a • f = C a * f := by
  ext
  simp

theorem X_inj [Nontrivial R] {s t : σ} : (X s : MvPowerSeries σ R) = X t ↔ s = t :=
  ⟨by
    classical
    intro h
    replace h := congr_arg (coeff (single s 1)) h
    rw [coeff_X, if_pos rfl, coeff_X] at h
    split_ifs at h with H
    · rw [Finsupp.single_eq_single_iff] at H
      rcases H with H | H
      · exact H.1
      · exfalso
        exact one_ne_zero H.1
    · exfalso
      exact one_ne_zero h, congr_arg X⟩

end Semiring

section Map

variable {S T : Type*} [Semiring R] [Semiring S] [Semiring T]
variable (f : R →+* S) (g : S →+* T)

/-- The map between multivariate formal power series induced by a map on the coefficients. -/
def map : MvPowerSeries σ R →+* MvPowerSeries σ S where
  toFun φ n := f <| coeff n φ
  map_zero' := ext fun _n => f.map_zero
  map_one' :=
    ext fun n =>
      show f (coeff n 1) = coeff n 1 by
        classical
        rw [coeff_one, coeff_one]
        split_ifs with h
        · simp only [map_one]
        · simp only [map_zero]
  map_add' φ ψ :=
    ext fun n => show f (coeff n (φ + ψ)) = f (coeff n φ) + f (coeff n ψ) by simp
  map_mul' φ ψ :=
    ext fun n =>
      show f _ = _ by
        classical
        rw [coeff_mul, map_sum, coeff_mul]
        apply Finset.sum_congr rfl
        rintro ⟨i, j⟩ _; rw [f.map_mul]; rfl

@[simp]
theorem map_id : map (σ := σ) (RingHom.id R) = RingHom.id _ :=
  rfl

theorem map_comp : map (σ := σ) (g.comp f) = (map g).comp (map f) :=
  rfl

@[simp]
theorem coeff_map (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) : coeff n (map f φ) = f (coeff n φ) :=
  rfl

@[simp]
theorem constantCoeff_map (φ : MvPowerSeries σ R) :
    constantCoeff (map f φ) = f (constantCoeff φ) :=
  rfl

@[simp]
theorem map_monomial (n : σ →₀ ℕ) (a : R) : map f (monomial n a) = monomial n (f a) := by
  classical
  ext m
  simp [coeff_monomial, apply_ite f]

@[simp]
theorem map_C (a : R) : map (σ := σ) f (C a) = C (f a) :=
  map_monomial _ _ _

@[simp]
theorem map_X (s : σ) : map f (X s) = X s := by simp [MvPowerSeries.X]

end Map

@[simp]
theorem map_eq_zero {S : Type*} [DivisionSemiring R] [Semiring S] [Nontrivial S]
    (φ : MvPowerSeries σ R) (f : R →+* S) : φ.map f = 0 ↔ φ = 0 := by
  simp only [MvPowerSeries.ext_iff]
  congr! with n
  simp

section Semiring

variable [Semiring R]

theorem X_pow_dvd_iff {s : σ} {n : ℕ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ^ n ∣ φ ↔ ∀ m : σ →₀ ℕ, m s < n → coeff m φ = 0 := by
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
    refine ⟨fun m => coeff (m + single s n) φ, ?_⟩
    ext m
    by_cases H : m - single s n + single s n = m
    · rw [coeff_mul, Finset.sum_eq_single (single s n, m - single s n)]
      · rw [coeff_X_pow, if_pos rfl, one_mul]
        simpa using congr_arg (fun m : σ →₀ ℕ => coeff m φ) H.symm
      · rintro ⟨i, j⟩ hij hne
        rw [mem_antidiagonal] at hij
        rw [coeff_X_pow]
        split_ifs with hi
        · exfalso
          apply hne
          rw [← hij, ← hi, Prod.mk_inj]
          refine ⟨rfl, ?_⟩
          ext t
          simp only [add_tsub_cancel_left]
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
        · simp [hst]

theorem X_dvd_iff {s : σ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ∣ φ ↔ ∀ m : σ →₀ ℕ, m s = 0 → coeff m φ = 0 := by
  rw [← pow_one (X s : MvPowerSeries σ R), X_pow_dvd_iff]
  constructor <;> intro h m hm
  · exact h m (hm.symm ▸ zero_lt_one)
  · exact h m (Nat.eq_zero_of_le_zero <| Nat.le_of_succ_le_succ hm)

end Semiring

section CommSemiring

open Finset.HasAntidiagonal Finset

variable {R : Type*} [CommSemiring R] {ι : Type*}

/-- Coefficients of a product of power series -/
theorem coeff_prod [DecidableEq ι] [DecidableEq σ]
    (f : ι → MvPowerSeries σ R) (d : σ →₀ ℕ) (s : Finset ι) :
    coeff d (∏ j ∈ s, f j) =
      ∑ l ∈ finsuppAntidiag s d,
        ∏ i ∈ s, coeff (l i) (f i) := by
  induction s using Finset.induction_on generalizing d with
  | empty =>
    simp only [prod_empty, sum_const, nsmul_eq_mul, mul_one, coeff_one, finsuppAntidiag_empty]
    split_ifs
    · simp only [card_singleton, Nat.cast_one]
    · simp only [card_empty, Nat.cast_zero]
  | insert a s ha ih =>
    rw [finsuppAntidiag_insert ha, prod_insert ha, coeff_mul, sum_biUnion]
    · apply Finset.sum_congr rfl
      simp only [mem_antidiagonal, sum_map, Function.Embedding.coeFn_mk, coe_update, Prod.forall]
      rintro u v rfl
      rw [ih, Finset.mul_sum, ← Finset.sum_attach]
      apply Finset.sum_congr rfl
      simp only [mem_attach, Finset.prod_insert ha, Function.update_self, forall_true_left,
        Subtype.forall]
      rintro x -
      rw [Finset.prod_congr rfl]
      intro i hi
      rw [Function.update_of_ne]
      exact ne_of_mem_of_not_mem hi ha
    · simp only [Set.PairwiseDisjoint, Set.Pairwise, mem_coe, mem_antidiagonal, ne_eq,
        disjoint_left, mem_map, mem_attach, Function.Embedding.coeFn_mk, true_and, Subtype.exists,
        exists_prop, not_exists, not_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        Prod.forall, Prod.mk.injEq]
      rintro u v rfl u' v' huv h k - l - hkl
      obtain rfl : u' = u := by
        simpa only [Finsupp.coe_update, Function.update_self] using DFunLike.congr_fun hkl a
      simp only [add_right_inj] at huv
      exact h rfl huv.symm

theorem prod_monomial (f : ι → σ →₀ ℕ) (g : ι → R) (s : Finset ι) :
    ∏ i ∈ s, monomial (f i) (g i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, g i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha h => simp [h, monomial_mul_monomial]

/-- The `d`th coefficient of a power of a multivariate power series
is the sum, indexed by `finsuppAntidiag (Finset.range n) d`, of products of coefficients -/
theorem coeff_pow [DecidableEq σ] (f : MvPowerSeries σ R) {n : ℕ} (d : σ →₀ ℕ) :
    coeff d (f ^ n) =
      ∑ l ∈ finsuppAntidiag (Finset.range n) d,
        ∏ i ∈ Finset.range n, coeff (l i) f := by
  suffices f ^ n = (Finset.range n).prod fun _ ↦ f by
    rw [this, coeff_prod]
  rw [Finset.prod_const, card_range]

theorem monmial_pow (m : σ →₀ ℕ) (a : R) (n : ℕ) :
    (monomial m a) ^ n = monomial (n • m) (a ^ n) := by
  rw [Finset.pow_eq_prod_const, prod_monomial, ← Finset.nsmul_eq_sum_const,
    ← Finset.pow_eq_prod_const]

/-- Vanishing of coefficients of powers of multivariate power series
when the constant coefficient is nilpotent
[N. Bourbaki, *Algebra {II}*, Chapter 4, §4, n°2, proposition 3][bourbaki1981] -/
theorem coeff_eq_zero_of_constantCoeff_nilpotent {f : MvPowerSeries σ R} {m : ℕ}
    (hf : constantCoeff f ^ m = 0) {d : σ →₀ ℕ} {n : ℕ} (hn : m + degree d ≤ n) :
    coeff d (f ^ n) = 0 := by
  classical
  rw [coeff_pow]
  apply sum_eq_zero
  intro k hk
  rw [mem_finsuppAntidiag] at hk
  set s := {i ∈ range n | k i = 0} with hs_def
  have hs : s ⊆ range n := filter_subset _ _
  have hs' (i : ℕ) (hi : i ∈ s) : coeff (k i) f = constantCoeff f := by
    simp only [hs_def, mem_filter] at hi
    rw [hi.2, coeff_zero_eq_constantCoeff]
  have hs'' (i : ℕ) (hi : i ∈ s) : k i = 0 := by
    simp only [hs_def, mem_filter] at hi
    rw [hi.2]
  rw [← prod_sdiff (s₁ := s) (filter_subset _ _)]
  apply mul_eq_zero_of_right
  rw [prod_congr rfl hs', prod_const]
  suffices m ≤ #s by
    obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le this
    rw [hm', pow_add, hf, zero_mul]
  rw [← Nat.add_le_add_iff_right, add_comm #s,
    Finset.card_sdiff_add_card_eq_card (filter_subset _ _), card_range]
  apply le_trans _ hn
  simp only [add_comm m, Nat.add_le_add_iff_right, ← hk.1,
    ← sum_sdiff (hs), sum_eq_zero (s := s) hs'', add_zero]
  rw [← hs_def]
  convert Finset.card_nsmul_le_sum (range n \ s) (fun x ↦ degree (k x)) 1 _
  · simp only [Algebra.id.smul_eq_mul, mul_one]
  · simp only [degree_eq_weight_one, map_sum]
  · simp only [hs_def, mem_filter, mem_sdiff, mem_range, not_and, and_imp]
    intro i hi hi'
    rw [← not_lt, Nat.lt_one_iff, degree_eq_zero_iff]
    exact hi' hi

end CommSemiring

section Algebra

variable {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  {B : Type*} [Semiring B] [Algebra R B]

instance : Algebra R (MvPowerSeries σ A) where
  algebraMap := (MvPowerSeries.map (algebraMap R A)).comp C
  commutes' := fun a φ => by
    ext n
    simp [Algebra.commutes]
  smul_def' := fun a σ => by
    ext n
    simp [(coeff A n).map_smul_of_tower a, Algebra.smul_def]

theorem c_eq_algebraMap : C = algebraMap R (MvPowerSeries σ R) :=
  rfl

theorem algebraMap_apply {r : R} :
    algebraMap R (MvPowerSeries σ A) r = C (algebraMap R A r) := by
  change (MvPowerSeries.map (algebraMap R A)).comp C r = _
  simp

/-- Change of coefficients in mv power series, as an `AlgHom` -/
def mapAlgHom (φ : A →ₐ[R] B) :
    MvPowerSeries σ A →ₐ[R] MvPowerSeries σ B where
  toRingHom := MvPowerSeries.map φ
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, MvPowerSeries.algebraMap_apply, map_C, RingHom.coe_coe, AlgHom.commutes]

theorem mapAlgHom_apply (φ : A →ₐ[R] B) (f : MvPowerSeries σ A) :
    mapAlgHom (σ := σ) φ f = MvPowerSeries.map φ f := rfl

instance [Nonempty σ] [Nontrivial R] : Nontrivial (Subalgebra R (MvPowerSeries σ R)) :=
  ⟨⟨⊥, ⊤, by
      classical
      rw [Ne, SetLike.ext_iff, not_forall]
      inhabit σ
      refine ⟨X default, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top]
      intro x
      rw [MvPowerSeries.ext_iff, not_forall]
      refine ⟨Finsupp.single default 1, ?_⟩
      simp [algebraMap_apply, coeff_C]⟩⟩

end Algebra


end MvPowerSeries

namespace MvPolynomial

open Finsupp

variable {σ : Type*} {R : Type*} [CommSemiring R] (φ ψ : MvPolynomial σ R)

/-- The natural inclusion from multivariate polynomials into multivariate formal power series. -/
@[coe]
def toMvPowerSeries : MvPolynomial σ R → MvPowerSeries σ R :=
  fun φ n => coeff n φ

/-- The natural inclusion from multivariate polynomials into multivariate formal power series. -/
instance coeToMvPowerSeries : Coe (MvPolynomial σ R) (MvPowerSeries σ R) :=
  ⟨toMvPowerSeries⟩

theorem coe_def : (φ : MvPowerSeries σ R) = fun n => coeff n φ :=
  rfl

@[simp, norm_cast]
theorem coeff_coe (n : σ →₀ ℕ) : MvPowerSeries.coeff n ↑φ = coeff n φ :=
  rfl

@[simp, norm_cast]
theorem coe_monomial (n : σ →₀ ℕ) (a : R) :
    (monomial n a : MvPowerSeries σ R) = MvPowerSeries.monomial n a :=
  MvPowerSeries.ext fun m => by
    classical
    rw [coeff_coe, coeff_monomial, MvPowerSeries.coeff_monomial]
    split_ifs with h₁ h₂ <;> first | rfl | subst m; contradiction

@[simp, norm_cast]
theorem coe_zero : ((0 : MvPolynomial σ R) : MvPowerSeries σ R) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1 :=
    coe_monomial _ _

@[simp, norm_cast]
theorem coe_add : ((φ + ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ + ψ :=
  rfl

@[simp, norm_cast]
theorem coe_mul : ((φ * ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ * ψ :=
  MvPowerSeries.ext fun n => by
    classical
    simp only [coeff_coe, MvPowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]
theorem coe_C (a : R) : ((C a : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.C a :=
  coe_monomial _ _

@[simp, norm_cast]
theorem coe_X (s : σ) : ((X s : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.X s :=
  coe_monomial _ _

variable (σ R)

theorem coe_injective : Function.Injective ((↑) : MvPolynomial σ R → MvPowerSeries σ R) := by
  intro x y h
  ext
  simp_rw [← coeff_coe, h]

variable {σ R φ ψ}

@[simp, norm_cast]
theorem coe_inj : (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ :=
  (coe_injective σ R).eq_iff

@[simp]
theorem coe_eq_zero_iff : (φ : MvPowerSeries σ R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]

@[simp]
theorem coe_eq_one_iff : (φ : MvPowerSeries σ R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]

/-- The coercion from multivariate polynomials to multivariate power series
as a ring homomorphism.
-/
def coeToMvPowerSeries.ringHom : MvPolynomial σ R →+* MvPowerSeries σ R where
  toFun := (Coe.coe : MvPolynomial σ R → MvPowerSeries σ R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp, norm_cast]
theorem coe_pow (n : ℕ) :
    ((φ ^ n : MvPolynomial σ R) : MvPowerSeries σ R) = (φ : MvPowerSeries σ R) ^ n :=
  coeToMvPowerSeries.ringHom.map_pow _ _

variable (φ ψ)

@[simp]
theorem coeToMvPowerSeries.ringHom_apply : coeToMvPowerSeries.ringHom φ = φ :=
  rfl

theorem _root_.MvPowerSeries.monomial_one_eq
    (e : σ →₀ ℕ) :
    MvPowerSeries.monomial e (1 : R) =
      e.prod fun s n ↦ (MvPowerSeries.X s) ^ n := by
  simp only [← coe_X, ← coe_pow, ← coe_monomial, monomial_eq, map_one, one_mul]
  simp only [← coeToMvPowerSeries.ringHom_apply, ← map_finsuppProd]

section Algebra

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- The coercion from multivariate polynomials to multivariate power series
as an algebra homomorphism.
-/
def coeToMvPowerSeries.algHom : MvPolynomial σ R →ₐ[R] MvPowerSeries σ A :=
  { (MvPowerSeries.map (algebraMap R A)).comp coeToMvPowerSeries.ringHom with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

@[simp]
theorem coeToMvPowerSeries.algHom_apply :
    coeToMvPowerSeries.algHom A φ = MvPowerSeries.map (algebraMap R A) ↑φ :=
  rfl

theorem _root_.MvPowerSeries.prod_smul_X_eq_smul_monomial_one
    {A : Type*} [CommSemiring A] [Algebra A R] (e : σ →₀ ℕ) (a : σ → A) :
    e.prod (fun s n ↦ ((a s • MvPowerSeries.X s) ^ n))
      = (e.prod fun s n ↦ (a s) ^ n) • MvPowerSeries.monomial (R := R) e 1 := by
  rw [Finsupp.prod_congr
    (g2 := fun s n ↦ ((MvPowerSeries.C (algebraMap A R (a s)) * (MvPowerSeries.X s)) ^ n))]
  · have (a : A) (f : MvPowerSeries σ R) : a • f =
      MvPowerSeries.C ((algebraMap A R) a) * f := by
      rw [← MvPowerSeries.smul_eq_C_mul, IsScalarTower.algebraMap_smul]
    simp only [mul_pow, Finsupp.prod_mul, ← map_pow, ← MvPowerSeries.monomial_one_eq, this]
    simp only [map_finsuppProd, map_pow]
  · intro x _
    rw [algebra_compatible_smul R, MvPowerSeries.smul_eq_C_mul]

theorem _root_.MvPowerSeries.monomial_eq (e : σ →₀ ℕ) (r : σ → R) :
    MvPowerSeries.monomial e (e.prod (fun s n => r s ^ n))
      = e.prod fun s e => (r s • MvPowerSeries.X s) ^ e := by
  rw [MvPowerSeries.prod_smul_X_eq_smul_monomial_one, ← map_smul, smul_eq_mul, mul_one]

theorem _root_.MvPowerSeries.monomial_smul_const
    {σ : Type*} {R : Type*} [CommSemiring R]
    (e : σ →₀ ℕ) (r : R) :
    MvPowerSeries.monomial e (r ^ (e.sum fun _ n => n))
      = (e.prod fun s e => (r • MvPowerSeries.X s) ^ e) := by
  rw [MvPowerSeries.prod_smul_X_eq_smul_monomial_one, ← map_smul, smul_eq_mul, mul_one]
  simp only [Finsupp.sum, Finsupp.prod, Finset.prod_pow_eq_pow_sum]

end Algebra

end MvPolynomial

namespace MvPowerSeries

variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : MvPowerSeries σ R)

instance algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPowerSeries σ A) :=
  RingHom.toAlgebra (MvPolynomial.coeToMvPowerSeries.algHom A).toRingHom

instance algebraMvPowerSeries : Algebra (MvPowerSeries σ R) (MvPowerSeries σ A) :=
  (map (algebraMap R A)).toAlgebra

variable (A)

theorem algebraMap_apply' (p : MvPolynomial σ R) :
    algebraMap (MvPolynomial σ R) (MvPowerSeries σ A) p = map (algebraMap R A) p :=
  rfl

theorem algebraMap_apply'' :
    algebraMap (MvPowerSeries σ R) (MvPowerSeries σ A) f = map (algebraMap R A) f :=
  rfl

end MvPowerSeries

end
