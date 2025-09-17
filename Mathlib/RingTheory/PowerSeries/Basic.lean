/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic.MoveAdd
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Basic

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
* `Mathlib/RingTheory/PowerSeries/Trunc.lean`, truncation of power series;
* `Mathlib/RingTheory/PowerSeries/Inverse.lean`, about inverses of power series,
  and the fact that power series over a local ring form a local ring;
* `Mathlib/RingTheory/PowerSeries/Order.lean`, the order of a power series at 0,
  and application to the fact that power series over an integral domain form an integral domain.

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
abbrev PowerSeries (R : Type*) :=
  MvPowerSeries Unit R

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section

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

variable [Semiring R]

/-- The `n`th coefficient of a formal power series. -/
def coeff (n : ℕ) : R⟦X⟧ →ₗ[R] R :=
  MvPowerSeries.coeff (single () n)

/-- The `n`th monomial with coefficient `a` as formal power series. -/
def monomial (n : ℕ) : R →ₗ[R] R⟦X⟧ :=
  MvPowerSeries.monomial (single () n)

theorem coeff_def {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) :
    coeff (R := R) n = MvPowerSeries.coeff s := by
  rw [coeff, ← h, ← Finsupp.unique_single s]

/-- Two formal power series are equal if all their coefficients are equal. -/
@[ext]
theorem ext {φ ψ : R⟦X⟧} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
  MvPowerSeries.ext fun n => by
    rw [← coeff_def]
    · apply h
    rfl

@[simp]
theorem forall_coeff_eq_zero (φ : R⟦X⟧) : (∀ n, coeff n φ = 0) ↔ φ = 0 :=
  ⟨fun h => ext h, fun h => by simp [h]⟩

/-- Two formal power series are equal if all their coefficients are equal. -/
add_decl_doc PowerSeries.ext_iff

instance [Subsingleton R] : Subsingleton R⟦X⟧ := by
  simp only [subsingleton_iff, PowerSeries.ext_iff]
  subsingleton

/-- Constructor for formal power series. -/
def mk {R} (f : ℕ → R) : R⟦X⟧ := fun s => f (s ())

@[simp]
theorem coeff_mk (n : ℕ) (f : ℕ → R) : coeff n (mk f) = f n :=
  congr_arg f Finsupp.single_eq_same

theorem coeff_monomial (m n : ℕ) (a : R) : coeff m (monomial n a) = if m = n then a else 0 :=
  calc
    coeff m (monomial n a) = _ := MvPowerSeries.coeff_monomial _ _ _
    _ = if m = n then a else 0 := by simp only [Finsupp.unique_single_eq_iff]

theorem monomial_eq_mk (n : ℕ) (a : R) : monomial n a = mk fun m => if m = n then a else 0 :=
  ext fun m => by rw [coeff_monomial, coeff_mk]

@[simp]
theorem coeff_monomial_same (n : ℕ) (a : R) : coeff n (monomial n a) = a :=
  MvPowerSeries.coeff_monomial_same _ _

@[simp]
theorem coeff_comp_monomial (n : ℕ) : (coeff (R := R) n).comp (monomial n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n

theorem monomial_mul_monomial (m n : ℕ) (a b : R) :
    monomial m a * monomial n b = monomial (m + n) (a * b) := by
  simpa [monomial] using
    MvPowerSeries.monomial_mul_monomial (Finsupp.single () m) (Finsupp.single () n) a b

/-- The constant coefficient of a formal power series. -/
def constantCoeff : R⟦X⟧ →+* R :=
  MvPowerSeries.constantCoeff

/-- The constant formal power series. -/
def C : R →+* R⟦X⟧ :=
  MvPowerSeries.C

@[simp] lemma algebraMap_eq {R : Type*} [CommSemiring R] : algebraMap R R⟦X⟧ = C := rfl

/-- The variable of the formal power series ring. -/
def X : R⟦X⟧ :=
  MvPowerSeries.X ()

theorem commute_X (φ : R⟦X⟧) : Commute φ X :=
  MvPowerSeries.commute_X _ _

theorem X_mul {φ : R⟦X⟧} : X * φ = φ * X :=
  MvPowerSeries.X_mul

theorem commute_X_pow (φ : R⟦X⟧) (n : ℕ) : Commute φ (X ^ n) :=
  MvPowerSeries.commute_X_pow _ _ _

theorem X_pow_mul {φ : R⟦X⟧} {n : ℕ} : X ^ n * φ = φ * X ^ n :=
  MvPowerSeries.X_pow_mul

@[simp]
theorem coeff_zero_eq_constantCoeff : ⇑(coeff (R := R) 0) = constantCoeff := by
  rw [coeff, Finsupp.single_zero]
  rfl

theorem coeff_zero_eq_constantCoeff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ := by
  rw [coeff_zero_eq_constantCoeff]

@[simp]
theorem monomial_zero_eq_C : ⇑(monomial (R := R) 0) = C := by
  -- This used to be `rw`, but we need `rw; rfl` after https://github.com/leanprover/lean4/pull/2644
  rw [monomial, Finsupp.single_zero, MvPowerSeries.monomial_zero_eq_C]
  rfl

theorem monomial_zero_eq_C_apply (a : R) : monomial 0 a = C a := by simp

theorem coeff_C (n : ℕ) (a : R) : coeff n (C a : R⟦X⟧) = if n = 0 then a else 0 := by
  rw [← monomial_zero_eq_C_apply, coeff_monomial]

@[simp]
theorem coeff_zero_C (a : R) : coeff 0 (C a) = a := by
  rw [coeff_C, if_pos rfl]

theorem coeff_ne_zero_C {a : R} {n : ℕ} (h : n ≠ 0) : coeff n (C a) = 0 := by
  rw [coeff_C, if_neg h]

@[simp]
theorem coeff_succ_C {a : R} {n : ℕ} : coeff (n + 1) (C a) = 0 :=
  coeff_ne_zero_C n.succ_ne_zero

theorem C_injective : Function.Injective (C (R := R)) := by
  intro a b H
  simp_rw [PowerSeries.ext_iff] at H
  simpa only [coeff_zero_C] using H 0

protected theorem subsingleton_iff : Subsingleton R⟦X⟧ ↔ Subsingleton R := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [subsingleton_iff] at h ⊢
  exact fun a b ↦ C_injective (h (C a) (C b))

theorem X_eq : (X : R⟦X⟧) = monomial 1 1 :=
  rfl

theorem coeff_X (n : ℕ) : coeff n (X : R⟦X⟧) = if n = 1 then 1 else 0 := by
  rw [X_eq, coeff_monomial]

@[simp]
theorem coeff_zero_X : coeff 0 (X : R⟦X⟧) = 0 := by
  rw [coeff, Finsupp.single_zero, X, MvPowerSeries.coeff_zero_X]

@[simp]
theorem coeff_one_X : coeff 1 (X : R⟦X⟧) = 1 := by rw [coeff_X, if_pos rfl]

@[simp]
theorem X_ne_zero [Nontrivial R] : (X : R⟦X⟧) ≠ 0 := fun H => by
  simpa only [coeff_one_X, one_ne_zero, map_zero] using congr_arg (coeff 1) H

theorem X_pow_eq (n : ℕ) : (X : R⟦X⟧) ^ n = monomial n 1 :=
  MvPowerSeries.X_pow_eq _ n

theorem coeff_X_pow (m n : ℕ) : coeff m ((X : R⟦X⟧) ^ n) = if m = n then 1 else 0 := by
  rw [X_pow_eq, coeff_monomial]

@[simp]
theorem coeff_X_pow_self (n : ℕ) : coeff n ((X : R⟦X⟧) ^ n) = 1 := by
  rw [coeff_X_pow, if_pos rfl]

@[simp]
theorem coeff_one (n : ℕ) : coeff n (1 : R⟦X⟧) = if n = 0 then 1 else 0 :=
  coeff_C n 1

theorem coeff_zero_one : coeff 0 (1 : R⟦X⟧) = 1 :=
  coeff_zero_C 1

theorem coeff_mul (n : ℕ) (φ ψ : R⟦X⟧) :
    coeff n (φ * ψ) = ∑ p ∈ antidiagonal n, coeff p.1 φ * coeff p.2 ψ := by
  -- `rw` can't see that `PowerSeries = MvPowerSeries Unit`, so use `.trans`
  refine (MvPowerSeries.coeff_mul _ φ ψ).trans ?_
  rw [Finsupp.antidiagonal_single, Finset.sum_map]
  rfl

@[simp]
theorem coeff_mul_C (n : ℕ) (φ : R⟦X⟧) (a : R) : coeff n (φ * C a) = coeff n φ * a :=
  MvPowerSeries.coeff_mul_C _ φ a

@[simp]
theorem coeff_C_mul (n : ℕ) (φ : R⟦X⟧) (a : R) : coeff n (C a * φ) = a * coeff n φ :=
  MvPowerSeries.coeff_C_mul _ φ a

@[simp]
theorem coeff_smul {S : Type*} [Semiring S] [Module R S] (n : ℕ) (φ : PowerSeries S) (a : R) :
    coeff n (a • φ) = a • coeff n φ :=
  rfl

@[simp]
theorem constantCoeff_smul {S : Type*} [Semiring S] [Module R S] (φ : PowerSeries S) (a : R) :
    constantCoeff (a • φ) = a • constantCoeff φ :=
  rfl

theorem smul_eq_C_mul (f : R⟦X⟧) (a : R) : a • f = C a * f := by
  ext
  simp

@[simp]
theorem coeff_succ_mul_X (n : ℕ) (φ : R⟦X⟧) : coeff (n + 1) (φ * X) = coeff n φ := by
  simp only [coeff, Finsupp.single_add]
  convert φ.coeff_add_mul_monomial (single () n) (single () 1) _
  rw [mul_one]

@[simp]
theorem coeff_succ_X_mul (n : ℕ) (φ : R⟦X⟧) : coeff (n + 1) (X * φ) = coeff n φ := by
  simp only [coeff, Finsupp.single_add, add_comm n 1]
  convert φ.coeff_add_monomial_mul (single () 1) (single () n) _
  rw [one_mul]

theorem mul_X_cancel {φ ψ : R⟦X⟧} (h : φ * X = ψ * X) : φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + 1)

theorem mul_X_injective : Function.Injective (· * X : R⟦X⟧ → R⟦X⟧) :=
  fun _ _ ↦ mul_X_cancel

theorem mul_X_inj {φ ψ : R⟦X⟧} : φ * X = ψ * X ↔ φ = ψ :=
  mul_X_injective.eq_iff

theorem X_mul_cancel {φ ψ : R⟦X⟧} (h : X * φ = X * ψ) : φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + 1)

theorem X_mul_injective : Function.Injective (X * · : R⟦X⟧ → R⟦X⟧) :=
  fun _ _ ↦ X_mul_cancel

theorem X_mul_inj {φ ψ : R⟦X⟧} : X * φ = X * ψ ↔ φ = ψ :=
  X_mul_injective.eq_iff

@[simp]
theorem constantCoeff_C (a : R) : constantCoeff (C a) = a :=
  rfl

@[simp]
theorem constantCoeff_comp_C : constantCoeff.comp C = RingHom.id R :=
  rfl

@[simp]
theorem constantCoeff_zero : constantCoeff (R := R) 0 = 0 :=
  rfl

@[simp]
theorem constantCoeff_one : constantCoeff (R := R) 1 = 1 :=
  rfl

@[simp]
theorem constantCoeff_X : constantCoeff (R := R) X = 0 :=
  MvPowerSeries.coeff_zero_X _

@[simp]
theorem constantCoeff_mk {f : ℕ → R} : constantCoeff (mk f) = f 0 := rfl

theorem coeff_zero_mul_X (φ : R⟦X⟧) : coeff 0 (φ * X) = 0 := by simp

theorem coeff_zero_X_mul (φ : R⟦X⟧) : coeff 0 (X * φ) = 0 := by simp

theorem constantCoeff_surj : Function.Surjective (constantCoeff (R := R)) :=
  fun r => ⟨C r, constantCoeff_C r⟩

-- The following section duplicates the API of `Mathlib.Data.Polynomial.Coeff` and should attempt
-- to keep up to date with that
section

theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) :
    coeff n (C x * X ^ k : R⟦X⟧) = if n = k then x else 0 := by
  simp [X_pow_eq, coeff_monomial]

@[simp]
theorem coeff_mul_X_pow (p : R⟦X⟧) (n d : ℕ) :
    coeff (d + n) (p * X ^ n) = coeff d p := by
  rw [coeff_mul, Finset.sum_eq_single (d, n), coeff_X_pow, if_pos rfl, mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow, if_neg, mul_zero]
    rintro rfl
    apply h2
    rw [mem_antidiagonal, add_right_cancel_iff] at h1
    subst h1
    rfl
  · exact fun h1 => (h1 (mem_antidiagonal.2 rfl)).elim

@[simp]
theorem coeff_X_pow_mul (p : R⟦X⟧) (n d : ℕ) :
    coeff (d + n) (X ^ n * p) = coeff d p := by
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

theorem mul_X_pow_cancel {k : ℕ} {φ ψ : R⟦X⟧} (h : φ * X ^ k = ψ * X ^ k) :
    φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + k)

theorem mul_X_pow_injective {k : ℕ} : Function.Injective (· * X ^ k : R⟦X⟧ → R⟦X⟧) :=
  fun _ _ ↦ mul_X_pow_cancel

theorem mul_X_pow_inj {k : ℕ} {φ ψ : R⟦X⟧} :
    φ * X ^ k = ψ * X ^ k ↔ φ = ψ :=
  mul_X_pow_injective.eq_iff

theorem X_pow_mul_cancel {k : ℕ} {φ ψ : R⟦X⟧} (h : X ^ k * φ = X ^ k * ψ) :
    φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + k)

theorem X_pow_mul_injective {k : ℕ} : Function.Injective (X ^ k * · : R⟦X⟧ → R⟦X⟧) :=
  fun _ _ ↦ X_pow_mul_cancel

theorem X_pow_mul_inj {k : ℕ} {φ ψ : R⟦X⟧} :
    X ^ k * φ = X ^ k * ψ ↔ φ = ψ :=
  X_pow_mul_injective.eq_iff

theorem coeff_mul_X_pow' (p : R⟦X⟧) (n d : ℕ) :
    coeff d (p * X ^ n) = ite (n ≤ d) (coeff (d - n) p) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow, if_neg, mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne

theorem coeff_X_pow_mul' (p : R⟦X⟧) (n d : ℕ) :
    coeff d (X ^ n * p) = ite (n ≤ d) (coeff (d - n) p) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_X_pow_mul]
    simp
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow, if_neg, zero_mul]
    have := mem_antidiagonal.mp hx
    rw [add_comm] at this
    exact ((le_of_add_le_right this.le).trans_lt <| not_le.mp h).ne

end

/-- If a formal power series is invertible, then so is its constant coefficient. -/
theorem isUnit_constantCoeff (φ : R⟦X⟧) (h : IsUnit φ) : IsUnit (constantCoeff φ) :=
  MvPowerSeries.isUnit_constantCoeff φ h

/-- Split off the constant coefficient. -/
theorem eq_shift_mul_X_add_const (φ : R⟦X⟧) :
    φ = (mk fun p => coeff (p + 1) φ) * X + C (constantCoeff φ) := by
  ext (_ | n)
  · simp only [coeff_zero_eq_constantCoeff, map_add, map_mul, constantCoeff_X,
      mul_zero, coeff_zero_C, zero_add]
  · simp only [coeff_succ_mul_X, coeff_mk, LinearMap.map_add, coeff_C, n.succ_ne_zero,
      if_false, add_zero]

/-- Split off the constant coefficient. -/
theorem eq_X_mul_shift_add_const (φ : R⟦X⟧) :
    φ = (X * mk fun p => coeff (p + 1) φ) + C (constantCoeff φ) := by
  ext (_ | n)
  · simp only [coeff_zero_eq_constantCoeff, map_add, map_mul, constantCoeff_X,
      zero_mul, coeff_zero_C, zero_add]
  · simp only [coeff_succ_X_mul, coeff_mk, LinearMap.map_add, coeff_C, n.succ_ne_zero,
      if_false, add_zero]

section Map

variable {S : Type*} {T : Type*} [Semiring S] [Semiring T]
variable (f : R →+* S) (g : S →+* T)

/-- The map between formal power series induced by a map on the coefficients. -/
def map : R⟦X⟧ →+* S⟦X⟧ :=
  MvPowerSeries.map f

@[simp]
theorem map_id : (map (RingHom.id R) : R⟦X⟧ → R⟦X⟧) = id :=
  rfl

theorem map_comp : map (g.comp f) = (map g).comp (map f) :=
  rfl

@[simp]
theorem coeff_map (n : ℕ) (φ : R⟦X⟧) : coeff n (map f φ) = f (coeff n φ) :=
  rfl

@[simp]
theorem map_C (r : R) : map f (C r) = C (f r) := by
  ext
  simp [coeff_C, apply_ite f]

@[simp]
theorem map_X : map f X = X := by
  ext
  simp [coeff_X, apply_ite f]

theorem map_surjective (f : S →+* T) (hf : Function.Surjective f) :
    Function.Surjective (PowerSeries.map f) := by
  intro g
  use PowerSeries.mk fun k ↦ Function.surjInv hf (PowerSeries.coeff k g)
  ext k
  simp only [Function.surjInv, coeff_map, coeff_mk]
  exact Classical.choose_spec (hf (coeff k g))

theorem map_injective (f : S →+* T) (hf : Function.Injective ⇑f) :
    Function.Injective (PowerSeries.map f) := by
  intro u v huv
  ext k
  apply hf
  rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map, huv]

end Map

@[simp]
theorem map_eq_zero {R S : Type*} [DivisionSemiring R] [Semiring S] [Nontrivial S] (φ : R⟦X⟧)
    (f : R →+* S) : φ.map f = 0 ↔ φ = 0 :=
  MvPowerSeries.map_eq_zero _ _

theorem X_pow_dvd_iff {n : ℕ} {φ : R⟦X⟧} :
    (X : R⟦X⟧) ^ n ∣ φ ↔ ∀ m, m < n → coeff m φ = 0 := by
  convert @MvPowerSeries.X_pow_dvd_iff Unit R _ () n φ
  constructor <;> intro h m hm
  · rw [Finsupp.unique_single m]
    convert h _ hm
  · apply h
    simpa only [Finsupp.single_eq_same] using hm

theorem X_dvd_iff {φ : R⟦X⟧} : (X : R⟦X⟧) ∣ φ ↔ constantCoeff φ = 0 := by
  rw [← pow_one (X : R⟦X⟧), X_pow_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]
  constructor <;> intro h
  · exact h 0 zero_lt_one
  · intro m hm
    rwa [Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hm)]

end Semiring

section CommSemiring

variable [CommSemiring R]

open Finset Nat

/-- The ring homomorphism taking a power series `f(X)` to `f(aX)`. -/
noncomputable def rescale (a : R) : R⟦X⟧ →+* R⟦X⟧ where
  toFun f := PowerSeries.mk fun n => a ^ n * PowerSeries.coeff n f
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

@[simp]
theorem coeff_rescale (f : R⟦X⟧) (a : R) (n : ℕ) :
    coeff n (rescale a f) = a ^ n * coeff n f :=
  coeff_mk n (fun n ↦ a ^ n * coeff n f)

@[simp]
theorem rescale_zero : rescale 0 = (C (R := R)).comp constantCoeff := by
  ext x n
  simp only [Function.comp_apply, RingHom.coe_comp, rescale, RingHom.coe_mk,
    coeff_C]
  split_ifs with h <;> simp [h]

theorem rescale_zero_apply (f : R⟦X⟧) : rescale 0 f = C (constantCoeff f) := by simp

@[simp]
theorem rescale_one : rescale 1 = RingHom.id R⟦X⟧ := by
  ext
  simp [coeff_rescale]

theorem rescale_mk (f : ℕ → R) (a : R) : rescale a (mk f) = mk fun n : ℕ => a ^ n * f n := by
  ext
  rw [coeff_rescale, coeff_mk, coeff_mk]

theorem rescale_rescale (f : R⟦X⟧) (a b : R) :
    rescale b (rescale a f) = rescale (a * b) f := by
  ext n
  simp_rw [coeff_rescale]
  rw [mul_pow, mul_comm _ (b ^ n), mul_assoc]

theorem rescale_mul (a b : R) : rescale (a * b) = (rescale b).comp (rescale a) := by
  ext
  simp [← rescale_rescale]

end CommSemiring

section CommSemiring

open Finset.HasAntidiagonal Finset

variable {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]

/-- Coefficients of a product of power series -/
theorem coeff_prod (f : ι → PowerSeries R) (d : ℕ) (s : Finset ι) :
    coeff d (∏ j ∈ s, f j) = ∑ l ∈ finsuppAntidiag s d, ∏ i ∈ s, coeff (l i) (f i) := by
  simp only [coeff]
  rw [MvPowerSeries.coeff_prod, ← AddEquiv.finsuppUnique_symm d, ← mapRange_finsuppAntidiag_eq,
    sum_map, sum_congr rfl]
  intro x _
  apply prod_congr rfl
  intro i _
  congr 2
  simp only [AddEquiv.toEquiv_eq_coe, Finsupp.mapRange.addEquiv_toEquiv, AddEquiv.toEquiv_symm,
    Equiv.coe_toEmbedding, Finsupp.mapRange.equiv_apply, AddEquiv.coe_toEquiv_symm,
    Finsupp.mapRange_apply, AddEquiv.finsuppUnique_symm]

theorem prod_monomial (f : ι → ℕ) (g : ι → R) (s : Finset ι) :
    ∏ i ∈ s, monomial (f i) (g i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, g i) := by
  simpa [monomial, Finsupp.single_finset_sum] using
    MvPowerSeries.prod_monomial (fun i ↦ Finsupp.single () (f i)) g s

theorem monmial_pow (m : ℕ) (a : R) (n : ℕ) : (monomial m a) ^ n = monomial (n * m) (a ^ n) := by
  simpa [monomial] using MvPowerSeries.monmial_pow (Finsupp.single () m) a n

/-- The `n`-th coefficient of the `k`-th power of a power series. -/
lemma coeff_pow (k n : ℕ) (φ : R⟦X⟧) :
    coeff n (φ ^ k) = ∑ l ∈ finsuppAntidiag (range k) n, ∏ i ∈ range k, coeff (l i) φ := by
  have h₁ (i : ℕ) : Function.const ℕ φ i = φ := rfl
  have h₂ (i : ℕ) : ∏ j ∈ range i, Function.const ℕ φ j = φ ^ i := by
    apply prod_range_induction (fun _ => φ) (fun i => φ ^ i) rfl i (fun _ => congrFun rfl)
  rw [← h₂, ← h₁ k]
  apply coeff_prod (f := Function.const ℕ φ) (d := n) (s := range k)

/-- First coefficient of the product of two power series. -/
lemma coeff_one_mul (φ ψ : R⟦X⟧) : coeff 1 (φ * ψ) =
    coeff 1 φ * constantCoeff ψ + coeff 1 ψ * constantCoeff φ := by
  have : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
  rw [coeff_mul, this, Finset.sum_insert, Finset.sum_singleton, coeff_zero_eq_constantCoeff,
    mul_comm, add_comm]
  norm_num

/-- First coefficient of the `n`-th power of a power series. -/
lemma coeff_one_pow (n : ℕ) (φ : R⟦X⟧) :
    coeff 1 (φ ^ n) = n * coeff 1 φ * (constantCoeff φ) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with (rfl | hn)
  · simp
  induction n with
  | zero => omega
  | succ n' ih =>
      have h₁ (m : ℕ) : φ ^ (m + 1) = φ ^ m * φ := by exact rfl
      have h₂ : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
      rw [h₁, coeff_mul, h₂, Finset.sum_insert, Finset.sum_singleton]
      · simp only [coeff_zero_eq_constantCoeff, map_pow, Nat.cast_add, Nat.cast_one,
          add_tsub_cancel_right]
        have h₀ : n' = 0 ∨ 1 ≤ n' := by omega
        rcases h₀ with h' | h'
        · by_contra h''
          rw [h'] at h''
          simp only [pow_zero, one_mul, coeff_one, one_ne_zero, ↓reduceIte, zero_mul, add_zero,
            mul_one] at h''
          norm_num at h''
        · rw [ih]
          · conv => lhs; arg 2; rw [mul_comm, ← mul_assoc]
            move_mul [← constantCoeff φ ^ (n' - 1)]
            conv => enter [1, 2, 1, 1, 2]; rw [← pow_one (a := constantCoeff φ)]
            rw [← pow_add (a := constantCoeff φ)]
            conv => enter [1, 2, 1, 1]; rw [Nat.sub_add_cancel h']
            ring
          exact h'
      · decide

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
theorem rescale_X (a : A) : rescale a X = C a * X := by
  ext
  simp only [coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with h <;> simp [h]

theorem rescale_neg_one_X : rescale (-1 : A) X = -X := by
  rw [rescale_X, map_neg, map_one, neg_one_mul]

/-- The ring homomorphism taking a power series `f(X)` to `f(-X)`. -/
noncomputable def evalNegHom : A⟦X⟧ →+* A⟦X⟧ :=
  rescale (-1 : A)

@[simp]
theorem evalNegHom_X : evalNegHom (X : A⟦X⟧) = -X :=
  rescale_neg_one_X

end CommRing

section Algebra

variable {A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem C_eq_algebraMap {r : R} : C r = (algebraMap R R⟦X⟧) r :=
  rfl

theorem algebraMap_apply {r : R} : algebraMap R A⟦X⟧ r = C (algebraMap R A r) :=
  MvPowerSeries.algebraMap_apply

instance [Nontrivial R] : Nontrivial (Subalgebra R R⟦X⟧) :=
  { inferInstanceAs <| Nontrivial <| Subalgebra R <| MvPowerSeries Unit R with }

/-- Change of coefficients in power series, as an `AlgHom` -/
def mapAlgHom (φ : A →ₐ[R] B) :
    PowerSeries A →ₐ[R] PowerSeries B :=
  MvPowerSeries.mapAlgHom φ

theorem mapAlgHom_apply (φ : A →ₐ[R] B) (f : A⟦X⟧) :
    mapAlgHom φ f = f.map φ :=
  MvPowerSeries.mapAlgHom_apply φ f

end Algebra

end PowerSeries

namespace Polynomial

open Finsupp Polynomial

section Semiring
variable {R : Type*} [Semiring R] (φ ψ : R[X])

/-- The natural inclusion from polynomials into formal power series. -/
@[coe]
def toPowerSeries : R[X] → PowerSeries R := fun φ =>
  PowerSeries.mk fun n => coeff φ n

/-- The natural inclusion from polynomials into formal power series. -/
instance coeToPowerSeries : Coe R[X] (PowerSeries R) :=
  ⟨toPowerSeries⟩

theorem coe_def : (φ : PowerSeries R) = PowerSeries.mk (coeff φ) :=
  rfl

@[simp, norm_cast]
theorem coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n :=
  congr_arg (coeff φ) Finsupp.single_eq_same

@[simp, norm_cast]
theorem coe_monomial (n : ℕ) (a : R) :
    (monomial n a : PowerSeries R) = PowerSeries.monomial n a := by
  ext
  simp [coeff_coe, PowerSeries.coeff_monomial, Polynomial.coeff_monomial, eq_comm]

@[simp, norm_cast]
theorem coe_zero : ((0 : R[X]) : PowerSeries R) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R[X]) : PowerSeries R) = 1 := by
  have := coe_monomial 0 (1 : R)
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]
theorem coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ := by
  ext
  simp

@[simp, norm_cast]
theorem coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ :=
  PowerSeries.ext fun n => by simp only [coeff_coe, PowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]
theorem coe_C (a : R) : ((C a : R[X]) : PowerSeries R) = PowerSeries.C a := by
  have := coe_monomial 0 a
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]
theorem coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X :=
  coe_monomial _ _

@[simp]
lemma polynomial_map_coe {U V : Type*} [CommSemiring U] [CommSemiring V] {φ : U →+* V}
    {f : Polynomial U} : Polynomial.map φ f = PowerSeries.map φ f := by
  ext
  simp

@[simp]
theorem constantCoeff_coe : PowerSeries.constantCoeff φ = φ.coeff 0 :=
  rfl

variable (R)

theorem coe_injective : Function.Injective ((↑) : R[X] → PowerSeries R) := fun x y h => by
  ext
  simp_rw [← coeff_coe, h]

variable {R φ ψ}

@[simp, norm_cast]
theorem coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ :=
  (coe_injective R).eq_iff

@[simp]
theorem coe_eq_zero_iff : (φ : PowerSeries R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]

@[simp]
theorem coe_eq_one_iff : (φ : PowerSeries R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]

/-- The coercion from polynomials to power series
as a ring homomorphism.
-/
def coeToPowerSeries.ringHom : R[X] →+* PowerSeries R where
  toFun := (↑)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp]
theorem coeToPowerSeries.ringHom_apply : coeToPowerSeries.ringHom φ = φ :=
  rfl

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((φ ^ n : R[X]) : PowerSeries R) = (φ : PowerSeries R) ^ n :=
  coeToPowerSeries.ringHom.map_pow _ _

theorem eval₂_C_X_eq_coe : φ.eval₂ PowerSeries.C PowerSeries.X = ↑φ := by
  nth_rw 2 [← eval₂_C_X (p := φ)]
  rw [← coeToPowerSeries.ringHom_apply, eval₂_eq_sum_range, eval₂_eq_sum_range, map_sum]
  apply Finset.sum_congr rfl
  intros
  rw [map_mul, map_pow, coeToPowerSeries.ringHom_apply,
    coeToPowerSeries.ringHom_apply, coe_C, coe_X]

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R] (φ ψ : R[X])

theorem _root_.MvPolynomial.toMvPowerSeries_pUnitAlgEquiv {f : MvPolynomial PUnit R} :
    (f.toMvPowerSeries : PowerSeries R) = (f.pUnitAlgEquiv R).toPowerSeries := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    --Note: this `have` should be a generic `simp` lemma for a `Unique` type with `()` replaced
    --by any element.
    have : single () (d ()) = d := by ext; simp
    simp only [MvPolynomial.coe_monomial, MvPolynomial.pUnitAlgEquiv_monomial,
      Polynomial.coe_monomial, PowerSeries.monomial, this]
  | add f g hf hg => simp [hf, hg]

theorem pUnitAlgEquiv_symm_toPowerSeries {f : Polynomial R} :
    ((f.toPowerSeries) : MvPowerSeries PUnit R)
      = ((MvPolynomial.pUnitAlgEquiv R).symm f).toMvPowerSeries := by
  set g := (MvPolynomial.pUnitAlgEquiv R).symm f
  have : f = MvPolynomial.pUnitAlgEquiv R g := by simp only [g, AlgEquiv.apply_symm_apply]
  rw [this, MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]

variable (A : Type*) [Semiring A] [Algebra R A]

/-- The coercion from polynomials to power series
as an algebra homomorphism.
-/
def coeToPowerSeries.algHom : R[X] →ₐ[R] PowerSeries A :=
  { (PowerSeries.map (algebraMap R A)).comp coeToPowerSeries.ringHom with
    commutes' := fun r => by simp [PowerSeries.algebraMap_apply] }

@[simp]
theorem coeToPowerSeries.algHom_apply :
    coeToPowerSeries.algHom A φ = PowerSeries.map (algebraMap R A) ↑φ :=
  rfl

end CommSemiring

section CommRing
variable {R : Type*} [CommRing R]

@[simp, norm_cast]
lemma coe_neg (p : R[X]) : ((-p : R[X]) : PowerSeries R) = -p :=
  coeToPowerSeries.ringHom.map_neg p

@[simp, norm_cast]
lemma coe_sub (p q : R[X]) : ((p - q : R[X]) : PowerSeries R) = p - q :=
  coeToPowerSeries.ringHom.map_sub p q

end CommRing

end Polynomial

namespace PowerSeries

section Algebra

open Polynomial

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : R⟦X⟧)

instance algebraPolynomial : Algebra R[X] A⟦X⟧ :=
  RingHom.toAlgebra (Polynomial.coeToPowerSeries.algHom A).toRingHom

instance algebraPowerSeries : Algebra R⟦X⟧ A⟦X⟧ :=
  (map (algebraMap R A)).toAlgebra

-- see Note [lower instance priority]
instance (priority := 100) algebraPolynomial' {A : Type*} [CommSemiring A] [Algebra R A[X]] :
    Algebra R A⟦X⟧ :=
  RingHom.toAlgebra <| Polynomial.coeToPowerSeries.ringHom.comp (algebraMap R A[X])

variable (A)

theorem algebraMap_apply' (p : R[X]) : algebraMap R[X] A⟦X⟧ p = map (algebraMap R A) p :=
  rfl

theorem algebraMap_apply'' :
    algebraMap R⟦X⟧ A⟦X⟧ f = map (algebraMap R A) f :=
  rfl

end Algebra

end PowerSeries

end
