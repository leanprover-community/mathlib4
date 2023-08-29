/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Coeff
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic.Linarith

#align_import ring_theory.power_series.basic from "leanprover-community/mathlib"@"2d5739b61641ee4e7e53eca5688a08f66f2e6a60"

/-!
# Formal power series

This file defines (multivariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from polynomials to formal power series.

## Generalities

The file starts with setting up the (semi)ring structure on multivariate power series.

`trunc n φ` truncates a formal power series to the polynomial
that has the same coefficients as `φ`, for all `m < n`, and `0` otherwise.

If the constant coefficient of a formal power series is invertible,
then this formal power series is invertible.

Formal power series over a local ring form a local ring.

## Formal power series in one variable

We prove that if the ring of coefficients is an integral domain,
then formal power series in one variable form an integral domain.

The `order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `order` is a valuation
(`order_mul`, `le_order_add`).

## Implementation notes

In this file we define multivariate formal power series with
variables indexed by `σ` and coefficients in `R` as
`MvPowerSeries σ R := (σ →₀ ℕ) → R`.
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

Formal power series in one variable are defined as
`PowerSeries R := MvPowerSeries Unit R`.

This allows us to port a lot of proofs and properties
from the multivariate case to the single variable case.
However, it means that formal power series are indexed by `Unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they are indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.
-/


noncomputable section

open Classical BigOperators Polynomial

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring.-/
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

/-- The `n`th monomial with coefficient `a` as multivariate formal power series.-/
def monomial (n : σ →₀ ℕ) : R →ₗ[R] MvPowerSeries σ R :=
  LinearMap.stdBasis R (fun _ ↦ R) n
#align mv_power_series.monomial MvPowerSeries.monomial

/-- The `n`th coefficient of a multivariate formal power series.-/
def coeff (n : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] R :=
  LinearMap.proj n
#align mv_power_series.coeff MvPowerSeries.coeff

variable {R}

/-- Two multivariate formal power series are equal if all their coefficients are equal.-/
@[ext]
theorem ext {φ ψ} (h : ∀ n : σ →₀ ℕ, coeff R n φ = coeff R n ψ) : φ = ψ :=
  funext h
#align mv_power_series.ext MvPowerSeries.ext

/-- Two multivariate formal power series are equal
 if and only if all their coefficients are equal.-/
theorem ext_iff {φ ψ : MvPowerSeries σ R} : φ = ψ ↔ ∀ n : σ →₀ ℕ, coeff R n φ = coeff R n ψ :=
  Function.funext_iff
#align mv_power_series.ext_iff MvPowerSeries.ext_iff

theorem monomial_def [DecidableEq σ] (n : σ →₀ ℕ) :
    (monomial R n) = LinearMap.stdBasis R (fun _ ↦ R) n := by
  rw [monomial]
  -- ⊢ LinearMap.stdBasis R (fun x => R) n = LinearMap.stdBasis R (fun x => R) n
  -- unify the `Decidable` arguments
  convert rfl
  -- 🎉 no goals
#align mv_power_series.monomial_def MvPowerSeries.monomial_def

theorem coeff_monomial [DecidableEq σ] (m n : σ →₀ ℕ) (a : R) :
    coeff R m (monomial R n a) = if m = n then a else 0 := by
  rw [coeff, monomial_def, LinearMap.proj_apply]
  -- ⊢ ↑(LinearMap.stdBasis R (fun x => R) n) a m = if m = n then a else 0
  dsimp only
  -- ⊢ ↑(LinearMap.stdBasis R (fun x => R) n) a m = if m = n then a else 0
  rw [LinearMap.stdBasis_apply, Function.update_apply, Pi.zero_apply]
  -- 🎉 no goals
#align mv_power_series.coeff_monomial MvPowerSeries.coeff_monomial

@[simp]
theorem coeff_monomial_same (n : σ →₀ ℕ) (a : R) : coeff R n (monomial R n a) = a := by
  rw [monomial_def]
  -- ⊢ ↑(coeff R n) (↑(LinearMap.stdBasis R (fun x => R) n) a) = a
  exact LinearMap.stdBasis_same R (fun _ ↦ R) n a
  -- 🎉 no goals
#align mv_power_series.coeff_monomial_same MvPowerSeries.coeff_monomial_same

theorem coeff_monomial_ne {m n : σ →₀ ℕ} (h : m ≠ n) (a : R) : coeff R m (monomial R n a) = 0 := by
  rw [monomial_def]
  -- ⊢ ↑(coeff R m) (↑(LinearMap.stdBasis R (fun x => R) n) a) = 0
  exact LinearMap.stdBasis_ne R (fun _ ↦ R) _ _ h a
  -- 🎉 no goals
#align mv_power_series.coeff_monomial_ne MvPowerSeries.coeff_monomial_ne

theorem eq_of_coeff_monomial_ne_zero {m n : σ →₀ ℕ} {a : R} (h : coeff R m (monomial R n a) ≠ 0) :
    m = n :=
  by_contra fun h' => h <| coeff_monomial_ne h' a
#align mv_power_series.eq_of_coeff_monomial_ne_zero MvPowerSeries.eq_of_coeff_monomial_ne_zero

@[simp]
theorem coeff_comp_monomial (n : σ →₀ ℕ) : (coeff R n).comp (monomial R n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n
#align mv_power_series.coeff_comp_monomial MvPowerSeries.coeff_comp_monomial

-- Porting note: simp can prove this.
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
                                          -- 🎉 no goals
    natCast := fun n => monomial R 0 n
    natCast_zero := by simp [Nat.cast]
                       -- 🎉 no goals
    natCast_succ := by simp [Nat.cast, monomial_zero_one]
                       -- 🎉 no goals
    one := 1 }

instance : Mul (MvPowerSeries σ R) :=
  ⟨fun φ ψ n => ∑ p in Finsupp.antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ⟩

theorem coeff_mul [DecidableEq σ] :
    coeff R n (φ * ψ) = ∑ p in Finsupp.antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  -- ⊢ antidiagonal n = antidiagonal n
  rw [Subsingleton.elim (fun a b => propDecidable (a = b)) ‹DecidableEq σ›]
  -- 🎉 no goals
#align mv_power_series.coeff_mul MvPowerSeries.coeff_mul

protected theorem zero_mul : (0 : MvPowerSeries σ R) * φ = 0 :=
  ext fun n => by simp [coeff_mul]
                  -- 🎉 no goals
#align mv_power_series.zero_mul MvPowerSeries.zero_mul

protected theorem mul_zero : φ * 0 = 0 :=
  ext fun n => by simp [coeff_mul]
                  -- 🎉 no goals
#align mv_power_series.mul_zero MvPowerSeries.mul_zero

theorem coeff_monomial_mul (a : R) :
    coeff R m (monomial R n a * φ) = if n ≤ m then a * coeff R (m - n) φ else 0 := by
  have :
    ∀ p ∈ antidiagonal m,
      coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 (monomial R n a) * coeff R p.2 φ ≠ 0 → p.1 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, antidiagonal_filter_fst_eq, Finset.sum_ite_index]
  -- ⊢ (if n ≤ m then ∑ x in {(n, m - n)}, ↑(coeff R x.fst) (↑(monomial R n) a) * ↑ …
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]
  -- 🎉 no goals
#align mv_power_series.coeff_monomial_mul MvPowerSeries.coeff_monomial_mul

theorem coeff_mul_monomial (a : R) :
    coeff R m (φ * monomial R n a) = if n ≤ m then coeff R (m - n) φ * a else 0 := by
  have :
    ∀ p ∈ antidiagonal m,
      coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 φ * coeff R p.2 (monomial R n a) ≠ 0 → p.2 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, antidiagonal_filter_snd_eq, Finset.sum_ite_index]
  -- ⊢ (if n ≤ m then ∑ x in {(m - n, n)}, ↑(coeff R x.fst) φ * ↑(coeff R x.snd) (↑ …
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]
  -- 🎉 no goals
#align mv_power_series.coeff_mul_monomial MvPowerSeries.coeff_mul_monomial

theorem coeff_add_monomial_mul (a : R) :
    coeff R (m + n) (monomial R m a * φ) = a * coeff R n φ := by
  rw [coeff_monomial_mul, if_pos, add_tsub_cancel_left]
  -- ⊢ m ≤ m + n
  exact le_add_right le_rfl
  -- 🎉 no goals
#align mv_power_series.coeff_add_monomial_mul MvPowerSeries.coeff_add_monomial_mul

theorem coeff_add_mul_monomial (a : R) :
    coeff R (m + n) (φ * monomial R n a) = coeff R m φ * a := by
  rw [coeff_mul_monomial, if_pos, add_tsub_cancel_right]
  -- ⊢ n ≤ m + n
  exact le_add_left le_rfl
  -- 🎉 no goals
#align mv_power_series.coeff_add_mul_monomial MvPowerSeries.coeff_add_mul_monomial

@[simp]
theorem commute_monomial {a : R} {n} :
    Commute φ (monomial R n a) ↔ ∀ m, Commute (coeff R m φ) a := by
  refine' ext_iff.trans ⟨fun h m => _, fun h m => _⟩
  -- ⊢ Commute (↑(coeff R m) φ) a
  · have := h (m + n)
    -- ⊢ Commute (↑(coeff R m) φ) a
    rwa [coeff_add_mul_monomial, add_comm, coeff_add_monomial_mul] at this
    -- 🎉 no goals
  · rw [coeff_mul_monomial, coeff_monomial_mul]
    -- ⊢ (if n ≤ m then ↑(coeff R (m - n)) φ * a else 0) = if n ≤ m then a * ↑(coeff  …
    split_ifs <;> [apply h; rfl]
    -- 🎉 no goals
#align mv_power_series.commute_monomial MvPowerSeries.commute_monomial

protected theorem one_mul : (1 : MvPowerSeries σ R) * φ = φ :=
  ext fun n => by simpa using coeff_add_monomial_mul 0 n φ 1
                  -- 🎉 no goals
#align mv_power_series.one_mul MvPowerSeries.one_mul

protected theorem mul_one : φ * 1 = φ :=
  ext fun n => by simpa using coeff_add_mul_monomial n 0 φ 1
                  -- 🎉 no goals
#align mv_power_series.mul_one MvPowerSeries.mul_one

protected theorem mul_add (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
  ext fun n => by simp only [coeff_mul, mul_add, Finset.sum_add_distrib, LinearMap.map_add]
                  -- 🎉 no goals
#align mv_power_series.mul_add MvPowerSeries.mul_add

protected theorem add_mul (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
  ext fun n => by simp only [coeff_mul, add_mul, Finset.sum_add_distrib, LinearMap.map_add]
                  -- 🎉 no goals
#align mv_power_series.add_mul MvPowerSeries.add_mul

protected theorem mul_assoc (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃) := by
  ext1 n
  -- ⊢ ↑(coeff R n) (φ₁ * φ₂ * φ₃) = ↑(coeff R n) (φ₁ * (φ₂ * φ₃))
  simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  -- ⊢ ∑ x in Finset.sigma (antidiagonal n) fun a => antidiagonal a.fst, ↑(coeff R  …
  refine' Finset.sum_bij (fun p _ => ⟨(p.2.1, p.2.2 + p.1.2), (p.2.2, p.1.2)⟩) _ _ _ _ <;>
    simp only [mem_antidiagonal, Finset.mem_sigma, heq_iff_eq, Prod.mk.inj_iff, and_imp,
      exists_prop]
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
    -- ⊢ { fst := (i, j), snd := (k, l) }.fst.fst + { fst := (i, j), snd := (k, l) }. …
    dsimp only
    -- ⊢ i + j = n → k + l = i → k + (l + j) = n ∧ True
    rintro rfl rfl
    -- ⊢ k + (l + j) = k + l + j ∧ True
    simp [add_assoc]
    -- 🎉 no goals
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    -- ⊢ { fst := (a, b), snd := (c, d) }.fst.fst + { fst := (a, b), snd := (c, d) }. …
    dsimp only
    -- ⊢ a + b = n → c + d = a → ↑(coeff R c) φ₁ * ↑(coeff R d) φ₂ * ↑(coeff R b) φ₃  …
    rintro rfl rfl
    -- ⊢ ↑(coeff R c) φ₁ * ↑(coeff R d) φ₂ * ↑(coeff R b) φ₃ = ↑(coeff R c) φ₁ * (↑(c …
    apply mul_assoc
    -- 🎉 no goals
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩
    -- ⊢ { fst := (a, b), snd := (c, d) }.fst.fst + { fst := (a, b), snd := (c, d) }. …
    dsimp only
    -- ⊢ a + b = n → c + d = a → i + j = n → k + l = i → { fst := (c, d + b), snd :=  …
    rintro rfl rfl - rfl
    -- ⊢ { fst := (c, d + b), snd := (d, b) } = { fst := (k, l + j), snd := (l, j) }  …
    simp only [Sigma.mk.inj_iff, Prod.mk.injEq, heq_iff_eq, and_imp]
    -- ⊢ c = k → d + b = l + j → d = l → b = j → (c + d = k + l ∧ b = j) ∧ c = k ∧ d  …
    rintro rfl - rfl rfl
    -- ⊢ (c + d = c + d ∧ b = b) ∧ c = c ∧ d = d
    simp only [and_self]
    -- 🎉 no goals
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
    -- ⊢ { fst := (i, j), snd := (k, l) }.fst.fst + { fst := (i, j), snd := (k, l) }. …
    dsimp only
    -- ⊢ i + j = n → k + l = j → ∃ a, (a.fst.fst + a.fst.snd = n ∧ a.snd.fst + a.snd. …
    rintro rfl rfl
    -- ⊢ ∃ a, (a.fst.fst + a.fst.snd = i + (k + l) ∧ a.snd.fst + a.snd.snd = a.fst.fs …
    refine' ⟨⟨(i + k, l), (i, k)⟩, _, _⟩ <;> simp [add_assoc]
    -- ⊢ { fst := (i + k, l), snd := (i, k) }.fst.fst + { fst := (i + k, l), snd := ( …
                                             -- 🎉 no goals
                                             -- 🎉 no goals
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
                                         -- 🎉 no goals
    mul_comm := fun φ ψ =>
      ext fun n => by
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
  ext k
  -- ⊢ ↑(coeff R k) (↑(monomial R m) a * ↑(monomial R n) b) = ↑(coeff R k) (↑(monom …
  simp only [coeff_mul_monomial, coeff_monomial]
  -- ⊢ (if n ≤ k then (if k - n = m then a else 0) * b else 0) = if k = m + n then  …
  split_ifs with h₁ h₂ h₃ h₃ h₂ <;> try rfl
                                    -- 🎉 no goals
                                    -- ⊢ a * b = 0
                                    -- ⊢ 0 * b = a * b
                                    -- ⊢ 0 * b = 0
                                    -- ⊢ 0 = a * b
                                    -- 🎉 no goals
  · rw [← h₂, tsub_add_cancel_of_le h₁] at h₃
    -- ⊢ a * b = 0
    exact (h₃ rfl).elim
    -- 🎉 no goals
  · rw [h₃, add_tsub_cancel_right] at h₂
    -- ⊢ 0 * b = a * b
    exact (h₂ rfl).elim
    -- 🎉 no goals
  · exact zero_mul b
    -- 🎉 no goals
  · rw [h₂] at h₁
    -- ⊢ 0 = a * b
    exact (h₁ <| le_add_left le_rfl).elim
    -- 🎉 no goals
#align mv_power_series.monomial_mul_monomial MvPowerSeries.monomial_mul_monomial

variable (σ) (R)

/-- The constant multivariate formal power series.-/
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

/-- The variables of the multivariate formal power series ring.-/
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
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_index_single_X MvPowerSeries.coeff_index_single_X

@[simp]
theorem coeff_index_single_self_X (s : σ) : coeff R (single s 1) (X s : MvPowerSeries σ R) = 1 :=
  coeff_monomial_same _ _
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_index_single_self_X MvPowerSeries.coeff_index_single_self_X

theorem coeff_zero_X (s : σ) : coeff R (0 : σ →₀ ℕ) (X s : MvPowerSeries σ R) = 0 := by
  rw [coeff_X, if_neg]
  -- ⊢ ¬0 = single s 1
  intro h
  -- ⊢ False
  exact one_ne_zero (single_eq_zero.mp h.symm)
  -- 🎉 no goals
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
  -- ⊢ X s ^ Nat.zero = ↑(monomial R (single s Nat.zero)) 1
  · simp
    -- 🎉 no goals
  · rw [pow_succ', ih, Nat.succ_eq_add_one, Finsupp.single_add, X, monomial_mul_monomial, one_mul]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_pow_eq MvPowerSeries.X_pow_eq

theorem coeff_X_pow [DecidableEq σ] (m : σ →₀ ℕ) (s : σ) (n : ℕ) :
    coeff R m ((X s : MvPowerSeries σ R) ^ n) = if m = single s n then 1 else 0 := by
  rw [X_pow_eq s n, coeff_monomial]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_X_pow MvPowerSeries.coeff_X_pow

@[simp]
theorem coeff_mul_C (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) :
    coeff R n (φ * C σ R a) = coeff R n φ * a := by simpa using coeff_add_mul_monomial n 0 φ a
                                                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_mul_C MvPowerSeries.coeff_mul_C

@[simp]
theorem coeff_C_mul (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) :
    coeff R n (C σ R a * φ) = a * coeff R n φ := by simpa using coeff_add_monomial_mul 0 n φ a
                                                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_C_mul MvPowerSeries.coeff_C_mul

theorem coeff_zero_mul_X (φ : MvPowerSeries σ R) (s : σ) : coeff R (0 : σ →₀ ℕ) (φ * X s) = 0 := by
  have : ¬single s 1 ≤ 0 := fun h => by simpa using h s
  -- ⊢ ↑(coeff R 0) (φ * X s) = 0
  simp only [X, coeff_mul_monomial, if_neg this]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_zero_mul_X MvPowerSeries.coeff_zero_mul_X

theorem coeff_zero_X_mul (φ : MvPowerSeries σ R) (s : σ) : coeff R (0 : σ →₀ ℕ) (X s * φ) = 0 := by
  rw [← (φ.commute_X s).eq, coeff_zero_mul_X]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_zero_X_mul MvPowerSeries.coeff_zero_X_mul

variable (σ) (R)

/-- The constant coefficient of a formal power series.-/
def constantCoeff : MvPowerSeries σ R →+* R :=
  { coeff R (0 : σ →₀ ℕ) with
    toFun := coeff R (0 : σ →₀ ℕ)
    map_one' := coeff_zero_one
    map_mul' := fun φ ψ => by simp [coeff_mul, support_single_ne_zero]
                              -- 🎉 no goals
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

-- Porting note: simp can prove this.
-- @[simp]
theorem constantCoeff_zero : constantCoeff σ R 0 = 0 :=
  rfl
#align mv_power_series.constant_coeff_zero MvPowerSeries.constantCoeff_zero

-- Porting note: simp can prove this.
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
 then so is its constant coefficient.-/
theorem isUnit_constantCoeff (φ : MvPowerSeries σ R) (h : IsUnit φ) :
    IsUnit (constantCoeff σ R φ) :=
  h.map _
#align mv_power_series.is_unit_constant_coeff MvPowerSeries.isUnit_constantCoeff

-- Porting note: simp can prove this.
-- @[simp]
theorem coeff_smul (f : MvPowerSeries σ R) (n) (a : R) : coeff _ n (a • f) = a * coeff _ n f :=
  rfl
#align mv_power_series.coeff_smul MvPowerSeries.coeff_smul

theorem smul_eq_C_mul (f : MvPowerSeries σ R) (a : R) : a • f = C σ R a * f := by
  ext
  -- ⊢ ↑(coeff R n✝) (a • f) = ↑(coeff R n✝) (↑(C σ R) a * f)
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.smul_eq_C_mul MvPowerSeries.smul_eq_C_mul

theorem X_inj [Nontrivial R] {s t : σ} : (X s : MvPowerSeries σ R) = X t ↔ s = t :=
  ⟨by
    intro h
    -- ⊢ s = t
    replace h := congr_arg (coeff R (single s 1)) h
    -- ⊢ s = t
    rw [coeff_X, if_pos rfl, coeff_X] at h
    -- ⊢ s = t
    split_ifs at h with H
    -- ⊢ s = t
    · rw [Finsupp.single_eq_single_iff] at H
      -- ⊢ s = t
      cases' H with H H
      -- ⊢ s = t
      · exact H.1
        -- 🎉 no goals
      · exfalso
        -- ⊢ False
        exact one_ne_zero H.1
        -- 🎉 no goals
    · exfalso
      -- ⊢ False
      exact one_ne_zero h, congr_arg X⟩
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_inj MvPowerSeries.X_inj

end Semiring

section Map

variable {S T : Type*} [Semiring R] [Semiring S] [Semiring T]

variable (f : R →+* S) (g : S →+* T)

variable (σ)

/-- The map between multivariate formal power series induced by a map on the coefficients.-/
def map : MvPowerSeries σ R →+* MvPowerSeries σ S where
  toFun φ n := f <| coeff R n φ
  map_zero' := ext fun _n => f.map_zero
  map_one' :=
    ext fun n =>
      show f ((coeff R n) 1) = (coeff S n) 1 by
        rw [coeff_one, coeff_one]
        -- ⊢ ↑f (if n = 0 then 1 else 0) = if n = 0 then 1 else 0
        split_ifs with h
        -- ⊢ ↑f (if n = 0 then 1 else 0) = 1
        · simp only [RingHom.map_ite_one_zero, ite_true, map_one, h]
          -- 🎉 no goals
        · simp only [RingHom.map_ite_one_zero, ite_false, map_zero, h]
          -- 🎉 no goals
  map_add' φ ψ :=
    ext fun n => show f ((coeff R n) (φ + ψ)) = f ((coeff R n) φ) + f ((coeff R n) ψ) by simp
                                                                                         -- 🎉 no goals
  map_mul' φ ψ :=
    ext fun n =>
      show f _ = _ by
        -- ⊢ ∑ x in antidiagonal n, ↑f (↑(coeff R x.fst) φ * ↑(coeff R x.snd) ψ) = ∑ p in …
        rw [coeff_mul, map_sum, coeff_mul]
        -- ⊢ ∀ (x : (σ →₀ ℕ) × (σ →₀ ℕ)), x ∈ antidiagonal n → ↑f (↑(coeff R x.fst) φ * ↑ …
        apply Finset.sum_congr rfl
        -- ⊢ ↑f (↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ) = ↑(coeff S (i, j).fs …
                         -- ⊢ ↑f (↑(coeff R (i, j).fst) φ) * ↑f (↑(coeff R (i, j).snd) ψ) = ↑(coeff S (i,  …
                                         -- 🎉 no goals
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
  ext m
  -- ⊢ ↑(coeff S m) (↑(map σ f) (↑(monomial R n) a)) = ↑(coeff S m) (↑(monomial S n …
  simp [coeff_monomial, apply_ite f]
  -- 🎉 no goals
#align mv_power_series.map_monomial MvPowerSeries.map_monomial

@[simp]
theorem map_C (a : R) : map σ f (C σ R a) = C σ S (f a) :=
  map_monomial _ _ _
set_option linter.uppercaseLean3 false in
#align mv_power_series.map_C MvPowerSeries.map_C

@[simp]
theorem map_X (s : σ) : map σ f (X s) = X s := by simp [MvPowerSeries.X]
                                                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.map_X MvPowerSeries.map_X

end Map

section Algebra

variable {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

instance : Algebra R (MvPowerSeries σ A) :=
  {
    show Module R (MvPowerSeries σ A) by infer_instance with
                                         -- 🎉 no goals
    commutes' := fun a φ => by
      ext n
      -- ⊢ ↑(coeff A n) (↑(RingHom.comp (map σ (algebraMap R A)) (C σ R)) a * φ) = ↑(co …
      simp [Algebra.commutes]
      -- 🎉 no goals
    smul_def' := fun a σ => by
      ext n
      -- ⊢ ↑(coeff A n) (a • σ) = ↑(coeff A n) (↑(RingHom.comp (map σ✝ (algebraMap R A) …
      simp [(coeff A n).map_smul_of_tower a, Algebra.smul_def]
      -- 🎉 no goals
    toRingHom := (MvPowerSeries.map σ (algebraMap R A)).comp (C σ R) }

theorem c_eq_algebraMap : C σ R = algebraMap R (MvPowerSeries σ R) :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.C_eq_algebra_map MvPowerSeries.c_eq_algebraMap

theorem algebraMap_apply {r : R} :
    algebraMap R (MvPowerSeries σ A) r = C σ A (algebraMap R A r) := by
  change (MvPowerSeries.map σ (algebraMap R A)).comp (C σ R) r = _
  -- ⊢ ↑(RingHom.comp (map σ (algebraMap R A)) (C σ R)) r = ↑(C σ A) (↑(algebraMap  …
  simp
  -- 🎉 no goals
#align mv_power_series.algebra_map_apply MvPowerSeries.algebraMap_apply

instance [Nonempty σ] [Nontrivial R] : Nontrivial (Subalgebra R (MvPowerSeries σ R)) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne.def, SetLike.ext_iff, not_forall]
      -- ⊢ ∃ x, ¬(x ∈ ⊥ ↔ x ∈ ⊤)
      inhabit σ
      -- ⊢ ∃ x, ¬(x ∈ ⊥ ↔ x ∈ ⊤)
      refine' ⟨X default, _⟩
      -- ⊢ ¬(X default ∈ ⊥ ↔ X default ∈ ⊤)
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true_iff, Algebra.mem_top]
      -- ⊢ ∀ (x : R), ¬↑(algebraMap R (MvPowerSeries σ R)) x = X default
      intro x
      -- ⊢ ¬↑(algebraMap R (MvPowerSeries σ R)) x = X default
      rw [ext_iff, not_forall]
      -- ⊢ ∃ x_1, ¬↑(coeff R x_1) (↑(algebraMap R (MvPowerSeries σ R)) x) = ↑(coeff R x …
      refine' ⟨Finsupp.single default 1, _⟩
      -- ⊢ ¬↑(coeff R (single default 1)) (↑(algebraMap R (MvPowerSeries σ R)) x) = ↑(c …
      simp [algebraMap_apply, coeff_C]⟩⟩
      -- 🎉 no goals

end Algebra

section Trunc

variable [CommSemiring R] (n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def truncFun (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m in Finset.Iio n, MvPolynomial.monomial m (coeff R m φ)
#align mv_power_series.trunc_fun MvPowerSeries.truncFun

theorem coeff_truncFun (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun n φ).coeff m = if m < n then coeff R m φ else 0 := by
  simp [truncFun, MvPolynomial.coeff_sum]
  -- 🎉 no goals
#align mv_power_series.coeff_trunc_fun MvPowerSeries.coeff_truncFun

variable (R)

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial -/
def trunc : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncFun n
  map_zero' := by
    ext
    -- ⊢ MvPolynomial.coeff m✝ (truncFun n 0) = MvPolynomial.coeff m✝ 0
    simp [coeff_truncFun]
    -- 🎉 no goals
  map_add' := by
    intros x y
    -- ⊢ ZeroHom.toFun { toFun := truncFun n, map_zero' := (_ : truncFun n 0 = 0) } ( …
    ext m
    -- ⊢ MvPolynomial.coeff m (ZeroHom.toFun { toFun := truncFun n, map_zero' := (_ : …
    simp only [coeff_truncFun, MvPolynomial.coeff_add]
    -- ⊢ (if m < n then ↑(coeff R m) (x + y) else 0) = (if m < n then ↑(coeff R m) x  …
    split_ifs
    -- ⊢ ↑(coeff R m) (x + y) = ↑(coeff R m) x + ↑(coeff R m) y
    · rw [map_add]
      -- 🎉 no goals
    · rw [zero_add]
      -- 🎉 no goals

#align mv_power_series.trunc MvPowerSeries.trunc

variable {R}

theorem coeff_trunc (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff R m φ else 0 := by simp [trunc, coeff_truncFun]
                                                                   -- 🎉 no goals
#align mv_power_series.coeff_trunc MvPowerSeries.coeff_trunc

@[simp]
theorem trunc_one (n : σ →₀ ℕ) (hnn : n ≠ 0) : trunc R n 1 = 1 :=
  MvPolynomial.ext _ _ fun m => by
    rw [coeff_trunc, coeff_one]
    -- ⊢ (if m < n then if m = 0 then 1 else 0 else 0) = MvPolynomial.coeff m 1
    split_ifs with H H'
    · subst m
      -- ⊢ 1 = MvPolynomial.coeff 0 1
      simp
      -- 🎉 no goals
    · symm
      -- ⊢ MvPolynomial.coeff m 1 = 0
      rw [MvPolynomial.coeff_one]
      -- ⊢ (if 0 = m then 1 else 0) = 0
      exact if_neg (Ne.symm H')
      -- 🎉 no goals
    · symm
      -- ⊢ MvPolynomial.coeff m 1 = 0
      rw [MvPolynomial.coeff_one]
      -- ⊢ (if 0 = m then 1 else 0) = 0
      refine' if_neg _
      -- ⊢ ¬0 = m
      rintro rfl
      -- ⊢ False
      apply H
      -- ⊢ 0 < n
      exact Ne.bot_lt hnn
      -- 🎉 no goals
#align mv_power_series.trunc_one MvPowerSeries.trunc_one

@[simp]
theorem trunc_c (n : σ →₀ ℕ) (hnn : n ≠ 0) (a : R) : trunc R n (C σ R a) = MvPolynomial.C a :=
  MvPolynomial.ext _ _ fun m => by
    rw [coeff_trunc, coeff_C, MvPolynomial.coeff_C]
    -- ⊢ (if m < n then if m = 0 then a else 0 else 0) = if 0 = m then a else 0
    split_ifs with H <;> first |rfl|try simp_all
                         -- 🎉 no goals
                         -- 🎉 no goals
                         -- 🎉 no goals
                         -- 🎉 no goals
                         -- ⊢ 0 = a
                         -- 🎉 no goals
    exfalso; apply H; subst m; exact Ne.bot_lt hnn
    -- ⊢ False
             -- ⊢ m < n
                      -- ⊢ 0 < n
                               -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.trunc_C MvPowerSeries.trunc_c

end Trunc

section Semiring

variable [Semiring R]

theorem X_pow_dvd_iff {s : σ} {n : ℕ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ^ n ∣ φ ↔ ∀ m : σ →₀ ℕ, m s < n → coeff R m φ = 0 := by
  constructor
  -- ⊢ X s ^ n ∣ φ → ∀ (m : σ →₀ ℕ), ↑m s < n → ↑(coeff R m) φ = 0
  · rintro ⟨φ, rfl⟩ m h
    -- ⊢ ↑(coeff R m) (X s ^ n * φ) = 0
    rw [coeff_mul, Finset.sum_eq_zero]
    -- ⊢ ∀ (x : (σ →₀ ℕ) × (σ →₀ ℕ)), x ∈ antidiagonal m → ↑(coeff R x.fst) (X s ^ n) …
    rintro ⟨i, j⟩ hij
    -- ⊢ ↑(coeff R (i, j).fst) (X s ^ n) * ↑(coeff R (i, j).snd) φ = 0
    rw [coeff_X_pow, if_neg, zero_mul]
    -- ⊢ ¬(i, j).fst = single s n
    contrapose! h
    -- ⊢ n ≤ ↑m s
    subst i
    -- ⊢ n ≤ ↑m s
    rw [Finsupp.mem_antidiagonal] at hij
    -- ⊢ n ≤ ↑m s
    rw [← hij, Finsupp.add_apply, Finsupp.single_eq_same]
    -- ⊢ n ≤ n + ↑(single s n, j).snd s
    exact Nat.le_add_right n _
    -- 🎉 no goals
  · intro h
    -- ⊢ X s ^ n ∣ φ
    refine' ⟨fun m => coeff R (m + single s n) φ, _⟩
    -- ⊢ φ = X s ^ n * fun m => ↑(coeff R (m + single s n)) φ
    ext m
    -- ⊢ ↑(coeff R m) φ = ↑(coeff R m) (X s ^ n * fun m => ↑(coeff R (m + single s n) …
    by_cases H : m - single s n + single s n = m
    -- ⊢ ↑(coeff R m) φ = ↑(coeff R m) (X s ^ n * fun m => ↑(coeff R (m + single s n) …
    · rw [coeff_mul, Finset.sum_eq_single (single s n, m - single s n)]
      · rw [coeff_X_pow, if_pos rfl, one_mul]
        -- ⊢ ↑(coeff R m) φ = ↑(coeff R (single s n, m - single s n).snd) fun m => ↑(coef …
        simpa using congr_arg (fun m : σ →₀ ℕ => coeff R m φ) H.symm
        -- 🎉 no goals
      · rintro ⟨i, j⟩ hij hne
        -- ⊢ (↑(coeff R (i, j).fst) (X s ^ n) * ↑(coeff R (i, j).snd) fun m => ↑(coeff R  …
        rw [Finsupp.mem_antidiagonal] at hij
        -- ⊢ (↑(coeff R (i, j).fst) (X s ^ n) * ↑(coeff R (i, j).snd) fun m => ↑(coeff R  …
        rw [coeff_X_pow]
        -- ⊢ ((if (i, j).fst = single s n then 1 else 0) * ↑(coeff R (i, j).snd) fun m => …
        split_ifs with hi
        -- ⊢ (1 * ↑(coeff R (i, j).snd) fun m => ↑(coeff R (m + single s n)) φ) = 0
        · exfalso
          -- ⊢ False
          apply hne
          -- ⊢ (i, j) = (single s n, m - single s n)
          rw [← hij, ← hi, Prod.mk.inj_iff]
          -- ⊢ i = (i, j).fst ∧ j = (i, j).fst + (i, j).snd - (i, j).fst
          refine' ⟨rfl, _⟩
          -- ⊢ j = (i, j).fst + (i, j).snd - (i, j).fst
          ext t
          -- ⊢ ↑j t = ↑((i, j).fst + (i, j).snd - (i, j).fst) t
          simp only [add_tsub_cancel_left, Finsupp.add_apply, Finsupp.tsub_apply]
          -- 🎉 no goals
        · exact zero_mul _
          -- 🎉 no goals
      · intro hni
        -- ⊢ (↑(coeff R (single s n, m - single s n).fst) (X s ^ n) * ↑(coeff R (single s …
        exfalso
        -- ⊢ False
        apply hni
        -- ⊢ (single s n, m - single s n) ∈ antidiagonal m
        rwa [Finsupp.mem_antidiagonal, add_comm]
        -- 🎉 no goals
    · rw [h, coeff_mul, Finset.sum_eq_zero]
      -- ⊢ ∀ (x : (σ →₀ ℕ) × (σ →₀ ℕ)), x ∈ antidiagonal m → (↑(coeff R x.fst) (X s ^ n …
      · rintro ⟨i, j⟩ hij
        -- ⊢ (↑(coeff R (i, j).fst) (X s ^ n) * ↑(coeff R (i, j).snd) fun m => ↑(coeff R  …
        rw [Finsupp.mem_antidiagonal] at hij
        -- ⊢ (↑(coeff R (i, j).fst) (X s ^ n) * ↑(coeff R (i, j).snd) fun m => ↑(coeff R  …
        rw [coeff_X_pow]
        -- ⊢ ((if (i, j).fst = single s n then 1 else 0) * ↑(coeff R (i, j).snd) fun m => …
        split_ifs with hi
        -- ⊢ (1 * ↑(coeff R (i, j).snd) fun m => ↑(coeff R (m + single s n)) φ) = 0
        · exfalso
          -- ⊢ False
          apply H
          -- ⊢ m - single s n + single s n = m
          rw [← hij, hi]
          -- ⊢ single s n + (i, j).snd - single s n + single s n = single s n + (i, j).snd
          ext
          -- ⊢ ↑(single s n + (i, j).snd - single s n + single s n) a✝ = ↑(single s n + (i, …
          rw [coe_add, coe_add, Pi.add_apply, Pi.add_apply, add_tsub_cancel_left, add_comm]
          -- 🎉 no goals
        · exact zero_mul _
          -- 🎉 no goals
      · contrapose! H
        -- ⊢ m - single s n + single s n = m
        ext t
        -- ⊢ ↑(m - single s n + single s n) t = ↑m t
        by_cases hst : s = t
        -- ⊢ ↑(m - single s n + single s n) t = ↑m t
        · subst t
          -- ⊢ ↑(m - single s n + single s n) s = ↑m s
          simpa using tsub_add_cancel_of_le H
          -- 🎉 no goals
        · simp [Finsupp.single_apply, hst]
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_pow_dvd_iff MvPowerSeries.X_pow_dvd_iff

theorem X_dvd_iff {s : σ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ∣ φ ↔ ∀ m : σ →₀ ℕ, m s = 0 → coeff R m φ = 0 := by
  rw [← pow_one (X s : MvPowerSeries σ R), X_pow_dvd_iff]
  -- ⊢ (∀ (m : σ →₀ ℕ), ↑m s < 1 → ↑(coeff R m) φ = 0) ↔ ∀ (m : σ →₀ ℕ), ↑m s = 0 → …
  constructor <;> intro h m hm
  -- ⊢ (∀ (m : σ →₀ ℕ), ↑m s < 1 → ↑(coeff R m) φ = 0) → ∀ (m : σ →₀ ℕ), ↑m s = 0 → …
                  -- ⊢ ↑(coeff R m) φ = 0
                  -- ⊢ ↑(coeff R m) φ = 0
  · exact h m (hm.symm ▸ zero_lt_one)
    -- 🎉 no goals
  · exact h m (Nat.eq_zero_of_le_zero <| Nat.le_of_succ_le_succ hm)
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_dvd_iff MvPowerSeries.X_dvd_iff

end Semiring

section Ring

variable [Ring R]

/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coefficients of the inverse.
-/
/-- Auxiliary definition that unifies
 the totalised inverse formal power series `(_)⁻¹` and
 the inverse formal power series that depends on
 an inverse of the constant coefficient `invOfUnit`.-/
protected noncomputable def inv.aux (a : R) (φ : MvPowerSeries σ R) : MvPowerSeries σ R
  | n =>
    if n = 0 then a
    else
      -a *
        ∑ x in n.antidiagonal, if _ : x.2 < n then coeff R x.1 φ * inv.aux a φ x.2 else 0
termination_by _ n => n
#align mv_power_series.inv.aux MvPowerSeries.inv.aux

theorem coeff_inv_aux [DecidableEq σ] (n : σ →₀ ℕ) (a : R) (φ : MvPowerSeries σ R) :
    coeff R n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x in n.antidiagonal, if x.2 < n then coeff R x.1 φ * coeff R x.2 (inv.aux a φ) else 0 :=
  show inv.aux a φ n = _ by
    rw [inv.aux]
    -- ⊢ (if n = 0 then a else -a * ∑ x in antidiagonal n, if x_1 : x.snd < n then ↑( …
    -- unify `Decidable` instances
    convert rfl
    -- 🎉 no goals
#align mv_power_series.coeff_inv_aux MvPowerSeries.coeff_inv_aux

/-- A multivariate formal power series is invertible if the constant coefficient is invertible.-/
def invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) : MvPowerSeries σ R :=
  inv.aux (↑u⁻¹) φ
#align mv_power_series.inv_of_unit MvPowerSeries.invOfUnit

theorem coeff_invOfUnit [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (u : Rˣ) :
    coeff R n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x in n.antidiagonal,
            if x.2 < n then coeff R x.1 φ * coeff R x.2 (invOfUnit φ u) else 0 := by
  convert coeff_inv_aux n (↑u⁻¹) φ
  -- 🎉 no goals
#align mv_power_series.coeff_inv_of_unit MvPowerSeries.coeff_invOfUnit

@[simp]
theorem constantCoeff_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) :
    constantCoeff σ R (invOfUnit φ u) = ↑u⁻¹ := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invOfUnit, if_pos rfl]
  -- 🎉 no goals
#align mv_power_series.constant_coeff_inv_of_unit MvPowerSeries.constantCoeff_invOfUnit

theorem mul_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff σ R φ = u) :
    φ * invOfUnit φ u = 1 :=
  ext fun n =>
    if H : n = 0 then by
      rw [H]
      -- ⊢ ↑(coeff R 0) (φ * invOfUnit φ u) = ↑(coeff R 0) 1
      simp [coeff_mul, support_single_ne_zero, h]
      -- 🎉 no goals
    else by
      have : ((0 : σ →₀ ℕ), n) ∈ n.antidiagonal := by rw [Finsupp.mem_antidiagonal, zero_add]
      -- ⊢ ↑(coeff R n) (φ * invOfUnit φ u) = ↑(coeff R n) 1
      rw [coeff_one, if_neg H, coeff_mul, ← Finset.insert_erase this,
        Finset.sum_insert (Finset.not_mem_erase _ _), coeff_zero_eq_constantCoeff_apply, h,
        coeff_invOfUnit, if_neg H, neg_mul, mul_neg, Units.mul_inv_cancel_left, ←
        Finset.insert_erase this, Finset.sum_insert (Finset.not_mem_erase _ _),
        Finset.insert_erase this, if_neg (not_lt_of_ge <| le_rfl), zero_add, add_comm, ←
        sub_eq_add_neg, sub_eq_zero, Finset.sum_congr rfl]
      rintro ⟨i, j⟩ hij
      -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) (invOfUnit φ u) = if (i, j). …
      rw [Finset.mem_erase, Finsupp.mem_antidiagonal] at hij
      -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) (invOfUnit φ u) = if (i, j). …
      cases' hij with h₁ h₂
      -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) (invOfUnit φ u) = if (i, j). …
      subst n
      -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) (invOfUnit φ u) = if (i, j). …
      rw [if_pos]
      -- ⊢ (i, j).snd < (0, (i, j).fst + (i, j).snd).snd
      suffices (0 : _) + j < i + j by simpa
      -- ⊢ 0 + j < i + j
      apply add_lt_add_right
      -- ⊢ 0 < i
      constructor
      -- ⊢ ∀ (i_1 : σ), PartialOrder.toPreorder.1.1 (↑0 i_1) (↑i i_1)
      · intro s
        -- ⊢ PartialOrder.toPreorder.1.1 (↑0 s) (↑i s)
        exact Nat.zero_le _
        -- 🎉 no goals
      · intro H
        -- ⊢ False
        apply h₁
        -- ⊢ (i, j) = (0, (i, j).fst + (i, j).snd)
        suffices i = 0 by simp [this]
        -- ⊢ i = 0
        ext1 s
        -- ⊢ ↑i s = ↑0 s
        exact Nat.eq_zero_of_le_zero (H s)
        -- 🎉 no goals
#align mv_power_series.mul_inv_of_unit MvPowerSeries.mul_invOfUnit

end Ring

section CommRing

variable [CommRing R]

/-- Multivariate formal power series over a local ring form a local ring. -/
instance [LocalRing R] : LocalRing (MvPowerSeries σ R) :=
  LocalRing.of_isUnit_or_isUnit_one_sub_self <| by
    intro φ
    -- ⊢ IsUnit φ ∨ IsUnit (1 - φ)
    rcases LocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff σ R φ) with (⟨u, h⟩ | ⟨u, h⟩) <;>
        [left; right] <;>
      · refine' isUnit_of_mul_eq_one _ _ (mul_invOfUnit _ u _)
        -- ⊢ ↑(constantCoeff σ ((fun x => R) φ)) φ = ↑u
        -- ⊢ ↑(constantCoeff σ ((fun x => R) φ)) (1 - φ) = ↑u
        -- 🎉 no goals
        simpa using h.symm
        -- 🎉 no goals

-- TODO(jmc): once adic topology lands, show that this is complete
end CommRing

section LocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) [IsLocalRingHom f]

-- Thanks to the linter for informing us that this instance does
-- not actually need R and S to be local rings!
/-- The map `A[[X]] → B[[X]]` induced by a local ring hom `A → B` is local -/
instance map.isLocalRingHom : IsLocalRingHom (map σ f) :=
  ⟨by
    rintro φ ⟨ψ, h⟩
    -- ⊢ IsUnit φ
    replace h := congr_arg (constantCoeff σ S) h
    -- ⊢ IsUnit φ
    rw [constantCoeff_map] at h
    -- ⊢ IsUnit φ
    have : IsUnit (constantCoeff σ S ↑ψ) := isUnit_constantCoeff (↑ψ) ψ.isUnit
    -- ⊢ IsUnit φ
    rw [h] at this
    -- ⊢ IsUnit φ
    rcases isUnit_of_map_unit f _ this with ⟨c, hc⟩
    -- ⊢ IsUnit φ
    exact isUnit_of_mul_eq_one φ (invOfUnit φ c) (mul_invOfUnit φ c hc.symm)⟩
    -- 🎉 no goals
#align mv_power_series.map.is_local_ring_hom MvPowerSeries.map.isLocalRingHom

end LocalRing

section Field

variable {k : Type*} [Field k]

/-- The inverse `1/f` of a multivariable power series `f` over a field -/
protected def inv (φ : MvPowerSeries σ k) : MvPowerSeries σ k :=
  inv.aux (constantCoeff σ k φ)⁻¹ φ
#align mv_power_series.inv MvPowerSeries.inv

instance : Inv (MvPowerSeries σ k) :=
  ⟨MvPowerSeries.inv⟩

theorem coeff_inv [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ k) :
    coeff k n φ⁻¹ =
      if n = 0 then (constantCoeff σ k φ)⁻¹
      else
        -(constantCoeff σ k φ)⁻¹ *
          ∑ x in n.antidiagonal, if x.2 < n then coeff k x.1 φ * coeff k x.2 φ⁻¹ else 0 :=
  coeff_inv_aux n _ φ
#align mv_power_series.coeff_inv MvPowerSeries.coeff_inv

@[simp]
theorem constantCoeff_inv (φ : MvPowerSeries σ k) :
    constantCoeff σ k φ⁻¹ = (constantCoeff σ k φ)⁻¹ := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_inv, if_pos rfl]
  -- 🎉 no goals
#align mv_power_series.constant_coeff_inv MvPowerSeries.constantCoeff_inv

theorem inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0 ↔ constantCoeff σ k φ = 0 :=
  ⟨fun h => by simpa using congr_arg (constantCoeff σ k) h, fun h =>
               -- 🎉 no goals
    ext fun n => by
      rw [coeff_inv]
      -- ⊢ (if n = 0 then (↑(constantCoeff σ k) φ)⁻¹ else -(↑(constantCoeff σ k) φ)⁻¹ * …
      split_ifs <;>
      -- ⊢ (↑(constantCoeff σ k) φ)⁻¹ = ↑(coeff k n) 0
        simp only [h, map_zero, zero_mul, inv_zero, neg_zero]⟩
        -- 🎉 no goals
        -- 🎉 no goals
#align mv_power_series.inv_eq_zero MvPowerSeries.inv_eq_zero

@[simp]
theorem zero_inv : (0 : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero, constantCoeff_zero]
  -- 🎉 no goals
#align mv_power_series.zero_inv MvPowerSeries.zero_inv

-- Porting note: simp can prove this.
-- @[simp]
theorem invOfUnit_eq (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  rfl
#align mv_power_series.inv_of_unit_eq MvPowerSeries.invOfUnit_eq

@[simp]
theorem invOfUnit_eq' (φ : MvPowerSeries σ k) (u : Units k) (h : constantCoeff σ k φ = u) :
    invOfUnit φ u = φ⁻¹ := by
  rw [← invOfUnit_eq φ (h.symm ▸ u.ne_zero)]
  -- ⊢ invOfUnit φ u = invOfUnit φ (Units.mk0 (↑(constantCoeff σ k) φ) (_ : ↑(const …
  apply congrArg (invOfUnit φ)
  -- ⊢ u = Units.mk0 (↑(constantCoeff σ k) φ) (_ : ↑(constantCoeff σ k) φ ≠ 0)
  rw [Units.ext_iff]
  -- ⊢ ↑u = ↑(Units.mk0 (↑(constantCoeff σ k) φ) (_ : ↑(constantCoeff σ k) φ ≠ 0))
  exact h.symm
  -- 🎉 no goals
#align mv_power_series.inv_of_unit_eq' MvPowerSeries.invOfUnit_eq'

@[simp]
protected theorem mul_inv_cancel (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) :
    φ * φ⁻¹ = 1 := by rw [← invOfUnit_eq φ h, mul_invOfUnit φ (Units.mk0 _ h) rfl]
                      -- 🎉 no goals
#align mv_power_series.mul_inv_cancel MvPowerSeries.mul_inv_cancel

@[simp]
protected theorem inv_mul_cancel (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) :
    φ⁻¹ * φ = 1 := by rw [mul_comm, φ.mul_inv_cancel h]
                      -- 🎉 no goals
#align mv_power_series.inv_mul_cancel MvPowerSeries.inv_mul_cancel

protected theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : MvPowerSeries σ k}
    (h : constantCoeff σ k φ₃ ≠ 0) : φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  ⟨fun k => by simp [k, mul_assoc, MvPowerSeries.inv_mul_cancel _ h], fun k => by
               -- 🎉 no goals
    simp [← k, mul_assoc, MvPowerSeries.mul_inv_cancel _ h]⟩
    -- 🎉 no goals
#align mv_power_series.eq_mul_inv_iff_mul_eq MvPowerSeries.eq_mul_inv_iff_mul_eq

protected theorem eq_inv_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff σ k ψ ≠ 0) :
    φ = ψ⁻¹ ↔ φ * ψ = 1 := by rw [← MvPowerSeries.eq_mul_inv_iff_mul_eq h, one_mul]
                              -- 🎉 no goals
#align mv_power_series.eq_inv_iff_mul_eq_one MvPowerSeries.eq_inv_iff_mul_eq_one

protected theorem inv_eq_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff σ k ψ ≠ 0) :
    ψ⁻¹ = φ ↔ φ * ψ = 1 := by rw [eq_comm, MvPowerSeries.eq_inv_iff_mul_eq_one h]
                              -- 🎉 no goals
#align mv_power_series.inv_eq_iff_mul_eq_one MvPowerSeries.inv_eq_iff_mul_eq_one

@[simp]
protected theorem mul_inv_rev (φ ψ : MvPowerSeries σ k) :
    (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ := by
  by_cases h : constantCoeff σ k (φ * ψ) = 0
  -- ⊢ (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹
  · rw [inv_eq_zero.mpr h]
    -- ⊢ 0 = ψ⁻¹ * φ⁻¹
    simp only [map_mul, mul_eq_zero] at h
    -- ⊢ 0 = ψ⁻¹ * φ⁻¹
    -- we don't have `NoZeroDivisors (MvPowerSeries σ k)` yet,
    cases' h with h h <;> simp [inv_eq_zero.mpr h]
    -- ⊢ 0 = ψ⁻¹ * φ⁻¹
                          -- 🎉 no goals
                          -- 🎉 no goals
  · rw [MvPowerSeries.inv_eq_iff_mul_eq_one h]
    -- ⊢ ψ⁻¹ * φ⁻¹ * (φ * ψ) = 1
    simp only [not_or, map_mul, mul_eq_zero] at h
    -- ⊢ ψ⁻¹ * φ⁻¹ * (φ * ψ) = 1
    rw [← mul_assoc, mul_assoc _⁻¹, MvPowerSeries.inv_mul_cancel _ h.left, mul_one,
      MvPowerSeries.inv_mul_cancel _ h.right]
#align mv_power_series.mul_inv_rev MvPowerSeries.mul_inv_rev

instance : InvOneClass (MvPowerSeries σ k) :=
  { inferInstanceAs (One (MvPowerSeries σ k)),
    inferInstanceAs (Inv (MvPowerSeries σ k)) with
    inv_one := by
      rw [MvPowerSeries.inv_eq_iff_mul_eq_one, mul_one]
      -- ⊢ ↑(constantCoeff σ k) 1 ≠ 0
      simp }
      -- 🎉 no goals

@[simp]
theorem C_inv (r : k) : (C σ k r)⁻¹ = C σ k r⁻¹ := by
  rcases eq_or_ne r 0 with (rfl | hr)
  -- ⊢ (↑(C σ k) 0)⁻¹ = ↑(C σ k) 0⁻¹
  · simp
    -- 🎉 no goals
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one, ← map_mul, inv_mul_cancel hr, map_one]
  -- ⊢ ↑(constantCoeff σ k) (↑(C σ k) r) ≠ 0
  simpa using hr
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.C_inv MvPowerSeries.C_inv

@[simp]
theorem X_inv (s : σ) : (X s : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero, constantCoeff_X]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_inv MvPowerSeries.X_inv

@[simp]
theorem smul_inv (r : k) (φ : MvPowerSeries σ k) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ := by
  simp [smul_eq_C_mul, mul_comm]
  -- 🎉 no goals
#align mv_power_series.smul_inv MvPowerSeries.smul_inv

end Field

end MvPowerSeries

namespace MvPolynomial

open Finsupp

variable {σ : Type*} {R : Type*} [CommSemiring R] (φ ψ : MvPolynomial σ R)

-- Porting note: added so we can add the `@[coe]` attribute
/-- The natural inclusion from multivariate polynomials into multivariate formal power series.-/
@[coe]
def toMvPowerSeries : MvPolynomial σ R → MvPowerSeries σ R :=
  fun φ n => coeff n φ

/-- The natural inclusion from multivariate polynomials into multivariate formal power series.-/
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
    rw [coeff_coe, coeff_monomial, MvPowerSeries.coeff_monomial]
    -- ⊢ (if n = m then a else 0) = if m = n then a else 0
    split_ifs with h₁ h₂ <;> first |rfl|subst m; contradiction
                             -- 🎉 no goals
                             -- 🎉 no goals
                             -- 🎉 no goals
                             -- 🎉 no goals
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
  MvPowerSeries.ext fun n => by simp only [coeff_coe, MvPowerSeries.coeff_mul, coeff_mul]
                                -- 🎉 no goals
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
  -- 🎉 no goals
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
  -- ⊢ coeff m✝ x = coeff m✝ y
  simp_rw [← coeff_coe]
  -- ⊢ ↑(MvPowerSeries.coeff R m✝) ↑x = ↑(MvPowerSeries.coeff R m✝) ↑y
  congr
  -- 🎉 no goals
#align mv_polynomial.coe_injective MvPolynomial.coe_injective

variable {σ R φ ψ}

@[simp, norm_cast]
theorem coe_inj : (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ :=
  (coe_injective σ R).eq_iff
#align mv_polynomial.coe_inj MvPolynomial.coe_inj

@[simp]
theorem coe_eq_zero_iff : (φ : MvPowerSeries σ R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]
                                                                    -- 🎉 no goals
#align mv_polynomial.coe_eq_zero_iff MvPolynomial.coe_eq_zero_iff

@[simp]
theorem coe_eq_one_iff : (φ : MvPowerSeries σ R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]
                                                                   -- 🎉 no goals
#align mv_polynomial.coe_eq_one_iff MvPolynomial.coe_eq_one_iff

/-- The coercion from multivariable polynomials to multivariable power series
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

/-- The coercion from multivariable polynomials to multivariable power series
as an algebra homomorphism.
-/
def coeToMvPowerSeries.algHom : MvPolynomial σ R →ₐ[R] MvPowerSeries σ A :=
  { (MvPowerSeries.map σ (algebraMap R A)).comp coeToMvPowerSeries.ringHom with
    commutes' := fun r => by simp [algebraMap_apply, MvPowerSeries.algebraMap_apply] }
                             -- 🎉 no goals
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

/-- Formal power series over the coefficient ring `R`.-/
def PowerSeries (R : Type*) :=
  MvPowerSeries Unit R
#align power_series PowerSeries

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section

-- Porting note: not available in Lean 4
-- local reducible PowerSeries

instance [Inhabited R] : Inhabited (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ Inhabited (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance [Zero R] : Zero (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ Zero (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance [AddMonoid R] : AddMonoid (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ AddMonoid (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance [AddGroup R] : AddGroup (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ AddGroup (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance [AddCommMonoid R] : AddCommMonoid (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ AddCommMonoid (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance [AddCommGroup R] : AddCommGroup (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ AddCommGroup (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance [Semiring R] : Semiring (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ Semiring (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance [CommSemiring R] : CommSemiring (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ CommSemiring (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance [Ring R] : Ring (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ Ring (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance [CommRing R] : CommRing (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ CommRing (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance [Nontrivial R] : Nontrivial (PowerSeries R) := by
  dsimp only [PowerSeries]
  -- ⊢ Nontrivial (MvPowerSeries Unit R)
  infer_instance
  -- 🎉 no goals

instance {A} [Semiring R] [AddCommMonoid A] [Module R A] : Module R (PowerSeries A) := by
  dsimp only [PowerSeries]
  -- ⊢ Module R (MvPowerSeries Unit A)
  infer_instance
  -- 🎉 no goals

instance {A S} [Semiring R] [Semiring S] [AddCommMonoid A] [Module R A] [Module S A] [SMul R S]
    [IsScalarTower R S A] : IsScalarTower R S (PowerSeries A) :=
  Pi.isScalarTower

instance {A} [Semiring A] [CommSemiring R] [Algebra R A] : Algebra R (PowerSeries A) := by
  dsimp only [PowerSeries]
  -- ⊢ Algebra R (MvPowerSeries Unit A)
  infer_instance
  -- 🎉 no goals

end

section Semiring

variable (R) [Semiring R]

/-- The `n`th coefficient of a formal power series.-/
def coeff (n : ℕ) : PowerSeries R →ₗ[R] R :=
  MvPowerSeries.coeff R (single () n)
#align power_series.coeff PowerSeries.coeff

/-- The `n`th monomial with coefficient `a` as formal power series.-/
def monomial (n : ℕ) : R →ₗ[R] PowerSeries R :=
  MvPowerSeries.monomial R (single () n)
#align power_series.monomial PowerSeries.monomial

variable {R}

theorem coeff_def {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) : coeff R n = MvPowerSeries.coeff R s := by
  erw [coeff, ← h, ← Finsupp.unique_single s]
  -- 🎉 no goals
#align power_series.coeff_def PowerSeries.coeff_def

/-- Two formal power series are equal if all their coefficients are equal.-/
@[ext]
theorem ext {φ ψ : PowerSeries R} (h : ∀ n, coeff R n φ = coeff R n ψ) : φ = ψ :=
  MvPowerSeries.ext fun n => by
    rw [← coeff_def]
    · apply h
      -- 🎉 no goals
    rfl
    -- 🎉 no goals
#align power_series.ext PowerSeries.ext

/-- Two formal power series are equal if all their coefficients are equal.-/
theorem ext_iff {φ ψ : PowerSeries R} : φ = ψ ↔ ∀ n, coeff R n φ = coeff R n ψ :=
  ⟨fun h n => congr_arg (coeff R n) h, ext⟩
#align power_series.ext_iff PowerSeries.ext_iff

/-- Constructor for formal power series.-/
def mk {R} (f : ℕ → R) : PowerSeries R := fun s => f (s ())
#align power_series.mk PowerSeries.mk

@[simp]
theorem coeff_mk (n : ℕ) (f : ℕ → R) : coeff R n (mk f) = f n :=
  congr_arg f Finsupp.single_eq_same
#align power_series.coeff_mk PowerSeries.coeff_mk

theorem coeff_monomial (m n : ℕ) (a : R) : coeff R m (monomial R n a) = if m = n then a else 0 :=
  calc
    coeff R m (monomial R n a) = _ := MvPowerSeries.coeff_monomial _ _ _
    _ = if m = n then a else 0 := by simp only [Finsupp.unique_single_eq_iff]
                                     -- 🎉 no goals

#align power_series.coeff_monomial PowerSeries.coeff_monomial

theorem monomial_eq_mk (n : ℕ) (a : R) : monomial R n a = mk fun m => if m = n then a else 0 :=
  ext fun m => by rw [coeff_monomial, coeff_mk]
                  -- 🎉 no goals
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
def constantCoeff : PowerSeries R →+* R :=
  MvPowerSeries.constantCoeff Unit R
#align power_series.constant_coeff PowerSeries.constantCoeff

/-- The constant formal power series.-/
def C : R →+* PowerSeries R :=
  MvPowerSeries.C Unit R
set_option linter.uppercaseLean3 false in
#align power_series.C PowerSeries.C

variable {R}

/-- The variable of the formal power series ring.-/
def X : PowerSeries R :=
  MvPowerSeries.X ()
set_option linter.uppercaseLean3 false in
#align power_series.X PowerSeries.X

theorem commute_X (φ : PowerSeries R) : Commute φ X :=
  MvPowerSeries.commute_X _ _
set_option linter.uppercaseLean3 false in
#align power_series.commute_X PowerSeries.commute_X

@[simp]
theorem coeff_zero_eq_constantCoeff : ⇑(coeff R 0) = constantCoeff R := by
  rw [coeff, Finsupp.single_zero]
  -- ⊢ ↑(MvPowerSeries.coeff R 0) = ↑(constantCoeff R)
  rfl
  -- 🎉 no goals
#align power_series.coeff_zero_eq_constant_coeff PowerSeries.coeff_zero_eq_constantCoeff

theorem coeff_zero_eq_constantCoeff_apply (φ : PowerSeries R) : coeff R 0 φ = constantCoeff R φ :=
  by rw [coeff_zero_eq_constantCoeff]
     -- 🎉 no goals
#align power_series.coeff_zero_eq_constant_coeff_apply PowerSeries.coeff_zero_eq_constantCoeff_apply

@[simp]
theorem monomial_zero_eq_C : ⇑(monomial R 0) = C R := by
  rw [monomial, Finsupp.single_zero, MvPowerSeries.monomial_zero_eq_C, C]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.monomial_zero_eq_C PowerSeries.monomial_zero_eq_C

theorem monomial_zero_eq_C_apply (a : R) : monomial R 0 a = C R a := by simp
                                                                        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.monomial_zero_eq_C_apply PowerSeries.monomial_zero_eq_C_apply

theorem coeff_C (n : ℕ) (a : R) : coeff R n (C R a : PowerSeries R) = if n = 0 then a else 0 := by
  rw [← monomial_zero_eq_C_apply, coeff_monomial]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_C PowerSeries.coeff_C

@[simp]
theorem coeff_zero_C (a : R) : coeff R 0 (C R a) = a := by
  rw [← monomial_zero_eq_C_apply, coeff_monomial_same 0 a]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_zero_C PowerSeries.coeff_zero_C

theorem X_eq : (X : PowerSeries R) = monomial R 1 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align power_series.X_eq PowerSeries.X_eq

theorem coeff_X (n : ℕ) : coeff R n (X : PowerSeries R) = if n = 1 then 1 else 0 := by
  rw [X_eq, coeff_monomial]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_X PowerSeries.coeff_X

@[simp]
theorem coeff_zero_X : coeff R 0 (X : PowerSeries R) = 0 := by
  rw [coeff, Finsupp.single_zero, X, MvPowerSeries.coeff_zero_X]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_zero_X PowerSeries.coeff_zero_X

@[simp]
theorem coeff_one_X : coeff R 1 (X : PowerSeries R) = 1 := by rw [coeff_X, if_pos rfl]
                                                              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_one_X PowerSeries.coeff_one_X

@[simp]
theorem X_ne_zero [Nontrivial R] : (X : PowerSeries R) ≠ 0 := fun H => by
  simpa only [coeff_one_X, one_ne_zero, map_zero] using congr_arg (coeff R 1) H
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.X_ne_zero PowerSeries.X_ne_zero

theorem X_pow_eq (n : ℕ) : (X : PowerSeries R) ^ n = monomial R n 1 :=
  MvPowerSeries.X_pow_eq _ n
set_option linter.uppercaseLean3 false in
#align power_series.X_pow_eq PowerSeries.X_pow_eq

theorem coeff_X_pow (m n : ℕ) : coeff R m ((X : PowerSeries R) ^ n) = if m = n then 1 else 0 := by
  rw [X_pow_eq, coeff_monomial]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_X_pow PowerSeries.coeff_X_pow

@[simp]
theorem coeff_X_pow_self (n : ℕ) : coeff R n ((X : PowerSeries R) ^ n) = 1 := by
  rw [coeff_X_pow, if_pos rfl]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_X_pow_self PowerSeries.coeff_X_pow_self

@[simp]
theorem coeff_one (n : ℕ) : coeff R n (1 : PowerSeries R) = if n = 0 then 1 else 0 :=
  coeff_C n 1
#align power_series.coeff_one PowerSeries.coeff_one

theorem coeff_zero_one : coeff R 0 (1 : PowerSeries R) = 1 :=
  coeff_zero_C 1
#align power_series.coeff_zero_one PowerSeries.coeff_zero_one

theorem coeff_mul (n : ℕ) (φ ψ : PowerSeries R) :
    coeff R n (φ * ψ) = ∑ p in Finset.Nat.antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ := by
  -- `rw` can't see that `PowerSeries = MvPowerSeries Unit`, so use `.trans`
  refine (MvPowerSeries.coeff_mul _ φ ψ).trans ?_
  -- ⊢ ∑ p in Finsupp.antidiagonal (single () n), ↑(MvPowerSeries.coeff R p.fst) φ  …
  rw [Finsupp.antidiagonal_single, Finset.sum_map]
  -- ⊢ ∑ x in Finset.Nat.antidiagonal n, ↑(MvPowerSeries.coeff R (↑(Function.Embedd …
  rfl
  -- 🎉 no goals
#align power_series.coeff_mul PowerSeries.coeff_mul

@[simp]
theorem coeff_mul_C (n : ℕ) (φ : PowerSeries R) (a : R) : coeff R n (φ * C R a) = coeff R n φ * a :=
  MvPowerSeries.coeff_mul_C _ φ a
set_option linter.uppercaseLean3 false in
#align power_series.coeff_mul_C PowerSeries.coeff_mul_C

@[simp]
theorem coeff_C_mul (n : ℕ) (φ : PowerSeries R) (a : R) : coeff R n (C R a * φ) = a * coeff R n φ :=
  MvPowerSeries.coeff_C_mul _ φ a
set_option linter.uppercaseLean3 false in
#align power_series.coeff_C_mul PowerSeries.coeff_C_mul

@[simp]
theorem coeff_smul {S : Type*} [Semiring S] [Module R S] (n : ℕ) (φ : PowerSeries S) (a : R) :
    coeff S n (a • φ) = a • coeff S n φ :=
  rfl
#align power_series.coeff_smul PowerSeries.coeff_smul

theorem smul_eq_C_mul (f : PowerSeries R) (a : R) : a • f = C R a * f := by
  ext
  -- ⊢ ↑(coeff R n✝) (a • f) = ↑(coeff R n✝) (↑(C R) a * f)
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.smul_eq_C_mul PowerSeries.smul_eq_C_mul

@[simp]
theorem coeff_succ_mul_X (n : ℕ) (φ : PowerSeries R) : coeff R (n + 1) (φ * X) = coeff R n φ := by
  simp only [coeff, Finsupp.single_add]
  -- ⊢ ↑(MvPowerSeries.coeff R (single () n + single () 1)) (φ * X) = ↑(MvPowerSeri …
  convert φ.coeff_add_mul_monomial (single () n) (single () 1) _
  -- ⊢ ↑(MvPowerSeries.coeff R (single () n)) φ = ↑(MvPowerSeries.coeff R (single ( …
  rw [mul_one]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_succ_mul_X PowerSeries.coeff_succ_mul_X

@[simp]
theorem coeff_succ_X_mul (n : ℕ) (φ : PowerSeries R) : coeff R (n + 1) (X * φ) = coeff R n φ := by
  simp only [coeff, Finsupp.single_add, add_comm n 1]
  -- ⊢ ↑(MvPowerSeries.coeff R (single () 1 + single () n)) (X * φ) = ↑(MvPowerSeri …
  convert φ.coeff_add_monomial_mul (single () 1) (single () n) _
  -- ⊢ ↑(MvPowerSeries.coeff R (single () n)) φ = 1 * ↑(MvPowerSeries.coeff R (sing …
  rw [one_mul]
  -- 🎉 no goals
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

-- Porting note: simp can prove this.
-- @[simp]
theorem constantCoeff_zero : constantCoeff R 0 = 0 :=
  rfl
#align power_series.constant_coeff_zero PowerSeries.constantCoeff_zero

-- Porting note: simp can prove this.
-- @[simp]
theorem constantCoeff_one : constantCoeff R 1 = 1 :=
  rfl
#align power_series.constant_coeff_one PowerSeries.constantCoeff_one

@[simp]
theorem constantCoeff_X : constantCoeff R X = 0 :=
  MvPowerSeries.coeff_zero_X _
set_option linter.uppercaseLean3 false in
#align power_series.constant_coeff_X PowerSeries.constantCoeff_X

theorem coeff_zero_mul_X (φ : PowerSeries R) : coeff R 0 (φ * X) = 0 := by simp
                                                                           -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_zero_mul_X PowerSeries.coeff_zero_mul_X

theorem coeff_zero_X_mul (φ : PowerSeries R) : coeff R 0 (X * φ) = 0 := by simp
                                                                           -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_zero_X_mul PowerSeries.coeff_zero_X_mul

-- The following section duplicates the api of `data.polynomial.coeff` and should attempt to keep
-- up to date with that
section

theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) :
    coeff R n (C R x * X ^ k : PowerSeries R) = if n = k then x else 0 := by
  simp [X_pow_eq, coeff_monomial]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_C_mul_X_pow PowerSeries.coeff_C_mul_X_pow

@[simp]
theorem coeff_mul_X_pow (p : PowerSeries R) (n d : ℕ) :
    coeff R (d + n) (p * X ^ n) = coeff R d p := by
  rw [coeff_mul, Finset.sum_eq_single (d, n), coeff_X_pow, if_pos rfl, mul_one]
  -- ⊢ ∀ (b : ℕ × ℕ), b ∈ Finset.Nat.antidiagonal (d + n) → b ≠ (d, n) → ↑(coeff R  …
  · rintro ⟨i, j⟩ h1 h2
    -- ⊢ ↑(coeff R (i, j).fst) p * ↑(coeff R (i, j).snd) (X ^ n) = 0
    rw [coeff_X_pow, if_neg, mul_zero]
    -- ⊢ ¬(i, j).snd = n
    rintro rfl
    -- ⊢ False
    apply h2
    -- ⊢ (i, j) = (d, (i, j).snd)
    rw [Finset.Nat.mem_antidiagonal, add_right_cancel_iff] at h1
    -- ⊢ (i, j) = (d, (i, j).snd)
    subst h1
    -- ⊢ (i, j) = ((i, j).fst, (i, j).snd)
    rfl
    -- 🎉 no goals
  · exact fun h1 => (h1 (Finset.Nat.mem_antidiagonal.2 rfl)).elim
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_mul_X_pow PowerSeries.coeff_mul_X_pow

@[simp]
theorem coeff_X_pow_mul (p : PowerSeries R) (n d : ℕ) :
    coeff R (d + n) (X ^ n * p) = coeff R d p := by
  rw [coeff_mul, Finset.sum_eq_single (n, d), coeff_X_pow, if_pos rfl, one_mul]
  -- ⊢ ∀ (b : ℕ × ℕ), b ∈ Finset.Nat.antidiagonal (d + n) → b ≠ (n, d) → ↑(coeff R  …
  · rintro ⟨i, j⟩ h1 h2
    -- ⊢ ↑(coeff R (i, j).fst) (X ^ n) * ↑(coeff R (i, j).snd) p = 0
    rw [coeff_X_pow, if_neg, zero_mul]
    -- ⊢ ¬(i, j).fst = n
    rintro rfl
    -- ⊢ False
    apply h2
    -- ⊢ (i, j) = ((i, j).fst, d)
    rw [Finset.Nat.mem_antidiagonal, add_comm, add_right_cancel_iff] at h1
    -- ⊢ (i, j) = ((i, j).fst, d)
    subst h1
    -- ⊢ (i, j) = ((i, j).fst, (i, j).snd)
    rfl
    -- 🎉 no goals
  · rw [add_comm]
    -- ⊢ ¬(n, d) ∈ Finset.Nat.antidiagonal (n + d) → ↑(coeff R (n, d).fst) (X ^ n) *  …
    exact fun h1 => (h1 (Finset.Nat.mem_antidiagonal.2 rfl)).elim
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_X_pow_mul PowerSeries.coeff_X_pow_mul

theorem coeff_mul_X_pow' (p : PowerSeries R) (n d : ℕ) :
    coeff R d (p * X ^ n) = ite (n ≤ d) (coeff R (d - n) p) 0 := by
  split_ifs with h
  -- ⊢ ↑(coeff R d) (p * X ^ n) = ↑(coeff R (d - n)) p
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
    -- 🎉 no goals
  · refine' (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => _)
    -- ⊢ ↑(coeff R x.fst) p * ↑(coeff R x.snd) (X ^ n) = 0
    rw [coeff_X_pow, if_neg, mul_zero]
    -- ⊢ ¬x.snd = n
    exact ((le_of_add_le_right (Finset.Nat.mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_mul_X_pow' PowerSeries.coeff_mul_X_pow'

theorem coeff_X_pow_mul' (p : PowerSeries R) (n d : ℕ) :
    coeff R d (X ^ n * p) = ite (n ≤ d) (coeff R (d - n) p) 0 := by
  split_ifs with h
  -- ⊢ ↑(coeff R d) (X ^ n * p) = ↑(coeff R (d - n)) p
  · rw [← tsub_add_cancel_of_le h, coeff_X_pow_mul]
    -- ⊢ ↑(coeff R (d - n)) p = ↑(coeff R (d - n + n - n)) p
    simp
    -- 🎉 no goals
  · refine' (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => _)
    -- ⊢ ↑(coeff R x.fst) (X ^ n) * ↑(coeff R x.snd) p = 0
    rw [coeff_X_pow, if_neg, zero_mul]
    -- ⊢ ¬x.fst = n
    have := Finset.Nat.mem_antidiagonal.mp hx
    -- ⊢ ¬x.fst = n
    rw [add_comm] at this
    -- ⊢ ¬x.fst = n
    exact ((le_of_add_le_right this.le).trans_lt <| not_le.mp h).ne
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.coeff_X_pow_mul' PowerSeries.coeff_X_pow_mul'

end

/-- If a formal power series is invertible, then so is its constant coefficient.-/
theorem isUnit_constantCoeff (φ : PowerSeries R) (h : IsUnit φ) : IsUnit (constantCoeff R φ) :=
  MvPowerSeries.isUnit_constantCoeff φ h
#align power_series.is_unit_constant_coeff PowerSeries.isUnit_constantCoeff

/-- Split off the constant coefficient. -/
theorem eq_shift_mul_X_add_const (φ : PowerSeries R) :
    φ = (mk fun p => coeff R (p + 1) φ) * X + C R (constantCoeff R φ) := by
  ext (_ | n)
  -- ⊢ ↑(coeff R Nat.zero) φ = ↑(coeff R Nat.zero) ((mk fun p => ↑(coeff R (p + 1)) …
  · simp only [Nat.zero_eq, coeff_zero_eq_constantCoeff, map_add, map_mul, constantCoeff_X,
      mul_zero, coeff_zero_C, zero_add]
  · simp only [coeff_succ_mul_X, coeff_mk, LinearMap.map_add, coeff_C, n.succ_ne_zero, sub_zero,
      if_false, add_zero]
set_option linter.uppercaseLean3 false in
#align power_series.eq_shift_mul_X_add_const PowerSeries.eq_shift_mul_X_add_const

/-- Split off the constant coefficient. -/
theorem eq_X_mul_shift_add_const (φ : PowerSeries R) :
    φ = (X * mk fun p => coeff R (p + 1) φ) + C R (constantCoeff R φ) := by
  ext (_ | n)
  -- ⊢ ↑(coeff R Nat.zero) φ = ↑(coeff R Nat.zero) ((X * mk fun p => ↑(coeff R (p + …
  · simp only [Nat.zero_eq, coeff_zero_eq_constantCoeff, map_add, map_mul, constantCoeff_X,
      zero_mul, coeff_zero_C, zero_add]
  · simp only [coeff_succ_X_mul, coeff_mk, LinearMap.map_add, coeff_C, n.succ_ne_zero, sub_zero,
      if_false, add_zero]
set_option linter.uppercaseLean3 false in
#align power_series.eq_X_mul_shift_add_const PowerSeries.eq_X_mul_shift_add_const

section Map

variable {S : Type*} {T : Type*} [Semiring S] [Semiring T]

variable (f : R →+* S) (g : S →+* T)

/-- The map between formal power series induced by a map on the coefficients.-/
def map : PowerSeries R →+* PowerSeries S :=
  MvPowerSeries.map _ f
#align power_series.map PowerSeries.map

@[simp]
theorem map_id : (map (RingHom.id R) : PowerSeries R → PowerSeries R) = id :=
  rfl
#align power_series.map_id PowerSeries.map_id

theorem map_comp : map (g.comp f) = (map g).comp (map f) :=
  rfl
#align power_series.map_comp PowerSeries.map_comp

@[simp]
theorem coeff_map (n : ℕ) (φ : PowerSeries R) : coeff S n (map f φ) = f (coeff R n φ) :=
  rfl
#align power_series.coeff_map PowerSeries.coeff_map

@[simp]
theorem map_C (r : R) : map f (C _ r) = C _ (f r) := by
  ext
  -- ⊢ ↑(coeff S n✝) (↑(map f) (↑(C R) r)) = ↑(coeff S n✝) (↑(C ((fun x => S) r)) ( …
  simp [coeff_C, apply_ite f]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.map_C PowerSeries.map_C

@[simp]
theorem map_X : map f X = X := by
  ext
  -- ⊢ ↑(coeff S n✝) (↑(map f) X) = ↑(coeff S n✝) X
  simp [coeff_X, apply_ite f]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.map_X PowerSeries.map_X

end Map

theorem X_pow_dvd_iff {n : ℕ} {φ : PowerSeries R} :
    (X : PowerSeries R) ^ n ∣ φ ↔ ∀ m, m < n → coeff R m φ = 0 := by
  convert@MvPowerSeries.X_pow_dvd_iff Unit R _ () n φ
  -- ⊢ (∀ (m : ℕ), m < n → ↑(coeff R m) φ = 0) ↔ ∀ (m : Unit →₀ ℕ), ↑m () < n → ↑(M …
  constructor <;> intro h m hm
  -- ⊢ (∀ (m : ℕ), m < n → ↑(coeff R m) φ = 0) → ∀ (m : Unit →₀ ℕ), ↑m () < n → ↑(M …
                  -- ⊢ ↑(MvPowerSeries.coeff R m) φ = 0
                  -- ⊢ ↑(coeff R m) φ = 0
  · rw [Finsupp.unique_single m]
    -- ⊢ ↑(MvPowerSeries.coeff R (single default (↑m default))) φ = 0
    convert h _ hm
    -- 🎉 no goals
  · apply h
    -- ⊢ ↑(single () m) () < n
    simpa only [Finsupp.single_eq_same] using hm
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.X_pow_dvd_iff PowerSeries.X_pow_dvd_iff

theorem X_dvd_iff {φ : PowerSeries R} : (X : PowerSeries R) ∣ φ ↔ constantCoeff R φ = 0 := by
  rw [← pow_one (X : PowerSeries R), X_pow_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]
  -- ⊢ (∀ (m : ℕ), m < 1 → ↑(coeff R m) φ = 0) ↔ ↑(coeff R 0) φ = 0
  constructor <;> intro h
  -- ⊢ (∀ (m : ℕ), m < 1 → ↑(coeff R m) φ = 0) → ↑(coeff R 0) φ = 0
                  -- ⊢ ↑(coeff R 0) φ = 0
                  -- ⊢ ∀ (m : ℕ), m < 1 → ↑(coeff R m) φ = 0
  · exact h 0 zero_lt_one
    -- 🎉 no goals
  · intro m hm
    -- ⊢ ↑(coeff R m) φ = 0
    rwa [Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hm)]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.X_dvd_iff PowerSeries.X_dvd_iff

end Semiring

section CommSemiring

variable [CommSemiring R]

open Finset Nat

/-- The ring homomorphism taking a power series `f(X)` to `f(aX)`. -/
noncomputable def rescale (a : R) : PowerSeries R →+* PowerSeries R where
  toFun f := PowerSeries.mk fun n => a ^ n * PowerSeries.coeff R n f
  map_zero' := by
    ext
    -- ⊢ ↑(coeff R n✝) (OneHom.toFun (↑{ toOneHom := { toFun := fun f => mk fun n =>  …
    simp only [LinearMap.map_zero, PowerSeries.coeff_mk, mul_zero]
    -- 🎉 no goals
    -- ⊢ ↑(coeff R n✝) ((fun f => mk fun n => a ^ n * ↑(coeff R n) f) 1) = ↑(coeff R  …
  map_one' := by
    -- ⊢ (if n✝ = 0 then a ^ n✝ else 0) = if n✝ = 0 then 1 else 0
    ext1
    -- ⊢ a ^ n✝ = 1
    simp only [mul_boole, PowerSeries.coeff_mk, PowerSeries.coeff_one]
      -- 🎉 no goals
    split_ifs with h
    -- 🎉 no goals
    · rw [h, pow_zero a]
    rfl
  map_add' := by
    intros
    -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := fun f => mk fun n => a ^ n * ↑(coeff …
    ext
    -- ⊢ ↑(coeff R n✝) (OneHom.toFun (↑{ toOneHom := { toFun := fun f => mk fun n =>  …
    -- ⊢ ↑(coeff R n✝) (OneHom.toFun { toFun := fun f => mk fun n => a ^ n * ↑(coeff  …
    dsimp only
    -- ⊢ ∑ x in antidiagonal n✝, a ^ n✝ * (↑(coeff R x.fst) f * ↑(coeff R x.snd) g) = …
    -- ⊢ ↑(coeff R n✝) (mk fun n => a ^ n * ↑(coeff R n) (x✝ + y✝)) = ↑(coeff R n✝) ( …
    -- ⊢ ∀ (x : ℕ × ℕ), x ∈ antidiagonal n✝ → a ^ n✝ * (↑(coeff R x.fst) f * ↑(coeff  …
    exact mul_add _ _ _
    -- ⊢ ∀ (a_1 b : ℕ), a_1 + b = n✝ → a ^ n✝ * (↑(coeff R a_1) f * ↑(coeff R b) g) = …
    -- 🎉 no goals
    -- ⊢ a ^ n✝ * (↑(coeff R b) f * ↑(coeff R c) g) = a ^ b * ↑(coeff R b) f * (a ^ c …
  map_mul' f g := by
    -- 🎉 no goals
    ext
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.mul_sum]
    apply sum_congr rfl
    simp only [coeff_mk, Prod.forall, Nat.mem_antidiagonal]
    intro b c H
    rw [← H, pow_add, mul_mul_mul_comm]
#align power_series.rescale PowerSeries.rescale

@[simp]
theorem coeff_rescale (f : PowerSeries R) (a : R) (n : ℕ) :
    coeff R n (rescale a f) = a ^ n * coeff R n f :=
  coeff_mk n (fun n ↦ a ^ n * (coeff R n) f)
#align power_series.coeff_rescale PowerSeries.coeff_rescale

@[simp]
theorem rescale_zero : rescale 0 = (C R).comp (constantCoeff R) := by
  ext x n
  -- ⊢ ↑(coeff R n) (↑(rescale 0) x) = ↑(coeff R n) (↑(RingHom.comp (C R) (constant …
  simp only [Function.comp_apply, RingHom.coe_comp, rescale, RingHom.coe_mk,
    PowerSeries.coeff_mk _ _, coeff_C]
  split_ifs with h <;> simp [h]
  -- ⊢ ↑(coeff R n) (↑{ toOneHom := { toFun := fun f => mk fun n => 0 ^ n * ↑(coeff …
                       -- 🎉 no goals
                       -- 🎉 no goals
#align power_series.rescale_zero PowerSeries.rescale_zero

theorem rescale_zero_apply : rescale 0 X = C R (constantCoeff R X) := by simp
                                                                         -- 🎉 no goals
#align power_series.rescale_zero_apply PowerSeries.rescale_zero_apply

@[simp]
theorem rescale_one : rescale 1 = RingHom.id (PowerSeries R) := by
  ext
  -- ⊢ ↑(coeff R n✝) (↑(rescale 1) x✝) = ↑(coeff R n✝) (↑(RingHom.id (PowerSeries R …
  simp only [coeff_rescale, one_pow, one_mul, RingHom.id_apply]
  -- 🎉 no goals
#align power_series.rescale_one PowerSeries.rescale_one

theorem rescale_mk (f : ℕ → R) (a : R) : rescale a (mk f) = mk fun n : ℕ => a ^ n * f n := by
  ext
  -- ⊢ ↑(coeff R n✝) (↑(rescale a) (mk f)) = ↑(coeff R n✝) (mk fun n => a ^ n * f n)
  rw [coeff_rescale, coeff_mk, coeff_mk]
  -- 🎉 no goals
#align power_series.rescale_mk PowerSeries.rescale_mk

theorem rescale_rescale (f : PowerSeries R) (a b : R) :
    rescale b (rescale a f) = rescale (a * b) f := by
  ext n
  -- ⊢ ↑(coeff R n) (↑(rescale b) (↑(rescale a) f)) = ↑(coeff R n) (↑(rescale (a *  …
  simp_rw [coeff_rescale]
  -- ⊢ b ^ n * (a ^ n * ↑(coeff R n) f) = (a * b) ^ n * ↑(coeff R n) f
  rw [mul_pow, mul_comm _ (b ^ n), mul_assoc]
  -- 🎉 no goals
#align power_series.rescale_rescale PowerSeries.rescale_rescale

theorem rescale_mul (a b : R) : rescale (a * b) = (rescale b).comp (rescale a) := by
  ext
  -- ⊢ ↑(coeff R n✝) (↑(rescale (a * b)) x✝) = ↑(coeff R n✝) (↑(RingHom.comp (resca …
  simp [← rescale_rescale]
  -- 🎉 no goals
#align power_series.rescale_mul PowerSeries.rescale_mul

section Trunc

/-- The `n`th truncation of a formal power series to a polynomial -/
def trunc (n : ℕ) (φ : PowerSeries R) : R[X] :=
  ∑ m in Ico 0 n, Polynomial.monomial m (coeff R m φ)
#align power_series.trunc PowerSeries.trunc

theorem coeff_trunc (m) (n) (φ : PowerSeries R) :
    (trunc n φ).coeff m = if m < n then coeff R m φ else 0 := by
  simp [trunc, Polynomial.coeff_sum, Polynomial.coeff_monomial, Nat.lt_succ_iff]
  -- 🎉 no goals
#align power_series.coeff_trunc PowerSeries.coeff_trunc

@[simp]
theorem trunc_zero (n) : trunc n (0 : PowerSeries R) = 0 :=
  Polynomial.ext fun m => by
    rw [coeff_trunc, LinearMap.map_zero, Polynomial.coeff_zero]
    -- ⊢ (if m < n then 0 else 0) = 0
    split_ifs <;> rfl
    -- ⊢ 0 = 0
                  -- 🎉 no goals
                  -- 🎉 no goals
#align power_series.trunc_zero PowerSeries.trunc_zero

@[simp]
theorem trunc_one (n) : trunc (n + 1) (1 : PowerSeries R) = 1 :=
  Polynomial.ext fun m => by
    rw [coeff_trunc, coeff_one]
    -- ⊢ (if m < n + 1 then if m = 0 then 1 else 0 else 0) = Polynomial.coeff 1 m
    split_ifs with H H' <;> rw [Polynomial.coeff_one]
                            -- ⊢ 1 = if 0 = m then 1 else 0
                            -- ⊢ 0 = if 0 = m then 1 else 0
                            -- ⊢ 0 = if 0 = m then 1 else 0
    · subst m
      -- ⊢ 1 = if 0 = 0 then 1 else 0
      rw [if_pos rfl]
      -- 🎉 no goals
    · symm
      -- ⊢ (if 0 = m then 1 else 0) = 0
      exact if_neg (Ne.elim (Ne.symm H'))
      -- 🎉 no goals
    · symm
      -- ⊢ (if 0 = m then 1 else 0) = 0
      refine' if_neg _
      -- ⊢ ¬0 = m
      rintro rfl
      -- ⊢ False
      apply H
      -- ⊢ 0 < n + 1
      exact Nat.zero_lt_succ _
      -- 🎉 no goals
#align power_series.trunc_one PowerSeries.trunc_one

@[simp]
theorem trunc_C (n) (a : R) : trunc (n + 1) (C R a) = Polynomial.C a :=
  Polynomial.ext fun m => by
    rw [coeff_trunc, coeff_C, Polynomial.coeff_C]
    -- ⊢ (if m < n + 1 then if m = 0 then a else 0 else 0) = if m = 0 then a else 0
    split_ifs with H <;> first |rfl|try simp_all
                         -- 🎉 no goals
                         -- 🎉 no goals
                         -- 🎉 no goals
                         -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.trunc_C PowerSeries.trunc_C

@[simp]
theorem trunc_add (n) (φ ψ : PowerSeries R) : trunc n (φ + ψ) = trunc n φ + trunc n ψ :=
  Polynomial.ext fun m => by
    simp only [coeff_trunc, AddMonoidHom.map_add, Polynomial.coeff_add]
    -- ⊢ (if m < n then ↑(coeff R m) (φ + ψ) else 0) = (if m < n then ↑(coeff R m) φ  …
    split_ifs with H
    -- ⊢ ↑(coeff R m) (φ + ψ) = ↑(coeff R m) φ + ↑(coeff R m) ψ
    · rfl
      -- 🎉 no goals
    · rw [zero_add]
      -- 🎉 no goals
#align power_series.trunc_add PowerSeries.trunc_add

end Trunc

end CommSemiring

section Ring

variable [Ring R]

/-- Auxiliary function used for computing inverse of a power series -/
protected def inv.aux : R → PowerSeries R → PowerSeries R :=
  MvPowerSeries.inv.aux
#align power_series.inv.aux PowerSeries.inv.aux

theorem coeff_inv_aux (n : ℕ) (a : R) (φ : PowerSeries R) :
    coeff R n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x in Finset.Nat.antidiagonal n,
            if x.2 < n then coeff R x.1 φ * coeff R x.2 (inv.aux a φ) else 0 := by
  rw [coeff, inv.aux, MvPowerSeries.coeff_inv_aux]
  -- ⊢ (if single () n = 0 then a else -a * ∑ x in Finsupp.antidiagonal (single ()  …
  simp only [Finsupp.single_eq_zero]
  -- ⊢ (if n = 0 then a else -a * ∑ x in Finsupp.antidiagonal (single () n), if x.s …
  split_ifs; · rfl
  -- ⊢ a = a
               -- 🎉 no goals
  congr 1
  -- ⊢ (∑ x in Finsupp.antidiagonal (single () n), if x.snd < single () n then ↑(Mv …
  symm
  -- ⊢ (∑ x in Finset.Nat.antidiagonal n, if x.snd < n then ↑(coeff R x.fst) φ * ↑( …
  apply Finset.sum_bij fun (p : ℕ × ℕ) _h => (single () p.1, single () p.2)
  · rintro ⟨i, j⟩ hij
    -- ⊢ (single () (i, j).fst, single () (i, j).snd) ∈ Finsupp.antidiagonal (single  …
    rw [Finset.Nat.mem_antidiagonal] at hij
    -- ⊢ (single () (i, j).fst, single () (i, j).snd) ∈ Finsupp.antidiagonal (single  …
    rw [Finsupp.mem_antidiagonal, ← Finsupp.single_add, hij]
    -- 🎉 no goals
  · rintro ⟨i, j⟩ _hij
    -- ⊢ (if (i, j).snd < n then ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) (MvP …
    by_cases H : j < n
    -- ⊢ (if (i, j).snd < n then ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) (MvP …
    · rw [if_pos H, if_pos]
      -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) (MvPowerSeries.inv.aux a φ)  …
      · rfl
        -- 🎉 no goals
      constructor
      -- ⊢ ∀ (i_1 : Unit), PartialOrder.toPreorder.1.1 (↑(single () (i, j).fst, single  …
      · rintro ⟨⟩
        -- ⊢ PartialOrder.toPreorder.1.1 (↑(single () (i, j).fst, single () (i, j).snd).s …
        simpa [Finsupp.single_eq_same] using le_of_lt H
        -- 🎉 no goals
      · intro hh
        -- ⊢ False
        rw [lt_iff_not_ge] at H
        -- ⊢ False
        apply H
        -- ⊢ j ≥ n
        simpa [Finsupp.single_eq_same] using hh ()
        -- 🎉 no goals
    · rw [if_neg H, if_neg]
      -- ⊢ ¬(single () (i, j).fst, single () (i, j).snd).snd < single () n
      rintro ⟨_h₁, h₂⟩
      -- ⊢ False
      apply h₂
      -- ⊢ ∀ (i_1 : Unit), PartialOrder.toPreorder.1.1 (↑(single () n) i_1) (↑(single ( …
      rintro ⟨⟩
      -- ⊢ PartialOrder.toPreorder.1.1 (↑(single () n) PUnit.unit) (↑(single () (i, j). …
      simpa [Finsupp.single_eq_same] using not_lt.1 H
      -- 🎉 no goals
  · rintro ⟨i, j⟩ ⟨k, l⟩ _hij _hkl
    -- ⊢ (single () (i, j).fst, single () (i, j).snd) = (single () (k, l).fst, single …
    simpa only [Prod.mk.inj_iff, Finsupp.unique_single_eq_iff] using id
    -- 🎉 no goals
  · rintro ⟨f, g⟩ hfg
    -- ⊢ ∃ a ha, (f, g) = (single () a.fst, single () a.snd)
    refine' ⟨(f (), g ()), _, _⟩
    -- ⊢ (↑f (), ↑g ()) ∈ Finset.Nat.antidiagonal n
    · rw [Finsupp.mem_antidiagonal] at hfg
      -- ⊢ (↑f (), ↑g ()) ∈ Finset.Nat.antidiagonal n
      rw [Finset.Nat.mem_antidiagonal, ← Finsupp.add_apply, hfg, Finsupp.single_eq_same]
      -- 🎉 no goals
    · rw [Prod.mk.inj_iff]
      -- ⊢ f = single () (↑f (), ↑g ()).fst ∧ g = single () (↑f (), ↑g ()).snd
      dsimp
      -- ⊢ f = single () (↑f ()) ∧ g = single () (↑g ())
      exact ⟨Finsupp.unique_single f, Finsupp.unique_single g⟩
      -- 🎉 no goals
#align power_series.coeff_inv_aux PowerSeries.coeff_inv_aux

/-- A formal power series is invertible if the constant coefficient is invertible.-/
def invOfUnit (φ : PowerSeries R) (u : Rˣ) : PowerSeries R :=
  MvPowerSeries.invOfUnit φ u
#align power_series.inv_of_unit PowerSeries.invOfUnit

theorem coeff_invOfUnit (n : ℕ) (φ : PowerSeries R) (u : Rˣ) :
    coeff R n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x in Finset.Nat.antidiagonal n,
            if x.2 < n then coeff R x.1 φ * coeff R x.2 (invOfUnit φ u) else 0 :=
  coeff_inv_aux n (↑u⁻¹ : R) φ
#align power_series.coeff_inv_of_unit PowerSeries.coeff_invOfUnit

@[simp]
theorem constantCoeff_invOfUnit (φ : PowerSeries R) (u : Rˣ) :
    constantCoeff R (invOfUnit φ u) = ↑u⁻¹ := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invOfUnit, if_pos rfl]
  -- 🎉 no goals
#align power_series.constant_coeff_inv_of_unit PowerSeries.constantCoeff_invOfUnit

theorem mul_invOfUnit (φ : PowerSeries R) (u : Rˣ) (h : constantCoeff R φ = u) :
    φ * invOfUnit φ u = 1 :=
  MvPowerSeries.mul_invOfUnit φ u <| h
#align power_series.mul_inv_of_unit PowerSeries.mul_invOfUnit

/-- Two ways of removing the constant coefficient of a power series are the same. -/
theorem sub_const_eq_shift_mul_X (φ : PowerSeries R) :
    φ - C R (constantCoeff R φ) = (PowerSeries.mk fun p => coeff R (p + 1) φ) * X :=
  sub_eq_iff_eq_add.mpr (eq_shift_mul_X_add_const φ)
set_option linter.uppercaseLean3 false in
#align power_series.sub_const_eq_shift_mul_X PowerSeries.sub_const_eq_shift_mul_X

theorem sub_const_eq_X_mul_shift (φ : PowerSeries R) :
    φ - C R (constantCoeff R φ) = X * PowerSeries.mk fun p => coeff R (p + 1) φ :=
  sub_eq_iff_eq_add.mpr (eq_X_mul_shift_add_const φ)
set_option linter.uppercaseLean3 false in
#align power_series.sub_const_eq_X_mul_shift PowerSeries.sub_const_eq_X_mul_shift

end Ring

section CommRing

variable {A : Type*} [CommRing A]

@[simp]
theorem rescale_X (a : A) : rescale a X = C A a * X := by
  ext
  -- ⊢ ↑(coeff A n✝) (↑(rescale a) X) = ↑(coeff A n✝) (↑(C A) a * X)
  simp only [coeff_rescale, coeff_C_mul, coeff_X]
  -- ⊢ (a ^ n✝ * if n✝ = 1 then 1 else 0) = a * if n✝ = 1 then 1 else 0
  split_ifs with h <;> simp [h]
  -- ⊢ a ^ n✝ * 1 = a * 1
                       -- 🎉 no goals
                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.rescale_X PowerSeries.rescale_X

theorem rescale_neg_one_X : rescale (-1 : A) X = -X := by
  rw [rescale_X, map_neg, map_one, neg_one_mul]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.rescale_neg_one_X PowerSeries.rescale_neg_one_X

/-- The ring homomorphism taking a power series `f(X)` to `f(-X)`. -/
noncomputable def evalNegHom : PowerSeries A →+* PowerSeries A :=
  rescale (-1 : A)
#align power_series.eval_neg_hom PowerSeries.evalNegHom

@[simp]
theorem evalNegHom_X : evalNegHom (X : PowerSeries A) = -X :=
  rescale_neg_one_X
set_option linter.uppercaseLean3 false in
#align power_series.eval_neg_hom_X PowerSeries.evalNegHom_X

end CommRing

section Domain

variable [Ring R]

theorem eq_zero_or_eq_zero_of_mul_eq_zero [NoZeroDivisors R] (φ ψ : PowerSeries R) (h : φ * ψ = 0) :
    φ = 0 ∨ ψ = 0 := by
  rw [or_iff_not_imp_left]
  -- ⊢ ¬φ = 0 → ψ = 0
  intro H
  -- ⊢ ψ = 0
  have ex : ∃ m, coeff R m φ ≠ 0 := by
    contrapose! H
    exact ext H
  let m := Nat.find ex
  -- ⊢ ψ = 0
  have hm₁ : coeff R m φ ≠ 0 := Nat.find_spec ex
  -- ⊢ ψ = 0
  have hm₂ : ∀ k < m, ¬coeff R k φ ≠ 0 := fun k => Nat.find_min ex
  -- ⊢ ψ = 0
  ext n
  -- ⊢ ↑(coeff R n) ψ = ↑(coeff R n) 0
  rw [(coeff R n).map_zero]
  -- ⊢ ↑(coeff R n) ψ = 0
  induction' n using Nat.strong_induction_on with n ih
  -- ⊢ ↑(coeff R n) ψ = 0
  replace h := congr_arg (coeff R (m + n)) h
  -- ⊢ ↑(coeff R n) ψ = 0
  rw [LinearMap.map_zero, coeff_mul, Finset.sum_eq_single (m, n)] at h
  · replace h := NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h
    -- ⊢ ↑(coeff R n) ψ = 0
    rw [or_iff_not_imp_left] at h
    -- ⊢ ↑(coeff R n) ψ = 0
    exact h hm₁
    -- 🎉 no goals
  · rintro ⟨i, j⟩ hij hne
    -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
    by_cases hj : j < n
    -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
    · rw [ih j hj, mul_zero]
      -- 🎉 no goals
    by_cases hi : i < m
    -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
    · specialize hm₂ _ hi
      -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
      push_neg at hm₂
      -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
      rw [hm₂, zero_mul]
      -- 🎉 no goals
    rw [Finset.Nat.mem_antidiagonal] at hij
    -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
    push_neg at hi hj
    -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
    suffices m < i by
      have : m + n < i + j := add_lt_add_of_lt_of_le this hj
      exfalso
      exact ne_of_lt this hij.symm
    contrapose! hne
    -- ⊢ (i, j) = (Nat.find ex, n)
    obtain rfl := le_antisymm hi hne
    -- ⊢ (Nat.find ex, j) = (Nat.find ex, n)
    simpa [Ne.def, Prod.mk.inj_iff] using (add_right_inj m).mp hij
    -- 🎉 no goals
  · contrapose!
    -- ⊢ ↑(coeff R (Nat.find ex)) φ * ↑(coeff R n) ψ ≠ 0 → (Nat.find ex, n) ∈ Finset. …
    intro
    -- ⊢ (Nat.find ex, n) ∈ Finset.Nat.antidiagonal (Nat.find ex + n)
    rw [Finset.Nat.mem_antidiagonal]
    -- 🎉 no goals
#align power_series.eq_zero_or_eq_zero_of_mul_eq_zero PowerSeries.eq_zero_or_eq_zero_of_mul_eq_zero

instance [NoZeroDivisors R] : NoZeroDivisors (PowerSeries R)
    where eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero _ _

instance [IsDomain R] : IsDomain (PowerSeries R) :=
  NoZeroDivisors.to_isDomain _

end Domain

section IsDomain

variable [CommRing R] [IsDomain R]

/-- The ideal spanned by the variable in the power series ring
 over an integral domain is a prime ideal.-/
theorem span_X_isPrime : (Ideal.span ({X} : Set (PowerSeries R))).IsPrime := by
  suffices Ideal.span ({X} : Set (PowerSeries R)) = RingHom.ker (constantCoeff R) by
    rw [this]
    exact RingHom.ker_isPrime _
  apply Ideal.ext
  -- ⊢ ∀ (x : PowerSeries R), x ∈ Ideal.span {X} ↔ x ∈ RingHom.ker (constantCoeff R)
  intro φ
  -- ⊢ φ ∈ Ideal.span {X} ↔ φ ∈ RingHom.ker (constantCoeff R)
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.span_X_is_prime PowerSeries.span_X_isPrime

/-- The variable of the power series ring over an integral domain is prime.-/
theorem X_prime : Prime (X : PowerSeries R) := by
  rw [← Ideal.span_singleton_prime]
  -- ⊢ Ideal.IsPrime (Ideal.span {X})
  · exact span_X_isPrime
    -- 🎉 no goals
  · intro h
    -- ⊢ False
    simpa [map_zero (coeff R 1)] using congr_arg (coeff R 1) h
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.X_prime PowerSeries.X_prime

theorem rescale_injective {a : R} (ha : a ≠ 0) : Function.Injective (rescale a) := by
  intro p q h
  -- ⊢ p = q
  rw [PowerSeries.ext_iff] at *
  -- ⊢ ∀ (n : ℕ), ↑(coeff R n) p = ↑(coeff R n) q
  intro n
  -- ⊢ ↑(coeff R n) p = ↑(coeff R n) q
  specialize h n
  -- ⊢ ↑(coeff R n) p = ↑(coeff R n) q
  rw [coeff_rescale, coeff_rescale, mul_eq_mul_left_iff] at h
  -- ⊢ ↑(coeff R n) p = ↑(coeff R n) q
  apply h.resolve_right
  -- ⊢ ¬a ^ n = 0
  intro h'
  -- ⊢ False
  exact ha (pow_eq_zero h')
  -- 🎉 no goals
#align power_series.rescale_injective PowerSeries.rescale_injective

end IsDomain

section LocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) [IsLocalRingHom f]

instance map.isLocalRingHom : IsLocalRingHom (map f) :=
  MvPowerSeries.map.isLocalRingHom f
#align power_series.map.is_local_ring_hom PowerSeries.map.isLocalRingHom

variable [LocalRing R] [LocalRing S]

instance : LocalRing (PowerSeries R) :=
  { inferInstanceAs <| LocalRing <| MvPowerSeries Unit R with }


end LocalRing

section Algebra

variable {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem C_eq_algebraMap {r : R} : C R r = (algebraMap R (PowerSeries R)) r :=
  rfl
set_option linter.uppercaseLean3 false in
#align power_series.C_eq_algebra_map PowerSeries.C_eq_algebraMap

theorem algebraMap_apply {r : R} : algebraMap R (PowerSeries A) r = C A (algebraMap R A r) :=
  MvPowerSeries.algebraMap_apply
#align power_series.algebra_map_apply PowerSeries.algebraMap_apply

instance [Nontrivial R] : Nontrivial (Subalgebra R (PowerSeries R)) :=
  { inferInstanceAs <| Nontrivial <| Subalgebra R <| MvPowerSeries Unit R with }

end Algebra

section Field

variable {k : Type*} [Field k]

/-- The inverse 1/f of a power series f defined over a field -/
protected def inv : PowerSeries k → PowerSeries k :=
  MvPowerSeries.inv
#align power_series.inv PowerSeries.inv

instance : Inv (PowerSeries k) :=
  ⟨PowerSeries.inv⟩

theorem inv_eq_inv_aux (φ : PowerSeries k) : φ⁻¹ = inv.aux (constantCoeff k φ)⁻¹ φ :=
  rfl
#align power_series.inv_eq_inv_aux PowerSeries.inv_eq_inv_aux

theorem coeff_inv (n) (φ : PowerSeries k) :
    coeff k n φ⁻¹ =
      if n = 0 then (constantCoeff k φ)⁻¹
      else
        -(constantCoeff k φ)⁻¹ *
          ∑ x in Finset.Nat.antidiagonal n,
            if x.2 < n then coeff k x.1 φ * coeff k x.2 φ⁻¹ else 0 :=
  by rw [inv_eq_inv_aux, coeff_inv_aux n (constantCoeff k φ)⁻¹ φ]
     -- 🎉 no goals
#align power_series.coeff_inv PowerSeries.coeff_inv

@[simp]
theorem constantCoeff_inv (φ : PowerSeries k) : constantCoeff k φ⁻¹ = (constantCoeff k φ)⁻¹ :=
  MvPowerSeries.constantCoeff_inv φ
#align power_series.constant_coeff_inv PowerSeries.constantCoeff_inv

theorem inv_eq_zero {φ : PowerSeries k} : φ⁻¹ = 0 ↔ constantCoeff k φ = 0 :=
  MvPowerSeries.inv_eq_zero
#align power_series.inv_eq_zero PowerSeries.inv_eq_zero

@[simp]
theorem zero_inv : (0 : PowerSeries k)⁻¹ = 0 :=
  MvPowerSeries.zero_inv
#align power_series.zero_inv PowerSeries.zero_inv

-- Porting note: simp can prove this.
-- @[simp]
theorem invOfUnit_eq (φ : PowerSeries k) (h : constantCoeff k φ ≠ 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  MvPowerSeries.invOfUnit_eq _ _
#align power_series.inv_of_unit_eq PowerSeries.invOfUnit_eq

@[simp]
theorem invOfUnit_eq' (φ : PowerSeries k) (u : Units k) (h : constantCoeff k φ = u) :
    invOfUnit φ u = φ⁻¹ :=
  MvPowerSeries.invOfUnit_eq' φ _ h
#align power_series.inv_of_unit_eq' PowerSeries.invOfUnit_eq'

@[simp]
protected theorem mul_inv_cancel (φ : PowerSeries k) (h : constantCoeff k φ ≠ 0) : φ * φ⁻¹ = 1 :=
  MvPowerSeries.mul_inv_cancel φ h
#align power_series.mul_inv_cancel PowerSeries.mul_inv_cancel

@[simp]
protected theorem inv_mul_cancel (φ : PowerSeries k) (h : constantCoeff k φ ≠ 0) : φ⁻¹ * φ = 1 :=
  MvPowerSeries.inv_mul_cancel φ h
#align power_series.inv_mul_cancel PowerSeries.inv_mul_cancel

theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : PowerSeries k} (h : constantCoeff k φ₃ ≠ 0) :
    φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  MvPowerSeries.eq_mul_inv_iff_mul_eq h
#align power_series.eq_mul_inv_iff_mul_eq PowerSeries.eq_mul_inv_iff_mul_eq

theorem eq_inv_iff_mul_eq_one {φ ψ : PowerSeries k} (h : constantCoeff k ψ ≠ 0) :
    φ = ψ⁻¹ ↔ φ * ψ = 1 :=
  MvPowerSeries.eq_inv_iff_mul_eq_one h
#align power_series.eq_inv_iff_mul_eq_one PowerSeries.eq_inv_iff_mul_eq_one

theorem inv_eq_iff_mul_eq_one {φ ψ : PowerSeries k} (h : constantCoeff k ψ ≠ 0) :
    ψ⁻¹ = φ ↔ φ * ψ = 1 :=
  MvPowerSeries.inv_eq_iff_mul_eq_one h
#align power_series.inv_eq_iff_mul_eq_one PowerSeries.inv_eq_iff_mul_eq_one

@[simp]
protected theorem mul_inv_rev (φ ψ : PowerSeries k) : (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ :=
  MvPowerSeries.mul_inv_rev _ _
#align power_series.mul_inv_rev PowerSeries.mul_inv_rev

instance : InvOneClass (PowerSeries k) :=
  { inferInstanceAs <| InvOneClass <| MvPowerSeries Unit k with }

@[simp]
theorem C_inv (r : k) : (C k r)⁻¹ = C k r⁻¹ :=
  MvPowerSeries.C_inv _
set_option linter.uppercaseLean3 false in
#align power_series.C_inv PowerSeries.C_inv

@[simp]
theorem X_inv : (X : PowerSeries k)⁻¹ = 0 :=
  MvPowerSeries.X_inv _
set_option linter.uppercaseLean3 false in
#align power_series.X_inv PowerSeries.X_inv

@[simp]
theorem smul_inv (r : k) (φ : PowerSeries k) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ :=
  MvPowerSeries.smul_inv _ _
#align power_series.smul_inv PowerSeries.smul_inv

end Field

end PowerSeries

namespace PowerSeries

variable {R : Type*}

attribute [local instance 1] Classical.propDecidable

section OrderBasic

open multiplicity

variable [Semiring R] {φ : PowerSeries R}

theorem exists_coeff_ne_zero_iff_ne_zero : (∃ n : ℕ, coeff R n φ ≠ 0) ↔ φ ≠ 0 := by
  refine' not_iff_not.mp _
  -- ⊢ (¬∃ n, ↑(coeff R n) φ ≠ 0) ↔ ¬φ ≠ 0
  push_neg
  -- ⊢ (∀ (n : ℕ), ↑(coeff R n) φ = 0) ↔ φ = 0
  simp [PowerSeries.ext_iff]
  -- 🎉 no goals
#align power_series.exists_coeff_ne_zero_iff_ne_zero PowerSeries.exists_coeff_ne_zero_iff_ne_zero

/-- The order of a formal power series `φ` is the greatest `n : PartENat`
such that `X^n` divides `φ`. The order is `⊤` if and only if `φ = 0`. -/
def order (φ : PowerSeries R) : PartENat :=
  if h : φ = 0 then ⊤ else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)
#align power_series.order PowerSeries.order

/-- The order of the `0` power series is infinite.-/
@[simp]
theorem order_zero : order (0 : PowerSeries R) = ⊤ :=
  dif_pos rfl
#align power_series.order_zero PowerSeries.order_zero

theorem order_finite_iff_ne_zero : (order φ).Dom ↔ φ ≠ 0 := by
  simp only [order]
  -- ⊢ (if h : φ = 0 then ⊤ else ↑(Nat.find (_ : ∃ n, ↑(coeff R n) φ ≠ 0))).Dom ↔ φ …
  constructor
  -- ⊢ (if h : φ = 0 then ⊤ else ↑(Nat.find (_ : ∃ n, ↑(coeff R n) φ ≠ 0))).Dom → φ …
  · split_ifs with h <;> intro H
    -- ⊢ ⊤.Dom → φ ≠ 0
                         -- ⊢ φ ≠ 0
                         -- ⊢ φ ≠ 0
    · contrapose! H
      -- ⊢ ¬⊤.Dom
      simp only [← Part.eq_none_iff']
      -- ⊢ ⊤ = Part.none
      rfl
      -- 🎉 no goals
    · exact h
      -- 🎉 no goals
  · intro h
    -- ⊢ (if h : φ = 0 then ⊤ else ↑(Nat.find (_ : ∃ n, ↑(coeff R n) φ ≠ 0))).Dom
    simp [h]
    -- 🎉 no goals
#align power_series.order_finite_iff_ne_zero PowerSeries.order_finite_iff_ne_zero

/-- If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero.-/
theorem coeff_order (h : (order φ).Dom) : coeff R (φ.order.get h) φ ≠ 0 := by
  simp only [order, order_finite_iff_ne_zero.mp h, not_false_iff, dif_neg, PartENat.get_natCast']
  -- ⊢ ↑(coeff R (Nat.find (_ : ∃ n, ↑(coeff R n) φ ≠ 0))) φ ≠ 0
  generalize_proofs h
  -- ⊢ ↑(coeff R (Nat.find h)) φ ≠ 0
  exact Nat.find_spec h
  -- 🎉 no goals
#align power_series.coeff_order PowerSeries.coeff_order

/-- If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`.-/
theorem order_le (n : ℕ) (h : coeff R n φ ≠ 0) : order φ ≤ n := by
  have _ :  ∃ n, coeff R n φ ≠ 0 := Exists.intro n h
  -- ⊢ order φ ≤ ↑n
  rw [order, dif_neg]
  -- ⊢ ↑(Nat.find (_ : ∃ n, ↑(coeff R n) φ ≠ 0)) ≤ ↑n
  · simp only [PartENat.coe_le_coe, Nat.find_le_iff]
    -- ⊢ ∃ m, m ≤ n ∧ ↑(coeff R m) φ ≠ 0
    exact ⟨n, le_rfl, h⟩
    -- 🎉 no goals
  · exact exists_coeff_ne_zero_iff_ne_zero.mp ⟨n, h⟩
    -- 🎉 no goals
#align power_series.order_le PowerSeries.order_le

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
theorem coeff_of_lt_order (n : ℕ) (h : ↑n < order φ) : coeff R n φ = 0 := by
  contrapose! h
  -- ⊢ order φ ≤ ↑n
  exact order_le _ h
  -- 🎉 no goals
#align power_series.coeff_of_lt_order PowerSeries.coeff_of_lt_order

/-- The `0` power series is the unique power series with infinite order.-/
@[simp]
theorem order_eq_top {φ : PowerSeries R} : φ.order = ⊤ ↔ φ = 0 := by
  constructor
  -- ⊢ order φ = ⊤ → φ = 0
  · intro h
    -- ⊢ φ = 0
    ext n
    -- ⊢ ↑(coeff R n) φ = ↑(coeff R n) 0
    rw [(coeff R n).map_zero, coeff_of_lt_order]
    -- ⊢ ↑n < order φ
    simp [h]
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ order 0 = ⊤
    exact order_zero
    -- 🎉 no goals
#align power_series.order_eq_top PowerSeries.order_eq_top

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
theorem nat_le_order (φ : PowerSeries R) (n : ℕ) (h : ∀ i < n, coeff R i φ = 0) : ↑n ≤ order φ := by
  by_contra H; rw [not_le] at H
  -- ⊢ False
               -- ⊢ False
  have : (order φ).Dom := PartENat.dom_of_le_natCast H.le
  -- ⊢ False
  rw [← PartENat.natCast_get this, PartENat.coe_lt_coe] at H
  -- ⊢ False
  exact coeff_order this (h _ H)
  -- 🎉 no goals
#align power_series.nat_le_order PowerSeries.nat_le_order

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
theorem le_order (φ : PowerSeries R) (n : PartENat) (h : ∀ i : ℕ, ↑i < n → coeff R i φ = 0) :
    n ≤ order φ := by
  induction n using PartENat.casesOn
  -- ⊢ ⊤ ≤ order φ
  · show _ ≤ _
    -- ⊢ ⊤ ≤ order φ
    rw [top_le_iff, order_eq_top]
    -- ⊢ φ = 0
    ext i
    -- ⊢ ↑(coeff R i) φ = ↑(coeff R i) 0
    exact h _ (PartENat.natCast_lt_top i)
    -- 🎉 no goals
  · apply nat_le_order
    -- ⊢ ∀ (i : ℕ), i < n✝ → ↑(coeff R i) φ = 0
    simpa only [PartENat.coe_lt_coe] using h
    -- 🎉 no goals
#align power_series.le_order PowerSeries.le_order

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
theorem order_eq_nat {φ : PowerSeries R} {n : ℕ} :
    order φ = n ↔ coeff R n φ ≠ 0 ∧ ∀ i, i < n → coeff R i φ = 0 := by
  rcases eq_or_ne φ 0 with (rfl | hφ)
  -- ⊢ order 0 = ↑n ↔ ↑(coeff R n) 0 ≠ 0 ∧ ∀ (i : ℕ), i < n → ↑(coeff R i) 0 = 0
  · simpa using (PartENat.natCast_ne_top _).symm
    -- 🎉 no goals
  simp [order, dif_neg hφ, Nat.find_eq_iff]
  -- 🎉 no goals
#align power_series.order_eq_nat PowerSeries.order_eq_nat

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
theorem order_eq {φ : PowerSeries R} {n : PartENat} :
    order φ = n ↔ (∀ i : ℕ, ↑i = n → coeff R i φ ≠ 0) ∧ ∀ i : ℕ, ↑i < n → coeff R i φ = 0 := by
  induction n using PartENat.casesOn
  -- ⊢ order φ = ⊤ ↔ (∀ (i : ℕ), ↑i = ⊤ → ↑(coeff R i) φ ≠ 0) ∧ ∀ (i : ℕ), ↑i < ⊤ → …
  · rw [order_eq_top]
    -- ⊢ φ = 0 ↔ (∀ (i : ℕ), ↑i = ⊤ → ↑(coeff R i) φ ≠ 0) ∧ ∀ (i : ℕ), ↑i < ⊤ → ↑(coe …
    constructor
    -- ⊢ φ = 0 → (∀ (i : ℕ), ↑i = ⊤ → ↑(coeff R i) φ ≠ 0) ∧ ∀ (i : ℕ), ↑i < ⊤ → ↑(coe …
    · rintro rfl
      -- ⊢ (∀ (i : ℕ), ↑i = ⊤ → ↑(coeff R i) 0 ≠ 0) ∧ ∀ (i : ℕ), ↑i < ⊤ → ↑(coeff R i)  …
      constructor <;> intros
      -- ⊢ ∀ (i : ℕ), ↑i = ⊤ → ↑(coeff R i) 0 ≠ 0
                      -- ⊢ ↑(coeff R i✝) 0 ≠ 0
                      -- ⊢ ↑(coeff R i✝) 0 = 0
      · exfalso
        -- ⊢ False
        exact PartENat.natCast_ne_top ‹_› ‹_›
        -- 🎉 no goals
      · exact (coeff _ _).map_zero
        -- 🎉 no goals
    · rintro ⟨_h₁, h₂⟩
      -- ⊢ φ = 0
      ext i
      -- ⊢ ↑(coeff R i) φ = ↑(coeff R i) 0
      exact h₂ i (PartENat.natCast_lt_top i)
      -- 🎉 no goals
  · simpa [PartENat.natCast_inj] using order_eq_nat
    -- 🎉 no goals
#align power_series.order_eq PowerSeries.order_eq

/-- The order of the sum of two formal power series
 is at least the minimum of their orders.-/
theorem le_order_add (φ ψ : PowerSeries R) : min (order φ) (order ψ) ≤ order (φ + ψ) := by
  refine' le_order _ _ _
  -- ⊢ ∀ (i : ℕ), ↑i < min (order φ) (order ψ) → ↑(coeff R i) (φ + ψ) = 0
  simp (config := { contextual := true }) [coeff_of_lt_order]
  -- 🎉 no goals
#align power_series.le_order_add PowerSeries.le_order_add

private theorem order_add_of_order_eq.aux (φ ψ : PowerSeries R) (_h : order φ ≠ order ψ)
    (H : order φ < order ψ) : order (φ + ψ) ≤ order φ ⊓ order ψ := by
  suffices order (φ + ψ) = order φ by
    rw [le_inf_iff, this]
    exact ⟨le_rfl, le_of_lt H⟩
  · rw [order_eq]
    -- ⊢ (∀ (i : ℕ), ↑i = order φ → ↑(coeff R i) (φ + ψ) ≠ 0) ∧ ∀ (i : ℕ), ↑i < order …
    constructor
    -- ⊢ ∀ (i : ℕ), ↑i = order φ → ↑(coeff R i) (φ + ψ) ≠ 0
    · intro i hi
      -- ⊢ ↑(coeff R i) (φ + ψ) ≠ 0
      rw [← hi] at H
      -- ⊢ ↑(coeff R i) (φ + ψ) ≠ 0
      rw [(coeff _ _).map_add, coeff_of_lt_order i H, add_zero]
      -- ⊢ ↑(coeff R i) φ ≠ 0
      exact (order_eq_nat.1 hi.symm).1
      -- 🎉 no goals
    · intro i hi
      -- ⊢ ↑(coeff R i) (φ + ψ) = 0
      rw [(coeff _ _).map_add, coeff_of_lt_order i hi, coeff_of_lt_order i (lt_trans hi H),
        zero_add]
-- #align power_series.order_add_of_order_eq.aux power_series.order_add_of_order_eq.aux

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
theorem order_add_of_order_eq (φ ψ : PowerSeries R) (h : order φ ≠ order ψ) :
    order (φ + ψ) = order φ ⊓ order ψ := by
  refine' le_antisymm _ (le_order_add _ _)
  -- ⊢ order (φ + ψ) ≤ order φ ⊓ order ψ
  by_cases H₁ : order φ < order ψ
  -- ⊢ order (φ + ψ) ≤ order φ ⊓ order ψ
  · apply order_add_of_order_eq.aux _ _ h H₁
    -- 🎉 no goals
  by_cases H₂ : order ψ < order φ
  -- ⊢ order (φ + ψ) ≤ order φ ⊓ order ψ
  · simpa only [add_comm, inf_comm] using order_add_of_order_eq.aux _ _ h.symm H₂
    -- 🎉 no goals
  exfalso; exact h (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁))
  -- ⊢ False
           -- 🎉 no goals
#align power_series.order_add_of_order_eq PowerSeries.order_add_of_order_eq

/-- The order of the product of two formal power series
 is at least the sum of their orders.-/
theorem order_mul_ge (φ ψ : PowerSeries R) : order φ + order ψ ≤ order (φ * ψ) := by
  apply le_order
  -- ⊢ ∀ (i : ℕ), ↑i < order φ + order ψ → ↑(coeff R i) (φ * ψ) = 0
  intro n hn; rw [coeff_mul, Finset.sum_eq_zero]
  -- ⊢ ↑(coeff R n) (φ * ψ) = 0
              -- ⊢ ∀ (x : ℕ × ℕ), x ∈ Finset.Nat.antidiagonal n → ↑(coeff R x.fst) φ * ↑(coeff  …
  rintro ⟨i, j⟩ hij
  -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
  by_cases hi : ↑i < order φ
  -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
  · rw [coeff_of_lt_order i hi, zero_mul]
    -- 🎉 no goals
  by_cases hj : ↑j < order ψ
  -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
  · rw [coeff_of_lt_order j hj, mul_zero]
    -- 🎉 no goals
  rw [not_lt] at hi hj; rw [Finset.Nat.mem_antidiagonal] at hij
  -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
                        -- ⊢ ↑(coeff R (i, j).fst) φ * ↑(coeff R (i, j).snd) ψ = 0
  exfalso
  -- ⊢ False
  apply ne_of_lt (lt_of_lt_of_le hn <| add_le_add hi hj)
  -- ⊢ ↑n = ↑i + ↑j
  rw [← Nat.cast_add, hij]
  -- 🎉 no goals
#align power_series.order_mul_ge PowerSeries.order_mul_ge

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise.-/
theorem order_monomial (n : ℕ) (a : R) [Decidable (a = 0)] :
    order (monomial R n a) = if a = 0 then (⊤ : PartENat) else n := by
  split_ifs with h
  -- ⊢ order (↑(monomial R n) a) = ⊤
  · rw [h, order_eq_top, LinearMap.map_zero]
    -- 🎉 no goals
  · rw [order_eq]
    -- ⊢ (∀ (i : ℕ), ↑i = ↑n → ↑(coeff R i) (↑(monomial R n) a) ≠ 0) ∧ ∀ (i : ℕ), ↑i  …
    constructor <;> intro i hi
    -- ⊢ ∀ (i : ℕ), ↑i = ↑n → ↑(coeff R i) (↑(monomial R n) a) ≠ 0
                    -- ⊢ ↑(coeff R i) (↑(monomial R n) a) ≠ 0
                    -- ⊢ ↑(coeff R i) (↑(monomial R n) a) = 0
    · rw [PartENat.natCast_inj] at hi
      -- ⊢ ↑(coeff R i) (↑(monomial R n) a) ≠ 0
      rwa [hi, coeff_monomial_same]
      -- 🎉 no goals
    · rw [PartENat.coe_lt_coe] at hi
      -- ⊢ ↑(coeff R i) (↑(monomial R n) a) = 0
      rw [coeff_monomial, if_neg]
      -- ⊢ ¬i = n
      exact ne_of_lt hi
      -- 🎉 no goals
#align power_series.order_monomial PowerSeries.order_monomial

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
theorem order_monomial_of_ne_zero (n : ℕ) (a : R) (h : a ≠ 0) : order (monomial R n a) = n := by
  rw [order_monomial, if_neg h]
  -- 🎉 no goals
#align power_series.order_monomial_of_ne_zero PowerSeries.order_monomial_of_ne_zero

/-- If `n` is strictly smaller than the order of `ψ`, then the `n`th coefficient of its product
with any other power series is `0`. -/
theorem coeff_mul_of_lt_order {φ ψ : PowerSeries R} {n : ℕ} (h : ↑n < ψ.order) :
    coeff R n (φ * ψ) = 0 := by
  suffices : coeff R n (φ * ψ) = ∑ p in Finset.Nat.antidiagonal n, 0
  -- ⊢ ↑(coeff R n) (φ * ψ) = 0
  rw [this, Finset.sum_const_zero]
  -- ⊢ ↑(coeff R n) (φ * ψ) = ∑ p in Finset.Nat.antidiagonal n, 0
  rw [coeff_mul]
  -- ⊢ ∑ p in Finset.Nat.antidiagonal n, ↑(coeff R p.fst) φ * ↑(coeff R p.snd) ψ =  …
  apply Finset.sum_congr rfl
  -- ⊢ ∀ (x : ℕ × ℕ), x ∈ Finset.Nat.antidiagonal n → ↑(coeff R x.fst) φ * ↑(coeff  …
  intro x hx
  -- ⊢ ↑(coeff R x.fst) φ * ↑(coeff R x.snd) ψ = 0
  refine' mul_eq_zero_of_right (coeff R x.fst φ) (coeff_of_lt_order x.snd (lt_of_le_of_lt _ h))
  -- ⊢ ↑x.snd ≤ ↑n
  rw [Finset.Nat.mem_antidiagonal] at hx
  -- ⊢ ↑x.snd ≤ ↑n
  norm_cast
  -- ⊢ x.snd ≤ n
  linarith
  -- 🎉 no goals
#align power_series.coeff_mul_of_lt_order PowerSeries.coeff_mul_of_lt_order

theorem coeff_mul_one_sub_of_lt_order {R : Type*} [CommRing R] {φ ψ : PowerSeries R} (n : ℕ)
    (h : ↑n < ψ.order) : coeff R n (φ * (1 - ψ)) = coeff R n φ := by
  simp [coeff_mul_of_lt_order h, mul_sub]
  -- 🎉 no goals
#align power_series.coeff_mul_one_sub_of_lt_order PowerSeries.coeff_mul_one_sub_of_lt_order

theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (k : ℕ) (s : Finset ι)
    (φ : PowerSeries R) (f : ι → PowerSeries R) :
    (∀ i ∈ s, ↑k < (f i).order) → coeff R k (φ * ∏ i in s, (1 - f i)) = coeff R k φ := by
  induction' s using Finset.induction_on with a s ha ih t
  -- ⊢ (∀ (i : ι), i ∈ ∅ → ↑k < order (f i)) → ↑(coeff R k) (φ * ∏ i in ∅, (1 - f i …
  · simp
    -- 🎉 no goals
  · intro t
    -- ⊢ ↑(coeff R k) (φ * ∏ i in insert a s, (1 - f i)) = ↑(coeff R k) φ
    simp only [Finset.mem_insert, forall_eq_or_imp] at t
    -- ⊢ ↑(coeff R k) (φ * ∏ i in insert a s, (1 - f i)) = ↑(coeff R k) φ
    rw [Finset.prod_insert ha, ← mul_assoc, mul_right_comm, coeff_mul_one_sub_of_lt_order _ t.1]
    -- ⊢ ↑(coeff R k) (φ * ∏ x in s, (1 - f x)) = ↑(coeff R k) φ
    exact ih t.2
    -- 🎉 no goals
#align power_series.coeff_mul_prod_one_sub_of_lt_order PowerSeries.coeff_mul_prod_one_sub_of_lt_order

-- TODO: link with `X_pow_dvd_iff`
theorem X_pow_order_dvd (h : (order φ).Dom) : X ^ (order φ).get h ∣ φ := by
  refine' ⟨PowerSeries.mk fun n => coeff R (n + (order φ).get h) φ, _⟩
  -- ⊢ φ = X ^ Part.get (order φ) h * mk fun n => ↑(coeff R (n + Part.get (order φ) …
  ext n
  -- ⊢ ↑(coeff R n) φ = ↑(coeff R n) (X ^ Part.get (order φ) h * mk fun n => ↑(coef …
  simp only [coeff_mul, coeff_X_pow, coeff_mk, boole_mul, Finset.sum_ite,
    Finset.Nat.filter_fst_eq_antidiagonal, Finset.sum_const_zero, add_zero]
  split_ifs with hn
  -- ⊢ ↑(coeff R n) φ = ∑ x in {(Part.get (order φ) h, n - Part.get (order φ) h)},  …
  · simp [tsub_add_cancel_of_le hn]
    -- 🎉 no goals
  · simp only [Finset.sum_empty]
    -- ⊢ ↑(coeff R n) φ = 0
    refine' coeff_of_lt_order _ _
    -- ⊢ ↑n < order φ
    simpa [PartENat.coe_lt_iff] using fun _ => hn
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.X_pow_order_dvd PowerSeries.X_pow_order_dvd

theorem order_eq_multiplicity_X {R : Type*} [Semiring R] (φ : PowerSeries R) :
    order φ = multiplicity X φ := by
  rcases eq_or_ne φ 0 with (rfl | hφ)
  -- ⊢ order 0 = multiplicity X 0
  · simp
    -- 🎉 no goals
  induction' ho : order φ using PartENat.casesOn with n
  -- ⊢ ⊤ = multiplicity X φ
  · simp [hφ] at ho
    -- 🎉 no goals
  have hn : φ.order.get (order_finite_iff_ne_zero.mpr hφ) = n := by simp [ho]
  -- ⊢ ↑n = multiplicity X φ
  rw [← hn]
  -- ⊢ ↑(Part.get (order φ) (_ : (order φ).Dom)) = multiplicity X φ
  refine'
    le_antisymm (le_multiplicity_of_pow_dvd <| X_pow_order_dvd (order_finite_iff_ne_zero.mpr hφ))
      (PartENat.find_le _ _ _)
  rintro ⟨ψ, H⟩
  -- ⊢ False
  have := congr_arg (coeff R n) H
  -- ⊢ False
  rw [← (ψ.commute_X.pow_right _).eq, coeff_mul_of_lt_order, ← hn] at this
  -- ⊢ False
  · exact coeff_order _ this
    -- 🎉 no goals
  · rw [X_pow_eq, order_monomial]
    -- ⊢ ↑n < if 1 = 0 then ⊤ else ↑(Part.get (order φ) (_ : (order φ).Dom) + 1)
    split_ifs
    -- ⊢ ↑n < ⊤
    · exact PartENat.natCast_lt_top _
      -- 🎉 no goals
    · rw [← hn, PartENat.coe_lt_coe]
      -- ⊢ Part.get (order φ) (_ : (order φ).Dom) < Part.get (order φ) (_ : (order φ).D …
      exact Nat.lt_succ_self _
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.order_eq_multiplicity_X PowerSeries.order_eq_multiplicity_X

end OrderBasic

section OrderZeroNeOne

variable [Semiring R] [Nontrivial R]

/-- The order of the formal power series `1` is `0`.-/
@[simp]
theorem order_one : order (1 : PowerSeries R) = 0 := by
  simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero
  -- 🎉 no goals
#align power_series.order_one PowerSeries.order_one

/-- The order of the formal power series `X` is `1`.-/
@[simp]
theorem order_X : order (X : PowerSeries R) = 1 := by
  simpa only [Nat.cast_one] using order_monomial_of_ne_zero 1 (1 : R) one_ne_zero
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.order_X PowerSeries.order_X

/-- The order of the formal power series `X^n` is `n`.-/
@[simp]
theorem order_X_pow (n : ℕ) : order ((X : PowerSeries R) ^ n) = n := by
  rw [X_pow_eq, order_monomial_of_ne_zero]
  -- ⊢ 1 ≠ 0
  exact one_ne_zero
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align power_series.order_X_pow PowerSeries.order_X_pow

end OrderZeroNeOne

section OrderIsDomain

-- TODO: generalize to `[Semiring R] [NoZeroDivisors R]`
variable [CommRing R] [IsDomain R]

/-- The order of the product of two formal power series over an integral domain
 is the sum of their orders.-/
theorem order_mul (φ ψ : PowerSeries R) : order (φ * ψ) = order φ + order ψ := by
  simp_rw [order_eq_multiplicity_X]
  -- ⊢ multiplicity X (φ * ψ) = multiplicity X φ + multiplicity X ψ
  exact multiplicity.mul X_prime
  -- 🎉 no goals
#align power_series.order_mul PowerSeries.order_mul

end OrderIsDomain

end PowerSeries

namespace Polynomial

open Finsupp

variable {σ : Type*} {R : Type*} [CommSemiring R] (φ ψ : R[X])

-- Porting note: added so we can add the `@[coe]` attribute
/-- The natural inclusion from polynomials into formal power series.-/
@[coe]
def ToPowerSeries : R[X] → (PowerSeries R) := fun φ =>
  PowerSeries.mk fun n => coeff φ n

/-- The natural inclusion from polynomials into formal power series.-/
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
  -- ⊢ ↑(PowerSeries.coeff R n✝) ↑(↑(monomial n) a) = ↑(PowerSeries.coeff R n✝) (↑( …
  simp [coeff_coe, PowerSeries.coeff_monomial, Polynomial.coeff_monomial, eq_comm]
  -- 🎉 no goals
#align polynomial.coe_monomial Polynomial.coe_monomial

@[simp, norm_cast]
theorem coe_zero : ((0 : R[X]) : PowerSeries R) = 0 :=
  rfl
#align polynomial.coe_zero Polynomial.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : R[X]) : PowerSeries R) = 1 := by
  have := coe_monomial 0 (1 : R)
  -- ⊢ ↑1 = 1
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this
  -- 🎉 no goals
#align polynomial.coe_one Polynomial.coe_one

@[simp, norm_cast]
theorem coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ := by
  ext
  -- ⊢ ↑(PowerSeries.coeff R n✝) ↑(φ + ψ) = ↑(PowerSeries.coeff R n✝) (↑φ + ↑ψ)
  simp
  -- 🎉 no goals
#align polynomial.coe_add Polynomial.coe_add

@[simp, norm_cast]
theorem coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ :=
  PowerSeries.ext fun n => by simp only [coeff_coe, PowerSeries.coeff_mul, coeff_mul]
                              -- 🎉 no goals
#align polynomial.coe_mul Polynomial.coe_mul

@[simp, norm_cast]
theorem coe_C (a : R) : ((C a : R[X]) : PowerSeries R) = PowerSeries.C R a := by
  have := coe_monomial 0 a
  -- ⊢ ↑(↑C a) = ↑(PowerSeries.C R) a
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this
  -- 🎉 no goals
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
  -- 🎉 no goals
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
  -- ⊢ coeff x n✝ = coeff y n✝
  simp_rw [← coeff_coe]
  -- ⊢ ↑(PowerSeries.coeff R n✝) ↑x = ↑(PowerSeries.coeff R n✝) ↑y
  congr
  -- 🎉 no goals
#align polynomial.coe_injective Polynomial.coe_injective

variable {R φ ψ}

@[simp, norm_cast]
theorem coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ :=
  (coe_injective R).eq_iff
#align polynomial.coe_inj Polynomial.coe_inj

@[simp]
theorem coe_eq_zero_iff : (φ : PowerSeries R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]
                                                                -- 🎉 no goals
#align polynomial.coe_eq_zero_iff Polynomial.coe_eq_zero_iff

@[simp]
theorem coe_eq_one_iff : (φ : PowerSeries R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]
                                                               -- 🎉 no goals
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

variable (A : Type*) [Semiring A] [Algebra R A]

/-- The coercion from polynomials to power series
as an algebra homomorphism.
-/
def coeToPowerSeries.algHom : R[X] →ₐ[R] PowerSeries A :=
  { (PowerSeries.map (algebraMap R A)).comp coeToPowerSeries.ringHom with
    commutes' := fun r => by simp [algebraMap_apply, PowerSeries.algebraMap_apply] }
                             -- 🎉 no goals
#align polynomial.coe_to_power_series.alg_hom Polynomial.coeToPowerSeries.algHom

@[simp]
theorem coeToPowerSeries.algHom_apply :
    coeToPowerSeries.algHom A φ = PowerSeries.map (algebraMap R A) ↑φ :=
  rfl
#align polynomial.coe_to_power_series.alg_hom_apply Polynomial.coeToPowerSeries.algHom_apply

end Polynomial

namespace PowerSeries

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : PowerSeries R)

instance algebraPolynomial : Algebra R[X] (PowerSeries A) :=
  RingHom.toAlgebra (Polynomial.coeToPowerSeries.algHom A).toRingHom
#align power_series.algebra_polynomial PowerSeries.algebraPolynomial

instance algebraPowerSeries : Algebra (PowerSeries R) (PowerSeries A) :=
  (map (algebraMap R A)).toAlgebra
#align power_series.algebra_power_series PowerSeries.algebraPowerSeries

-- see Note [lower instance priority]
instance (priority := 100) algebraPolynomial' {A : Type*} [CommSemiring A] [Algebra R A[X]] :
    Algebra R (PowerSeries A) :=
  RingHom.toAlgebra <| Polynomial.coeToPowerSeries.ringHom.comp (algebraMap R A[X])
#align power_series.algebra_polynomial' PowerSeries.algebraPolynomial'

variable (A)

theorem algebraMap_apply' (p : R[X]) : algebraMap R[X] (PowerSeries A) p = map (algebraMap R A) p :=
  rfl
#align power_series.algebra_map_apply' PowerSeries.algebraMap_apply'

theorem algebraMap_apply'' :
    algebraMap (PowerSeries R) (PowerSeries A) f = map (algebraMap R A) f :=
  rfl
#align power_series.algebra_map_apply'' PowerSeries.algebraMap_apply''

end PowerSeries
