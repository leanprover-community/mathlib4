/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.Data.Finsupp.PWO

/-!
# Comparison between Hahn series and power series
If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `R⟦Γ⟧`.  When `R` is a semiring and `Γ = ℕ`, then
we get the more familiar semiring of formal power series with coefficients in `R`.

## Main Definitions
* `toPowerSeries` the isomorphism from `R⟦ℕ⟧` to `PowerSeries R`.
* `ofPowerSeries` the inverse, casting a `PowerSeries R` to a `R⟦ℕ⟧`.

## Instances
* For `Finite σ`, the instance `NoZeroDivisors R⟦σ →₀ ℕ⟧`,
  deduced from the case of `MvPowerSeries`
  The case of `R⟦ℕ⟧` is taken care of by `instNoZeroDivisors`.

## TODO
* Build an API for the variable `X` (defined to be `single 1 1 : R⟦Γ⟧`) in analogy to
  `X : R[X]` and `X : PowerSeries R`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


open Finset Function Pointwise Polynomial

noncomputable section

variable {Γ R : Type*}

namespace HahnSeries

section Semiring

variable [Semiring R]

/-- The ring `R⟦ℕ⟧` is isomorphic to `PowerSeries R`. -/
@[simps]
def toPowerSeries : R⟦ℕ⟧ ≃+* PowerSeries R where
  toFun f := PowerSeries.mk f.coeff
  invFun f := ⟨fun n => PowerSeries.coeff n f, .of_linearOrder _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, coeff_mul]
    classical
    refine (sum_filter_ne_zero _).symm.trans <| (sum_congr ?_ fun _ _ ↦ rfl).trans <|
      sum_filter_ne_zero _
    ext m
    simp only [mem_antidiagonal, mem_addAntidiagonal, and_congr_left_iff, mem_filter,
      mem_support]
    rintro h
    rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]

theorem coeff_toPowerSeries {f : R⟦ℕ⟧} {n : ℕ} :
    PowerSeries.coeff n (toPowerSeries f) = f.coeff n :=
  PowerSeries.coeff_mk _ _

theorem coeff_toPowerSeries_symm {f : PowerSeries R} {n : ℕ} :
    (HahnSeries.toPowerSeries.symm f).coeff n = PowerSeries.coeff n f :=
  rfl

variable (Γ R) [Semiring Γ] [PartialOrder Γ] [IsStrictOrderedRing Γ]

/-- Casts a power series as a Hahn series with coefficients from a `StrictOrderedSemiring`. -/
def ofPowerSeries : PowerSeries R →+* R⟦Γ⟧ :=
  (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (RingEquiv.toRingHom toPowerSeries.symm)

variable {Γ R}

theorem ofPowerSeries_injective : Function.Injective (ofPowerSeries Γ R) :=
  embDomain_injective.comp toPowerSeries.symm.injective

-- Not `@[simp]` since the RHS is more complicated and it makes linter failures elsewhere
theorem ofPowerSeries_apply (x : PowerSeries R) :
    ofPowerSeries Γ R x = embDomain Nat.castOrderEmbedding (toPowerSeries.symm x) :=
  rfl

theorem ofPowerSeries_apply_coeff (x : PowerSeries R) (n : ℕ) :
    (ofPowerSeries Γ R x).coeff n = PowerSeries.coeff n x := by
  trans (embDomain (Nat.castOrderEmbedding (α := Γ)) (toPowerSeries.symm x)).coeff
    (Nat.castOrderEmbedding n)
  · simp [ofPowerSeries_apply]
  rw [embDomain_coeff]
  simp

@[simp]
theorem ofPowerSeries_C (r : R) : ofPowerSeries Γ R (PowerSeries.C r) = HahnSeries.C r := by
  ext n
  simp only [ofPowerSeries_apply, C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_single]
  split_ifs with hn
  · subst hn
    convert! embDomain_coeff (a := 0) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_C]
    intro
    simp +contextual [Ne.symm hn]

@[simp]
theorem ofPowerSeries_X : ofPowerSeries Γ R PowerSeries.X = single 1 1 := by
  ext n
  simp only [coeff_single, ofPowerSeries_apply]
  split_ifs with hn
  · rw [hn]
    convert! embDomain_coeff (a := 1) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_X]
    intro
    simp +contextual [Ne.symm hn]

theorem ofPowerSeries_X_pow {R} [Semiring R] (n : ℕ) :
    ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1 := by
  simp

set_option backward.isDefEq.respectTransparency false in
-- Lemmas about converting hahn_series over fintype to and from mv_power_series
/-- The ring `R⟦σ →₀ ℕ⟧` is isomorphic to `MvPowerSeries σ R` for a `Finite` `σ`.
We take the index set of the hahn series to be `Finsupp` rather than `pi`,
even though we assume `Finite σ` as this is more natural for alignment with `MvPowerSeries`.
After importing `Mathlib/Algebra/Order/Pi.lean` the ring `R⟦σ → ℕ⟧` could be constructed
instead.
-/
@[simps]
def toMvPowerSeries {σ : Type*} [Finite σ] : R⟦σ →₀ ℕ⟧ ≃+* MvPowerSeries σ R where
  toFun f := f.coeff
  invFun f := ⟨(f : (σ →₀ ℕ) → R), Set.isPWO_of_wellQuasiOrderedLE _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    classical
      change (f * g).coeff n = _
      simp_rw [coeff_mul]
      refine (sum_filter_ne_zero _).symm.trans <| (sum_congr ?_ fun _ _ ↦ rfl).trans <|
        sum_filter_ne_zero _
      ext m
      simp only [and_congr_left_iff, mem_addAntidiagonal, mem_filter, mem_support,
        Finset.mem_antidiagonal]
      rintro h
      rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]

variable {σ : Type*} [Finite σ]

-- TODO : generalize to all (?) rings of Hahn Series
/-- If R has no zero divisors and `σ` is finite,
then `R⟦σ →₀ ℕ⟧` has no zero divisors -/
instance [NoZeroDivisors R] : NoZeroDivisors (R⟦σ →₀ ℕ⟧) :=
  toMvPowerSeries.toMulEquiv.noZeroDivisors (A := R⟦σ →₀ ℕ⟧) (MvPowerSeries σ R)

theorem coeff_toMvPowerSeries {f : R⟦σ →₀ ℕ⟧} {n : σ →₀ ℕ} :
    MvPowerSeries.coeff n (toMvPowerSeries f) = f.coeff n :=
  rfl

theorem coeff_toMvPowerSeries_symm {f : MvPowerSeries σ R} {n : σ →₀ ℕ} :
    (HahnSeries.toMvPowerSeries.symm f).coeff n = MvPowerSeries.coeff n f :=
  rfl

end Semiring

section Algebra

variable (R) [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

/-- The `R`-algebra `A⟦ℕ⟧` is isomorphic to `PowerSeries A`. -/
@[simps!]
def toPowerSeriesAlg : A⟦ℕ⟧ ≃ₐ[R] PowerSeries A :=
  { toPowerSeries with
    commutes' := fun r => by
      ext n
      cases n <;> simp [algebraMap_apply, PowerSeries.algebraMap_apply] }

variable (Γ) [Semiring Γ] [PartialOrder Γ] [IsStrictOrderedRing Γ]

/-- Casting a power series as a Hahn series with coefficients from a `StrictOrderedSemiring`
  is an algebra homomorphism. -/
@[simps!]
def ofPowerSeriesAlg : PowerSeries A →ₐ[R] A⟦Γ⟧ :=
  (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (AlgEquiv.toAlgHom (toPowerSeriesAlg R).symm)

instance powerSeriesAlgebra {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)] :
    Algebra S R⟦Γ⟧ :=
  RingHom.toAlgebra <| (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))

variable {R}
variable {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)]

theorem algebraMap_apply' (x : S) :
    algebraMap S R⟦Γ⟧ x = ofPowerSeries Γ R (algebraMap S (PowerSeries R) x) :=
  rfl

@[simp]
theorem _root_.Polynomial.algebraMap_hahnSeries_apply (f : R[X]) :
    algebraMap R[X] R⟦Γ⟧ f = ofPowerSeries Γ R f :=
  rfl

theorem _root_.Polynomial.algebraMap_hahnSeries_injective :
    Function.Injective (algebraMap R[X] R⟦Γ⟧) :=
  ofPowerSeries_injective.comp (Polynomial.coe_injective R)

end Algebra

end HahnSeries
