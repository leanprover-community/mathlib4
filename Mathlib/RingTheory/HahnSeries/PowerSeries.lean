/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Data.Finsupp.PWO

/-!
# Comparison between Hahn series and power series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`.  When `R` is a semiring and `Γ = ℕ`, then
we get the more familiar semiring of formal power series with coefficients in `R`.

## Main Definitions
* `toPowerSeries` the isomorphism from `HahnSeries ℕ R` to `PowerSeries R`.
* `ofPowerSeries` the inverse, casting a `PowerSeries R` to a `HahnSeries ℕ R`.

## Instances
* For `Finite σ`, the instance `NoZeroDivisors (HahnSeries (σ →₀ ℕ) R)`,
  deduced from the case of `MvPowerSeries`
  The case of `HahnSeries ℕ R` is taken care of by `instNoZeroDivisors`.

## TODO
* Build an API for the variable `X` (defined to be `single 1 1 : HahnSeries Γ R`) in analogy to
  `X : R[X]` and `X : PowerSeries R`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/


open Finset Function Pointwise Polynomial

noncomputable section

variable {Γ R : Type*}

namespace HahnSeries

section Semiring

variable [Semiring R]

/-- The ring `HahnSeries ℕ R` is isomorphic to `PowerSeries R`. -/
@[simps]
def toPowerSeries : HahnSeries ℕ R ≃+* PowerSeries R where
  toFun f := PowerSeries.mk f.coeff
  invFun f := ⟨fun n => PowerSeries.coeff R n f, .of_linearOrder _⟩
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
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, coeff_mul, isPWO_support]
    classical
    refine (sum_filter_ne_zero _).symm.trans <| (sum_congr ?_ fun _ _ ↦ rfl).trans <|
      sum_filter_ne_zero _
    ext m
    simp only [mem_antidiagonal, mem_addAntidiagonal, and_congr_left_iff, mem_filter,
      mem_support]
    rintro h
    rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]

theorem coeff_toPowerSeries {f : HahnSeries ℕ R} {n : ℕ} :
    PowerSeries.coeff R n (toPowerSeries f) = f.coeff n :=
  PowerSeries.coeff_mk _ _

theorem coeff_toPowerSeries_symm {f : PowerSeries R} {n : ℕ} :
    (HahnSeries.toPowerSeries.symm f).coeff n = PowerSeries.coeff R n f :=
  rfl

variable (Γ R) [Semiring Γ] [PartialOrder Γ] [IsStrictOrderedRing Γ]

/-- Casts a power series as a Hahn series with coefficients from a `StrictOrderedSemiring`. -/
def ofPowerSeries : PowerSeries R →+* HahnSeries Γ R :=
  (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (RingEquiv.toRingHom toPowerSeries.symm)

variable {Γ} {R}

theorem ofPowerSeries_injective : Function.Injective (ofPowerSeries Γ R) :=
  embDomain_injective.comp toPowerSeries.symm.injective

/-@[simp] Porting note: removing simp. RHS is more complicated and it makes linter
failures elsewhere -/
theorem ofPowerSeries_apply (x : PowerSeries R) :
    ofPowerSeries Γ R x =
      HahnSeries.embDomain
        ⟨⟨((↑) : ℕ → Γ), Nat.strictMono_cast.injective⟩, by
          simp only [Function.Embedding.coeFn_mk]
          exact Nat.cast_le⟩
        (toPowerSeries.symm x) :=
  rfl

theorem ofPowerSeries_apply_coeff (x : PowerSeries R) (n : ℕ) :
    (ofPowerSeries Γ R x).coeff n = PowerSeries.coeff R n x := by simp [ofPowerSeries_apply]

@[simp]
theorem ofPowerSeries_C (r : R) : ofPowerSeries Γ R (PowerSeries.C R r) = HahnSeries.C r := by
  ext n
  simp only [ofPowerSeries_apply, C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq,
    coeff_single]
  split_ifs with hn
  · subst hn
    convert embDomain_coeff (a := 0) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_C]
    intro
    simp +contextual [Ne.symm hn]

@[simp]
theorem ofPowerSeries_X : ofPowerSeries Γ R PowerSeries.X = single 1 1 := by
  ext n
  simp only [coeff_single, ofPowerSeries_apply, RingHom.coe_mk]
  split_ifs with hn
  · rw [hn]
    convert embDomain_coeff (a := 1) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_X]
    intro
    simp +contextual [Ne.symm hn]

theorem ofPowerSeries_X_pow {R} [Semiring R] (n : ℕ) :
    ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1 := by
  simp

-- Lemmas about converting hahn_series over fintype to and from mv_power_series
/-- The ring `HahnSeries (σ →₀ ℕ) R` is isomorphic to `MvPowerSeries σ R` for a `Finite` `σ`.
We take the index set of the hahn series to be `Finsupp` rather than `pi`,
even though we assume `Finite σ` as this is more natural for alignment with `MvPowerSeries`.
After importing `Mathlib/Algebra/Order/Pi.lean` the ring `HahnSeries (σ → ℕ) R` could be constructed
instead.
-/
@[simps]
def toMvPowerSeries {σ : Type*} [Finite σ] : HahnSeries (σ →₀ ℕ) R ≃+* MvPowerSeries σ R where
  toFun f := f.coeff
  invFun f := ⟨(f : (σ →₀ ℕ) → R), Finsupp.isPWO _⟩
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
then `HahnSeries (σ →₀ ℕ) R` has no zero divisors -/
instance [NoZeroDivisors R] : NoZeroDivisors (HahnSeries (σ →₀ ℕ) R) :=
  toMvPowerSeries.toMulEquiv.noZeroDivisors (A := HahnSeries (σ →₀ ℕ) R) (MvPowerSeries σ R)

theorem coeff_toMvPowerSeries {f : HahnSeries (σ →₀ ℕ) R} {n : σ →₀ ℕ} :
    MvPowerSeries.coeff R n (toMvPowerSeries f) = f.coeff n :=
  rfl

theorem coeff_toMvPowerSeries_symm {f : MvPowerSeries σ R} {n : σ →₀ ℕ} :
    (HahnSeries.toMvPowerSeries.symm f).coeff n = MvPowerSeries.coeff R n f :=
  rfl

end Semiring

section Algebra

variable (R) [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

/-- The `R`-algebra `HahnSeries ℕ A` is isomorphic to `PowerSeries A`. -/
@[simps!]
def toPowerSeriesAlg : HahnSeries ℕ A ≃ₐ[R] PowerSeries A :=
  { toPowerSeries with
    commutes' := fun r => by
      ext n
      cases n <;> simp [algebraMap_apply, PowerSeries.algebraMap_apply] }

variable (Γ) [Semiring Γ] [PartialOrder Γ] [IsStrictOrderedRing Γ]

/-- Casting a power series as a Hahn series with coefficients from a `StrictOrderedSemiring`
  is an algebra homomorphism. -/
@[simps!]
def ofPowerSeriesAlg : PowerSeries A →ₐ[R] HahnSeries Γ A :=
  (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (AlgEquiv.toAlgHom (toPowerSeriesAlg R).symm)

instance powerSeriesAlgebra {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)] :
    Algebra S (HahnSeries Γ R) :=
  RingHom.toAlgebra <| (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))

variable {R}
variable {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)]

theorem algebraMap_apply' (x : S) :
    algebraMap S (HahnSeries Γ R) x = ofPowerSeries Γ R (algebraMap S (PowerSeries R) x) :=
  rfl

@[simp]
theorem _root_.Polynomial.algebraMap_hahnSeries_apply (f : R[X]) :
    algebraMap R[X] (HahnSeries Γ R) f = ofPowerSeries Γ R f :=
  rfl

theorem _root_.Polynomial.algebraMap_hahnSeries_injective :
    Function.Injective (algebraMap R[X] (HahnSeries Γ R)) :=
  ofPowerSeries_injective.comp (Polynomial.coe_injective R)

end Algebra

end HahnSeries
