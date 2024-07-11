/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Finsupp.PWO
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.PowerSeries.Basic

#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Comparison between Hahn series and power series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`.  When `R` is a semiring and `Γ = ℕ`, then
we get the more familiar semiring of formal power series with coefficients in `R`.

## Main Definitions
  * `toPowerSeries` the isomorphism from `HahnSeries ℕ R` to `PowerSeries R`.
  * `ofPowerSeries` the inverse, casting a `PowerSeries R` to a `HahnSeries ℕ R`.

## TODO
  * Build an API for the variable `X` (defined to be `single 1 1 : HahnSeries Γ R`) in analogy to
    `X : R[X]` and `X : PowerSeries R`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

set_option linter.uppercaseLean3 false

open Finset Function

open scoped Classical
open Pointwise Polynomial

noncomputable section

variable {Γ : Type*} {R : Type*}

namespace HahnSeries

section Semiring

variable [Semiring R]

/-- The ring `HahnSeries ℕ R` is isomorphic to `PowerSeries R`. -/
@[simps]
def toPowerSeries : HahnSeries ℕ R ≃+* PowerSeries R where
  toFun f := PowerSeries.mk f.coeff
  invFun f := ⟨fun n => PowerSeries.coeff R n f, (Nat.lt_wfRel.wf.isWF _).isPWO⟩
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
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, mul_coeff, isPWO_support]
    classical
    refine (sum_filter_ne_zero _).symm.trans <| (sum_congr ?_ fun _ _ ↦ rfl).trans <|
      sum_filter_ne_zero _
    ext m
    simp only [mem_antidiagonal, mem_addAntidiagonal, and_congr_left_iff, mem_filter,
      mem_support]
    rintro h
    rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]
#align hahn_series.to_power_series HahnSeries.toPowerSeries

theorem coeff_toPowerSeries {f : HahnSeries ℕ R} {n : ℕ} :
    PowerSeries.coeff R n (toPowerSeries f) = f.coeff n :=
  PowerSeries.coeff_mk _ _
#align hahn_series.coeff_to_power_series HahnSeries.coeff_toPowerSeries

theorem coeff_toPowerSeries_symm {f : PowerSeries R} {n : ℕ} :
    (HahnSeries.toPowerSeries.symm f).coeff n = PowerSeries.coeff R n f :=
  rfl
#align hahn_series.coeff_to_power_series_symm HahnSeries.coeff_toPowerSeries_symm

variable (Γ R) [StrictOrderedSemiring Γ]

/-- Casts a power series as a Hahn series with coefficients from a `StrictOrderedSemiring`. -/
def ofPowerSeries : PowerSeries R →+* HahnSeries Γ R :=
  (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (RingEquiv.toRingHom toPowerSeries.symm)
#align hahn_series.of_power_series HahnSeries.ofPowerSeries

variable {Γ} {R}

theorem ofPowerSeries_injective : Function.Injective (ofPowerSeries Γ R) :=
  embDomain_injective.comp toPowerSeries.symm.injective
#align hahn_series.of_power_series_injective HahnSeries.ofPowerSeries_injective

/-@[simp] Porting note: removing simp. RHS is more complicated and it makes linter
failures elsewhere-/
theorem ofPowerSeries_apply (x : PowerSeries R) :
    ofPowerSeries Γ R x =
      HahnSeries.embDomain
        ⟨⟨((↑) : ℕ → Γ), Nat.strictMono_cast.injective⟩, by
          simp only [Function.Embedding.coeFn_mk]
          exact Nat.cast_le⟩
        (toPowerSeries.symm x) :=
  rfl
#align hahn_series.of_power_series_apply HahnSeries.ofPowerSeries_apply

theorem ofPowerSeries_apply_coeff (x : PowerSeries R) (n : ℕ) :
    (ofPowerSeries Γ R x).coeff n = PowerSeries.coeff R n x := by simp [ofPowerSeries_apply]
#align hahn_series.of_power_series_apply_coeff HahnSeries.ofPowerSeries_apply_coeff

@[simp]
theorem ofPowerSeries_C (r : R) : ofPowerSeries Γ R (PowerSeries.C R r) = HahnSeries.C r := by
  ext n
  simp only [ofPowerSeries_apply, C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq,
    single_coeff]
  split_ifs with hn
  · subst hn
    convert @embDomain_coeff ℕ R _ _ Γ _ _ _ 0 <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_C]
    intro
    simp (config := { contextual := true }) [Ne.symm hn]
#align hahn_series.of_power_series_C HahnSeries.ofPowerSeries_C

@[simp]
theorem ofPowerSeries_X : ofPowerSeries Γ R PowerSeries.X = single 1 1 := by
  ext n
  simp only [single_coeff, ofPowerSeries_apply, RingHom.coe_mk]
  split_ifs with hn
  · rw [hn]
    convert @embDomain_coeff ℕ R _ _ Γ _ _ _ 1 <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_X]
    intro
    simp (config := { contextual := true }) [Ne.symm hn]
#align hahn_series.of_power_series_X HahnSeries.ofPowerSeries_X

theorem ofPowerSeries_X_pow {R} [Semiring R] (n : ℕ) :
    ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1 := by
  simp
#align hahn_series.of_power_series_X_pow HahnSeries.ofPowerSeries_X_pow

-- Lemmas about converting hahn_series over fintype to and from mv_power_series
/-- The ring `HahnSeries (σ →₀ ℕ) R` is isomorphic to `MvPowerSeries σ R` for a `Finite` `σ`.
We take the index set of the hahn series to be `Finsupp` rather than `pi`,
even though we assume `Finite σ` as this is more natural for alignment with `MvPowerSeries`.
After importing `Algebra.Order.Pi` the ring `HahnSeries (σ → ℕ) R` could be constructed instead.
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
    simp only [MvPowerSeries.coeff_mul]
    classical
      change (f * g).coeff n = _
      simp_rw [mul_coeff]
      refine (sum_filter_ne_zero _).symm.trans <| (sum_congr ?_ fun _ _ ↦ rfl).trans <|
        sum_filter_ne_zero _
      ext m
      simp only [and_congr_left_iff, mem_addAntidiagonal, mem_filter, mem_support,
        Finset.mem_antidiagonal]
      rintro h
      rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]
#align hahn_series.to_mv_power_series HahnSeries.toMvPowerSeries

variable {σ : Type*} [Finite σ]

theorem coeff_toMvPowerSeries {f : HahnSeries (σ →₀ ℕ) R} {n : σ →₀ ℕ} :
    MvPowerSeries.coeff R n (toMvPowerSeries f) = f.coeff n :=
  rfl
#align hahn_series.coeff_to_mv_power_series HahnSeries.coeff_toMvPowerSeries

theorem coeff_toMvPowerSeries_symm {f : MvPowerSeries σ R} {n : σ →₀ ℕ} :
    (HahnSeries.toMvPowerSeries.symm f).coeff n = MvPowerSeries.coeff R n f :=
  rfl
#align hahn_series.coeff_to_mv_power_series_symm HahnSeries.coeff_toMvPowerSeries_symm

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
#align hahn_series.to_power_series_alg HahnSeries.toPowerSeriesAlg

variable (Γ) [StrictOrderedSemiring Γ]

/-- Casting a power series as a Hahn series with coefficients from a `StrictOrderedSemiring`
  is an algebra homomorphism. -/
@[simps!]
def ofPowerSeriesAlg : PowerSeries A →ₐ[R] HahnSeries Γ A :=
  (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (AlgEquiv.toAlgHom (toPowerSeriesAlg R).symm)
#align hahn_series.of_power_series_alg HahnSeries.ofPowerSeriesAlg

instance powerSeriesAlgebra {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)] :
    Algebra S (HahnSeries Γ R) :=
  RingHom.toAlgebra <| (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))
#align hahn_series.power_series_algebra HahnSeries.powerSeriesAlgebra

variable {R}
variable {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)]

theorem algebraMap_apply' (x : S) :
    algebraMap S (HahnSeries Γ R) x = ofPowerSeries Γ R (algebraMap S (PowerSeries R) x) :=
  rfl
#align hahn_series.algebra_map_apply' HahnSeries.algebraMap_apply'

@[simp]
theorem _root_.Polynomial.algebraMap_hahnSeries_apply (f : R[X]) :
    algebraMap R[X] (HahnSeries Γ R) f = ofPowerSeries Γ R f :=
  rfl
#align polynomial.algebra_map_hahn_series_apply Polynomial.algebraMap_hahnSeries_apply

theorem _root_.Polynomial.algebraMap_hahnSeries_injective :
    Function.Injective (algebraMap R[X] (HahnSeries Γ R)) :=
  ofPowerSeries_injective.comp (Polynomial.coe_injective R)
#align polynomial.algebra_map_hahn_series_injective Polynomial.algebraMap_hahnSeries_injective

end Algebra

section meval

variable [LinearOrderedCancelAddCommMonoid Γ]

/-- Monomial evaluation of a power series by substitution of `X` into a Hahn series single of
strictly positive order. -/
def meval [CommSemiring R] {g : Γ} (hg : 0 < g) (r : R) : PowerSeries R →+* HahnSeries Γ R :=
  ((embDomainRingHom (multiplesHom Γ g) (StrictMono.injective (nsmul_left_strictMono hg))
      (fun _ _ => StrictMono.le_iff_le (nsmul_left_strictMono hg))).comp
      (toPowerSeries (R := R)).symm).comp (PowerSeries.rescale r)

--delete
theorem meval_add [CommSemiring R] {g : Γ} (hg : 0 < g) (r : R) (a b : PowerSeries R) :
    meval hg r (a + b) = meval hg r a + meval hg r b :=
  RingHom.map_add (meval hg r) a b

--delete
theorem meval_sub [CommRing R] {g : Γ} (hg : 0 < g) (r : R) (a b : PowerSeries R) :
    meval hg r (a - b) = meval hg r a - meval hg r b :=
  RingHom.map_sub (meval hg r) a b

--delete
theorem meval_pow [CommSemiring R] {g : Γ} (hg : 0 < g) (r : R) (a : PowerSeries R) (n : ℕ) :
    meval hg r (a ^ n) = (meval hg r a) ^ n :=
  RingHom.map_pow (meval hg r) a n

theorem meval_X [CommSemiring R] {g : Γ} (hg : 0 < g) (r : R) :
    meval hg r PowerSeries.X = single g r := by
  let f : ℕ ↪o Γ := ⟨⟨multiplesHom Γ g, StrictMono.injective (nsmul_left_strictMono hg)⟩,
      (StrictMono.le_iff_le (nsmul_left_strictMono hg))⟩
  have hemb : single g r = embDomain f (single 1 r) := by
    rw [show g = (f 1) by simp [f, multiplesHom]]
    exact (embDomain_single (f := f) (g := (1 : ℕ)) (r := r)).symm
  rw [hemb, meval, RingHom.comp_assoc]
  simp only [RingHom.coe_comp, RingHom.coe_coe, comp_apply, embDomainRingHom_apply]
  congr 1
  ext n
  by_cases hn : n = 1
  · rw [hn, toPowerSeries_symm_apply_coeff, PowerSeries.coeff_rescale, PowerSeries.coeff_one_X,
      single_coeff_same, pow_one, mul_one]
  · rw [toPowerSeries_symm_apply_coeff, PowerSeries.coeff_rescale, PowerSeries.coeff_X,
      single_coeff_of_ne hn]
    simp_all only [ite_false, mul_zero]

theorem meval_X_npow [CommSemiring R] {g : Γ} (hg : 0 < g) (r : R) (n : ℕ) :
    meval hg r (PowerSeries.X ^ n) = single (n • g) (r ^ n) := by
  rw [RingHom.map_pow (meval hg r) _ n, meval_X, single_pow g n r]

theorem meval_C [CommSemiring R] {g : Γ} (hg : 0 < g) (r s : R) :
    meval hg r (PowerSeries.C R s) = C s := by
  let f : ℕ ↪o Γ := ⟨⟨multiplesHom Γ g, StrictMono.injective (nsmul_left_strictMono hg)⟩,
      (StrictMono.le_iff_le (nsmul_left_strictMono hg))⟩
  have hemb : single 0 s = embDomain f (single 0 s) := by
    rw [show 0 = f 0 by simp [f]]
    exact (embDomain_single (f := f) (g := (0 : ℕ)) (r := s)).symm
  rw [C_apply, hemb, meval]
  simp only [RingHom.coe_comp, RingHom.coe_coe, comp_apply, embDomainRingHom_apply]
  congr 1
  ext n
  by_cases hn : n = 0
  · rw [hn, toPowerSeries_symm_apply_coeff, PowerSeries.coeff_rescale, single_coeff_same,
      PowerSeries.coeff_zero_C, pow_zero, one_mul]
  · rw [toPowerSeries_symm_apply_coeff, PowerSeries.coeff_rescale, PowerSeries.coeff_ne_zero_C hn,
      single_coeff_of_ne hn, mul_zero]

theorem meval_apply_coeff [CommSemiring R] {g : Γ} (hg : 0 < g) (r : R) (a : PowerSeries R)
    (n : ℕ) : (meval hg r a).coeff (n • g) = r ^ n * PowerSeries.coeff R n a := by
  let f : ℕ ↪o Γ := ⟨⟨multiplesHom Γ g, StrictMono.injective (nsmul_left_strictMono hg)⟩,
      (StrictMono.le_iff_le (nsmul_left_strictMono hg))⟩
  rw [meval, RingHom.comp_apply, RingHom.comp_apply, embDomainRingHom_apply,
    show n • g = f n by rfl, embDomain_coeff]
  simp

theorem meval_notin_range [CommSemiring R] {g g' : Γ} (hg : 0 < g) (r : R) (a : PowerSeries R)
    (hg' : g' ∉ Set.range (multiplesHom Γ g)) : (meval hg r a).coeff g' = 0 := by
  rw [meval, RingHom.comp_apply, RingHom.comp_apply, embDomainRingHom_apply]
  exact embDomain_notin_range hg'

end meval
