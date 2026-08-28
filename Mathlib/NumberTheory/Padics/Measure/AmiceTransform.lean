/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.Padics.AddChar
public import Mathlib.NumberTheory.Padics.Measure.Group
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The Amice transform

We identify the measures on `ℤ_[p]` with the power series ring `ℤ_[p]⟦X⟧`, by sending a measure `μ`
to the power series with `n`-th coefficient `μ (mahler n)`.

More suggestively, this is the series `∫ a : ℤ_[p], (1 + X) ^ a dμ`.

## Main statements

* `AbstractMeasure.amiceTransform`: the Amice transform as an `R`-linear map into `R⟦X⟧`, allowing
  `R` to be any normed `ℤ_[p]`-algebra
* `AbstractMeasure.coeff_amiceTransform`: the `n`-th coefficient of `μ.amiceTransform` is
  `μ (mahler n)`
* `AbstractMeasure.amiceTransformEquiv`: the Amice transform with `ℤ_[p]`-coefficients, bundled
  as a linear equivalence.

## TODO

Define the Amice transform as an equivalence over more general base rings; this requires developing
some theory of _bounded_ power series over normed rings.

## References

* [P. Colmez, *Fonctions d'une variable p-adique*][colmez2010], section II.2

-/

public noncomputable section

open scoped AbstractMeasure PowerSeries

open Submodule

variable {p : ℕ} [Fact p.Prime]

section Preliminaries

variable {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
  [IsBoundedSMul ℤ_[p] R]

/-- Reformulation of `PadicInt.ext_mahler` in terms of the type synonym `D(ℤ_[p], R)`. -/
lemma AbstractMeasure.ext_mahler {μ : D(ℤ_[p], R)}
    (hμ : ∀ n, μ ((mahler n : C(ℤ_[p], ℤ_[p])) • 1) = 0) : μ = 0 := by
  obtain ⟨b, rfl⟩ := toCLMEquiv.symm.surjective μ
  simpa using PadicInt.ext_mahler (by simpa using hμ)

end Preliminaries

namespace AbstractMeasure

section Definitions

variable {R : Type*} [CommRing R] [TopologicalSpace R]
  [Algebra ℤ_[p] R] [ContinuousSMul ℤ_[p] R] [IsTopologicalRing R]

/--
The Amice transform, sending a measure `μ` on `ℤ_[p]` to the power series with `n`-th
coefficient `μ (mahler n)`. More suggestively, this is the series `∫ a : ℤ_[p], (1 + X) ^ a dμ`.

See also `amiceTransformEquiv` for the same map bundled as a linear equivalence.
-/
def amiceTransform : D(ℤ_[p], R) →ₗ[R] R⟦X⟧ where
  toFun μ := .mk fun n ↦ μ ((mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R)))
  map_add' μ ν := by ext; simp
  map_smul' r μ := by ext; simp

lemma coeff_amiceTransform (μ : D(ℤ_[p], R)) (n : ℕ) :
    μ.amiceTransform.coeff n = μ ((mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R))) := by
  simp [amiceTransform]

end Definitions

section Injectivity

variable {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
  [IsBoundedSMul ℤ_[p] R]

lemma injective_amiceTransform : Function.Injective (amiceTransform : D(ℤ_[p], R) → _) := by
  rw [injective_iff_map_eq_zero]
  intro μ hμ
  apply ext_mahler
  simp_all [PowerSeries.ext_iff, coeff_amiceTransform]

end Injectivity

section Inverse

private lemma invTransformSummable (F : ℤ_[p]⟦X⟧) (f : C(ℤ_[p], ℤ_[p])) :
    Summable fun i ↦ PadicInt.mahlerEquiv ℤ_[p] f i * F.coeff i := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero, ← Filter.cocompact_eq_cofinite]
  simp only [norm_mul, mul_comm _ ‖F.coeff _‖]
  apply bdd_le_mul_tendsto_zero'
  · filter_upwards with i
    simpa using PadicInt.norm_le_one _
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact ZeroAtInftyContinuousMap.zero_at_infty' _

private def invTransformₗ (F : ℤ_[p]⟦X⟧) : C(ℤ_[p], ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p] where
  toFun f := ∑' i, PadicInt.mahlerEquiv ℤ_[p] f i * F.coeff i
  map_add' f g := by
    simp only [map_add, ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, add_mul]
    rw [Summable.tsum_add] <;> apply invTransformSummable
  map_smul' r f := by
    simp only [map_smul, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
      RingHom.id_apply]
    simp_rw [← smul_eq_mul]
    rw [Summable.tsum_const_smul]
    exact invTransformSummable F f

/--
The inverse of the Amice transform, sending a power series `F` to the unique measure that sends
`mahler n` to the `n`-th coefficient of `F`.
-/
def invTransform (F : ℤ_[p]⟦X⟧) : D(ℤ_[p], ℤ_[p]) :=
  AbstractMeasure.toCLMEquiv.symm <| (invTransformₗ F).mkContinuous 1 <| by
    intro f
    apply IsUltrametricDist.norm_tsum_le_of_forall_le
    intro i
    grw [norm_mul, (F.coeff i).norm_le_one, mul_one, one_mul, ← ge_iff_le]
    calc ‖f‖ = ‖PadicInt.mahlerEquiv ℤ_[p] f‖ := by rw [← (PadicInt.mahlerEquiv ℤ_[p]).norm_map]
      _ = ‖(PadicInt.mahlerEquiv ℤ_[p] f).toBCF‖ := by
        rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      _ ≥ _ := BoundedContinuousFunction.norm_coe_le_norm ..

lemma invTransform_apply (F : ℤ_[p]⟦X⟧) (f : C(ℤ_[p], ℤ_[p])) :
    invTransform F f = ∑' i, PadicInt.mahlerEquiv ℤ_[p] f i * F.coeff i := by
  simp [invTransform, invTransformₗ]

lemma amiceTransform_invTransform (F : ℤ_[p]⟦X⟧) :
    amiceTransform (invTransform F) = F := by
  ext n
  have (i : ℕ) : (fwdDiff 1)^[i] (fun x : ℤ_[p] ↦ mahler n x) 0 = if i = n then 1 else 0 := by
    simp [← fwdDiff_iter_choose_zero n i, fwdDiff_iter_eq_sum_shift, mahler_natCast_eq]
  simp [coeff_amiceTransform, invTransform_apply, PadicInt.mahlerEquiv_apply, this]

/--
The Amice transform bundled as a linear equivalence (with coefficients in `ℤ_[p]`).

(TODO: Define this more generally -- this will need a definition for bounded power series over a
normed ring.)
-/
def amiceTransformEquiv : D(ℤ_[p], ℤ_[p]) ≃ₗ[ℤ_[p]] ℤ_[p]⟦X⟧ where
  __ := amiceTransform
  invFun := invTransform
  right_inv := amiceTransform_invTransform
  left_inv μ := by simp [← injective_amiceTransform.eq_iff, amiceTransform_invTransform]

@[simp] lemma amiceTransformEquiv_apply (μ : D(ℤ_[p], ℤ_[p])) :
    μ.amiceTransformEquiv = μ.amiceTransform :=
  (rfl)

lemma coeff_amiceTransformEquiv (μ : D(ℤ_[p], ℤ_[p])) (n : ℕ) :
    μ.amiceTransformEquiv.coeff n = μ (mahler n : C(ℤ_[p], ℤ_[p])) := by
  simp [coeff_amiceTransform]

end Inverse

section multiplicative

variable {R : Type*} [CommRing R] [TopologicalSpace R] [Algebra ℤ_[p] R] [ContinuousSMul ℤ_[p] R]

/-- A multiplicative version of the Mahler basis functions. -/
@[expose, simps -isSimp]
def mulMahler (n : ℕ) : C(Multiplicative ℤ_[p], R) where
  toFun x := mahler n (Multiplicative.toAdd x) • 1
  continuous_toFun := (mahler n).continuous.comp continuous_toAdd |>.smul continuous_const

lemma mulMahler_mul (n : ℕ) (x y : Multiplicative ℤ_[p]) :
    (mulMahler n (x * y) : R) = ∑ i ∈ .antidiagonal n, mulMahler i.1 x * mulMahler i.2 y := by
  simp only [mulMahler_apply, toAdd_mul, smul_one_mul, ← mul_smul,
    ← Finset.sum_smul]
  simp [mahler_apply, Ring.add_choose_eq n (Commute.all x.toAdd y.toAdd)]

private lemma mulMahler_mul' (n : ℕ) (x y : Multiplicative ℤ_[p]) :
    (mulMahler n (x * y) : R) = ∑ i ∈ .antidiagonal n, mulMahler i.2 x * mulMahler i.1 y := by
  rw [mulMahler_mul, ← Finset.Nat.sum_antidiagonal_swap]
  simp

variable [IsTopologicalRing R]

section MultiplicativeEquivs

@[simps]
private def ofAddFunEquiv : C(Multiplicative ℤ_[p], R) ≃L[R] C(ℤ_[p], R) where
  toFun f := f.comp ⟨_, continuous_ofAdd⟩
  invFun f := f.comp ⟨_, continuous_toAdd⟩
  map_add' f g := rfl
  map_smul' r g := rfl

private def ofAddDistEquiv : D(Multiplicative ℤ_[p], R) ≃ₗ[R] D(ℤ_[p], R) :=
  AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm

end MultiplicativeEquivs

private def amiceTransformₘ : D(Multiplicative ℤ_[p], R) →ₗ[R] PowerSeries R :=
  amiceTransform.comp ofAddDistEquiv.toLinearMap

private lemma coeff_amiceTransformₘ (μ : D(Multiplicative ℤ_[p], R)) (n : ℕ) :
    (amiceTransformₘ μ).coeff n = μ (mulMahler n) := by
  simp [amiceTransformₘ, coeff_amiceTransform, ofAddDistEquiv, mulMahler, ContinuousMap.comp,
    Function.comp_def]

private lemma amiceTransformₘ_mul (μ ν : D(Multiplicative ℤ_[p], R)) :
    amiceTransformₘ (μ * ν : AbstractMeasure (Multiplicative ℤ_[p]) R R) =
      amiceTransformₘ μ * amiceTransformₘ ν := by
  ext n -- check coefficient-wise
  simp_rw [mul_comm (amiceTransformₘ μ) (amiceTransformₘ ν), coeff_amiceTransformₘ,
    AbstractMeasure.mul_apply, PowerSeries.coeff_mul, coeff_amiceTransformₘ, ← smul_eq_mul,
    ← map_smul, ← map_sum]
  congr 1 with x -- peel away μ
  simp only [AbstractMeasure.convolveFunRight_apply, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [mul_comm (ν _), ← smul_eq_mul (α := R), ← map_smul, ← map_sum]
  congr 1 with y -- peel away ν
  simp [mulMahler_mul']

/--
The Amice transform `D(Multiplicative ℤ_[p], R) → R[X]`, as a homomorphism of `R`-algebras.
-/
def amiceTransformₐ : D(Multiplicative ℤ_[p], R) →ₐ[R] PowerSeries R :=
  { amiceTransformₘ with
    map_one' := by
      ext
      simp [coeff_amiceTransformₘ, mulMahler_apply, mahler_apply, Ring.choose_zero_ite]
    map_mul' := amiceTransformₘ_mul
    map_zero' := by simp
    commutes' r := by
      ext n
      simp [coeff_amiceTransformₘ, Algebra.algebraMap_eq_smul_one, PowerSeries.coeff_C,
        mulMahler_apply, mahler_apply, Ring.choose_zero_ite]  }

lemma coeff_amiceTransformₐ (μ : D(Multiplicative ℤ_[p], R)) (n : ℕ) :
    (amiceTransformₐ μ).coeff n = μ (mulMahler n) :=
  coeff_amiceTransformₘ ..

/--
The Amice transform `D(Multiplicative ℤ_[p], R) → R[X]`, as an isomorphism of `R`-algebras.
-/
def amiceTransformEquivₐ : D(Multiplicative ℤ_[p], ℤ_[p]) ≃ₐ[ℤ_[p]] PowerSeries ℤ_[p] :=
  { amiceTransformₐ with
    invFun := (ofAddDistEquiv.trans amiceTransformEquiv).invFun
    left_inv μ := by
      suffices amiceTransformₐ μ = amiceTransformEquiv (ofAddDistEquiv μ) by
        simpa [LinearEquiv.symm_apply_eq]
      ext
      simp only [coeff_amiceTransformₐ, ofAddDistEquiv, AbstractMeasure.coe_arrowCongrLeft,
        amiceTransformEquiv_apply, coeff_amiceTransform, smul_eq_mul, mul_one,
        AbstractMeasure.map_apply]
      congr 1 with x
      simp [mulMahler_apply]
    right_inv F := by
      suffices amiceTransformₐ (ofAddDistEquiv.symm (amiceTransformEquiv.symm F)) = F by simpa
      ext
      simp only [ofAddDistEquiv, AbstractMeasure.arrowCongrLeft_symm, Homeomorph.symm_symm,
        AbstractMeasure.coe_arrowCongrLeft, coeff_amiceTransformₐ, AbstractMeasure.map_apply]
      rw [show F = amiceTransformEquiv (amiceTransformEquiv.symm F) by simp]
      generalize amiceTransformEquiv.symm F = μ
      simp only [coeff_amiceTransformEquiv, LinearEquiv.symm_apply_apply]
      congr 1 with x
      simp [mulMahler_apply] }

end multiplicative

end AbstractMeasure

end
