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

We identify the measures on `ℤ_[p]` with the power series ring `ℤ_[p]⟦X⟧`.
-/

public noncomputable section

open scoped AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

section prelim

variable {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
  [IsBoundedSMul ℤ_[p] R] [IsTopologicalRing R]

theorem dense_span_mahler : Dense (Submodule.span R
      (Set.range fun n ↦ (mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R))) : Set C(ℤ_[p], R)) := by
  refine fun f ↦ mem_closure_of_tendsto (PadicInt.hasSum_mahler _) ?_
  refine .of_forall fun s ↦ Submodule.sum_mem _ fun c _ ↦ ?_
  simp only [Submodule.span_range_eq_iSup]
  apply Submodule.mem_iSup_of_mem (i := c)
  rw [Submodule.mem_span_singleton]
  use (fwdDiff 1)^[c] f 0
  ext x
  simp [PadicInt.mahlerTerm]

lemma ext_mahler (μ : D(ℤ_[p], R)) (hμ : ∀ n, μ ((mahler n : C(ℤ_[p], ℤ_[p])) • 1) = 0) :
    μ = 0 := by
  revert μ
  simp only [AbstractMeasure.toCLMEquiv.toEquiv.forall_congr_left, LinearEquiv.coe_symm_toEquiv,
    AbstractMeasure.coe_symm_toCLMEquiv, EmbeddingLike.map_eq_zero_iff]
  intro ψ hψ
  apply ContinuousLinearMap.ext_on dense_span_mahler
  rintro _ ⟨n, rfl⟩
  simp_all

end prelim


section defs

variable {R : Type*} [CommRing R] [TopologicalSpace R]
  [Algebra ℤ_[p] R] [ContinuousSMul ℤ_[p] R] [IsTopologicalRing R]

/--
The Amice transform, sending a measure `μ` on `ℤ_[p]` to the power series with `n`-th
coefficient `μ (mahler n)`. More suggestively, this is the series `∫ a : ℤ_[p], (1 + X) ^ a dμ`.
-/
def amiceTransform : D(ℤ_[p], R) →ₗ[R] PowerSeries R where
  toFun μ := .mk fun n ↦ μ ((mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R)))
  map_add' μ ν := by ext; simp
  map_smul' r μ := by ext; simp

lemma coeff_amiceTransform (μ : D(ℤ_[p], R)) (n : ℕ) :
    (amiceTransform μ).coeff n = μ ((mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R))) := by
  simp [amiceTransform]

end defs

section injectivity

variable {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
  [IsBoundedSMul ℤ_[p] R] [IsTopologicalRing R]

lemma injective_amiceTransform : Function.Injective (amiceTransform : D(ℤ_[p], R) → _) := by
  rw [injective_iff_map_eq_zero]
  intro μ hμ
  apply ext_mahler
  simp_all [PowerSeries.ext_iff, coeff_amiceTransform]

end injectivity

section inverse

private lemma invTransformSummable (F : PowerSeries ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) :
    Summable fun i ↦ PadicInt.mahlerEquiv ℤ_[p] f i * F.coeff i := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero, ← Filter.cocompact_eq_cofinite]
  simp only [norm_mul, mul_comm _ ‖F.coeff _‖]
  apply bdd_le_mul_tendsto_zero'
  · filter_upwards with i
    simpa using PadicInt.norm_le_one _
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact ZeroAtInftyContinuousMap.zero_at_infty' _

private def invTransformₗ (F : PowerSeries ℤ_[p]) : C(ℤ_[p], ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p] where
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
def invTransform (F : PowerSeries ℤ_[p]) : D(ℤ_[p], ℤ_[p]) :=
  AbstractMeasure.toCLMEquiv.symm <| (invTransformₗ F).mkContinuous 1 <| by
    intro f
    simp only [invTransformₗ, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    apply IsUltrametricDist.norm_tsum_le_of_forall_le
    intro i
    grw [norm_mul, (F.coeff i).norm_le_one, mul_one]
    have := (PadicInt.mahlerEquiv ℤ_[p]).norm_map f
    -- looks like `ZeroAtInftyContinuousMap.norm_coe_le_norm` is missing
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at this
    have := (BoundedContinuousFunction.norm_coe_le_norm _ (x := i)).trans_eq this
    rw [ZeroAtInftyContinuousMap.toBCF_apply] at this
    grw [this, ContinuousMap.norm_le]
    · exact ContinuousMap.norm_coe_le_norm _
    · positivity

lemma invTransform_apply (F : PowerSeries ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) :
    invTransform F f = ∑' i, PadicInt.mahlerEquiv ℤ_[p] f i * F.coeff i := by
  simp only [invTransform, AbstractMeasure.coe_symm_toCLMEquiv]
  rfl

lemma amiceTransform_invTransform (F : PowerSeries ℤ_[p]) :
    amiceTransform (invTransform F) = F := by
  ext n
  have (i : ℕ) : (fwdDiff 1)^[i] (fun x : ℤ_[p] ↦ mahler n x) 0 = if i = n then 1 else 0 := by
    convert fwdDiff_iter_choose_zero n i
    simp [fwdDiff_iter_eq_sum_shift, mahler_natCast_eq]
  simp [coeff_amiceTransform, invTransform_apply, PadicInt.mahlerEquiv_apply, this]

/--
The Amice transform bundled as a linear equivalence.
-/
def amiceTransformEquiv : D(ℤ_[p], ℤ_[p]) ≃ₗ[ℤ_[p]] PowerSeries ℤ_[p] where
  __ := amiceTransform
  invFun := invTransform
  right_inv := amiceTransform_invTransform
  left_inv μ := by simp [← injective_amiceTransform.eq_iff, amiceTransform_invTransform]

@[simp] lemma amiceTransformEquiv_apply (μ : D(ℤ_[p], ℤ_[p])) :
    amiceTransformEquiv μ = amiceTransform μ :=
  (rfl)

lemma coeff_amiceTransformEquiv (μ : D(ℤ_[p], ℤ_[p])) (n : ℕ) :
    (amiceTransformEquiv μ).coeff n = μ (mahler n : C(ℤ_[p], ℤ_[p])) := by
  simp [coeff_amiceTransform]

end inverse

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

end
