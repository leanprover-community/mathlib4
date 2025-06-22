/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProductMeasure

open Complex MeasureTheory Measure ProbabilityTheory

open scoped ENNReal RealInnerProductSpace

variable {E F Ω : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace ℝ E]
  [InnerProductSpace ℝ F] [MeasurableSpace E] [mF : MeasurableSpace F]
  [OpensMeasurableSpace E] [OpensMeasurableSpace F]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E} {Y : Ω → F}
  (t : WithLp 2 (E × F))

lemma IndepFun.charFun_eq_mul (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) (h : IndepFun X Y μ) :
    charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm (X ω, Y ω)) t =
      charFun (μ.map X) (WithLp.equiv 2 (E × F) t).1 *
      charFun (μ.map Y) (WithLp.equiv 2 (E × F) t).2 := by
  change charFun (μ.map (_ ∘ _)) t = _
  rw [← AEMeasurable.map_map_of_aemeasurable, (indepFun_iff_map_prod_eq_prod_map_map mX mY).1 h]
  · simp_rw [charFun, WithLp.prod_inner_apply, ofReal_add, add_mul, exp_add]
    rw [integral_map]
    · simp only [Equiv.apply_symm_apply, WithLp.equiv_fst, WithLp.equiv_snd]
      rw [← integral_prod_mul]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  all_goals fun_prop

lemma omg [CompleteSpace E] [CompleteSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ ∀ t,
      charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm (X ω, Y ω)) t =
      charFun (μ.map X) (WithLp.equiv 2 (E × F) t).1 *
      charFun (μ.map Y) (WithLp.equiv 2 (E × F) t).2 where
  mp := fun h t ↦ test t mX mY h
  mpr h := by
    rw [indepFun_iff_map_prod_eq_prod_map_map mX mY]
    apply (MeasurableEquiv.toLp 2 (E × F)).map_measurableEquiv_injective
    apply Measure.ext_of_charFun
    ext t
    rw [MeasurableEquiv.coe_toLp, AEMeasurable.map_map_of_aemeasurable]
    · change charFun (μ.map (fun ω ↦ (WithLp.equiv 2 (E × F)).symm (X ω, Y ω))) t = _
      rw [h, oops]
    all_goals fun_prop

variable {ι Ω : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] {mE : ∀ i, MeasurableSpace (E i)}
  [∀ i, OpensMeasurableSpace (E i)]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Π i, Ω → (E i)}
  (t : PiLp 2 E)

lemma testbis (mX : ∀ i, AEMeasurable (X i) μ) (h : iIndepFun X μ) :
    charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm fun i ↦ X i ω) t =
    ∏ i, charFun (μ.map (X i)) (t i) := by
  change charFun (μ.map (_ ∘ _)) t = _
  rw [← AEMeasurable.map_map_of_aemeasurable, (iIndepFun_iff_map_fun_eq_pi_map mX).1 h]
  · simp_rw [charFun, PiLp.inner_apply, ofReal_sum, Finset.sum_mul, exp_sum]
    rw [integral_map]
    · simp only [WithLp.equiv_symm_pi_apply]
      rw [← integral_fintype_prod_eq_prod]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  all_goals fun_prop

lemma oopsbis {μ : (i : ι) → Measure (E i)} [∀ i, IsFiniteMeasure (μ i)]
    (t : PiLp 2 E) :
    charFun ((Measure.pi μ).map (WithLp.equiv 2 _).symm) t =
    ∏ i, charFun (μ i) (t i) := by
  simp_rw [charFun, PiLp.inner_apply]
  rw [integral_map]
  · simp only [WithLp.equiv_symm_pi_apply, ofReal_sum, Finset.sum_mul, exp_sum]
    rw [← integral_fintype_prod_eq_prod]
  · fun_prop
  · exact Measurable.aestronglyMeasurable <| by fun_prop

lemma omgbis [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)]
    (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ t,
      charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm fun i ↦ X i ω) t =
      ∏ i, charFun (μ.map (X i)) (t i) where
  mp := fun h t ↦ testbis t mX h
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_pi_map mX]
    apply (MeasurableEquiv.toLp 2 (Π i, E i)).map_measurableEquiv_injective
    apply Measure.ext_of_charFun
    ext t
    rw [MeasurableEquiv.coe_toLp, AEMeasurable.map_map_of_aemeasurable]
    · change charFun (μ.map (fun ω ↦ (WithLp.equiv 2 _).symm _)) t = _
      rw [h, oopsbis]
    all_goals fun_prop

/-- The characteristic function of a product measure is the product
of the characteristic functions. -/
lemma charFun_pi {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] (μ : (i : ι) → Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] (t : PiLp 2 E) :
    charFun ((Measure.pi μ).map (WithLp.equiv 2 (Π i, E i)).symm) t = ∏ i, charFun (μ i) (t i) := by

  change charFun (μ.map (_ ∘ _)) t = _
  rw [← AEMeasurable.map_map_of_aemeasurable, (indepFun_iff_map_prod_eq_prod_map_map mX mY).1 h]
  · simp_rw [charFun, WithLp.prod_inner_apply, ofReal_add, add_mul, exp_add]
    rw [integral_map]
    · simp only [Equiv.apply_symm_apply, WithLp.equiv_fst, WithLp.equiv_snd]
      rw [← integral_prod_mul (fun x ↦ exp (⟪x, t.1⟫ * I)) (fun x ↦ exp (⟪x, t.2⟫ * I))]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  all_goals fun_prop

  simp_rw [charFun, PiLp.inner_apply, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, PiLp,
    WithLp, integral_fintype_prod_eq_prod (f := fun i x ↦ Complex.exp (⟪x, t i⟫ * Complex.I))]
