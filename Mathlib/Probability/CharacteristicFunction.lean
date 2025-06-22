/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Analysis.Norm.Lp.MeasurableSpace
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProductMeasure

open Complex MeasureTheory Measure ProbabilityTheory

open scoped ENNReal RealInnerProductSpace

variable {E F Ω : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace ℝ E]
  [InnerProductSpace ℝ F] {mE : MeasurableSpace E} {mF : MeasurableSpace F}
  [OpensMeasurableSpace E] [OpensMeasurableSpace F]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E} {Y : Ω → F}
  (t : WithLp 2 (E × F))

lemma mdr (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) (h : IndepFun X Y μ) :
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

lemma test (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) (h : IndepFun X Y μ) :
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

lemma oops {μ : Measure E} {ν : Measure F} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (t : WithLp 2 (E × F)) :
    charFun ((μ.prod ν).map (WithLp.equiv 2 (E × F)).symm) t =
      charFun μ ((WithLp.equiv 2 (E × F)) t).1 *
      charFun ν ((WithLp.equiv 2 (E × F)) t).2 := by
  simp_rw [charFun, WithLp.prod_inner_apply]
  rw [integral_map]
  · simp only [Equiv.apply_symm_apply, WithLp.equiv_fst, WithLp.equiv_snd, ofReal_add, add_mul,
    exp_add, WithLp.equiv_symm_fst, WithLp.equiv_symm_snd]
    rw [← integral_prod_mul]
  · fun_prop
  · exact Measurable.aestronglyMeasurable <| by fun_prop

lemma merde {X Y : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
    {μ : Measure X} {ν : Measure X} (f : X ≃ᵐ Y) :
    μ = ν ↔ μ.map f = ν.map f where
  mp h := by rw [h]
  mpr h := by
    rw [← map_id (μ := μ), ← map_id (μ := ν), ← f.symm_comp_self, ← map_map, ← map_map, h]
    all_goals fun_prop

instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] (p : ℝ≥0∞) :
    SecondCountableTopology (WithLp p (X × Y)) :=
  inferInstanceAs <| SecondCountableTopology (X × Y)

instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [SecondCountableTopologyEither X Y] [BorelSpace X] [BorelSpace Y] (p : ℝ≥0∞) :
    BorelSpace (WithLp p (X × Y)) :=
  inferInstanceAs <| BorelSpace (X × Y)

lemma omg [CompleteSpace E] [CompleteSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ ∀ t,
      charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm (X ω, Y ω)) t =
      charFun (μ.map X) (WithLp.equiv 2 (E × F) t).1 *
      charFun (μ.map Y) (WithLp.equiv 2 (E × F) t).2 where
  mp := fun h t ↦ test t mX mY h
  mpr h := by
    rw [indepFun_iff_map_prod_eq_prod_map_map mX mY, merde (WithLp.measurableEquiv 2 (E × F))]
    apply Measure.ext_of_charFun
    ext t
    rw [WithLp.coe_measurableEquiv, AEMeasurable.map_map_of_aemeasurable]
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

instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {p : ℝ≥0∞} :
    TopologicalSpace (PiLp p X) := inferInstanceAs <| TopologicalSpace (Π i, X i)

instance {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, SecondCountableTopology (X i)] (p : ℝ≥0∞) :
    SecondCountableTopology (PiLp p X) :=
  inferInstanceAs <| SecondCountableTopology (Π i, X i)

instance {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, SecondCountableTopology (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, BorelSpace (X i)] (p : ℝ≥0∞) :
    BorelSpace (PiLp p X) :=
  inferInstanceAs <| BorelSpace (Π i, X i)

instance {ι : Type*} {X : ι → Type*} [∀ i, UniformSpace (X i)]
    [∀ i, CompleteSpace (X i)] (p : ℝ≥0∞) :
    CompleteSpace (PiLp p X) :=
  inferInstanceAs <| CompleteSpace (Π i, X i)

lemma omgbis [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)]
    (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ t,
      charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm fun i ↦ X i ω) t =
      ∏ i, charFun (μ.map (X i)) (t i) where
  mp := fun h t ↦ testbis t mX h
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_pi_map mX, merde (WithLp.measurableEquiv 2 (Π i, E i))]
    apply Measure.ext_of_charFun
    ext t
    rw [WithLp.coe_measurableEquiv, AEMeasurable.map_map_of_aemeasurable]
    · change charFun (μ.map (fun ω ↦ (WithLp.equiv 2 _).symm _)) t = _
      rw [h, oopsbis]
    all_goals fun_prop

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝒳 : ι → Type*}
    {m𝒳 : ∀ i, MeasurableSpace (𝒳 i)} (X : Π i, Ω → 𝒳 i)

lemma lol : iIndepFun X μ ↔ ∀ s : Finset ι, iIndepFun (s.restrict X) μ where
  mp h s := by
    apply iIndepFun.precomp Subtype.val_injective h -- exact does not work
  mpr h := by
    rw [iIndepFun_iff]
    intro s f hs
    have : ⋂ i ∈ s, f i = ⋂ i : s, f i := by ext; simp
    rw [← Finset.prod_coe_sort, this]
    refine (h s).meas_iInter fun i ↦ hs i i.2

lemma iIndepFun.congr_iff (Y : Π i, Ω → 𝒳 i) (h : ∀ i, X i =ᵐ[μ] Y i) :
    iIndepFun X μ ↔ iIndepFun Y μ :=
  ⟨fun h' ↦ h'.congr h, fun h' ↦ h'.congr (fun i ↦ (h i).symm)⟩

variable [IsProbabilityMeasure μ]

lemma iIndepFun_iff_map_fun_eq_infinitePi_map (mX : ∀ i, Measurable (X i)) :
    haveI _ i : IsProbabilityMeasure (μ.map (X i)) := isProbabilityMeasure_map (mX i).aemeasurable
    iIndepFun X μ ↔ μ.map (fun ω i ↦ X i ω) = (infinitePi (fun i ↦ μ.map (X i))) where
  mp h := by
    haveI _ i : IsProbabilityMeasure (μ.map (X i)) := isProbabilityMeasure_map (mX i).aemeasurable
    apply eq_infinitePi
    intro s t ht
    rw [lol] at h
    have : s.toSet.pi t = s.restrict ⁻¹' ((@Set.univ s ).pi fun i ↦ t i) := by ext; simp
    rw [this, ← map_apply, map_map]
    · have : s.restrict ∘ (fun ω i ↦ X i ω) = fun ω i ↦ s.restrict X i ω := by ext; simp
      rw [this, (iIndepFun_iff_map_fun_eq_pi_map ?_).1 (h s), pi_pi]
      · simp only [Finset.restrict]
        rw [s.prod_coe_sort fun i ↦ μ.map (X i) (t i)]
      exact fun i ↦ (mX i).aemeasurable
    any_goals fun_prop
    refine MeasurableSet.univ_pi fun i ↦ ht i i.2
  mpr h := by
    rw [lol]
    intro s
    rw [iIndepFun_iff_map_fun_eq_pi_map]
    · have : s.restrict ∘ (fun ω i ↦ X i ω) = fun ω i ↦ s.restrict X i ω := by ext; simp
      rw [← this, ← map_map, h, infinitePi_map_restrict]
      · simp
      all_goals fun_prop
    exact fun i ↦ (mX i).aemeasurable

lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀ [Countable ι] (mX : ∀ i, AEMeasurable (X i) μ) :
    haveI _ i := isProbabilityMeasure_map (mX i)
    iIndepFun X μ ↔ μ.map (fun ω i ↦ X i ω) = (infinitePi (fun i ↦ μ.map (X i))) := by
  rw [iIndepFun.congr_iff _ _ (fun i ↦ (mX i).ae_eq_mk), iIndepFun_iff_map_fun_eq_infinitePi_map]
  · have : (fun ω i ↦ (mX i).mk (X i) ω) =ᵐ[μ] fun ω i ↦ X i ω := by
      change ∀ᵐ ω ∂μ, (fun i ↦ (mX i).mk (X i) ω) = fun i ↦ X i ω
      simp_rw [funext_iff]
      rw [MeasureTheory.ae_all_iff]
      exact fun i ↦ (mX i).ae_eq_mk.symm
    rw [Measure.map_congr this]
    simp_rw [fun i ↦ Measure.map_congr (mX i).ae_eq_mk.symm]
  exact fun i ↦ (mX i).measurable_mk

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
