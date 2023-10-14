import Mathlib.Analysis.NormedSpace.SphereNormEquiv
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
-/

open Set Function Metric MeasurableSpace
open scoped Pointwise ENNReal NNReal

local notation "dim" => FiniteDimensional.finrank ℝ

namespace MeasureTheory

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def toSphere (μ : Measure E) : Measure (sphere (0 : E) 1) :=
  dim E • ((μ.comap (Subtype.val ∘ (homeomorphUnitSphereProd E).symm)).restrict
    (univ ×ˢ Iio ⟨1, mem_Ioi.2 one_pos⟩)).fst

variable (μ : Measure E)

theorem toSphere_apply' {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    μ.toSphere s = dim E * μ (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  rw [toSphere, smul_apply, fst_apply hs, restrict_apply (measurable_fst hs),
    univ_prod, ← Set.prod_eq, ← image2_smul, image2_image_right, nsmul_eq_mul,
    comap_apply _ (Subtype.val_injective.comp (homeomorphUnitSphereProd E).symm.injective)]
  · simp only [(· ∘ ·), homeomorphUnitSphereProd_symm_apply_coe]
    congr 2
    rw [image_prod fun (x : sphere (0 : E) 1) (y : Ioi (0 : ℝ)) ↦ y.1 • x.1,
      ← image2_image_right fun (x : sphere (0 : E) 1) (y : ℝ) ↦ y • x.1, image2_swap,
      image_subtype_val_Ioi_Iio]; rfl
  · intro t ht
    rw [image_comp, Homeomorph.image_symm]
    exact .subtype_image (measurableSet_singleton _).compl (Homeomorph.measurable _ ht)
  · exact hs.prod measurableSet_Iio

theorem toSphere_apply_univ' : μ.toSphere univ = dim E * μ (ball 0 1 \ {0}) := by
  rw [μ.toSphere_apply' .univ, image_univ, Subtype.range_coe, Ioo_smul_sphere_zero] <;> simp

theorem toSphere_apply_univ [μ.IsAddHaarMeasure] [Nontrivial E] :
    μ.toSphere univ = dim E * μ (ball 0 1) := by
  rw [toSphere_apply_univ', measure_diff_null (measure_singleton _)]

variable [μ.IsAddHaarMeasure]

instance : IsFiniteMeasure μ.toSphere where
  measure_univ_lt_top := by
    rw [toSphere_apply_univ']
    exact ENNReal.mul_lt_top (ENNReal.nat_ne_top _) <|
      ne_top_of_le_ne_top measure_ball_lt_top.ne <| measure_mono (diff_subset _ _)

theorem measurePreserving_homeomorphUnitSphereProd :
    MeasurePreserving (homeomorphUnitSphereProd E) (μ.comap (↑))
      (.prod μ.toSphere <| .withDensity (.comap Subtype.val volume) fun r ↦
        .some (⟨r.1, r.2.out.le⟩ ^ (dim E - 1))) := by
  set ν : Measure (Ioi (0 : ℝ)) := ((volume : Measure ℝ).comap Subtype.val).withDensity fun r ↦
    .some (⟨r.1, r.2.out.le⟩ ^ (dim E - 1))
  cases subsingleton_or_nontrivial E
  · have : IsEmpty (sphere (0 : E) 1) := sphere_isEmpty_of_subsingleton one_ne_zero
    exact .of_isEmpty ..
  have : ∀ r : Ioi (0 : ℝ), ν (Iio r) = .some (⟨r.1, r.2.out.le⟩ ^ dim E / dim E) := fun r ↦ by
    rw [withDensity_apply _ measurableSet_Iio, lintegral_coe_eq_integral,
      ← preimage_subtype_val_Iio, restrict_comap_preimage]
    
    refine ⟨(homeomorphUnitSphereProd E).measurable, .symm ?_⟩
  refine prod_eq_generateFrom generateFrom_measurableSet
    ((borel_eq_generateFrom_Iio _).symm.trans BorelSpace.measurable_eq.symm)
    isPiSystem_measurableSet isPiSystem_Iio μ.toSphere.toFiniteSpanningSetsIn ?_ fun s hs ↦
      forall_range_iff.2 fun r ↦ ?_
  

end Measure

end MeasureTheory
