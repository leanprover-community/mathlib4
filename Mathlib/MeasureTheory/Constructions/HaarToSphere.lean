import Mathlib.Algebra.Order.Pointwise
import Mathlib.Analysis.NormedSpace.SphereNormEquiv
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
-/

open Set Function Metric MeasurableSpace intervalIntegral
open scoped Pointwise ENNReal NNReal

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220
local notation "dim" => FiniteDimensional.finrank ℝ

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Measure


noncomputable def toSphere (μ : Measure E) : Measure (sphere (0 : E) 1) :=
  dim E • ((μ.comap (Subtype.val ∘ (homeomorphUnitSphereProd E).symm)).restrict
    (univ ×ˢ Iio ⟨1, mem_Ioi.2 one_pos⟩)).fst

variable (μ : Measure E)

theorem toSphere_apply_aux (s : Set (sphere (0 : E) 1)) (r : Ioi (0 : ℝ)) :
    μ ((↑) '' (homeomorphUnitSphereProd E ⁻¹' s ×ˢ Iio r)) = μ (Ioo (0 : ℝ) r • ((↑) '' s)) := by
  rw [← image2_smul, image2_image_right, ← Homeomorph.image_symm, image_image,
    ← image_subtype_val_Ioi_Iio, image2_image_left, image2_swap, ← image_prod]
  rfl

theorem toSphere_apply' {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    μ.toSphere s = dim E * μ (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  rw [toSphere, smul_apply, fst_apply hs, restrict_apply (measurable_fst hs),
    ((MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).comp
      (Homeomorph.measurableEmbedding _)).comap_apply,
    image_comp, Homeomorph.image_symm, univ_prod, ← Set.prod_eq, nsmul_eq_mul, toSphere_apply_aux]

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
        .ofReal (r.1 ^ (dim E - 1))) := by
  set ν : Measure (Ioi (0 : ℝ)) := ((volume : Measure ℝ).comap Subtype.val).withDensity fun r ↦
    .ofReal (r.1 ^ (dim E - 1))
  cases subsingleton_or_nontrivial E
  · have : IsEmpty (sphere (0 : E) 1) := sphere_isEmpty_of_subsingleton one_ne_zero
    exact .of_isEmpty ..
  have hpos : 0 < dim E := FiniteDimensional.finrank_pos
  have h₁ : 1 ≤ dim E := hpos
  have hν : ∀ r : Ioi (0 : ℝ), ν (Iio r) = ENNReal.ofReal (r.1 ^ dim E / dim E) := fun r ↦ by
    have hr₀ : 0 ≤ r.1 := le_of_lt r.2
    rw [withDensity_apply _ measurableSet_Iio,
      set_lintegral_subtype measurableSet_Ioi _ fun a : ℝ ↦ .ofReal (a ^ (dim E - 1)),
      image_subtype_val_Ioi_Iio, restrict_congr_set Ioo_ae_eq_Ioc,
      ← ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_pow _).1, ← integral_of_le hr₀]
    · simp [Nat.sub_add_cancel h₁, hpos.ne', hpos]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact pow_nonneg hx.1.le _
  refine ⟨(homeomorphUnitSphereProd E).measurable, .symm ?_⟩
  refine prod_eq_generateFrom generateFrom_measurableSet
    ((borel_eq_generateFrom_Iio _).symm.trans BorelSpace.measurable_eq.symm)
    isPiSystem_measurableSet isPiSystem_Iio μ.toSphere.toFiniteSpanningSetsIn ?_ fun s hs ↦
      forall_range_iff.2 fun r ↦ ?_
  · refine ⟨fun n ↦ Iio ⟨n + 1, mem_Ioi.2 n.cast_add_one_pos⟩, fun _ ↦ mem_range_self _,
      fun n ↦ ?_, ?_⟩
    · rw [hν]
      exact ENNReal.ofReal_lt_top
    · exact iUnion_eq_univ_iff.2 fun x ↦ ⟨⌊x.1⌋₊, Nat.lt_floor_add_one x.1⟩
  · rw [(Homeomorph.measurableEmbedding _).map_apply, hν, toSphere_apply' _ hs,
      comap_subtype_coe_apply (measurableSet_singleton _).compl, toSphere_apply_aux]
    calc
      μ (Ioo (0 : ℝ) r • (↑) '' s) = μ (r.1 • Ioo (0 : ℝ) 1 • (↑) '' s) := by
        rw [← smul_assoc, LinearOrderedField.smul_Ioo r.2.out, smul_zero, smul_eq_mul, mul_one]
      _ = _ := by
        rw [μ.addHaar_smul_of_nonneg r.2.out.le, mul_right_comm, ← ENNReal.ofReal_coe_nat,
          ← ENNReal.ofReal_mul, mul_div_cancel']
        exacts [(Nat.cast_pos.2 hpos).ne', Nat.cast_nonneg _]

end Measure

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma integral_fun_norm_addHaar (f : ℝ → F) :
    ∫ x, f (‖x‖) ∂μ = dim E • (μ (ball 0 1)).toReal • ∫ y in Ioi (0 : ℝ), y ^ (dim E - 1) • f y :=
  calc
    ∫ x, f (‖x‖) ∂μ = ∫ x : ({(0)}ᶜ : Set E), f (‖x.1‖) ∂(μ.comap (↑)) := by
      rw [← set_integral_eq_subtype' (measurableSet_singleton _).compl fun x ↦ f (‖x‖),
        restrict_compl_singleton]
    _ = ∫ x : sphere (0 : E) 1 × Ioi (0 : ℝ), f x.2 ∂_ :=
      μ.measurePreserving_homeomorphUnitSphereProd.integral_comp (Homeomorph.measurableEmbedding _)
        (f ∘ Subtype.val ∘ Prod.snd)
    _ = (μ.toSphere univ).toReal • ∫ x : Ioi (0 : ℝ), f x ∂_ := _
    _ = _ := _
  

end MeasureTheory
