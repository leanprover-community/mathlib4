import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Independence.Integration

open MeasureTheory Measure ProbabilityTheory ENNReal
open scoped BoundedContinuousFunction

variable {Ω E F : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [TopologicalSpace E] [mE : MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
  [TopologicalSpace F] [mF : MeasurableSpace F] [BorelSpace F] [HasOuterApproxClosed F]
  {X : Ω → E} {Y : Ω → F}

lemma indepFun_of_boundedContinuousFunction [IsFiniteMeasure P]
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P)
    (h : ∀ (f : E →ᵇ ℝ) (g : F →ᵇ ℝ), P[(f ∘ X) * (g ∘ Y)] = P[f ∘ X] * P[g ∘ Y]) :
    X ⟂ᵢ[P] Y := by
  rw [indepFun_iff_map_prod_eq_prod_map_map mX mY]
  refine eq_prod_of_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map, integral_map, integral_map]
  · exact h f g
  any_goals fun_prop
  exact (f.continuous.aestronglyMeasurable.comp_measurable measurable_fst).mul
    (g.continuous.aestronglyMeasurable.comp_measurable measurable_snd)

lemma indepSet_comap_of_boundedContinuousFunction [IsProbabilityMeasure P]
    (mX : AEMeasurable X P) {A : Set Ω}
    (hA : MeasurableSet A) (h : ∀ f : E →ᵇ ℝ, ∫ ω in A, f (X ω) ∂P = P.real A * P[f ∘ X]) :
    IndepSets {A} {s | MeasurableSet[mE.comap X] s} P := by
  suffices (A.indicator (1 : Ω → ℝ)) ⟂ᵢ[P] X by
    rw [IndepSets_iff]
    rintro s - hs ⟨t, ht, rfl⟩
    rw [Set.mem_singleton_iff.1 hs]
    have hA' : A = A.indicator (1 : Ω → ℝ) ⁻¹' {1} := by ext; simp [Set.indicator]
    rw [hA']
    exact this.measure_inter_preimage_eq_mul _ _ (by simp) ht
  refine indepFun_of_boundedContinuousFunction
    ((measurable_indicator_const_iff 1).2 hA).aemeasurable mX fun f g ↦ ?_
  have h1 ω : f (A.indicator 1 ω) * g (X ω) = A.indicator (fun ω ↦ f 1 * g (X ω)) ω +
      f 0 * g (X ω) - A.indicator (fun ω ↦ f 0 * g (X ω)) ω := by
    classical
    rw [Set.indicator_apply]
    split_ifs <;> simp_all
  have h2 ω : f (A.indicator 1 ω) =
      A.indicator (fun _ ↦ f 1) ω + Aᶜ.indicator (fun _ ↦ f 0) ω := by
    classical
    rw [Set.indicator_apply]
    split_ifs <;> simp_all
  simp_rw [Pi.mul_apply, Function.comp_apply, h1, h2]
  rw [integral_sub, integral_add, integral_indicator hA, integral_indicator hA, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_add, integral_indicator hA,
    integral_indicator hA.compl, integral_const, integral_const, h]
  · simp [measureReal_compl hA]
    ring
  · exact (integrable_const _).indicator hA
  · exact (integrable_const _).indicator hA.compl
  · refine Integrable.of_bound ?_ (|f 1| * ‖g‖) (ae_of_all _ fun ω ↦ ?_)
    · exact AEStronglyMeasurable.indicator
        ((g.continuous.aestronglyMeasurable.comp_aemeasurable mX).const_mul _) hA
    · simp only [Set.indicator, Real.norm_eq_abs]
      split_ifs
      swap; · simp only [abs_zero]; positivity
      grw [abs_mul, g.abs_apply_le_norm]
  · refine Integrable.of_bound ?_ (|f 0| * ‖g‖) (ae_of_all _ fun ω ↦ ?_)
    · exact (g.continuous.aestronglyMeasurable.comp_aemeasurable mX).const_mul _
    · grw [Real.norm_eq_abs, abs_mul, g.abs_apply_le_norm]
  · apply Integrable.add
    · refine Integrable.of_bound ?_ (|f 1| * ‖g‖) (ae_of_all _ fun ω ↦ ?_)
      · exact AEStronglyMeasurable.indicator
          ((g.continuous.aestronglyMeasurable.comp_aemeasurable mX).const_mul _) hA
      · simp only [Set.indicator, Real.norm_eq_abs]
        split_ifs
        swap; · simp only [abs_zero]; positivity
        grw [abs_mul, g.abs_apply_le_norm]
    · refine Integrable.of_bound ?_ (|f 0| * ‖g‖) (ae_of_all _ fun ω ↦ ?_)
      · exact (g.continuous.aestronglyMeasurable.comp_aemeasurable mX).const_mul _
      · grw [Real.norm_eq_abs, abs_mul, g.abs_apply_le_norm]
  · refine Integrable.of_bound ?_ (|f 0| * ‖g‖) (ae_of_all _ fun ω ↦ ?_)
    · exact AEStronglyMeasurable.indicator
        ((g.continuous.aestronglyMeasurable.comp_aemeasurable mX).const_mul _) hA
    · simp only [Set.indicator, Real.norm_eq_abs]
      split_ifs
      swap; · simp only [abs_zero]; positivity
      grw [abs_mul, g.abs_apply_le_norm]
