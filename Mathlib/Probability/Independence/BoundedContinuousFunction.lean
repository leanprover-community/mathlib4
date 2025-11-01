import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process

open MeasureTheory Measure ProbabilityTheory ENNReal
open scoped BoundedContinuousFunction

variable {Ω S T : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

lemma IndepFun.indepSets_of_indicator {𝓧 : Type*} [mX : MeasurableSpace 𝓧] {A : Set Ω} {X : Ω → 𝓧}
    (h : (A.indicator (1 : Ω → ℝ)) ⟂ᵢ[P] X) :
    IndepSets {A} {s | MeasurableSet[mX.comap X] s} P := by
  rw [IndepSets_iff]
  rintro s - hs ⟨t, ht, rfl⟩
  rw [Set.mem_singleton_iff.1 hs]
  have hA' : A = A.indicator (1 : Ω → ℝ) ⁻¹' {1} := by ext; simp [Set.indicator]
  rw [hA']
  exact h.measure_inter_preimage_eq_mul _ _ (by simp) ht

section Process

variable {E : S → Type*} {F : T → Type*} {G H : Type*}
  [∀ s, TopologicalSpace (E s)] [∀ s, MeasurableSpace (E s)] [∀ s, BorelSpace (E s)]
  [∀ s, HasOuterApproxClosed (E s)]
  [∀ t, TopologicalSpace (F t)] [∀ t, MeasurableSpace (F t)] [∀ t, BorelSpace (F t)]
  [∀ t, HasOuterApproxClosed (F t)]
  [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [HasOuterApproxClosed G]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [HasOuterApproxClosed H]
  {X : (s : S) → Ω → E s} {Y : (t : T) → Ω → F t} {Z : Ω → G} {U : Ω → H}

section Fintype

variable [Fintype S] [Fintype T]

lemma pi_indepFun_pi_of_bcf [IsFiniteMeasure P] (mX : ∀ s, AEMeasurable (X s) P)
    (mY : ∀ t, AEMeasurable (Y t) P)
    (h : ∀ (f : (s : S) → E s →ᵇ ℝ) (g : (t : T) → F t →ᵇ ℝ),
      P[(∏ s, f s ∘ (X s)) * (∏ t, g t ∘ (Y t))] = P[∏ s, f s ∘ (X s)] * P[∏ t, g t ∘ (Y t)]) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (aemeasurable_pi_lambda _ mX)
    (aemeasurable_pi_lambda _ mY)]
  refine eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map, integral_map, integral_map]
  · convert h f g <;> simp
  any_goals fun_prop
  all_goals exact Measurable.aestronglyMeasurable (by fun_prop)

lemma indepFun_pi_of_bcf [IsFiniteMeasure P] (mZ : AEMeasurable Z P)
    (mY : ∀ t, AEMeasurable (Y t) P)
    (h : ∀ (f : G →ᵇ ℝ) (g : (t : T) → F t →ᵇ ℝ),
      P[f ∘ Z * (∏ t, g t ∘ (Y t))] = P[f ∘ Z] * P[∏ t, g t ∘ (Y t)]) :
    IndepFun Z (fun ω t ↦ Y t ω) P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map mZ (aemeasurable_pi_lambda _ mY)]
  refine eq_prod_of_integral_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map, integral_map, integral_map]
  · convert h f g <;> simp
  any_goals fun_prop
  all_goals exact Measurable.aestronglyMeasurable (by fun_prop)

lemma pi_indepFun_of_bcf [IsFiniteMeasure P] (mX : ∀ s, AEMeasurable (X s) P)
    (mU : AEMeasurable U P)
    (h : ∀ (f : (s : S) → E s →ᵇ ℝ) (g : H →ᵇ ℝ),
      P[(∏ s, f s ∘ (X s)) * g ∘ U] = P[∏ s, f s ∘ (X s)] * P[g ∘ U]) :
    IndepFun (fun ω s ↦ X s ω) U P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (aemeasurable_pi_lambda _ mX) mU]
  refine eq_prod_of_integral_prod_mul_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map, integral_map, integral_map]
  · convert h f g <;> simp
  any_goals fun_prop
  all_goals exact Measurable.aestronglyMeasurable (by fun_prop)

lemma indepFun_of_bcf [IsFiniteMeasure P] (mZ : AEMeasurable Z P) (mU : AEMeasurable U P)
    (h : ∀ (f : G →ᵇ ℝ) (g : H →ᵇ ℝ), P[f ∘ Z * g ∘ U] = P[f ∘ Z] * P[g ∘ U]) :
    IndepFun Z U P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map mZ mU]
  refine eq_prod_of_integral_mul_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map, integral_map, integral_map]
  · exact h f g
  any_goals fun_prop
  exact Measurable.aestronglyMeasurable (by fun_prop)

lemma indicator_indepFun_of_bcf [IsFiniteMeasure P] {A : Set Ω} (mA : NullMeasurableSet A P)
    (mX : ∀ s, AEMeasurable (X s) P)
    (h : ∀ f : (s : S) → E s →ᵇ ℝ, ∫ ω in A, ∏ s, f s (X s ω) ∂P =
      P.real A * ∫ ω, ∏ s, f s (X s ω) ∂P) :
    (A.indicator (1 : Ω → ℝ)) ⟂ᵢ[P] (fun ω s ↦ X s ω) := by
  refine indepFun_pi_of_bcf
    ((aemeasurable_indicator_const_iff 1).2 mA) mX fun f g ↦ ?_
  have h1 ω : f (A.indicator 1 ω) * ∏ s, g s (X s ω) =
      A.indicator (fun ω ↦ f 1 * ∏ s, g s (X s ω)) ω +
      f 0 * ∏ s, g s (X s ω) - A.indicator (fun ω ↦ f 0 * ∏ s, g s (X s ω)) ω := by
    classical
    rw [Set.indicator_apply]
    split_ifs <;> simp_all
  have h2 ω : f (A.indicator 1 ω) =
      A.indicator (fun _ ↦ f 1) ω + Aᶜ.indicator (fun _ ↦ f 0) ω := by
    classical
    rw [Set.indicator_apply]
    split_ifs <;> simp_all
  simp_rw [Pi.mul_apply, Finset.prod_apply, Function.comp_apply, h1, h2]
  rw [integral_sub, integral_add, integral_indicator₀ mA, integral_indicator₀ mA,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_add,
    integral_indicator₀ mA, integral_indicator₀ mA.compl, integral_const, integral_const, h]
  · simp [measureReal_compl mA]
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

end Fintype

lemma process_indepFun_process_of_bcf [IsZeroOrProbabilityMeasure P]
    (mX : ∀ s, Measurable (X s)) (mY : ∀ t, Measurable (Y t))
    (h : ∀ (I : Finset S) (J : Finset T) (f : (s : I) → E s →ᵇ ℝ) (g : (t : J) → F t →ᵇ ℝ),
      P[(∏ s, f s ∘ (X s)) * (∏ t, g t ∘ (Y t))] = P[∏ s, f s ∘ (X s)] * P[∏ t, g t ∘ (Y t)]) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  IndepFun.process_indepFun_process mX mY
    fun I J ↦ pi_indepFun_pi_of_bcf (by fun_prop) (by fun_prop) (h I J)

lemma indepFun_process_of_bcf [IsZeroOrProbabilityMeasure P]
    (mZ : AEMeasurable Z P) (mY : ∀ t, Measurable (Y t))
    (h : ∀ (f : G →ᵇ ℝ) (J : Finset T) (g : (t : J) → F t →ᵇ ℝ),
      P[f ∘ Z * (∏ t, g t ∘ (Y t))] = P[f ∘ Z] * P[∏ t, g t ∘ (Y t)]) :
    IndepFun Z (fun ω t ↦ Y t ω) P :=
  IndepFun.indepFun_process mZ mY fun J ↦ indepFun_pi_of_bcf (by fun_prop) (by fun_prop) (h · J)

lemma process_indepFun_of_bcf [IsZeroOrProbabilityMeasure P]
    (mX : ∀ s, Measurable (X s)) (mU : AEMeasurable U P)
    (h : ∀ (I : Finset S) (f : (s : I) → E s →ᵇ ℝ) (g : H →ᵇ ℝ),
      P[(∏ s, f s ∘ (X s)) * g ∘ U] = P[∏ s, f s ∘ (X s)] * P[g ∘ U]) :
    IndepFun (fun ω s ↦ X s ω) U P :=
  IndepFun.process_indepFun mX mU fun I ↦ pi_indepFun_of_bcf (by fun_prop) (by fun_prop) (h I)

end Process

variable {Ω E F : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [TopologicalSpace E] [mE : MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
  [TopologicalSpace F] [mF : MeasurableSpace F] [BorelSpace F] [HasOuterApproxClosed F]
  {X : Ω → E} {Y : Ω → F}

lemma indepFun_of_boundedContinuousFunction [IsFiniteMeasure P]
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P)
    (h : ∀ (f : E →ᵇ ℝ) (g : F →ᵇ ℝ), P[(f ∘ X) * (g ∘ Y)] = P[f ∘ X] * P[g ∘ Y]) :
    X ⟂ᵢ[P] Y := by
  rw [indepFun_iff_map_prod_eq_prod_map_map mX mY]
  refine eq_prod_of_integral_mul_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map, integral_map, integral_map]
  · exact h f g
  any_goals fun_prop
  exact (f.continuous.aestronglyMeasurable.comp_measurable measurable_fst).mul
    (g.continuous.aestronglyMeasurable.comp_measurable measurable_snd)

lemma indepSet_iff_compl_indepSet {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    [IsZeroOrProbabilityMeasure P] :
    IndepSet A B P ↔ IndepSet Aᶜ B P := by
  obtain rfl | _ : P = 0 ∨ IsProbabilityMeasure P := by
    obtain h | h := IsZeroOrProbabilityMeasure.measure_univ (μ := P)
    · simp_all
    · exact Or.inr ⟨h⟩
  · simp_rw [IndepSet]
    simp
  suffices ∀ A B, MeasurableSet A → MeasurableSet B → IndepSet A B P → IndepSet Aᶜ B P by
    refine ⟨this A B hA hB, fun h ↦ ?_⟩
    convert this _ _ hA.compl hB h
    simp
  intro A B hA hB hAB
  rw [indepSet_iff_measure_inter_eq_mul hA.compl hB P]
  rw [indepSet_iff_measure_inter_eq_mul hA hB P] at hAB
  calc
    P (Aᶜ ∩ B) = P (B \ (A ∩ B)) := by congr 1; grind
    _ = P B - P (A ∩ B) := by rw [measure_diff (by grind) (by measurability) (by simp)]
    _ = P B - P A * P B := by rw [hAB]
    _ = (1 - P A) * P B := by rw [ENNReal.sub_mul (by simp)]; simp
    _ = P Aᶜ * P B := by rw [measure_compl hA (by simp)]; simp

lemma singleton_indepSets_comap_iff_indicator_indepFun (mX : Measurable X) {A : Set Ω}
    (hA : MeasurableSet A) [hP : IsProbabilityMeasure P] :
    IndepSets {A} {s | MeasurableSet[mE.comap X] s} P ↔
    (A.indicator (1 : Ω → ℝ)) ⟂ᵢ[P] X where
  mp h := by
    rw [IndepFun_iff]
    rintro - - ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    classical
    by_cases h0 : 0 ∈ s <;> by_cases h1 : 1 ∈ s
    · have : A.indicator 1 ⁻¹' s = Set.univ := by
        ext
        simp only [Set.mem_preimage, Set.indicator_apply, Pi.one_apply, Set.mem_univ, iff_true]
        split_ifs <;> simp_all
      rw [this]
      simp
    · have : A.indicator 1 ⁻¹' s = Aᶜ := by
        ext
        simp only [Set.mem_preimage, Set.indicator_apply, Pi.ofNat_apply, Set.mem_compl_iff]
        split_ifs <;> simp_all
      rw [this]
      have : IndepSet Aᶜ (X ⁻¹' t) P := by
        rw [← indepSet_iff_compl_indepSet hA (mX ht)]
        exact IndepSets.indepSet_of_mem {A} {s | MeasurableSet[mE.comap X] s}
          (by simp) ⟨t, ht, rfl⟩ hA (mX ht) P h
      exact this.measure_inter_eq_mul
    · have : A.indicator 1 ⁻¹' s = A := by
        ext
        simp only [Set.mem_preimage, Set.indicator_apply, Pi.one_apply]
        split_ifs <;> simp_all
      rw [this]
      exact (IndepSets_iff _ _ P).1 h _ _ (by simp) ⟨t, ht, rfl⟩
    · have : A.indicator 1 ⁻¹' s = ∅ := by
        ext
        simp only [Set.mem_preimage, Set.indicator_apply, Pi.one_apply, Set.mem_empty_iff_false,
          iff_false]
        split_ifs <;> simp_all
      rw [this]
      simp
  mpr h := by
    rw [IndepSets_iff]
    rintro s - hs ⟨t, ht, rfl⟩
    rw [Set.mem_singleton_iff.1 hs]
    have hA' : A = A.indicator (1 : Ω → ℝ) ⁻¹' {1} := by ext; simp [Set.indicator]
    rw [hA']
    exact h.measure_inter_preimage_eq_mul _ _ (by simp) ht

lemma indepSets_singleton_comap_of_boundedContinuousFunction [IsProbabilityMeasure P]
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

lemma indepSets_comap_of_boundedContinuousFunction [IsProbabilityMeasure P]
    (mX : AEMeasurable X P) {A : Set (Set Ω)}
    (hA : ∀ s ∈ A, MeasurableSet s)
    (h : ∀ s ∈ A, ∀ f : E →ᵇ ℝ, ∫ ω in s, f (X ω) ∂P = P.real s * P[f ∘ X]) :
    IndepSets A {s | MeasurableSet[mE.comap X] s} P := by
  rw [← A.biUnion_of_singleton]
  exact IndepSets.biUnion fun s hs ↦
    indepSets_singleton_comap_of_boundedContinuousFunction mX (hA s hs) (h s hs)

lemma indep_comap_of_boundedContinuousFunction (hm : m ≤ mΩ) [IsProbabilityMeasure P]
    (mX : AEMeasurable X P)
    (h : ∀ s, MeasurableSet[m] s → ∀ f : E →ᵇ ℝ, ∫ ω in s, f (X ω) ∂P = P.real s * P[f ∘ X]) :
    Indep m (mE.comap X) P :=
  (Indep_iff_IndepSets ..).2 <|
    indepSets_comap_of_boundedContinuousFunction mX (fun s hs ↦ hm s hs) h
