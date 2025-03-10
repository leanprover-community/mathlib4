/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.MeasureTheory.Integral.Lebesgue

/-!
# The Giry monad

Let X be a measurable space. The collection of all measures on X again
forms a measurable space. This construction forms a monad on
measurable spaces and measurable functions, called the Giry monad.

Note that most sources use the term "Giry monad" for the restriction
to *probability* measures. Here we include all measures on X.

See also `MeasureTheory/Category/MeasCat.lean`, containing an upgrade of the type-level
monad to an honest monad of the functor `measure : MeasCat ⥤ MeasCat`.

## References

* <https://ncatlab.org/nlab/show/Giry+monad>

## Tags

giry monad
-/


noncomputable section

open ENNReal Set Filter

variable {α β : Type*}

namespace MeasureTheory

namespace Measure

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Measurability structure on `Measure`: Measures are measurable w.r.t. all projections -/
instance instMeasurableSpace : MeasurableSpace (Measure α) :=
  ⨆ (s : Set α) (_ : MeasurableSet s), (borel ℝ≥0∞).comap fun μ => μ s

theorem measurable_coe {s : Set α} (hs : MeasurableSet s) : Measurable fun μ : Measure α => μ s :=
  Measurable.of_comap_le <| le_iSup_of_le s <| le_iSup_of_le hs <| le_rfl

theorem measurable_of_measurable_coe (f : β → Measure α)
    (h : ∀ (s : Set α), MeasurableSet s → Measurable fun b => f b s) : Measurable f :=
  Measurable.of_le_map <|
    iSup₂_le fun s hs =>
      MeasurableSpace.comap_le_iff_le_map.2 <| by rw [MeasurableSpace.map_comp]; exact h s hs

instance instMeasurableAdd₂ {α : Type*} {m : MeasurableSpace α} : MeasurableAdd₂ (Measure α) := by
  refine ⟨Measure.measurable_of_measurable_coe _ fun s hs => ?_⟩
  simp_rw [Measure.coe_add, Pi.add_apply]
  refine Measurable.add ?_ ?_
  · exact (Measure.measurable_coe hs).comp measurable_fst
  · exact (Measure.measurable_coe hs).comp measurable_snd

theorem measurable_measure {μ : α → Measure β} :
    Measurable μ ↔ ∀ (s : Set β), MeasurableSet s → Measurable fun b => μ b s :=
  ⟨fun hμ _s hs => (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩

theorem _root_.Measurable.measure_of_isPiSystem {μ : α → Measure β} [∀ a, IsFiniteMeasure (μ a)]
    {S : Set (Set β)} (hgen : ‹MeasurableSpace β› = .generateFrom S) (hpi : IsPiSystem S)
    (h_basic : ∀ s ∈ S, Measurable fun a ↦ μ a s) (h_univ : Measurable fun a ↦ μ a univ) :
    Measurable μ := by
  rw [measurable_measure]
  intro s hs
  induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp
  | basic s hs => exact h_basic s hs
  | compl s hsm ihs =>
    simp only [measure_compl hsm (measure_ne_top _ _)]
    exact h_univ.sub ihs
  | iUnion f hfd hfm ihf =>
    simpa only [measure_iUnion hfd hfm] using .ennreal_tsum ihf

theorem _root_.Measurable.measure_of_isPiSystem_of_isProbabilityMeasure {μ : α → Measure β}
    [∀ a, IsProbabilityMeasure (μ a)]
    {S : Set (Set β)} (hgen : ‹MeasurableSpace β› = .generateFrom S) (hpi : IsPiSystem S)
    (h_basic : ∀ s ∈ S, Measurable fun a ↦ μ a s) : Measurable μ :=
  .measure_of_isPiSystem hgen hpi h_basic <| by simp

@[fun_prop]
theorem measurable_map (f : α → β) (hf : Measurable f) :
    Measurable fun μ : Measure α => map f μ := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [map_apply hf hs]
  exact measurable_coe (hf hs)

@[fun_prop]
theorem measurable_dirac : Measurable (Measure.dirac : α → Measure α) := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [dirac_apply' _ hs]
  exact measurable_one.indicator hs

@[fun_prop]
theorem measurable_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun μ : Measure α => ∫⁻ x, f x ∂μ := by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine .iSup fun n => Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.const_mul ?_ _
  exact measurable_coe ((SimpleFunc.eapprox f n).measurableSet_preimage _)

/-- Monadic join on `Measure` in the category of measurable spaces and measurable
functions. -/
def join (m : Measure (Measure α)) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, zero_mul])
    (by
      intro f hf h
      simp_rw [measure_iUnion h hf]
      apply lintegral_tsum
      intro i; exact (measurable_coe (hf i)).aemeasurable)

@[simp]
theorem join_apply {m : Measure (Measure α)} {s : Set α} (hs : MeasurableSet s) :
    join m s = ∫⁻ μ, μ s ∂m :=
  Measure.ofMeasurable_apply s hs

@[simp]
theorem join_zero : (0 : Measure (Measure α)).join = 0 := by
  ext1 s hs
  simp only [hs, join_apply, lintegral_zero_measure, coe_zero, Pi.zero_apply]

@[fun_prop]
theorem measurable_join : Measurable (join : Measure (Measure α) → Measure α) :=
  measurable_of_measurable_coe _ fun s hs => by
    simp only [join_apply hs]; exact measurable_lintegral (measurable_coe hs)

theorem lintegral_join {m : Measure (Measure α)} {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂join m = ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m := by
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hf, SimpleFunc.lintegral,
    join_apply (SimpleFunc.measurableSet_preimage _ _)]
  suffices
    ∀ (s : ℕ → Finset ℝ≥0∞) (f : ℕ → ℝ≥0∞ → Measure α → ℝ≥0∞), (∀ n r, Measurable (f n r)) →
      Monotone (fun n μ => ∑ r ∈ s n, r * f n r μ) →
      ⨆ n, ∑ r ∈ s n, r * ∫⁻ μ, f n r μ ∂m = ∫⁻ μ, ⨆ n, ∑ r ∈ s n, r * f n r μ ∂m by
    refine
      this (fun n => SimpleFunc.range (SimpleFunc.eapprox f n))
        (fun n r μ => μ (SimpleFunc.eapprox f n ⁻¹' {r})) ?_ ?_
    · exact fun n r => measurable_coe (SimpleFunc.measurableSet_preimage _ _)
    · exact fun n m h μ => SimpleFunc.lintegral_mono (SimpleFunc.monotone_eapprox _ h) le_rfl
  intro s f hf hm
  rw [lintegral_iSup _ hm]
  swap
  · fun_prop
  congr
  funext n
  rw [lintegral_finset_sum (s n)]
  · simp_rw [lintegral_const_mul _ (hf _ _)]
  · exact fun r _ => (hf _ _).const_mul _

/-- Monadic bind on `Measure`, only works in the category of measurable spaces and measurable
functions. When the function `f` is not measurable the result is not well defined. -/
def bind (m : Measure α) (f : α → Measure β) : Measure β :=
  join (map f m)

@[simp]
theorem bind_zero_left (f : α → Measure β) : bind (0 : Measure α) f = 0 := by simp [bind]

@[simp]
theorem bind_zero_right (m : Measure α) : bind m (0 : α → Measure β) = 0 := by
  ext1 s hs
  simp only [bind, hs, join_apply, coe_zero, Pi.zero_apply]
  rw [lintegral_map (measurable_coe hs) measurable_zero]
  simp only [Pi.zero_apply, coe_zero, lintegral_const, zero_mul]

@[simp]
theorem bind_zero_right' (m : Measure α) : bind m (fun _ => 0 : α → Measure β) = 0 :=
  bind_zero_right m

@[simp]
theorem bind_apply {m : Measure α} {f : α → Measure β} {s : Set β} (hs : MeasurableSet s)
    (hf : Measurable f) : bind m f s = ∫⁻ a, f a s ∂m := by
  rw [bind, join_apply hs, lintegral_map (measurable_coe hs) hf]

@[simp]
lemma bind_const {m : Measure α} {ν : Measure β} : m.bind (fun _ ↦ ν) = m Set.univ • ν := by
  ext s hs
  rw [bind_apply hs measurable_const, lintegral_const, smul_apply, smul_eq_mul, mul_comm]

@[fun_prop]
theorem measurable_bind' {g : α → Measure β} (hg : Measurable g) :
    Measurable fun m : Measure α => bind m g :=
  measurable_join.comp (measurable_map _ hg)

theorem lintegral_bind {m : Measure α} {μ : α → Measure β} {f : β → ℝ≥0∞} (hμ : Measurable μ)
    (hf : Measurable f) : ∫⁻ x, f x ∂bind m μ = ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  (lintegral_join hf).trans (lintegral_map (measurable_lintegral hf) hμ)

theorem bind_bind {γ} [MeasurableSpace γ] {m : Measure α} {f : α → Measure β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) : bind (bind m f) g = bind m fun a => bind (f a) g := by
  ext1 s hs
  erw [bind_apply hs hg, bind_apply hs ((measurable_bind' hg).comp hf),
    lintegral_bind hf ((measurable_coe hs).comp hg)]
  conv_rhs => enter [2, a]; erw [bind_apply hs hg]
  rfl

theorem dirac_bind {f : α → Measure β} (hf : Measurable f) (a : α) : bind (dirac a) f = f a := by
  ext1 s hs
  erw [bind_apply hs hf, lintegral_dirac' a ((measurable_coe hs).comp hf)]
  rfl

@[simp]
theorem bind_dirac {m : Measure α} : bind m dirac = m := by
  ext1 s hs
  simp only [bind_apply hs measurable_dirac, dirac_apply' _ hs, lintegral_indicator hs,
    Pi.one_apply, lintegral_one, restrict_apply, MeasurableSet.univ, univ_inter]

@[simp]
lemma bind_dirac_eq_map (m : Measure α) {f : α → β} (hf : Measurable f) :
    m.bind (fun x ↦ Measure.dirac (f x)) = m.map f := by
  ext s hs
  rw [bind_apply hs]
  swap; · fun_prop
  simp_rw [dirac_apply' _ hs]
  rw [← lintegral_map _ hf, lintegral_indicator_one hs]
  exact measurable_const.indicator hs

theorem join_eq_bind (μ : Measure (Measure α)) : join μ = bind μ id := by rw [bind, map_id]

theorem join_map_map {f : α → β} (hf : Measurable f) (μ : Measure (Measure α)) :
    join (map (map f) μ) = map f (join μ) := by
  ext1 s hs
  rw [join_apply hs, map_apply hf hs, join_apply (hf hs),
    lintegral_map (measurable_coe hs) (measurable_map f hf)]
  simp_rw [map_apply hf hs]

theorem join_map_join (μ : Measure (Measure (Measure α))) : join (map join μ) = join (join μ) := by
  show bind μ join = join (join μ)
  rw [join_eq_bind, join_eq_bind, bind_bind measurable_id measurable_id]
  apply congr_arg (bind μ)
  funext ν
  exact join_eq_bind ν

theorem join_map_dirac (μ : Measure α) : join (map dirac μ) = μ := bind_dirac

theorem join_dirac (μ : Measure α) : join (dirac μ) = μ :=
  (join_eq_bind (dirac μ)).trans (dirac_bind measurable_id _)

end Measure

end MeasureTheory
