/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The product measure

In this file we define and prove properties about the binary product measure. If `α` and `β` have
s-finite measures `μ` resp. `ν` then `α × β` can be equipped with a s-finite measure `μ.prod ν` that
satisfies `(μ.prod ν) s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`.
We also have `(μ.prod ν) (s ×ˢ t) = μ s * ν t`, i.e. the measure of a rectangle is the product of
the measures of the sides.

We also prove Tonelli's theorem.

## Main definition

* `MeasureTheory.Measure.prod`: The product of two measures.

## Main results

* `MeasureTheory.Measure.prod_apply` states `μ.prod ν s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`
  for measurable `s`. `MeasureTheory.Measure.prod_apply_symm` is the reversed version.
* `MeasureTheory.Measure.prod_prod` states `μ.prod ν (s ×ˢ t) = μ s * ν t` for measurable sets
  `s` and `t`.
* `MeasureTheory.lintegral_prod`: Tonelli's theorem. It states that for a measurable function
  `α × β → ℝ≥0∞` we have `∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ`. The version
  for functions `α → β → ℝ≥0∞` is reversed, and called `lintegral_lintegral`. Both versions have
  a variant with `_symm` appended, where the order of integration is reversed.
  The lemma `Measurable.lintegral_prod_right'` states that the inner integral of the right-hand side
  is measurable.

## Implementation Notes

Many results are proven twice, once for functions in curried form (`α → β → γ`) and one for
functions in uncurried form (`α × β → γ`). The former often has an assumption
`Measurable (uncurry f)`, which could be inconvenient to discharge, but for the latter it is more
common that the function has to be given explicitly, since Lean cannot synthesize the function by
itself. We name the lemmas about the uncurried form with a prime.
Tonelli's theorem has a different naming scheme, since the version for the uncurried version is
reversed.

## Tags

product measure, Tonelli's theorem, Fubini-Tonelli theorem
-/


noncomputable section

open Topology ENNReal MeasureTheory Set Function Real ENNReal MeasurableSpace MeasureTheory.Measure

open TopologicalSpace hiding generateFrom

open Filter hiding prod_eq map

variable {α β γ : Type*}

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {μ μ' : Measure α} {ν ν' : Measure β} {τ : Measure γ}

/-- If `ν` is a finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
  a measurable function. `measurable_measure_prod_mk_left` is strictly more general. -/
theorem measurable_measure_prod_mk_left_finite [IsFiniteMeasure ν] {s : Set (α × β)}
    (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻¹' s) := by
  induction s, hs using induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical simpa only [mk_preimage_prod_right_eq_if, measure_if]
      using measurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, measure_compl (measurable_prod_mk_left hs) (measure_ne_top ν _)]
    exact ihs.const_sub _
  | iUnion f hfd hfm ihf =>
    have (a : α) : ν (Prod.mk a ⁻¹' ⋃ i, f i) = ∑' i, ν (Prod.mk a ⁻¹' f i) := by
      rw [preimage_iUnion, measure_iUnion]
      exacts [hfd.mono fun _ _ ↦ .preimage _, fun i ↦ measurable_prod_mk_left (hfm i)]
    simpa only [this] using Measurable.ennreal_tsum ihf

/-- If `ν` is an s-finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }`
is a measurable function.

Not true without the s-finite assumption: on `ℝ × ℝ` with the product sigma-algebra, let `s` be the
diagonal and let `ν` be an uncountable sum of Dirac measures (all Dirac measures for points in a
set `t`). Then `ν (Prod.mk x ⁻¹' s) = ν {x} = if x ∈ t then 1 else 0`. If `t` is chosen
non-measurable, this will not be measurable. -/
theorem measurable_measure_prod_mk_left [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun x => ν (Prod.mk x ⁻¹' s) := by
  rw [← sum_sfiniteSeq ν]
  simp_rw [Measure.sum_apply_of_countable]
  exact Measurable.ennreal_tsum (fun i ↦ measurable_measure_prod_mk_left_finite hs)

/-- If `μ` is an s-finite measure, and `s ⊆ α × β` is measurable, then `y ↦ μ { x | (x, y) ∈ s }` is
  a measurable function. -/
theorem measurable_measure_prod_mk_right {μ : Measure α} [SFinite μ] {s : Set (α × β)}
    (hs : MeasurableSet s) : Measurable fun y => μ ((fun x => (x, y)) ⁻¹' s) :=
  measurable_measure_prod_mk_left (measurableSet_swap_iff.mpr hs)

theorem Measurable.map_prod_mk_left [SFinite ν] :
    Measurable fun x : α => map (Prod.mk x) ν := by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prod_mk_left hs]
  exact measurable_measure_prod_mk_left hs

theorem Measurable.map_prod_mk_right {μ : Measure α} [SFinite μ] :
    Measurable fun y : β => map (fun x : α => (x, y)) μ := by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prod_mk_right hs]
  exact measurable_measure_prod_mk_right hs

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable. -/
theorem Measurable.lintegral_prod_right' [SFinite ν] :
    ∀ {f : α × β → ℝ≥0∞}, Measurable f → Measurable fun x => ∫⁻ y, f (x, y) ∂ν := by
  have m := @measurable_prod_mk_left
  refine Measurable.ennreal_induction (P := fun f => Measurable fun (x : α) => ∫⁻ y, f (x, y) ∂ν)
    ?_ ?_ ?_
  · intro c s hs
    simp only [← indicator_comp_right]
    suffices Measurable fun x => c * ν (Prod.mk x ⁻¹' s) by simpa [lintegral_indicator (m hs)]
    exact (measurable_measure_prod_mk_left hs).const_mul _
  · rintro f g - hf - h2f h2g
    simp only [Pi.add_apply]
    conv => enter [1, x]; erw [lintegral_add_left (hf.comp m)]
    exact h2f.add h2g
  · intro f hf h2f h3f
    have : ∀ x, Monotone fun n y => f n (x, y) := fun x i j hij y => h2f hij (x, y)
    conv => enter [1, x]; erw [lintegral_iSup (fun n => (hf n).comp m) (this x)]
    exact .iSup h3f

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
theorem Measurable.lintegral_prod_right [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun x => ∫⁻ y, f x y ∂ν :=
  hf.lintegral_prod_right'

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable. -/
theorem Measurable.lintegral_prod_left' [SFinite μ] {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun y => ∫⁻ x, f (x, y) ∂μ :=
  (measurable_swap_iff.mpr hf).lintegral_prod_right'

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
theorem Measurable.lintegral_prod_left [SFinite μ] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun y => ∫⁻ x, f x y ∂μ :=
  hf.lintegral_prod_left'

/-! ### The product measure -/


namespace MeasureTheory

namespace Measure

/-- The binary product of measures. They are defined for arbitrary measures, but we basically
  prove all properties under the assumption that at least one of them is s-finite. -/
protected irreducible_def prod (μ : Measure α) (ν : Measure β) : Measure (α × β) :=
  bind μ fun x : α => map (Prod.mk x) ν

instance prod.measureSpace {α β} [MeasureSpace α] [MeasureSpace β] : MeasureSpace (α × β) where
  volume := volume.prod volume

theorem volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β] :
    (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β) :=
  rfl

variable [SFinite ν]

theorem prod_apply {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := by
  simp_rw [Measure.prod, bind_apply hs (Measurable.map_prod_mk_left (ν := ν)),
    map_apply measurable_prod_mk_left hs]

/-- The product measure of the product of two sets is the product of their measures. Note that we
do not need the sets to be measurable. -/
@[simp]
theorem prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  classical
  apply le_antisymm
  · set S := toMeasurable μ s
    set T := toMeasurable ν t
    have hSTm : MeasurableSet (S ×ˢ T) :=
      (measurableSet_toMeasurable _ _).prod (measurableSet_toMeasurable _ _)
    calc
      μ.prod ν (s ×ˢ t) ≤ μ.prod ν (S ×ˢ T) := by gcongr <;> apply subset_toMeasurable
      _ = μ S * ν T := by
        rw [prod_apply hSTm]
        simp_rw [S, mk_preimage_prod_right_eq_if, measure_if,
          lintegral_indicator (measurableSet_toMeasurable _ _), lintegral_const,
          restrict_apply_univ, mul_comm]
      _ = μ s * ν t := by rw [measure_toMeasurable, measure_toMeasurable]
  · -- Formalization is based on https://mathoverflow.net/a/254134/136589
    set ST := toMeasurable (μ.prod ν) (s ×ˢ t)
    have hSTm : MeasurableSet ST := measurableSet_toMeasurable _ _
    have hST : s ×ˢ t ⊆ ST := subset_toMeasurable _ _
    set f : α → ℝ≥0∞ := fun x => ν (Prod.mk x ⁻¹' ST)
    have hfm : Measurable f := measurable_measure_prod_mk_left hSTm
    set s' : Set α := { x | ν t ≤ f x }
    have hss' : s ⊆ s' := fun x hx => measure_mono fun y hy => hST <| mk_mem_prod hx hy
    calc
      μ s * ν t ≤ μ s' * ν t := by gcongr
      _ = ∫⁻ _ in s', ν t ∂μ := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ x in s', f x ∂μ := setLIntegral_mono hfm fun x => id
      _ ≤ ∫⁻ x, f x ∂μ := lintegral_mono' restrict_le_self le_rfl
      _ = μ.prod ν ST := (prod_apply hSTm).symm
      _ = μ.prod ν (s ×ˢ t) := measure_toMeasurable _

@[simp] lemma map_fst_prod : Measure.map Prod.fst (μ.prod ν) = (ν univ) • μ := by
  ext s hs
  simp [Measure.map_apply measurable_fst hs, ← prod_univ, mul_comm]

@[simp] lemma map_snd_prod : Measure.map Prod.snd (μ.prod ν) = (μ univ) • ν := by
  ext s hs
  simp [Measure.map_apply measurable_snd hs, ← univ_prod]

instance prod.instIsOpenPosMeasure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {m : MeasurableSpace X} {μ : Measure X} [IsOpenPosMeasure μ] {m' : MeasurableSpace Y}
    {ν : Measure Y} [IsOpenPosMeasure ν] [SFinite ν] : IsOpenPosMeasure (μ.prod ν) := by
  constructor
  rintro U U_open ⟨⟨x, y⟩, hxy⟩
  rcases isOpen_prod_iff.1 U_open x y hxy with ⟨u, v, u_open, v_open, xu, yv, huv⟩
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono huv))
  simp only [prod_prod, CanonicallyOrderedAdd.mul_pos]
  constructor
  · exact u_open.measure_pos μ ⟨x, xu⟩
  · exact v_open.measure_pos ν ⟨y, yv⟩

instance {X Y : Type*}
    [TopologicalSpace X] [MeasureSpace X] [IsOpenPosMeasure (volume : Measure X)]
    [TopologicalSpace Y] [MeasureSpace Y] [IsOpenPosMeasure (volume : Measure Y)]
    [SFinite (volume : Measure Y)] : IsOpenPosMeasure (volume : Measure (X × Y)) :=
  prod.instIsOpenPosMeasure

instance prod.instIsFiniteMeasure {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (μ.prod ν) := by
  constructor
  rw [← univ_prod_univ, prod_prod]
  exact mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)

instance {α β : Type*} [MeasureSpace α] [MeasureSpace β] [IsFiniteMeasure (volume : Measure α)]
    [IsFiniteMeasure (volume : Measure β)] : IsFiniteMeasure (volume : Measure (α × β)) :=
  prod.instIsFiniteMeasure _ _

instance prod.instIsProbabilityMeasure {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (μ.prod ν) :=
  ⟨by rw [← univ_prod_univ, prod_prod, measure_univ, measure_univ, mul_one]⟩

instance {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [IsProbabilityMeasure (volume : Measure α)] [IsProbabilityMeasure (volume : Measure β)] :
    IsProbabilityMeasure (volume : Measure (α × β)) :=
  prod.instIsProbabilityMeasure _ _

instance prod.instIsFiniteMeasureOnCompacts {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] [SFinite ν] :
    IsFiniteMeasureOnCompacts (μ.prod ν) := by
  refine ⟨fun K hK => ?_⟩
  set L := (Prod.fst '' K) ×ˢ (Prod.snd '' K) with hL
  have : K ⊆ L := by
    rintro ⟨x, y⟩ hxy
    simp only [L, prod_mk_mem_set_prod_eq, mem_image, Prod.exists, exists_and_right,
      exists_eq_right]
    exact ⟨⟨y, hxy⟩, ⟨x, hxy⟩⟩
  apply lt_of_le_of_lt (measure_mono this)
  rw [hL, prod_prod]
  exact mul_lt_top (hK.image continuous_fst).measure_lt_top (hK.image continuous_snd).measure_lt_top

instance {X Y : Type*}
    [TopologicalSpace X] [MeasureSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [TopologicalSpace Y] [MeasureSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    [SFinite (volume : Measure Y)] : IsFiniteMeasureOnCompacts (volume : Measure (X × Y)) :=
  prod.instIsFiniteMeasureOnCompacts _ _

instance prod.instNoAtoms_fst [NoAtoms μ] :
    NoAtoms (Measure.prod μ ν) := by
  refine NoAtoms.mk (fun x => ?_)
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, measure_singleton, zero_mul]

instance prod.instNoAtoms_snd [NoAtoms ν] :
    NoAtoms (Measure.prod μ ν) := by
  refine NoAtoms.mk (fun x => ?_)
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, measure_singleton (μ := ν), mul_zero]

theorem ae_measure_lt_top {s : Set (α × β)} (hs : MeasurableSet s) (h2s : (μ.prod ν) s ≠ ∞) :
    ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' s) < ∞ := by
  rw [prod_apply hs] at h2s
  exact ae_lt_top (measurable_measure_prod_mk_left hs) h2s

/-- Note: the assumption `hs` cannot be dropped. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
theorem measure_prod_null {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = 0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  rw [prod_apply hs, lintegral_eq_zero_iff (measurable_measure_prod_mk_left hs)]

/-- Note: the converse is not true without assuming that `s` is measurable. For a counterexample,
  see Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
theorem measure_ae_null_of_prod_null {s : Set (α × β)} (h : μ.prod ν s = 0) :
    (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  rw [measure_prod_null mt] at ht
  rw [eventuallyLE_antisymm_iff]
  exact
    ⟨EventuallyLE.trans_eq (Eventually.of_forall fun x => measure_mono (preimage_mono hst))
        ht,
      Eventually.of_forall fun x => zero_le _⟩

theorem AbsolutelyContinuous.prod [SFinite ν'] (h1 : μ ≪ μ') (h2 : ν ≪ ν') :
    μ.prod ν ≪ μ'.prod ν' := by
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  rw [measure_prod_null hs] at h2s ⊢
  exact (h2s.filter_mono h1.ae_le).mono fun _ h => h2 h

/-- Note: the converse is not true. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. It is true if the set is
  measurable, see `ae_prod_mem_iff_ae_ae_mem`. -/
theorem ae_ae_of_ae_prod {p : α × β → Prop} (h : ∀ᵐ z ∂μ.prod ν, p z) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y) :=
  measure_ae_null_of_prod_null h

theorem ae_ae_eq_curry_of_prod {γ : Type*} {f g : α × β → γ} (h : f =ᵐ[μ.prod ν] g) :
    ∀ᵐ x ∂μ, curry f x =ᵐ[ν] curry g x :=
  ae_ae_of_ae_prod h

theorem ae_ae_eq_of_ae_eq_uncurry {γ : Type*} {f g : α → β → γ}
    (h : uncurry f =ᵐ[μ.prod ν] uncurry g) : ∀ᵐ x ∂μ, f x =ᵐ[ν] g x :=
  ae_ae_eq_curry_of_prod h

theorem ae_prod_iff_ae_ae {p : α × β → Prop} (hp : MeasurableSet {x | p x}) :
    (∀ᵐ z ∂μ.prod ν, p z) ↔ ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y) :=
  measure_prod_null hp.compl

theorem ae_prod_mem_iff_ae_ae_mem {s : Set (α × β)} (hs : MeasurableSet s) :
    (∀ᵐ z ∂μ.prod ν, z ∈ s) ↔ ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (x, y) ∈ s :=
  measure_prod_null hs.compl

theorem quasiMeasurePreserving_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ := by
  refine ⟨measurable_fst, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply measurable_fst hs, ← prod_univ, prod_prod, h2s, zero_mul]

theorem quasiMeasurePreserving_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν := by
  refine ⟨measurable_snd, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply measurable_snd hs, ← univ_prod, prod_prod, h2s, mul_zero]

lemma set_prod_ae_eq {s s' : Set α} {t t' : Set β} (hs : s =ᵐ[μ] s') (ht : t =ᵐ[ν] t') :
    (s ×ˢ t : Set (α × β)) =ᵐ[μ.prod ν] (s' ×ˢ t' : Set (α × β)) :=
  (quasiMeasurePreserving_fst.preimage_ae_eq hs).inter
    (quasiMeasurePreserving_snd.preimage_ae_eq ht)

lemma measure_prod_compl_eq_zero {s : Set α} {t : Set β}
    (s_ae_univ : μ sᶜ = 0) (t_ae_univ : ν tᶜ = 0) :
    μ.prod ν (s ×ˢ t)ᶜ = 0 := by
  rw [Set.compl_prod_eq_union, measure_union_null_iff]
  simp [s_ae_univ, t_ae_univ]

lemma _root_.MeasureTheory.NullMeasurableSet.prod {s : Set α} {t : Set β}
    (s_mble : NullMeasurableSet s μ) (t_mble : NullMeasurableSet t ν) :
    NullMeasurableSet (s ×ˢ t) (μ.prod ν) :=
  let ⟨s₀, mble_s₀, s_aeeq_s₀⟩ := s_mble
  let ⟨t₀, mble_t₀, t_aeeq_t₀⟩ := t_mble
  ⟨s₀ ×ˢ t₀, ⟨mble_s₀.prod mble_t₀, set_prod_ae_eq s_aeeq_s₀ t_aeeq_t₀⟩⟩

/-- If `s ×ˢ t` is a null measurable set and `μ s ≠ 0`, then `t` is a null measurable set. -/
lemma _root_.MeasureTheory.NullMeasurableSet.right_of_prod {s : Set α} {t : Set β}
    (h : NullMeasurableSet (s ×ˢ t) (μ.prod ν)) (hs : μ s ≠ 0) : NullMeasurableSet t ν := by
  rcases h with ⟨u, hum, hu⟩
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, (Prod.mk x ⁻¹' (s ×ˢ t)) =ᵐ[ν] (Prod.mk x ⁻¹' u) :=
    ((frequently_ae_iff.2 hs).and_eventually (ae_ae_eq_curry_of_prod hu)).exists
  refine ⟨Prod.mk x ⁻¹' u, measurable_prod_mk_left hum, ?_⟩
  rwa [mk_preimage_prod_right hxs] at hx

/-- If `Prod.snd ⁻¹' t` is a null measurable set and `μ ≠ 0`, then `t` is a null measurable set. -/
lemma _root_.MeasureTheory.NullMeasurableSet.of_preimage_snd [NeZero μ] {t : Set β}
    (h : NullMeasurableSet (Prod.snd ⁻¹' t) (μ.prod ν)) : NullMeasurableSet t ν :=
  .right_of_prod (by rwa [univ_prod]) (NeZero.ne (μ univ))

/-- `Prod.snd ⁻¹' t` is null measurable w.r.t. `μ.prod ν` iff `t` is null measurable w.r.t. `ν`
provided that `μ ≠ 0`. -/
lemma nullMeasurableSet_preimage_snd [NeZero μ] {t : Set β} :
    NullMeasurableSet (Prod.snd ⁻¹' t) (μ.prod ν) ↔ NullMeasurableSet t ν :=
  ⟨.of_preimage_snd, (.preimage · quasiMeasurePreserving_snd)⟩

lemma nullMeasurable_comp_snd [NeZero μ] {f : β → γ} :
    NullMeasurable (f ∘ Prod.snd) (μ.prod ν) ↔ NullMeasurable f ν :=
  forall₂_congr fun s _ ↦ nullMeasurableSet_preimage_snd (t := f ⁻¹' s)

/-- `μ.prod ν` has finite spanning sets in rectangles of finite spanning sets. -/
noncomputable def FiniteSpanningSetsIn.prod {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
    (hμ : μ.FiniteSpanningSetsIn C) (hν : ν.FiniteSpanningSetsIn D) :
    (μ.prod ν).FiniteSpanningSetsIn (image2 (· ×ˢ ·) C D) := by
  haveI := hν.sigmaFinite
  refine
    ⟨fun n => hμ.set n.unpair.1 ×ˢ hν.set n.unpair.2, fun n =>
      mem_image2_of_mem (hμ.set_mem _) (hν.set_mem _), fun n => ?_, ?_⟩
  · rw [prod_prod]
    exact mul_lt_top (hμ.finite _) (hν.finite _)
  · simp_rw [iUnion_unpair_prod, hμ.spanning, hν.spanning, univ_prod_univ]

lemma prod_sum_left {ι : Type*} (m : ι → Measure α) (μ : Measure β) [SFinite μ] :
    (Measure.sum m).prod μ = Measure.sum (fun i ↦ (m i).prod μ) := by
  ext s hs
  simp only [prod_apply hs, lintegral_sum_measure, hs, sum_apply, ENNReal.tsum_prod']

lemma prod_sum_right {ι' : Type*} [Countable ι'] (m : Measure α) (m' : ι' → Measure β)
    [∀ n, SFinite (m' n)] :
    m.prod (Measure.sum m') = Measure.sum (fun p ↦ m.prod (m' p)) := by
  ext s hs
  simp only [prod_apply hs, lintegral_sum_measure, hs, sum_apply, ENNReal.tsum_prod']
  have M : ∀ x, MeasurableSet (Prod.mk x ⁻¹' s) := fun x => measurable_prod_mk_left hs
  simp_rw [Measure.sum_apply _ (M _)]
  rw [lintegral_tsum (fun i ↦ (measurable_measure_prod_mk_left hs).aemeasurable)]

lemma prod_sum {ι ι' : Type*} [Countable ι'] (m : ι → Measure α) (m' : ι' → Measure β)
    [∀ n, SFinite (m' n)] :
    (Measure.sum m).prod (Measure.sum m') =
      Measure.sum (fun (p : ι × ι') ↦ (m p.1).prod (m' p.2)) := by
  simp_rw [prod_sum_left, prod_sum_right, sum_sum]

instance prod.instSigmaFinite {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SigmaFinite μ] {_ : MeasurableSpace β} {ν : Measure β} [SigmaFinite ν] :
    SigmaFinite (μ.prod ν) :=
  (μ.toFiniteSpanningSetsIn.prod ν.toFiniteSpanningSetsIn).sigmaFinite

instance prod.instSFinite {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] {_ : MeasurableSpace β} {ν : Measure β} [SFinite ν] :
    SFinite (μ.prod ν) := by
  have : μ.prod ν =
      Measure.sum (fun (p : ℕ × ℕ) ↦ (sfiniteSeq μ p.1).prod (sfiniteSeq ν p.2)) := by
    conv_lhs => rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν]
    apply prod_sum
  rw [this]
  infer_instance

instance {α β} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    [MeasureSpace β] [SigmaFinite (volume : Measure β)] : SigmaFinite (volume : Measure (α × β)) :=
  prod.instSigmaFinite

instance {α β} [MeasureSpace α] [SFinite (volume : Measure α)]
    [MeasureSpace β] [SFinite (volume : Measure β)] : SFinite (volume : Measure (α × β)) :=
  prod.instSFinite

/-- A measure on a product space equals the product measure if they are equal on rectangles
  with as sides sets that generate the corresponding σ-algebras. -/
theorem prod_eq_generateFrom {μ : Measure α} {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
    (hC : generateFrom C = ‹_›) (hD : generateFrom D = ‹_›) (h2C : IsPiSystem C)
    (h2D : IsPiSystem D) (h3C : μ.FiniteSpanningSetsIn C) (h3D : ν.FiniteSpanningSetsIn D)
    {μν : Measure (α × β)} (h₁ : ∀ s ∈ C, ∀ t ∈ D, μν (s ×ˢ t) = μ s * ν t) : μ.prod ν = μν := by
  refine
    (h3C.prod h3D).ext
      (generateFrom_eq_prod hC hD h3C.isCountablySpanning h3D.isCountablySpanning).symm
      (h2C.prod h2D) ?_
  rintro _ ⟨s, hs, t, ht, rfl⟩
  haveI := h3D.sigmaFinite
  rw [h₁ s hs t ht, prod_prod]

/- Note that the next theorem is not true for s-finite measures: let `μ = ν = ∞ • Leb` on `[0,1]`
(they are  s-finite as countable sums of the finite Lebesgue measure), and let `μν = μ.prod ν + λ`
where `λ` is Lebesgue measure on the diagonal. Then both measures give infinite mass to rectangles
`s × t` whose sides have positive Lebesgue measure, and `0` measure when one of the sides has zero
Lebesgue measure. And yet they do not coincide, as the first one gives zero mass to the diagonal,
and the second one gives mass one.
-/
/-- A measure on a product space equals the product measure of sigma-finite measures if they are
equal on rectangles. -/
theorem prod_eq {μ : Measure α} [SigmaFinite μ] {ν : Measure β} [SigmaFinite ν]
    {μν : Measure (α × β)}
    (h : ∀ s t, MeasurableSet s → MeasurableSet t → μν (s ×ˢ t) = μ s * ν t) : μ.prod ν = μν :=
  prod_eq_generateFrom generateFrom_measurableSet generateFrom_measurableSet
    isPiSystem_measurableSet isPiSystem_measurableSet μ.toFiniteSpanningSetsIn
    ν.toFiniteSpanningSetsIn fun s hs t ht => h s t hs ht

variable [SFinite μ]

theorem prod_swap : map Prod.swap (μ.prod ν) = ν.prod μ := by
  have : sum (fun (i : ℕ × ℕ) ↦ map Prod.swap ((sfiniteSeq μ i.1).prod (sfiniteSeq ν i.2)))
       = sum (fun (i : ℕ × ℕ) ↦ map Prod.swap ((sfiniteSeq μ i.2).prod (sfiniteSeq ν i.1))) := by
    ext s hs
    rw [sum_apply _ hs, sum_apply _ hs]
    exact ((Equiv.prodComm ℕ ℕ).tsum_eq _).symm
  rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν, prod_sum, prod_sum,
    map_sum measurable_swap.aemeasurable, this]
  congr 1
  ext1 i
  refine (prod_eq ?_).symm
  intro s t hs ht
  simp_rw [map_apply measurable_swap (hs.prod ht), preimage_swap_prod, prod_prod, mul_comm]

theorem measurePreserving_swap : MeasurePreserving Prod.swap (μ.prod ν) (ν.prod μ) :=
  ⟨measurable_swap, prod_swap⟩

theorem prod_apply_symm {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν := by
  rw [← prod_swap, map_apply measurable_swap hs, prod_apply (measurable_swap hs)]
  rfl

theorem ae_ae_comm {p : α → β → Prop} (h : MeasurableSet {x : α × β | p x.1 x.2}) :
    (∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p x y) ↔ ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, p x y := calc
  _ ↔ ∀ᵐ x ∂μ.prod ν, p x.1 x.2 := .symm <| ae_prod_iff_ae_ae h
  _ ↔ ∀ᵐ x ∂ν.prod μ, p x.2 x.1 := by rw [← prod_swap, ae_map_iff (by fun_prop) h]; simp
  _ ↔ ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, p x y := ae_prod_iff_ae_ae <| measurable_swap h

/-- If `s ×ˢ t` is a null measurable set and `ν t ≠ 0`, then `s` is a null measurable set. -/
lemma _root_.MeasureTheory.NullMeasurableSet.left_of_prod {s : Set α} {t : Set β}
    (h : NullMeasurableSet (s ×ˢ t) (μ.prod ν)) (ht : ν t ≠ 0) : NullMeasurableSet s μ := by
  refine .right_of_prod ?_ ht
  rw [← preimage_swap_prod]
  exact h.preimage measurePreserving_swap.quasiMeasurePreserving

/-- If `Prod.fst ⁻¹' s` is a null measurable set and `ν ≠ 0`, then `s` is a null measurable set. -/
lemma _root_.MeasureTheory.NullMeasurableSet.of_preimage_fst [NeZero ν] {s : Set α}
    (h : NullMeasurableSet (Prod.fst ⁻¹' s) (μ.prod ν)) : NullMeasurableSet s μ :=
  .left_of_prod (by rwa [prod_univ]) (NeZero.ne (ν univ))

/-- `Prod.fst ⁻¹' s` is null measurable w.r.t. `μ.prod ν` iff `s` is null measurable w.r.t. `μ`
provided that `ν ≠ 0`. -/
lemma nullMeasurableSet_preimage_fst [NeZero ν] {s : Set α} :
    NullMeasurableSet (Prod.fst ⁻¹' s) (μ.prod ν) ↔ NullMeasurableSet s μ :=
  ⟨.of_preimage_fst, (.preimage · quasiMeasurePreserving_fst)⟩

lemma nullMeasurable_comp_fst [NeZero ν] {f : α → γ} :
    NullMeasurable (f ∘ Prod.fst) (μ.prod ν) ↔ NullMeasurable f μ :=
  forall₂_congr fun s _ ↦ nullMeasurableSet_preimage_fst (s := f ⁻¹' s)

/-- The product of two non-null sets is null measurable
if and only if both of them are null measurable. -/
lemma nullMeasurableSet_prod_of_ne_zero {s : Set α} {t : Set β} (hs : μ s ≠ 0) (ht : ν t ≠ 0) :
    NullMeasurableSet (s ×ˢ t) (μ.prod ν) ↔ NullMeasurableSet s μ ∧ NullMeasurableSet t ν :=
  ⟨fun h ↦ ⟨h.left_of_prod ht, h.right_of_prod hs⟩, fun ⟨hs, ht⟩ ↦ hs.prod ht⟩

/-- The product of two sets is null measurable
if and only if both of them are null measurable or one of them has measure zero. -/
lemma nullMeasurableSet_prod {s : Set α} {t : Set β} :
    NullMeasurableSet (s ×ˢ t) (μ.prod ν) ↔
      NullMeasurableSet s μ ∧ NullMeasurableSet t ν ∨ μ s = 0 ∨ ν t = 0 := by
  rcases eq_or_ne (μ s) 0 with hs | hs; · simp [NullMeasurableSet.of_null, *]
  rcases eq_or_ne (ν t) 0 with ht | ht; · simp [NullMeasurableSet.of_null, *]
  simp [*, nullMeasurableSet_prod_of_ne_zero]

theorem prodAssoc_prod [SFinite τ] :
    map MeasurableEquiv.prodAssoc ((μ.prod ν).prod τ) = μ.prod (ν.prod τ) := by
  have : sum (fun (p : ℕ × ℕ × ℕ) ↦
        (sfiniteSeq μ p.1).prod ((sfiniteSeq ν p.2.1).prod (sfiniteSeq τ p.2.2)))
      = sum (fun (p : (ℕ × ℕ) × ℕ) ↦
        (sfiniteSeq μ p.1.1).prod ((sfiniteSeq ν p.1.2).prod (sfiniteSeq τ p.2))) := by
    ext s hs
    rw [sum_apply _ hs, sum_apply _ hs, ← (Equiv.prodAssoc _ _ _).tsum_eq]
    simp only [Equiv.prodAssoc_apply]
  rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν, ← sum_sfiniteSeq τ, prod_sum, prod_sum,
    map_sum MeasurableEquiv.prodAssoc.measurable.aemeasurable, prod_sum, prod_sum, this]
  congr
  ext1 i
  refine (prod_eq_generateFrom generateFrom_measurableSet generateFrom_prod
    isPiSystem_measurableSet isPiSystem_prod ((sfiniteSeq μ i.1.1)).toFiniteSpanningSetsIn
    ((sfiniteSeq ν i.1.2).toFiniteSpanningSetsIn.prod (sfiniteSeq τ i.2).toFiniteSpanningSetsIn)
      ?_).symm
  rintro s hs _ ⟨t, ht, u, hu, rfl⟩; rw [mem_setOf_eq] at hs ht hu
  simp_rw [map_apply (MeasurableEquiv.measurable _) (hs.prod (ht.prod hu)),
    MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prod_assoc_preimage, prod_prod,
    mul_assoc]

/-! ### The product of specific measures -/

theorem prod_restrict (s : Set α) (t : Set β) :
    (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t) := by
  rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν, restrict_sum_of_countable, restrict_sum_of_countable,
    prod_sum, prod_sum, restrict_sum_of_countable]
  congr 1
  ext1 i
  refine prod_eq fun s' t' hs' ht' => ?_
  rw [restrict_apply (hs'.prod ht'), prod_inter_prod, prod_prod, restrict_apply hs',
    restrict_apply ht']

theorem restrict_prod_eq_prod_univ (s : Set α) :
    (μ.restrict s).prod ν = (μ.prod ν).restrict (s ×ˢ univ) := by
  have : ν = ν.restrict Set.univ := Measure.restrict_univ.symm
  rw [this, Measure.prod_restrict, ← this]

theorem prod_dirac (y : β) : μ.prod (dirac y) = map (fun x => (x, y)) μ := by
  classical
  rw [← sum_sfiniteSeq μ, prod_sum_left, map_sum measurable_prod_mk_right.aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  simp_rw [map_apply measurable_prod_mk_right (hs.prod ht), mk_preimage_prod_left_eq_if, measure_if,
    dirac_apply' _ ht, ← indicator_mul_right _ fun _ => sfiniteSeq μ i s, Pi.one_apply, mul_one]

theorem dirac_prod (x : α) : (dirac x).prod ν = map (Prod.mk x) ν := by
  classical
  rw [← sum_sfiniteSeq ν, prod_sum_right, map_sum measurable_prod_mk_left.aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  simp_rw [map_apply measurable_prod_mk_left (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
    dirac_apply' _ hs, ← indicator_mul_left _ _ fun _ => sfiniteSeq ν i t, Pi.one_apply, one_mul]

theorem dirac_prod_dirac {x : α} {y : β} : (dirac x).prod (dirac y) = dirac (x, y) := by
  rw [prod_dirac, map_dirac measurable_prod_mk_right]

theorem prod_add (ν' : Measure β) [SFinite ν'] : μ.prod (ν + ν') = μ.prod ν + μ.prod ν' := by
  simp_rw [← sum_sfiniteSeq ν, ← sum_sfiniteSeq ν', sum_add_sum, ← sum_sfiniteSeq μ, prod_sum,
    sum_add_sum]
  congr
  ext1 i
  refine prod_eq fun s t _ _ => ?_
  simp_rw [add_apply, prod_prod, left_distrib]

theorem add_prod (μ' : Measure α) [SFinite μ'] : (μ + μ').prod ν = μ.prod ν + μ'.prod ν := by
  simp_rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq μ', sum_add_sum, ← sum_sfiniteSeq ν, prod_sum,
    sum_add_sum]
  congr
  ext1 i
  refine prod_eq fun s t _ _ => ?_
  simp_rw [add_apply, prod_prod, right_distrib]

@[simp]
theorem zero_prod (ν : Measure β) : (0 : Measure α).prod ν = 0 := by
  rw [Measure.prod]
  exact bind_zero_left _

@[simp]
theorem prod_zero (μ : Measure α) : μ.prod (0 : Measure β) = 0 := by simp [Measure.prod]

theorem map_prod_map {δ} [MeasurableSpace δ] {f : α → β} {g : γ → δ} (μa : Measure α)
    (μc : Measure γ) [SFinite μa] [SFinite μc] (hf : Measurable f) (hg : Measurable g) :
    (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc) := by
  simp_rw [← sum_sfiniteSeq μa, ← sum_sfiniteSeq μc, map_sum hf.aemeasurable,
    map_sum hg.aemeasurable, prod_sum, map_sum (hf.prod_map hg).aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  rw [map_apply (hf.prod_map hg) (hs.prod ht), map_apply hf hs, map_apply hg ht]
  exact prod_prod (f ⁻¹' s) (g ⁻¹' t)


/-! ### The monoidal product in the Giry monad -/

-- theorem _root_.Measurable.measure_of_isPiSystem {μ : α → Measure β} [∀ a, IsFiniteMeasure (μ a)]
--     {S : Set (Set β)} (hgen : ‹MeasurableSpace β› = .generateFrom S) (hpi : IsPiSystem S)
--     (h_basic : ∀ s ∈ S, Measurable fun a ↦ μ a s) (h_univ : Measurable fun a ↦ μ a univ) :
--     Measurable μ := by
--   rw [measurable_measure]
--   intro s hs
--   induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
--   | empty => simp
--   | basic s hs => exact h_basic s hs
--   | compl s hsm ihs =>
--     simp only [measure_compl hsm (measure_ne_top _ _)]
--     exact h_univ.sub ihs
--   | iUnion f hfd hfm ihf =>
--     simpa only [measure_iUnion hfd hfm] using .ennreal_tsum ihf
--
-- theorem _root_.Measurable.measure_of_isPiSystem_of_isProbabilityMeasure {μ : α → Measure β}
--     [∀ a, IsProbabilityMeasure (μ a)]
--     {S : Set (Set β)} (hgen : ‹MeasurableSpace β› = .generateFrom S) (hpi : IsPiSystem S)
--     (h_basic : ∀ s ∈ S, Measurable fun a ↦ μ a s) : Measurable μ :=
--   .measure_of_isPiSystem hgen hpi h_basic <| by simp

abbrev ProbProduct (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :=
  { μ : Measure α × Measure β // IsProbabilityMeasure μ.1 ∧ IsProbabilityMeasure μ.2 }

abbrev monoidal_product (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    ProbProduct α β -> Measure (α × β) :=
  fun μ => Measure.prod (Subtype.val μ).1 (Subtype.val μ).2

local instance (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] (z : ProbProduct α β) :
    IsProbabilityMeasure (monoidal_product α β z) where
  measure_univ := by rcases z with ⟨_, ⟨_, _⟩⟩; simp

theorem measurable_monoidal_product : Measurable (monoidal_product α β) :=
  Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_prod.symm isPiSystem_prod <| by
    simp only [Set.mem_image2, forall_exists_index, and_imp]
    intros _ u Hu v Hv Heq
    let _ (a : ProbProduct α β) : SFinite a.val.2 := by rcases a with ⟨_, ⟨_, _⟩⟩; infer_instance
    rw [<- Heq, funext <| fun a => MeasureTheory.Measure.prod_prod u v]
    apply Measurable.mul
    · rw [<- comp_def (fun μ => μ u) (fun (μ : ProbProduct α β) => (Subtype.val μ).1),
          <- comp_def Prod.fst _]
      apply Measurable.comp (measurable_coe Hu) <|
            Measurable.comp measurable_fst measurable_subtype_coe
    · rw [<- comp_def (fun μ => μ v) (fun (μ : ProbProduct α β) => (Subtype.val μ).2),
          <- comp_def Prod.snd _]
      apply Measurable.comp (measurable_coe Hv) <|
            Measurable.comp measurable_snd measurable_subtype_coe


end Measure

open Measure

namespace MeasurePreserving

variable {δ : Type*} [MeasurableSpace δ] {μa : Measure α} {μb : Measure β} {μc : Measure γ}
  {μd : Measure δ}

/-- Let `f : α → β` be a measure preserving map.
For a.e. all `a`, let `g a : γ → δ` be a measure preserving map.
Also suppose that `g` is measurable as a function of two arguments.
Then the map `fun (a, c) ↦ (f a, g a c)` is a measure preserving map
for the product measures on `α × γ` and `β × δ`.

Some authors call a map of the form `fun (a, c) ↦ (f a, g a c)` a *skew product* over `f`,
thus the choice of a name.
-/
theorem skew_product [SFinite μa] [SFinite μc] {f : α → β} (hf : MeasurePreserving f μa μb)
    {g : α → γ → δ} (hgm : Measurable (uncurry g)) (hg : ∀ᵐ a ∂μa, map (g a) μc = μd) :
    MeasurePreserving (fun p : α × γ => (f p.1, g p.1 p.2)) (μa.prod μc) (μb.prod μd) := by
  have : Measurable fun p : α × γ => (f p.1, g p.1 p.2) := (hf.1.comp measurable_fst).prod_mk hgm
  use this
  /- if `μa = 0`, then the lemma is trivial, otherwise we can use `hg`
    to deduce `SFinite μd`. -/
  rcases eq_zero_or_neZero μa with rfl | _
  · simp [← hf.map_eq]
  have sf : SFinite μd := by
    obtain ⟨a, ha⟩ : ∃ a, map (g a) μc = μd := hg.exists
    rw [← ha]
    infer_instance
  -- Thus we can use the integral formula for the product measure, and compute things explicitly
  ext s hs
  rw [map_apply this hs, prod_apply (this hs), prod_apply hs,
    ← hf.lintegral_comp (measurable_measure_prod_mk_left hs)]
  apply lintegral_congr_ae
  filter_upwards [hg] with a ha
  rw [← ha, map_apply hgm.of_uncurry_left (measurable_prod_mk_left hs), preimage_preimage,
    preimage_preimage]

/-- If `f : α → β` sends the measure `μa` to `μb` and `g : γ → δ` sends the measure `μc` to `μd`,
then `Prod.map f g` sends `μa.prod μc` to `μb.prod μd`. -/
protected theorem prod [SFinite μa] [SFinite μc] {f : α → β} {g : γ → δ}
    (hf : MeasurePreserving f μa μb) (hg : MeasurePreserving g μc μd) :
    MeasurePreserving (Prod.map f g) (μa.prod μc) (μb.prod μd) :=
  have : Measurable (uncurry fun _ : α => g) := hg.1.comp measurable_snd
  hf.skew_product this <| ae_of_all _ fun _ => hg.map_eq

end MeasurePreserving

namespace QuasiMeasurePreserving

theorem prod_of_right {f : α × β → γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ}
    (hf : Measurable f) [SFinite ν]
    (h2f : ∀ᵐ x ∂μ, QuasiMeasurePreserving (fun y => f (x, y)) ν τ) :
    QuasiMeasurePreserving f (μ.prod ν) τ := by
  refine ⟨hf, ?_⟩
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  rw [map_apply hf hs, prod_apply (hf hs)]; simp_rw [preimage_preimage]
  rw [lintegral_congr_ae (h2f.mono fun x hx => hx.preimage_null h2s), lintegral_zero]

theorem prod_of_left {α β γ} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α × β → γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ} (hf : Measurable f)
    [SFinite μ] [SFinite ν]
    (h2f : ∀ᵐ y ∂ν, QuasiMeasurePreserving (fun x => f (x, y)) μ τ) :
    QuasiMeasurePreserving f (μ.prod ν) τ := by
  rw [← prod_swap]
  convert (QuasiMeasurePreserving.prod_of_right (hf.comp measurable_swap) h2f).comp
      ((measurable_swap.measurePreserving (ν.prod μ)).symm
          MeasurableEquiv.prodComm).quasiMeasurePreserving

end QuasiMeasurePreserving

end MeasureTheory

open MeasureTheory.Measure

section

theorem AEMeasurable.prod_swap [SFinite μ] [SFinite ν] {f : β × α → γ}
    (hf : AEMeasurable f (ν.prod μ)) : AEMeasurable (fun z : α × β => f z.swap) (μ.prod ν) := by
  rw [← Measure.prod_swap] at hf
  exact hf.comp_measurable measurable_swap

-- TODO: make this theorem usable with `fun_prop`
theorem AEMeasurable.fst [SFinite ν] {f : α → γ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun z : α × β => f z.1) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

-- TODO: make this theorem usable with `fun_prop`
theorem AEMeasurable.snd [SFinite ν] {f : β → γ} (hf : AEMeasurable f ν) :
    AEMeasurable (fun z : α × β => f z.2) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

end

namespace MeasureTheory

/-! ### The Lebesgue integral on a product -/


variable [SFinite ν]

theorem lintegral_prod_swap [SFinite μ] (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z.swap ∂ν.prod μ = ∫⁻ z, f z ∂μ.prod ν :=
  measurePreserving_swap.lintegral_comp_emb MeasurableEquiv.prodComm.measurableEmbedding f

/-- **Tonelli's Theorem**: For `ℝ≥0∞`-valued measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
theorem lintegral_prod_of_measurable :
    ∀ (f : α × β → ℝ≥0∞), Measurable f → ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  have m := @measurable_prod_mk_left
  refine Measurable.ennreal_induction
    (P := fun f => ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ) ?_ ?_ ?_
  · intro c s hs
    conv_rhs =>
      enter [2, x, 2, y]
      rw [← indicator_comp_right, const_def, const_comp, ← const_def]
    conv_rhs =>
      enter [2, x]
      rw [lintegral_indicator (m (x := x) hs), lintegral_const,
        Measure.restrict_apply MeasurableSet.univ, univ_inter]
    simp [hs, lintegral_const_mul, measurable_measure_prod_mk_left (ν := ν) hs, prod_apply]
  · rintro f g - hf _ h2f h2g
    simp only [Pi.add_apply]
    conv_lhs => rw [lintegral_add_left hf]
    conv_rhs => enter [2, x]; erw [lintegral_add_left (hf.comp (m (x := x)))]
    simp [lintegral_add_left, Measurable.lintegral_prod_right', hf, h2f, h2g]
  · intro f hf h2f h3f
    have kf : ∀ x n, Measurable fun y => f n (x, y) := fun x n => (hf n).comp m
    have k2f : ∀ x, Monotone fun n y => f n (x, y) := fun x i j hij y => h2f hij (x, y)
    have lf : ∀ n, Measurable fun x => ∫⁻ y, f n (x, y) ∂ν := fun n => (hf n).lintegral_prod_right'
    have l2f : Monotone fun n x => ∫⁻ y, f n (x, y) ∂ν := fun i j hij x =>
      lintegral_mono (k2f x hij)
    simp only [lintegral_iSup hf h2f, lintegral_iSup (kf _), k2f, lintegral_iSup lf l2f, h3f]

/-- **Tonelli's Theorem**: For `ℝ≥0∞`-valued almost everywhere measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
theorem lintegral_prod (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  have A : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ z, hf.mk f z ∂μ.prod ν := lintegral_congr_ae hf.ae_eq_mk
  have B : (∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ) = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂ν ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with _ ha using lintegral_congr_ae ha
  rw [A, B, lintegral_prod_of_measurable _ hf.measurable_mk]

/-- **Tonelli's Theorem for set integrals**: For `ℝ≥0∞`-valued almost everywhere measurable
  functions on `s ×ˢ t`, the integral of `f` on `s ×ˢ t` is equal to the iterated integral on `s`
  and `t` respectively. -/
theorem setLIntegral_prod [SFinite μ] {s : Set α} (t : Set β) (f : α × β → ENNReal)
    (hf : AEMeasurable f ((μ.prod ν).restrict (s ×ˢ t))) :
    ∫⁻ z in s ×ˢ t, f z ∂μ.prod ν = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂ν ∂μ := by
  rw [← Measure.prod_restrict, lintegral_prod _ (by rwa [Measure.prod_restrict])]

/-- The symmetric version of Tonelli's Theorem: For `ℝ≥0∞`-valued almost everywhere measurable
functions on `α × β`, the integral of `f` is equal to the iterated integral, in reverse order. -/
theorem lintegral_prod_symm [SFinite μ] (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  simp_rw [← lintegral_prod_swap f]
  exact lintegral_prod _ hf.prod_swap

/-- The symmetric version of Tonelli's Theorem: For `ℝ≥0∞`-valued measurable
functions on `α × β`, the integral of `f` is equal to the iterated integral, in reverse order. -/
theorem lintegral_prod_symm' [SFinite μ] (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
  lintegral_prod_symm f hf.aemeasurable

/-- The reversed version of **Tonelli's Theorem**. In this version `f` is in curried form, which
makes it easier for the elaborator to figure out `f` automatically. -/
theorem lintegral_lintegral ⦃f : α → β → ℝ≥0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.1 z.2 ∂μ.prod ν :=
  (lintegral_prod _ hf).symm

/-- The reversed version of **Tonelli's Theorem** (symmetric version). In this version `f` is in
curried form, which makes it easier for the elaborator to figure out `f` automatically. -/
theorem lintegral_lintegral_symm [SFinite μ] ⦃f : α → β → ℝ≥0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.2 z.1 ∂ν.prod μ :=
  (lintegral_prod_symm _ hf.prod_swap).symm

/-- Change the order of Lebesgue integration. -/
theorem lintegral_lintegral_swap [SFinite μ] ⦃f : α → β → ℝ≥0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν :=
  (lintegral_lintegral hf).trans (lintegral_prod_symm _ hf)

theorem lintegral_prod_mul {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g ν) : ∫⁻ z, f z.1 * g z.2 ∂μ.prod ν = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  simp [lintegral_prod _ (hf.fst.mul hg.snd), lintegral_lintegral_mul hf hg]

/-! ### Marginals of a measure defined on a product -/


namespace Measure

variable {ρ : Measure (α × β)}

/-- Marginal measure on `α` obtained from a measure `ρ` on `α × β`, defined by `ρ.map Prod.fst`. -/
noncomputable def fst (ρ : Measure (α × β)) : Measure α :=
  ρ.map Prod.fst

theorem fst_apply {s : Set α} (hs : MeasurableSet s) : ρ.fst s = ρ (Prod.fst ⁻¹' s) := by
  rw [fst, Measure.map_apply measurable_fst hs]

theorem fst_univ : ρ.fst univ = ρ univ := by rw [fst_apply MeasurableSet.univ, preimage_univ]

@[simp] theorem fst_zero : fst (0 : Measure (α × β)) = 0 := by simp [fst]

instance [SFinite ρ] : SFinite ρ.fst := by
  rw [fst]
  infer_instance

instance fst.instIsFiniteMeasure [IsFiniteMeasure ρ] : IsFiniteMeasure ρ.fst := by
  rw [fst]
  infer_instance

instance fst.instIsProbabilityMeasure [IsProbabilityMeasure ρ] : IsProbabilityMeasure ρ.fst where
  measure_univ := by
    rw [fst_univ]
    exact measure_univ

instance fst.instIsZeroOrProbabilityMeasure [IsZeroOrProbabilityMeasure ρ] :
    IsZeroOrProbabilityMeasure ρ.fst := by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, fst_zero]
    infer_instance
  · infer_instance

@[simp]
lemma fst_prod [IsProbabilityMeasure ν] : (μ.prod ν).fst = μ := by
  ext1 s hs
  rw [fst_apply hs, ← prod_univ, prod_prod, measure_univ, mul_one]

theorem fst_map_prod_mk₀ {X : α → β} {Y : α → γ} {μ : Measure α}
    (hY : AEMeasurable Y μ) : (μ.map fun a => (X a, Y a)).fst = μ.map X := by
  by_cases hX : AEMeasurable X μ
  · ext1 s hs
    rw [Measure.fst_apply hs, Measure.map_apply_of_aemeasurable (hX.prod_mk hY) (measurable_fst hs),
      Measure.map_apply_of_aemeasurable hX hs, ← prod_univ, mk_preimage_prod, preimage_univ,
      inter_univ]
  · have : ¬AEMeasurable (fun x ↦ (X x, Y x)) μ := by
      contrapose! hX; exact measurable_fst.comp_aemeasurable hX
    simp [map_of_not_aemeasurable, hX, this]

theorem fst_map_prod_mk {X : α → β} {Y : α → γ} {μ : Measure α}
    (hY : Measurable Y) : (μ.map fun a => (X a, Y a)).fst = μ.map X :=
  fst_map_prod_mk₀ hY.aemeasurable

@[simp]
lemma fst_add {μ ν : Measure (α × β)} : (μ + ν).fst = μ.fst + ν.fst := by
  ext s hs
  simp_rw [coe_add, Pi.add_apply, fst_apply hs, coe_add, Pi.add_apply]

lemma fst_sum {ι : Type*} (μ : ι → Measure (α × β)) : (sum μ).fst = sum (fun n ↦ (μ n).fst) := by
  ext s hs
  rw [fst_apply hs, sum_apply, sum_apply _ hs]
  · simp_rw [fst_apply hs]
  · exact measurable_fst hs

@[gcongr]
theorem fst_mono {μ : Measure (α × β)} (h : ρ ≤ μ) : ρ.fst ≤ μ.fst := map_mono h measurable_fst

/-- Marginal measure on `β` obtained from a measure on `ρ` `α × β`, defined by `ρ.map Prod.snd`. -/
noncomputable def snd (ρ : Measure (α × β)) : Measure β :=
  ρ.map Prod.snd

theorem snd_apply {s : Set β} (hs : MeasurableSet s) : ρ.snd s = ρ (Prod.snd ⁻¹' s) := by
  rw [snd, Measure.map_apply measurable_snd hs]

theorem snd_univ : ρ.snd univ = ρ univ := by rw [snd_apply MeasurableSet.univ, preimage_univ]

@[simp] theorem snd_zero : snd (0 : Measure (α × β)) = 0 := by simp [snd]

instance [SFinite ρ] : SFinite ρ.snd := by
  rw [snd]
  infer_instance

instance snd.instIsFiniteMeasure [IsFiniteMeasure ρ] : IsFiniteMeasure ρ.snd := by
  rw [snd]
  infer_instance

instance snd.instIsProbabilityMeasure [IsProbabilityMeasure ρ] : IsProbabilityMeasure ρ.snd where
  measure_univ := by
    rw [snd_univ]
    exact measure_univ

instance snd.instIsZeroOrProbabilityMeasure [IsZeroOrProbabilityMeasure ρ] :
    IsZeroOrProbabilityMeasure ρ.snd := by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, snd_zero]
    infer_instance
  · infer_instance

@[simp]
lemma snd_prod [IsProbabilityMeasure μ] : (μ.prod ν).snd = ν := by
  ext1 s hs
  rw [snd_apply hs, ← univ_prod, prod_prod, measure_univ, one_mul]

theorem snd_map_prod_mk₀ {X : α → β} {Y : α → γ} {μ : Measure α} (hX : AEMeasurable X μ) :
    (μ.map fun a => (X a, Y a)).snd = μ.map Y := by
  by_cases hY : AEMeasurable Y μ
  · ext1 s hs
    rw [Measure.snd_apply hs, Measure.map_apply_of_aemeasurable (hX.prod_mk hY) (measurable_snd hs),
      Measure.map_apply_of_aemeasurable hY hs, ← univ_prod, mk_preimage_prod, preimage_univ,
      univ_inter]
  · have : ¬AEMeasurable (fun x ↦ (X x, Y x)) μ := by
      contrapose! hY; exact measurable_snd.comp_aemeasurable hY
    simp [map_of_not_aemeasurable, hY, this]

theorem snd_map_prod_mk {X : α → β} {Y : α → γ} {μ : Measure α} (hX : Measurable X) :
    (μ.map fun a => (X a, Y a)).snd = μ.map Y :=
  snd_map_prod_mk₀ hX.aemeasurable

@[simp]
lemma snd_add {μ ν : Measure (α × β)} : (μ + ν).snd = μ.snd + ν.snd := by
  ext s hs
  simp_rw [coe_add, Pi.add_apply, snd_apply hs, coe_add, Pi.add_apply]

lemma snd_sum {ι : Type*} (μ : ι → Measure (α × β)) : (sum μ).snd = sum (fun n ↦ (μ n).snd) := by
  ext s hs
  rw [snd_apply hs, sum_apply, sum_apply _ hs]
  · simp_rw [snd_apply hs]
  · exact measurable_snd hs

@[gcongr]
theorem snd_mono {μ : Measure (α × β)} (h : ρ ≤ μ) : ρ.snd ≤ μ.snd := map_mono h measurable_snd

@[simp] lemma fst_map_swap : (ρ.map Prod.swap).fst = ρ.snd := by
  rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
  rfl

@[simp] lemma snd_map_swap : (ρ.map Prod.swap).snd = ρ.fst := by
  rw [Measure.snd, Measure.map_map measurable_snd measurable_swap]
  rfl

end Measure

section MeasurePreserving

-- Note that these results cannot be put in the previous `measurePreserving` section since
-- they use `lintegral_prod`.

/-- The measurable equiv induced by the equiv `(α × β) × γ ≃ α × (β × γ)` is measure preserving. -/
theorem _root_.MeasureTheory.measurePreserving_prodAssoc (μa : Measure α) (μb : Measure β)
    (μc : Measure γ) [SFinite μb] [SFinite μc] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ)
      ((μa.prod μb).prod μc) (μa.prod (μb.prod μc)) where
  measurable := MeasurableEquiv.prodAssoc.measurable
  map_eq := by
    ext s hs
    have A (x : α) : MeasurableSet (Prod.mk x ⁻¹' s) := measurable_prod_mk_left hs
    have B : MeasurableSet (MeasurableEquiv.prodAssoc ⁻¹' s) :=
      MeasurableEquiv.prodAssoc.measurable hs
    simp_rw [map_apply MeasurableEquiv.prodAssoc.measurable hs, prod_apply hs, prod_apply (A _),
      prod_apply B, lintegral_prod _ (measurable_measure_prod_mk_left B).aemeasurable]
    rfl

theorem _root_.MeasureTheory.volume_preserving_prodAssoc {α₁ β₁ γ₁ : Type*} [MeasureSpace α₁]
    [MeasureSpace β₁] [MeasureSpace γ₁] [SFinite (volume : Measure β₁)]
    [SFinite (volume : Measure γ₁)] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α₁ × β₁) × γ₁ ≃ᵐ α₁ × β₁ × γ₁) :=
  MeasureTheory.measurePreserving_prodAssoc volume volume volume

end MeasurePreserving

end MeasureTheory
