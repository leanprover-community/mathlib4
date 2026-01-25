/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.VectorMeasure.AddContent
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Vector valued Stieltjes measure associated to a bounded variation function

Let `α` be a dense linear order with compact segments (e.g. `ℝ` or `ℝ≥0`), and `f : α → E` a
bounded variation function to a normed group.
We associate to `f` a vector measure, called `BoundedVariationOn.vectorMeasure`. It gives
mass `f.rightLim b - f.leftLim a` to the interval `[a, b]` (with similar formulas for
other types of intervals).

For the construction, we define first a content on the set of open-closed intervals `(a, b]`,
mapping this interval to `f.rightLim b - f.rightLim a`. To extend this content to the whole
sigma-algebra, we show that it is dominated by a finite measure, the Stieltjes measure associated
to the variation of `f.rightLim`. This extension is not exactly the desired limit, as we need to
tweak things if there is a bot element `a`: the previous measure gives to `{a}` the mass `0` instead
of the desired `f.rightLim a - f a`, so we add a Dirac mass to correct this defect.
-/

@[expose] public section

open Filter Set MeasureTheory MeasurableSpace MeasureTheory
open scoped symmDiff Topology NNReal ENNReal

variable {α : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
  [SecondCountableTopology α] [CompactIccSpace α] [hα : MeasurableSpace α] [BorelSpace α]
  {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  {f : α → E} {a b : α}

namespace BoundedVariationOn

/-- The Stieltjes function associated to a bounded variation function. It is given by
the variation of the function `f.rightLim` from a fixed base point.
Using right limits ensures the right continuity, which is used to construct Sieltjes measures. -/
@[simps] noncomputable def stieltjesFunctionRightLim
    (hf : BoundedVariationOn f univ) (x₀ : α) : StieltjesFunction α where
  toFun x := variationOnFromTo f.rightLim univ x₀ x
  mono' := by
    rw [← monotoneOn_univ]
    exact variationOnFromTo.monotoneOn hf.rightLim.locallyBoundedVariationOn (mem_univ _)
  right_continuous' x := hf.continuousWithinAt_variationOnFromTo_rightLim_Ici

open scoped Classical in
/-- Auxiliary measure used to construct the vector measure associated to a bounded variation
function. This is *not* the total variation of this measure in general, as we need to adjust things
when there is a bot element by adding a Dirac mass there. -/
noncomputable def measureAux (hf : BoundedVariationOn f univ) : Measure α :=
  if h : Nonempty α then (hf.stieltjesFunctionRightLim h.some).measure else 0

instance (hf : BoundedVariationOn f univ) : IsFiniteMeasure hf.measureAux := by
  by_cases h : Nonempty α; swap
  · simp only [BoundedVariationOn.measureAux, h, ↓reduceDIte]
    infer_instance
  simp only [BoundedVariationOn.measureAux, h, ↓reduceDIte]
  apply StieltjesFunction.isFiniteMeasure_of_forall_abs_le
    (C := (eVariationOn f.rightLim univ).toReal) _ (fun x ↦ ?_)
  exact variationOnFromTo.abs_le_eVariationOn hf.rightLim

/-- Given a bounded variation function `f`, we can construct a vector measure giving
mass `f.rightLim v - f.rightLim a` to each open-closed interval `(a, b]`. This is *not* the
measure associated to `f` in general, as we may need to adjust things at the bot element if
there is one. -/
lemma exists_vectorMeasure_le_measureAux (hf : BoundedVariationOn f univ) :
    ∃ m : VectorMeasure α E, (∀ u v, u ≤ v → m (Set.Ioc u v) = f.rightLim v - f.rightLim u) ∧
      m botSet = 0 ∧ ∀ s, ‖m s‖ₑ ≤ hf.measureAux s := by
  rcases isEmpty_or_nonempty α with h'α | h'α
  · exact ⟨0, by simp⟩
  let m := AddContent.onIoc f.rightLim
  have A : ∀ s ∈ {s | ∃ u v, u ≤ v ∧ s = Ioc u v}, ‖m s‖ₑ ≤ hf.measureAux s := by
    rintro s ⟨u, v, huv, rfl⟩
    rw [AddContent.onIoc_apply huv]
    simp only [BoundedVariationOn.measureAux, h'α, ↓reduceDIte, StieltjesFunction.measure_Ioc,
      BoundedVariationOn.stieltjesFunctionRightLim_apply]
    rw [← variationOnFromTo.add hf.rightLim.locallyBoundedVariationOn
      (mem_univ h'α.some) (mem_univ u) (mem_univ v)]
    simp only [add_sub_cancel_left, variationOnFromTo, huv, ↓reduceIte, univ_inter]
    rw [ENNReal.ofReal_toReal]; swap
    · exact ((eVariationOn.mono _ (subset_univ _)).trans_lt hf.rightLim.lt_top).ne
    rw [← edist_eq_enorm_sub]
    exact eVariationOn.edist_le _ (by grind) (by grind)
  have B : hα = generateFrom {s | ∃ u v, u ≤ v ∧ s = Ioc u v} := by
    borelize α
    convert borel_eq_generateFrom_Ioc_le α using 2
    grind only
  have C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ {s | ∃ u v, u ≤ v ∧ s = Ioc u v}
      ∧ hf.measureAux (⋃₀ D)ᶜ = 0 := by
    obtain ⟨s, s_count, s_dense, s_bot, s_top⟩ :
        ∃ s, s.Countable ∧ Dense s ∧ (∀ (x : α), IsBot x → x ∈ s) ∧ ∀ (x : α), IsTop x → x ∈ s :=
      exists_countable_dense_bot_top α
    let D := {t : Set α | ∃ u v, u ≤ v ∧ t = Ioc u v ∧ u ∈ s ∧ v ∈ s}
    refine ⟨D, ?_, by grind, ?_⟩
    · have : D ⊆ (fun (p : α × α) ↦ Ioc p.1 p.2) '' (s ×ˢ s) := by
        rintro - ⟨u, v, -, rfl, us, vs⟩
        exact mem_image_of_mem (x := (u, v)) _ (by simp [us, vs])
      exact Countable.mono this ((s_count.prod s_count).image _)
    have : (⋃₀ D)ᶜ ⊆ botSet := by
      rw [compl_subset_comm, botSet]
      intro x hx
      simp only [mem_sUnion]
      obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, y < x := by
        have : (Iio x).Nonempty := by simpa [IsBot] using hx
        exact s_dense.exists_mem_open isOpen_Iio this
      by_cases h'x : IsTop x
      · exact ⟨Ioc y x, ⟨y, x, hy.le, rfl, ys, s_top _ h'x⟩, ⟨hy, le_rfl⟩⟩
      obtain ⟨z, zs, hz⟩ : ∃ z ∈ s, x < z := by
        have : (Ioi x).Nonempty := by simpa [IsTop] using h'x
        exact s_dense.exists_mem_open isOpen_Ioi this
      exact ⟨Ioc y z, ⟨y, z, (hy.trans hz).le, rfl, ys, zs⟩, ⟨hy, hz.le⟩⟩
    exact measure_mono_null this (by simp [measureAux, h'α])
  rcases VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom
    IsSetSemiring.Ioc A B C with ⟨m', hm', h'm'⟩
  refine ⟨m', fun u v huv ↦ ?_, ?_, h'm'⟩
  · rw [hm']
    · exact AddContent.onIoc_apply huv
    · exact ⟨u, v, huv, rfl⟩
  · apply enorm_eq_zero.1
    apply le_bot_iff.1
    exact (h'm' _).trans (by simp [measureAux, h'α])

open scoped Classical in
/-- The vector measure associated to a bounded variation function `f`, giving mass
`f.rightLim b - f.leftLim a` to closed intervals `[a, b]`, and similarly for other intervals. -/
noncomputable irreducible_def vectorMeasure (hf : BoundedVariationOn f univ) : VectorMeasure α E :=
  hf.exists_vectorMeasure_le_measureAux.choose +
  (if h : ∃ x, IsBot x then VectorMeasure.dirac h.choose (f.rightLim h.choose - f h.choose) else 0)

lemma vectorMeasure_Ioc (hf : BoundedVariationOn f univ) (h : a ≤ b) :
    hf.vectorMeasure (Ioc a b) = f.rightLim b - f.rightLim a := by
  classical
  have A : hf.exists_vectorMeasure_le_measureAux.choose (Ioc a b) =
      f.rightLim b - f.rightLim a :=
    hf.exists_vectorMeasure_le_measureAux.choose_spec.1 a b h
  have B : (if hx : ∃ (x : α), IsBot x then VectorMeasure.dirac hx.choose
      (f.rightLim hx.choose - f hx.choose) else 0) (Ioc a b) = 0 := by
    by_cases hx : ∃ (x : α), IsBot x
    · simp only [hx, ↓reduceDIte]
      rw [VectorMeasure.dirac_apply_of_notMem]
      simp only [mem_Ioc, not_and_or, not_lt, not_le]
      exact Or.inl (hx.choose_spec _)
    · simp [hx]
  simp [vectorMeasure, A, B]

lemma vectorMeasure_singleton (hf : BoundedVariationOn f univ) :
    hf.vectorMeasure {a} = f.rightLim a - f.leftLim a := by
  by_cases ha : IsBot a
  · have h : ∃ x, IsBot x := ⟨a, ha⟩
    have heqa : h.choose = a := by
      have := h.choose_spec
      apply subsingleton_isBot _ h.choose_spec ha
    have A : hf.exists_vectorMeasure_le_measureAux.choose {a} = 0 := by
      rw [← botSet_eq_singleton_of_isBot ha]
      exact hf.exists_vectorMeasure_le_measureAux.choose_spec.2.1
    simp only [vectorMeasure, h, ↓reduceDIte, VectorMeasure.coe_add, Pi.add_apply, A,
      zero_add]
    rw [VectorMeasure.dirac_apply_of_mem (MeasurableSet.singleton a)]
    · simpa only [heqa, sub_right_inj] using (leftLim_eq_of_isBot ha).symm
    · simp [heqa]
  obtain ⟨b, hb⟩ : ∃ b, b < a := by simpa only [IsBot, not_forall, not_le] using ha
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n : ℕ, u n ∈ Ioo b a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto' hb
  replace u_lt_a n : u n < a := (u_lt_a n).2
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine Subset.antisymm (fun x hx => by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx => ?_
    replace hx : ∀ (i : ℕ), u i < x ∧ x ≤ a := by simpa using hx
    have : a ≤ x := le_of_tendsto' u_lim fun n => (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n ↦ hf.vectorMeasure (Ioc (u n) a)) atTop (𝓝 (hf.vectorMeasure {a})) := by
    rw [A]
    apply VectorMeasure.tendsto_vectorMeasure_iInter_atTop_nat ?_ (fun n ↦ measurableSet_Ioc)
    exact fun m n hmn ↦ Ioc_subset_Ioc_left (u_mono.monotone hmn)
  have L2 : Tendsto (fun n ↦ hf.vectorMeasure (Ioc (u n) a)) atTop
      (𝓝 (f.rightLim a - f.leftLim a)) := by
    simp_rw [hf.vectorMeasure_Ioc (u_lt_a _).le]
    apply tendsto_const_nhds.sub
    have : Tendsto u atTop (𝓝[<] a) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      u_lim (Eventually.of_forall u_lt_a)
    convert (hf.rightLim.tendsto_leftLim a).comp this using 2
    have : (𝓝[<] a).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' ⟨b, hb⟩]
      exact self_mem_Iic
    exact (leftLim_rightLim (hf.tendsto_leftLim _)).symm
  exact tendsto_nhds_unique L1 L2

lemma vectorMeasure_Icc (hf : BoundedVariationOn f univ) (h : a ≤ b) :
    hf.vectorMeasure (Icc a b) = f.rightLim b - f.leftLim a := by
  rw [← Icc_union_Ioc_eq_Icc le_rfl h, VectorMeasure.of_union (by simp)
    measurableSet_Icc measurableSet_Ioc, Icc_self, hf.vectorMeasure_singleton,
    hf.vectorMeasure_Ioc h]
  simp

theorem vectorMeasure_Ioo (hf : BoundedVariationOn f univ) (h : a < b) :
    hf.vectorMeasure (Ioo a b) = f.leftLim b - f.rightLim a := by
  have := hf.vectorMeasure_Ioc h.le
  rw [← Ioo_union_Icc_eq_Ioc h le_rfl, VectorMeasure.of_union (by simp) measurableSet_Ioo
    measurableSet_Icc, hf.vectorMeasure_Icc le_rfl] at this
  grind

theorem vectorMeasure_Ico (hf : BoundedVariationOn f univ) (h : a ≤ b) :
    hf.vectorMeasure (Ico a b) = f.leftLim b - f.leftLim a := by
  rcases h.eq_or_lt with rfl | h'
  · simp
  rw [← Icc_union_Ioo_eq_Ico le_rfl h', VectorMeasure.of_union (by simp) measurableSet_Icc
    measurableSet_Ioo, hf.vectorMeasure_Icc le_rfl, hf.vectorMeasure_Ioo h']
  abel

end BoundedVariationOn
