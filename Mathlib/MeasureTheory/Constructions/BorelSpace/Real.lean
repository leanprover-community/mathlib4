/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Borel (measurable) spaces ℝ, ℝ≥0, ℝ≥0∞

## Main statements

* `borel_eq_generateFrom_Ixx_rat` (where Ixx is one of {Ioo, Ioi, Iio, Ici, Iic):
  the Borel sigma algebra on ℝ is generated by intervals with rational endpoints;
* `isPiSystem_Ixx_rat` (where Ixx is one of {Ioo, Ioi, Iio, Ici, Iic):
  intervals with rational endpoints form a pi system on ℝ;
* `measurable_real_toNNReal`, `measurable_coe_nnreal_real`, `measurable_coe_nnreal_ennreal`,
  `ENNReal.measurable_ofReal`, `ENNReal.measurable_toReal`:
  measurability of various coercions between ℝ, ℝ≥0, and ℝ≥0∞;
* `Measurable.real_toNNReal`, `Measurable.coe_nnreal_real`, `Measurable.coe_nnreal_ennreal`,
  `Measurable.ennreal_ofReal`, `Measurable.ennreal_toNNReal`, `Measurable.ennreal_toReal`:
  measurability of functions composed with various coercions between ℝ, ℝ≥0, and ℝ≥0∞
  (also similar results for a.e.-measurability);
* `Measurable.ennreal*` : measurability of special cases for arithmetic operations on `ℝ≥0∞`.
-/

open Set Filter MeasureTheory MeasurableSpace

open scoped Topology NNReal ENNReal

universe u v w x y

variable {α β γ δ : Type*} {ι : Sort y} {s t u : Set α}

namespace Real

theorem borel_eq_generateFrom_Ioo_rat :
    borel ℝ = .generateFrom (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) (b : ℝ)}) :=
  isTopologicalBasis_Ioo_rat.borel_eq_generateFrom

theorem borel_eq_generateFrom_Iio_rat : borel ℝ = .generateFrom (⋃ a : ℚ, {Iio (a : ℝ)}) := by
  rw [borel_eq_generateFrom_Iio]
  refine le_antisymm
    (generateFrom_le ?_)
    (generateFrom_mono <| iUnion_subset fun q ↦ singleton_subset_iff.mpr <| mem_range_self _)
  rintro _ ⟨a, rfl⟩
  have : IsLUB (range ((↑) : ℚ → ℝ) ∩ Iio a) a := by
    simp [isLUB_iff_le_iff, mem_upperBounds, ← le_iff_forall_rat_lt_imp_le]
  rw [← this.biUnion_Iio_eq, ← image_univ, ← image_inter_preimage, univ_inter, biUnion_image]
  exact MeasurableSet.biUnion (to_countable _)
    fun b _ => GenerateMeasurable.basic (Iio (b : ℝ)) (by simp)

theorem borel_eq_generateFrom_Ioi_rat : borel ℝ = .generateFrom (⋃ a : ℚ, {Ioi (a : ℝ)}) := by
  rw [borel_eq_generateFrom_Ioi]
  refine le_antisymm
    (generateFrom_le ?_)
    (generateFrom_mono <| iUnion_subset fun q ↦ singleton_subset_iff.mpr <| mem_range_self _)
  rintro _ ⟨a, rfl⟩
  have : IsGLB (range ((↑) : ℚ → ℝ) ∩ Ioi a) a := by
    simp [isGLB_iff_le_iff, mem_lowerBounds, ← le_iff_forall_lt_rat_imp_le]
  rw [← this.biUnion_Ioi_eq, ← image_univ, ← image_inter_preimage, univ_inter, biUnion_image]
  exact MeasurableSet.biUnion (to_countable _)
    fun b _ => GenerateMeasurable.basic (Ioi (b : ℝ)) (by simp)

theorem borel_eq_generateFrom_Iic_rat : borel ℝ = .generateFrom (⋃ a : ℚ, {Iic (a : ℝ)}) := by
  rw [borel_eq_generateFrom_Ioi_rat, iUnion_singleton_eq_range, iUnion_singleton_eq_range]
  refine le_antisymm (generateFrom_le ?_) (generateFrom_le ?_) <;>
  rintro _ ⟨q, rfl⟩ <;>
  dsimp only <;>
  [rw [← compl_Iic]; rw [← compl_Ioi]] <;>
  exact MeasurableSet.compl (GenerateMeasurable.basic _ (mem_range_self q))

theorem borel_eq_generateFrom_Ici_rat : borel ℝ = .generateFrom (⋃ a : ℚ, {Ici (a : ℝ)}) := by
  rw [borel_eq_generateFrom_Iio_rat, iUnion_singleton_eq_range, iUnion_singleton_eq_range]
  refine le_antisymm (generateFrom_le ?_) (generateFrom_le ?_) <;>
  rintro _ ⟨q, rfl⟩ <;>
  dsimp only <;>
  [rw [← compl_Ici]; rw [← compl_Iio]] <;>
  exact MeasurableSet.compl (GenerateMeasurable.basic _ (mem_range_self q))

theorem isPiSystem_Ioo_rat :
    IsPiSystem (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) (b : ℝ)}) := by
  convert isPiSystem_Ioo ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)
  ext x
  simp [eq_comm]

theorem isPiSystem_Iio_rat : IsPiSystem (⋃ a : ℚ, {Iio (a : ℝ)}) := by
  convert isPiSystem_image_Iio (((↑) : ℚ → ℝ) '' univ)
  ext x
  simp only [iUnion_singleton_eq_range, mem_range, image_univ, mem_image, exists_exists_eq_and]

theorem isPiSystem_Ioi_rat : IsPiSystem (⋃ a : ℚ, {Ioi (a : ℝ)}) := by
  convert isPiSystem_image_Ioi (((↑) : ℚ → ℝ) '' univ)
  ext x
  simp only [iUnion_singleton_eq_range, mem_range, image_univ, mem_image, exists_exists_eq_and]

theorem isPiSystem_Iic_rat : IsPiSystem (⋃ a : ℚ, {Iic (a : ℝ)}) := by
  convert isPiSystem_image_Iic (((↑) : ℚ → ℝ) '' univ)
  ext x
  simp only [iUnion_singleton_eq_range, mem_range, image_univ, mem_image, exists_exists_eq_and]

theorem isPiSystem_Ici_rat : IsPiSystem (⋃ a : ℚ, {Ici (a : ℝ)}) := by
  convert isPiSystem_image_Ici (((↑) : ℚ → ℝ) '' univ)
  ext x
  simp only [iUnion_singleton_eq_range, mem_range, image_univ, mem_image, exists_exists_eq_and]

/-- The intervals `(-(n + 1), (n + 1))` form a finite spanning sets in the set of open intervals
with rational endpoints for a locally finite measure `μ` on `ℝ`. -/
def finiteSpanningSetsInIooRat (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) (b : ℝ)}) where
  set n := Ioo (-(n + 1)) (n + 1)
  set_mem n := by
    simp only [mem_iUnion, mem_singleton_iff]
    refine ⟨-(n + 1 : ℕ), n + 1, ?_, by simp⟩
    -- TODO: norm_cast fails here?
    push_cast
    exact neg_lt_self n.cast_add_one_pos
  finite _ := measure_Ioo_lt_top
  spanning :=
    iUnion_eq_univ_iff.2 fun x =>
      ⟨⌊|x|⌋₊, neg_lt.1 ((neg_le_abs x).trans_lt (Nat.lt_floor_add_one _)),
        (le_abs_self x).trans_lt (Nat.lt_floor_add_one _)⟩

theorem measure_ext_Ioo_rat {μ ν : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (h : ∀ a b : ℚ, μ (Ioo a b) = ν (Ioo a b)) : μ = ν :=
  (finiteSpanningSetsInIooRat μ).ext borel_eq_generateFrom_Ioo_rat isPiSystem_Ioo_rat <| by
    simp only [mem_iUnion, mem_singleton_iff]
    rintro _ ⟨a, b, -, rfl⟩
    apply h

end Real

variable {mα : MeasurableSpace α}

@[measurability, fun_prop]
theorem measurable_real_toNNReal : Measurable Real.toNNReal :=
  continuous_real_toNNReal.measurable

@[measurability, fun_prop]
theorem Measurable.real_toNNReal {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x => Real.toNNReal (f x) :=
  measurable_real_toNNReal.comp hf

@[measurability, fun_prop]
theorem AEMeasurable.real_toNNReal {f : α → ℝ} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => Real.toNNReal (f x)) μ :=
  measurable_real_toNNReal.comp_aemeasurable hf

@[measurability]
theorem measurable_coe_nnreal_real : Measurable ((↑) : ℝ≥0 → ℝ) :=
  NNReal.continuous_coe.measurable

@[measurability, fun_prop]
theorem Measurable.coe_nnreal_real {f : α → ℝ≥0} (hf : Measurable f) :
    Measurable fun x => (f x : ℝ) :=
  measurable_coe_nnreal_real.comp hf

@[measurability, fun_prop]
theorem AEMeasurable.coe_nnreal_real {f : α → ℝ≥0} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x : ℝ)) μ :=
  measurable_coe_nnreal_real.comp_aemeasurable hf

@[measurability]
theorem measurable_coe_nnreal_ennreal : Measurable ((↑) : ℝ≥0 → ℝ≥0∞) :=
  ENNReal.continuous_coe.measurable

@[measurability, fun_prop]
theorem Measurable.coe_nnreal_ennreal {f : α → ℝ≥0} (hf : Measurable f) :
    Measurable fun x => (f x : ℝ≥0∞) :=
  ENNReal.continuous_coe.measurable.comp hf

@[measurability, fun_prop]
theorem AEMeasurable.coe_nnreal_ennreal {f : α → ℝ≥0} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x : ℝ≥0∞)) μ :=
  ENNReal.continuous_coe.measurable.comp_aemeasurable hf

@[measurability, fun_prop]
theorem Measurable.ennreal_ofReal {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x => ENNReal.ofReal (f x) :=
  ENNReal.continuous_ofReal.measurable.comp hf

@[measurability, fun_prop]
lemma AEMeasurable.ennreal_ofReal {f : α → ℝ} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ ENNReal.ofReal (f x)) μ :=
  ENNReal.continuous_ofReal.measurable.comp_aemeasurable hf

@[simp, norm_cast]
theorem measurable_coe_nnreal_real_iff {f : α → ℝ≥0} :
    Measurable (fun x => f x : α → ℝ) ↔ Measurable f :=
  ⟨fun h => by simpa only [Real.toNNReal_coe] using h.real_toNNReal, Measurable.coe_nnreal_real⟩

@[simp, norm_cast]
theorem aemeasurable_coe_nnreal_real_iff {f : α → ℝ≥0} {μ : Measure α} :
    AEMeasurable (fun x => f x : α → ℝ) μ ↔ AEMeasurable f μ :=
  ⟨fun h ↦ by simpa only [Real.toNNReal_coe] using h.real_toNNReal, AEMeasurable.coe_nnreal_real⟩

/-- The set of finite `ℝ≥0∞` numbers is `MeasurableEquiv` to `ℝ≥0`. -/
def MeasurableEquiv.ennrealEquivNNReal : { r : ℝ≥0∞ | r ≠ ∞ } ≃ᵐ ℝ≥0 :=
  ENNReal.neTopHomeomorphNNReal.toMeasurableEquiv

namespace ENNReal

theorem measurable_of_measurable_nnreal {f : ℝ≥0∞ → α} (h : Measurable fun p : ℝ≥0 => f p) :
    Measurable f :=
  measurable_of_measurable_on_compl_singleton ∞
    (MeasurableEquiv.ennrealEquivNNReal.symm.measurable_comp_iff.1 h)

/-- `ℝ≥0∞` is `MeasurableEquiv` to `ℝ≥0 ⊕ Unit`. -/
def ennrealEquivSum : ℝ≥0∞ ≃ᵐ ℝ≥0 ⊕ Unit :=
  { Equiv.optionEquivSumPUnit ℝ≥0 with
    measurable_toFun := measurable_of_measurable_nnreal measurable_inl
    measurable_invFun :=
      measurable_sum measurable_coe_nnreal_ennreal (@measurable_const ℝ≥0∞ Unit _ _ ∞) }

open Function (uncurry)

theorem measurable_of_measurable_nnreal_prod {_ : MeasurableSpace β} {_ : MeasurableSpace γ}
    {f : ℝ≥0∞ × β → γ} (H₁ : Measurable fun p : ℝ≥0 × β => f (p.1, p.2))
    (H₂ : Measurable fun x => f (∞, x)) : Measurable f :=
  let e : ℝ≥0∞ × β ≃ᵐ (ℝ≥0 × β) ⊕ (Unit × β) :=
    (ennrealEquivSum.prodCongr (MeasurableEquiv.refl β)).trans
      (MeasurableEquiv.sumProdDistrib _ _ _)
  e.symm.measurable_comp_iff.1 <| measurable_sum H₁ (H₂.comp measurable_id.snd)

theorem measurable_of_measurable_nnreal_nnreal {_ : MeasurableSpace β} {f : ℝ≥0∞ × ℝ≥0∞ → β}
    (h₁ : Measurable fun p : ℝ≥0 × ℝ≥0 => f (p.1, p.2)) (h₂ : Measurable fun r : ℝ≥0 => f (∞, r))
    (h₃ : Measurable fun r : ℝ≥0 => f (r, ∞)) : Measurable f :=
  measurable_of_measurable_nnreal_prod
    (measurable_swap_iff.1 <| measurable_of_measurable_nnreal_prod (h₁.comp measurable_swap) h₃)
    (measurable_of_measurable_nnreal h₂)

@[measurability]
theorem measurable_ofReal : Measurable ENNReal.ofReal :=
  ENNReal.continuous_ofReal.measurable

@[measurability]
theorem measurable_toReal : Measurable ENNReal.toReal :=
  ENNReal.measurable_of_measurable_nnreal measurable_coe_nnreal_real

@[measurability]
theorem measurable_toNNReal : Measurable ENNReal.toNNReal :=
  ENNReal.measurable_of_measurable_nnreal measurable_id

instance instMeasurableMul₂ : MeasurableMul₂ ℝ≥0∞ := by
  refine ⟨measurable_of_measurable_nnreal_nnreal ?_ ?_ ?_⟩
  · simp only [← ENNReal.coe_mul, measurable_mul.coe_nnreal_ennreal]
  · simp only [ENNReal.top_mul', ENNReal.coe_eq_zero]
    exact measurable_const.piecewise (measurableSet_singleton _) measurable_const
  · simp only [ENNReal.mul_top', ENNReal.coe_eq_zero]
    exact measurable_const.piecewise (measurableSet_singleton _) measurable_const

instance instMeasurableSub₂ : MeasurableSub₂ ℝ≥0∞ :=
  ⟨by
    apply measurable_of_measurable_nnreal_nnreal <;>
      simp [← WithTop.coe_sub, tsub_eq_zero_of_le];
        exact continuous_sub.measurable.coe_nnreal_ennreal⟩

instance instMeasurableInv : MeasurableInv ℝ≥0∞ :=
  ⟨continuous_inv.measurable⟩

instance : MeasurableSMul ℝ≥0 ℝ≥0∞ where
  measurable_const_smul := by
    simp_rw [ENNReal.smul_def]
    exact fun _ ↦ MeasurableSMul.measurable_const_smul _
  measurable_smul_const := fun x ↦ by
    simp_rw [ENNReal.smul_def]
    exact measurable_coe_nnreal_ennreal.mul_const _

/-- A limit (over a general filter) of measurable `ℝ≥0∞` valued functions is measurable. -/
theorem measurable_of_tendsto' {ι : Type*} {f : ι → α → ℝ≥0∞} {g : α → ℝ≥0∞} (u : Filter ι)
    [NeBot u] [IsCountablyGenerated u] (hf : ∀ i, Measurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    Measurable g := by
  rcases u.exists_seq_tendsto with ⟨x, hx⟩
  rw [tendsto_pi_nhds] at lim
  have : (fun y => liminf (fun n => (f (x n) y : ℝ≥0∞)) atTop) = g := by
    ext1 y
    exact ((lim y).comp hx).liminf_eq
  rw [← this]
  show Measurable fun y => liminf (fun n => (f (x n) y : ℝ≥0∞)) atTop
  exact .liminf fun n => hf (x n)

/-- A sequential limit of measurable `ℝ≥0∞` valued functions is measurable. -/
theorem measurable_of_tendsto {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto' atTop hf lim

/-- A limit (over a general filter) of a.e.-measurable `ℝ≥0∞` valued functions is
a.e.-measurable. -/
lemma aemeasurable_of_tendsto' {ι : Type*} {f : ι → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    {μ : Measure α} (u : Filter ι) [NeBot u] [IsCountablyGenerated u]
    (hf : ∀ i, AEMeasurable (f i) μ) (hlim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) u (𝓝 (g a))) :
    AEMeasurable g μ := by
  rcases u.exists_seq_tendsto with ⟨v, hv⟩
  have h'f : ∀ n, AEMeasurable (f (v n)) μ := fun n ↦ hf (v n)
  set p : α → (ℕ → ℝ≥0∞) → Prop := fun x f' ↦ Tendsto f' atTop (𝓝 (g x))
  have hp : ∀ᵐ x ∂μ, p x fun n ↦ f (v n) x := by
    filter_upwards [hlim] with x hx using hx.comp hv
  classical
  set aeSeqLim := fun x ↦ ite (x ∈ aeSeqSet h'f p) (g x) (⟨f (v 0) x⟩ : Nonempty ℝ≥0∞).some
  refine ⟨aeSeqLim, measurable_of_tendsto' atTop (aeSeq.measurable h'f p)
    (tendsto_pi_nhds.mpr fun x ↦ ?_), ?_⟩
  · unfold aeSeqLim
    simp_rw [aeSeq]
    split_ifs with hx
    · simp_rw [aeSeq.mk_eq_fun_of_mem_aeSeqSet h'f hx]
      exact aeSeq.fun_prop_of_mem_aeSeqSet h'f hx
    · exact tendsto_const_nhds
  · exact (ite_ae_eq_of_measure_compl_zero g (fun x ↦ (⟨f (v 0) x⟩ : Nonempty ℝ≥0∞).some)
      (aeSeqSet h'f p) (aeSeq.measure_compl_aeSeqSet_eq_zero h'f hp)).symm

/-- A limit of a.e.-measurable `ℝ≥0∞` valued functions is a.e.-measurable. -/
lemma aemeasurable_of_tendsto {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞} {μ : Measure α}
    (hf : ∀ i, AEMeasurable (f i) μ) (hlim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (g a))) :
    AEMeasurable g μ :=
  aemeasurable_of_tendsto' atTop hf hlim

end ENNReal

@[measurability, fun_prop]
theorem Measurable.ennreal_toNNReal {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x => (f x).toNNReal :=
  ENNReal.measurable_toNNReal.comp hf

@[measurability, fun_prop]
theorem AEMeasurable.ennreal_toNNReal {f : α → ℝ≥0∞} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x).toNNReal) μ :=
  ENNReal.measurable_toNNReal.comp_aemeasurable hf

@[simp, norm_cast]
theorem measurable_coe_nnreal_ennreal_iff {f : α → ℝ≥0} :
    (Measurable fun x => (f x : ℝ≥0∞)) ↔ Measurable f :=
  ⟨fun h => h.ennreal_toNNReal, fun h => h.coe_nnreal_ennreal⟩

@[simp, norm_cast]
theorem aemeasurable_coe_nnreal_ennreal_iff {f : α → ℝ≥0} {μ : Measure α} :
    AEMeasurable (fun x => (f x : ℝ≥0∞)) μ ↔ AEMeasurable f μ :=
  ⟨fun h => h.ennreal_toNNReal, fun h => h.coe_nnreal_ennreal⟩

@[measurability, fun_prop]
theorem Measurable.ennreal_toReal {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x => ENNReal.toReal (f x) :=
  ENNReal.measurable_toReal.comp hf

@[measurability, fun_prop]
theorem AEMeasurable.ennreal_toReal {f : α → ℝ≥0∞} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => ENNReal.toReal (f x)) μ :=
  ENNReal.measurable_toReal.comp_aemeasurable hf

/-- note: `ℝ≥0∞` can probably be generalized in a future version of this lemma. -/
@[measurability, fun_prop]
theorem Measurable.ennreal_tsum {ι} [Countable ι] {f : ι → α → ℝ≥0∞} (h : ∀ i, Measurable (f i)) :
    Measurable fun x => ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact .iSup fun s ↦ s.measurable_sum fun i _ => h i

@[measurability, fun_prop]
theorem Measurable.ennreal_tsum' {ι} [Countable ι] {f : ι → α → ℝ≥0∞} (h : ∀ i, Measurable (f i)) :
    Measurable (∑' i, f i) := by
  convert Measurable.ennreal_tsum h with x
  exact tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)

@[measurability, fun_prop]
theorem Measurable.nnreal_tsum {ι} [Countable ι] {f : ι → α → ℝ≥0} (h : ∀ i, Measurable (f i)) :
    Measurable fun x => ∑' i, f i x := by
  simp_rw [NNReal.tsum_eq_toNNReal_tsum]
  exact (Measurable.ennreal_tsum fun i => (h i).coe_nnreal_ennreal).ennreal_toNNReal

@[measurability, fun_prop]
theorem AEMeasurable.ennreal_tsum {ι} [Countable ι] {f : ι → α → ℝ≥0∞} {μ : Measure α}
    (h : ∀ i, AEMeasurable (f i) μ) : AEMeasurable (fun x => ∑' i, f i x) μ := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact .iSup fun s ↦ Finset.aemeasurable_sum s fun i _ => h i

@[measurability, fun_prop]
theorem AEMeasurable.nnreal_tsum {α : Type*} {_ : MeasurableSpace α} {ι : Type*} [Countable ι]
    {f : ι → α → NNReal} {μ : Measure α} (h : ∀ i : ι, AEMeasurable (f i) μ) :
    AEMeasurable (fun x : α => ∑' i : ι, f i x) μ := by
  simp_rw [NNReal.tsum_eq_toNNReal_tsum]
  exact (AEMeasurable.ennreal_tsum fun i => (h i).coe_nnreal_ennreal).ennreal_toNNReal

@[measurability, fun_prop]
theorem measurable_coe_real_ereal : Measurable ((↑) : ℝ → EReal) :=
  continuous_coe_real_ereal.measurable

@[measurability]
theorem Measurable.coe_real_ereal {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x => (f x : EReal) :=
  measurable_coe_real_ereal.comp hf

@[measurability]
theorem AEMeasurable.coe_real_ereal {f : α → ℝ} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x : EReal)) μ :=
  measurable_coe_real_ereal.comp_aemeasurable hf

/-- The set of finite `EReal` numbers is `MeasurableEquiv` to `ℝ`. -/
def MeasurableEquiv.erealEquivReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ᵐ ℝ :=
  EReal.neBotTopHomeomorphReal.toMeasurableEquiv

theorem EReal.measurable_of_measurable_real {f : EReal → α} (h : Measurable fun p : ℝ => f p) :
    Measurable f :=
  measurable_of_measurable_on_compl_finite {⊥, ⊤} (by simp)
    (MeasurableEquiv.erealEquivReal.symm.measurable_comp_iff.1 h)

@[measurability]
theorem measurable_ereal_toReal : Measurable EReal.toReal :=
  EReal.measurable_of_measurable_real (by simpa using measurable_id)

@[measurability, fun_prop]
theorem Measurable.ereal_toReal {f : α → EReal} (hf : Measurable f) :
    Measurable fun x => (f x).toReal :=
  measurable_ereal_toReal.comp hf

@[measurability, fun_prop]
theorem AEMeasurable.ereal_toReal {f : α → EReal} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x).toReal) μ :=
  measurable_ereal_toReal.comp_aemeasurable hf

@[measurability]
theorem measurable_coe_ennreal_ereal : Measurable ((↑) : ℝ≥0∞ → EReal) :=
  continuous_coe_ennreal_ereal.measurable

@[measurability, fun_prop]
theorem Measurable.coe_ereal_ennreal {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x => (f x : EReal) :=
  measurable_coe_ennreal_ereal.comp hf

@[measurability, fun_prop]
theorem AEMeasurable.coe_ereal_ennreal {f : α → ℝ≥0∞} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x : EReal)) μ :=
  measurable_coe_ennreal_ereal.comp_aemeasurable hf

@[measurability]
theorem measurable_ereal_toENNReal : Measurable EReal.toENNReal :=
  EReal.measurable_of_measurable_real (by simpa using ENNReal.measurable_ofReal)

@[measurability, fun_prop]
theorem Measurable.ereal_toENNReal {f : α → EReal} (hf : Measurable f) :
    Measurable fun x => (f x).toENNReal :=
  measurable_ereal_toENNReal.comp hf

@[measurability, fun_prop]
theorem AEMeasurable.ereal_toENNReal {f : α → EReal} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x).toENNReal) μ :=
  measurable_ereal_toENNReal.comp_aemeasurable hf

namespace NNReal

instance : MeasurableSMul₂ ℝ≥0 ℝ≥0∞ where
  measurable_smul := show Measurable fun r : ℝ≥0 × ℝ≥0∞ ↦ (r.1 : ℝ≥0) * r.2 by fun_prop

/-- A limit (over a general filter) of measurable `ℝ≥0` valued functions is measurable. -/
theorem measurable_of_tendsto' {ι} {f : ι → α → ℝ≥0} {g : α → ℝ≥0} (u : Filter ι) [NeBot u]
    [IsCountablyGenerated u] (hf : ∀ i, Measurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    Measurable g := by
  simp_rw [← measurable_coe_nnreal_ennreal_iff] at hf ⊢
  refine ENNReal.measurable_of_tendsto' u hf ?_
  rw [tendsto_pi_nhds] at lim ⊢
  exact fun x => (ENNReal.continuous_coe.tendsto (g x)).comp (lim x)

/-- A sequential limit of measurable `ℝ≥0` valued functions is measurable. -/
theorem measurable_of_tendsto {f : ℕ → α → ℝ≥0} {g : α → ℝ≥0} (hf : ∀ i, Measurable (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto' atTop hf lim

end NNReal

namespace EReal

lemma measurableEmbedding_coe : MeasurableEmbedding Real.toEReal :=
  isOpenEmbedding_coe.measurableEmbedding

instance : MeasurableAdd₂ EReal := ⟨EReal.lowerSemicontinuous_add.measurable⟩

section MeasurableMul

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

lemma measurable_of_real_prod {f : EReal × β → γ}
    (h_real : Measurable fun p : ℝ × β ↦ f (p.1, p.2))
    (h_bot : Measurable fun x ↦ f (⊥, x)) (h_top : Measurable fun x ↦ f (⊤, x)) : Measurable f :=
  .of_union₃_range_cover (measurableEmbedding_prodMk_left _) (measurableEmbedding_prodMk_left _)
    (measurableEmbedding_coe.prodMap .id) (by simp [-univ_subset_iff, subset_def, EReal.forall])
    h_bot h_top h_real

lemma measurable_of_real_real {f : EReal × EReal → β}
    (h_real : Measurable fun p : ℝ × ℝ ↦ f (p.1, p.2))
    (h_bot_left : Measurable fun r : ℝ ↦ f (⊥, r))
    (h_top_left : Measurable fun r : ℝ ↦ f (⊤, r))
    (h_bot_right : Measurable fun r : ℝ ↦ f (r, ⊥))
    (h_top_right : Measurable fun r : ℝ ↦ f (r, ⊤)) :
    Measurable f := by
  refine measurable_of_real_prod ?_ ?_ ?_
  · refine measurable_swap_iff.mp <| measurable_of_real_prod ?_ h_bot_right h_top_right
    exact h_real.comp measurable_swap
  · exact measurable_of_measurable_real h_bot_left
  · exact measurable_of_measurable_real h_top_left

private lemma measurable_const_mul (c : EReal) : Measurable fun (x : EReal) ↦ c * x := by
  refine measurable_of_measurable_real ?_
  have h1 : (fun (p : ℝ) ↦ (⊥ : EReal) * p)
      = fun p ↦ if p = 0 then (0 : EReal) else (if p < 0 then ⊤ else ⊥) := by
    ext p
    split_ifs with h1 h2
    · simp [h1]
    · rw [bot_mul_coe_of_neg h2]
    · rw [bot_mul_coe_of_pos]
      exact lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
  have h2 : Measurable fun (p : ℝ) ↦ if p = 0 then (0 : EReal) else if p < 0 then ⊤ else ⊥ := by
    refine Measurable.piecewise (measurableSet_singleton _) measurable_const ?_
    exact Measurable.piecewise measurableSet_Iio measurable_const measurable_const
  induction c with
  | bot => rwa [h1]
  | coe c => exact (measurable_id.const_mul _).coe_real_ereal
  | top =>
    simp_rw [← neg_bot, neg_mul]
    apply Measurable.neg
    rwa [h1]

instance : MeasurableMul₂ EReal := by
  refine ⟨measurable_of_real_real ?_ ?_ ?_ ?_ ?_⟩
  · exact (measurable_fst.mul measurable_snd).coe_real_ereal
  · exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · simp_rw [mul_comm _ ⊥]
    exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · simp_rw [mul_comm _ ⊤]
    exact (measurable_const_mul _).comp measurable_coe_real_ereal

end MeasurableMul

end EReal

/-- If a function `f : α → ℝ≥0` is measurable and the measure is σ-finite, then there exists
spanning measurable sets with finite measure on which `f` is bounded.
See also `StronglyMeasurable.exists_spanning_measurableSet_norm_le` for functions into normed
groups. -/
theorem exists_spanning_measurableSet_le {f : α → ℝ≥0} (hf : Measurable f) (μ : Measure α)
    [SigmaFinite μ] :
    ∃ s : ℕ → Set α,
      (∀ n, MeasurableSet (s n) ∧ μ (s n) < ∞ ∧ ∀ x ∈ s n, f x ≤ n) ∧
      ⋃ i, s i = Set.univ := by
  let sigma_finite_sets := spanningSets μ
  let norm_sets := fun n : ℕ => { x | f x ≤ n }
  have norm_sets_spanning : ⋃ n, norm_sets n = Set.univ := by
    ext1 x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exists_nat_ge (f x)
  let sets n := sigma_finite_sets n ∩ norm_sets n
  have h_meas : ∀ n, MeasurableSet (sets n) := by
    refine fun n => MeasurableSet.inter ?_ ?_
    · exact measurableSet_spanningSets μ n
    · exact hf measurableSet_Iic
  have h_finite : ∀ n, μ (sets n) < ∞ := by
    refine fun n => (measure_mono Set.inter_subset_left).trans_lt ?_
    exact measure_spanningSets_lt_top μ n
  refine ⟨sets, fun n => ⟨h_meas n, h_finite n, ?_⟩, ?_⟩
  · exact fun x hx => hx.2
  · have :
      ⋃ i, sigma_finite_sets i ∩ norm_sets i = (⋃ i, sigma_finite_sets i) ∩ ⋃ i, norm_sets i := by
      refine Set.iUnion_inter_of_monotone (monotone_spanningSets μ) fun i j hij x => ?_
      simp only [norm_sets, Set.mem_setOf_eq]
      refine fun hif => hif.trans ?_
      exact mod_cast hij
    rw [this, norm_sets_spanning, iUnion_spanningSets μ, Set.inter_univ]

variable (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]

lemma tendsto_measure_Icc_nhdsWithin_right' (b : ℝ) :
    Tendsto (fun δ ↦ μ (Icc (b - δ) (b + δ))) (𝓝[>] (0 : ℝ)) (𝓝 (μ {b})) := by
  rw [Real.singleton_eq_inter_Icc]
  apply tendsto_measure_biInter_gt (fun r hr ↦ nullMeasurableSet_Icc)
  · intro r s _rpos hrs
    exact Icc_subset_Icc (by linarith) (by linarith)
  · exact ⟨1, zero_lt_one, isCompact_Icc.measure_ne_top⟩

lemma tendsto_measure_Icc_nhdsWithin_right (b : ℝ) :
    Tendsto (fun δ ↦ μ (Icc (b - δ) (b + δ))) (𝓝[≥] (0 : ℝ)) (𝓝 (μ {b})) := by
  simp only [← nhdsWithin_right_sup_nhds_singleton, nhdsWithin_singleton, tendsto_sup,
    tendsto_measure_Icc_nhdsWithin_right' μ b, true_and, tendsto_pure_left]
  intro s hs
  simpa using mem_of_mem_nhds hs

lemma tendsto_measure_Icc [NoAtoms μ] (b : ℝ) :
    Tendsto (fun δ ↦ μ (Icc (b - δ) (b + δ))) (𝓝 (0 : ℝ)) (𝓝 0) := by
  rw [← nhdsLT_sup_nhdsGE, tendsto_sup]
  constructor
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r (hr : r < 0)
    rw [Icc_eq_empty (by linarith), measure_empty]
  · simpa only [measure_singleton] using tendsto_measure_Icc_nhdsWithin_right μ b
