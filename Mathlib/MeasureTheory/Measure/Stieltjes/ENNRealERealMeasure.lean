/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Stieltjes.ENNRealEReal

/-!
# Stieltjes measures on the real line

Consider a function `f : ℝ → EReal` which is monotone and right-continuous. Then one can define a
corresponding measure, giving mass `f b - f a` to the interval `(a, b]`.

## Main definitions

* `ERealStieltjes` is a structure containing a function from `ℝ → EReal`, together with the
assertions that it is monotone and right-continuous. To `f : ERealStieltjes`, one associates
a Borel measure `f.measure`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = ofReal (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = ofReal (leftLim f b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
-/

noncomputable section

open Set Filter Function ENNReal NNReal Topology MeasureTheory

namespace ERealStieltjes

/-! ### The outer measure associated to a Stieltjes function -/

variable (f : ERealStieltjes)

open Classical in
/-- Length of an interval. This is the largest monotone function which correctly measures all
intervals. -/
def length (s : Set ℝ≥0∞) : ℝ≥0∞ :=
  if s ⊆ {0} then 0
  else ⨅ (a) (b) (_ : s ⊆ Ioc a b), (f b - f a).toENNReal

lemma length_of_subset_singleton_zero {s : Set ℝ≥0∞} (hs : s ⊆ {0}) : f.length s = 0 := if_pos hs

lemma length_of_not_subset_singleton_zero {s : Set ℝ≥0∞} (hs : ¬ s ⊆ {0}) :
  f.length s = ⨅ (a) (b) (_ : s ⊆ Ioc a b), (f b - f a).toENNReal := if_neg hs

@[simp]
theorem length_empty : f.length ∅ = 0 := by
  rw [length, if_pos (empty_subset _)]
  -- refine nonpos_iff_eq_zero.1 <| iInf_le_of_le 0 <| iInf_le_of_le 0 <| ?_
  -- simp only [lt_self_iff_false, not_false_eq_true, Ioc_eq_empty, subset_refl, iInf_pos,
  --   nonpos_iff_eq_zero]
  -- rw [EReal.toENNReal_eq_zero_iff]
  -- exact EReal.sub_self_le_zero

@[simp]
lemma length_singleton_zero : f.length {0} = 0 := by simp [length]

section

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Antitone f) {x y : α}
include hf

theorem Antitone.leftLim_eq_sInf [TopologicalSpace α] [OrderTopology α] (h : 𝓝[<] x ≠ ⊥) :
    leftLim f x = sInf (f '' Iio x) :=
  leftLim_eq_of_tendsto h (hf.tendsto_nhdsLT x)

theorem Antitone.rightLim_eq_sSup [TopologicalSpace α] [OrderTopology α] (h : 𝓝[>] x ≠ ⊥) :
    rightLim f x = sSup (f '' Ioi x) :=
  rightLim_eq_of_tendsto h (hf.tendsto_nhdsGT x)

end

@[simp]
lemma length_singleton_top : f.length {∞} = leftLim (fun x ↦ (f ∞ - f x).toENNReal) ∞ := by
  rw [f.length_of_not_subset_singleton_zero (by simp)]
  simp only [singleton_subset_iff, mem_Ioc, top_le_iff]
  rw [Antitone.leftLim_eq_sInf]
  rotate_left
  · exact antitone_toENNReal_const_sub _ _
  · suffices (𝓝[<] ∞).NeBot from this.1
    simp
  calc (⨅ a, ⨅ b, ⨅ (_ : a < ⊤ ∧ b = ⊤), (f b - f a).toENNReal)
  _ = (⨅ a, ⨅ (_ : a < ⊤), (f ∞ - f a).toENNReal) := by
    congr with a
    sorry
  _ = sInf ((fun x ↦ (f ⊤ - f x).toENNReal) '' Iio ⊤) := by simp [sInf_image]

@[simp]
theorem length_Ioc (a b : ℝ≥0∞) : f.length (Ioc a b) = (f b - f a).toENNReal := by
  rcases le_or_lt b a with hab | hab
  · simp only [not_lt, hab, Ioc_eq_empty, length_empty]
    symm
    rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono hab
  have : ¬ Ioc a b ⊆ {0} := by
    simp only [subset_singleton_iff, mem_Ioc, and_imp, not_forall, Classical.not_imp]
    exact ⟨b, hab, le_rfl, ne_bot_of_gt hab⟩
  rw [length, if_neg this]
  refine le_antisymm (iInf_le_of_le a <| iInf₂_le b Subset.rfl)
      (le_iInf fun a' ↦ le_iInf fun b' ↦ le_iInf fun h ↦ ?_)
  rcases le_or_lt b a with ab | ab
  · rw [EReal.toENNReal_of_nonpos (EReal.sub_nonpos.mpr (f.mono ab))]
    exact zero_le'
  refine EReal.toENNReal_le_toENNReal ?_
  obtain ⟨h₁, h₂⟩ := (Ioc_subset_Ioc_iff ab).1 h
  exact EReal.sub_le_sub (f.mono h₁) (f.mono h₂)

theorem length_mono {s₁ s₂ : Set ℝ≥0∞} (h : s₁ ⊆ s₂) : f.length s₁ ≤ f.length s₂ := by
  by_cases hs₂ : s₂ ⊆ {0}
  · rw [length, length, if_pos hs₂, if_pos (h.trans hs₂)]
  by_cases hs₁ : s₁ ⊆ {0}
  · rw [length_of_subset_singleton_zero _ hs₁]
    exact zero_le'
  rw [f.length_of_not_subset_singleton_zero hs₁, f.length_of_not_subset_singleton_zero hs₂]
  exact iInf_mono fun _ ↦ biInf_mono fun _ ↦ h.trans

lemma length_of_subset_Iic {s : Set ℝ≥0∞} {c : ℝ≥0∞} (hs_zero : ¬ s ⊆ {0}) (hs : s ⊆ Iic c) :
    f.length s = ⨅ (a) (b) (_ : b ≤ c) (_ : s ⊆ Ioc a b), (f b - f a).toENNReal := by
  rw [length, if_neg hs_zero]
  congr with a
  sorry

open MeasureTheory

open Classical in
/-- The Stieltjes outer measure associated to a Stieltjes function. -/
protected def outer : OuterMeasure ℝ≥0∞ :=
  OuterMeasure.ofFunction f.length f.length_empty

lemma outer_def : f.outer = OuterMeasure.ofFunction f.length f.length_empty := rfl

theorem outer_le_length (s : Set ℝ≥0∞) : f.outer s ≤ f.length s :=
  OuterMeasure.ofFunction_le _

-- todo: generalize to ofFunction_mono
lemma outer_mono {s t : Set ℝ≥0∞} (hst : s ⊆ t) : f.outer s ≤ f.outer t := by
  rw [outer_def, OuterMeasure.ofFunction_apply, OuterMeasure.ofFunction_apply]
  exact le_iInf₂ (fun ts hts ↦ iInf₂_le ts (hst.trans hts))

/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set. -/
theorem length_subadditive_Icc_Ioo {a b : ℝ≥0∞} {c d : ℕ → ℝ≥0∞}
    (ss : Icc a b ⊆ ⋃ i, Ioo (c i) (d i)) :
    (f b - f a).toENNReal ≤ ∑' i, (f (d i) - f (c i)).toENNReal := by
  suffices
    ∀ (s : Finset ℕ) (b), Icc a b ⊆ (⋃ i ∈ (s : Set ℕ), Ioo (c i) (d i)) →
      (f b - f a).toENNReal ≤ ∑ i ∈ s, (f (d i) - f (c i)).toENNReal by
    rcases isCompact_Icc.elim_finite_subcover_image
        (fun (i : ℕ) (_ : i ∈ univ) => @isOpen_Ioo _ _ _ _ (c i) (d i)) (by simpa using ss) with
      ⟨s, _, hf, hs⟩
    have e : ⋃ i ∈ (hf.toFinset : Set ℕ), Ioo (c i) (d i) = ⋃ i ∈ s, Ioo (c i) (d i) := by
      simp only [Set.ext_iff, exists_prop, Finset.set_biUnion_coe, mem_iUnion, forall_const,
        Finite.mem_toFinset]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_trans ?_ (le_iSup _ hf.toFinset)
    exact this hf.toFinset _ (by simpa only [e] )
  clear ss b
  refine fun s => Finset.strongInductionOn s fun s IH b cv => ?_
  rcases le_total b a with ab | ab
  · rw [EReal.toENNReal_of_nonpos (EReal.sub_nonpos.2 (f.mono ab))]
    exact zero_le _
  have := cv ⟨ab, le_rfl⟩
  simp only [Finset.mem_coe, gt_iff_lt, not_lt, mem_iUnion, mem_Ioo, exists_and_left,
    exists_prop] at this
  rcases this with ⟨i, cb, is, bd⟩
  rw [← Finset.insert_erase is] at cv ⊢
  rw [Finset.coe_insert, biUnion_insert] at cv
  rw [Finset.sum_insert (Finset.not_mem_erase _ _)]
  refine le_trans ?_ (add_le_add_left (IH _ (Finset.erase_ssubset is) (c i) ?_) _)
  · refine (EReal.toENNReal_sub_le_add _ _ (f (c i))).trans ?_
    gcongr
    exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub (f.mono bd.le) le_rfl)
  · rintro x ⟨h₁, h₂⟩
    exact (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left (mt And.left (not_lt_of_le h₂))

-- todo: added `b ≠ ∞`
theorem outer_Ioc_of_ne_bot (a b : ℝ≥0∞) (ha : f a ≠ ⊥) (hb : b ≠ ∞) :
    f.outer (Ioc a b) = (f b - f a).toENNReal := by
  -- if `b ≤ a` then `Ioc a b = ∅` and the r.h.s. is zero since `f` is monotone
  rcases le_or_lt b a with hba | hab
  · simp only [not_lt, hba, Ioc_eq_empty, measure_empty]
    symm
    rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono hba
  have : (𝓝[>] a).NeBot := by simp [ne_top_of_lt hab]
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
    by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
    intervals, while we would like to have a compact interval covered by open intervals to use
    compactness and finite sums, as provided by `length_subadditive_Icc_Ioo`. The trick is to use
    the right-continuity of `f`. If `a'` is close enough to `a` on its right, then `[a', b]` is
    still covered by the sets `s i` and moreover `f b - f a'` is very close to `f b - f a`
    (up to `ε/2`).
    Also, by definition one can cover `s i` by a half-closed interval `(p i, q i]` with `f`-length
    very close to that of `s i` (within a suitably small `ε' i`, say). If one moves `q i` very
    slightly to the right, then the `f`-length will change very little by right continuity, and we
    will get an open interval `(p i, q' i)` covering `s i` with `f (q' i) - f (p i)` within `ε' i`
    of the `f`-length of `s i`. -/
  refine le_antisymm ((f.length_Ioc _ _).symm ▸ outer_le_length _ _) ?_
  refine le_iInf₂ fun s' hs' ↦ ENNReal.le_of_forall_pos_le_add fun ε εpos h' ↦ ?_
  -- We ensure that `f x ≥ f a > ⊥` for all points in the sets `s i`
  let s : ℕ → Set ℝ≥0∞ := fun i ↦ s' i ∩ Ioc a b
  have hsab i : s i ⊆ Ioc a b := inter_subset_right
  have hs : Ioc a b = ⋃ i, s i := by
    rw [← iUnion_inter]
    simp [hs']
  have h : ∑' i, f.length (s i) < ⊤ := by
    refine (tsum_mono ENNReal.summable ENNReal.summable fun n ↦ ?_).trans_lt h'
    exact f.length_mono inter_subset_left
  suffices (f b - f a).toENNReal ≤ ∑' i, f.length (s i) + ε by
    refine this.trans ?_
    gcongr with i
    exact f.length_mono inter_subset_left
  -- we can w.l.o.g. assume that `f a ≠ ⊤`
  by_cases ha_top : f a = ⊤
  · simp [sub_eq_add_neg, ha_top]
  -- main case
  let δ := ε / 2
  have δpos : 0 < (δ : ℝ≥0∞) := by simpa [δ] using εpos.ne'
  rcases ENNReal.exists_pos_sum_of_countable δpos.ne' ℕ with ⟨ε', ε'0, hε⟩
  obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a' := by
    have A : ContinuousWithinAt (fun r ↦ f r - f a) (Ioi a) a := by
      refine f.continuousWithinAt_sub_const_Ioi (.inl ha)
    have B : f a - f a < δ := by
      rw [EReal.sub_self ha_top ha]
      exact mod_cast δpos
    exact (((tendsto_order.1 A).2 _ B).and self_mem_nhdsWithin).exists
  have : ∀ i, ∃ p : ℝ≥0∞ × ℝ≥0∞, s i ⊆ Ioo p.1 p.2
      ∧ (f p.2 - f p.1).toENNReal < f.length (s i) + ε' i := by
    intro i
    have hl :=
      ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_ne_zero.2 (ε'0 i).ne')
    have hsi_ne_zero : ¬ s i ⊆ {0} := by
      specialize hsab i
      sorry
    conv_lhs at hl => rw [f.length_of_subset_Iic hsi_ne_zero ((hsab i).trans Ioc_subset_Iic_self)]
    -- todo: do better here to avoid `q' = ∞`
    simp only [iInf_lt_iff, exists_prop] at hl
    rcases hl with ⟨p, q', hq'b, spq, hq'⟩
    have hqa (h : q' ≤ a) : s i = ∅ := by
      have : s i ⊆ Ioc p q' ∩ Ioc a b := by simp [spq, hsab]
      rw [← subset_empty_iff]
      refine this.trans (subset_empty_iff.mpr ?_)
      rw [Ioc_inter_Ioc, Ioc_eq_empty]
      simp [h]
    classical
    let p'' := if s i = ∅ then a else p
    let q'' := if s i = ∅ then a else q'
    have hq''a : a ≤ q'' := by
      unfold q''
      split_ifs with h_empty
      · simp [h_empty]
      · have h : ¬q' ≤ a := hqa.mt h_empty
        exact (not_le.mp h).le
    have spq'' : s i ⊆ Ioc p'' q'' := by
      unfold q'' p''
      split_ifs with h_empty <;> simp [h_empty, spq]
    have hq'' : (f q'' - f p'').toENNReal < f.length (s i) + ↑(ε' i) := by
      unfold p'' q''
      split_ifs with h_empty
      rw [EReal.sub_self ha_top ha]
      · simp only [ne_eq, EReal.zero_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
        EReal.toReal_zero, ofReal_zero, add_pos_iff, ENNReal.coe_pos]
        exact .inr (ε'0 i)
      · exact hq'
    have : ContinuousWithinAt (fun r => (f r - f p'').toENNReal) (Ioi q'') q'' := by
      refine EReal.continuous_toENNReal.continuousAt.comp_continuousWithinAt ?_
      refine f.continuousWithinAt_sub_const_Ioi ?_
      exact .inl <| ne_of_gt (ha.bot_lt.trans_le (f.mono hq''a))
    have hq''_top : q'' ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := b) hb ?_
      unfold q''
      split_ifs with h_si
      · exact hab.le
      · exact hq'b
    have h_neBot : (𝓝[>] q'').NeBot := by simp [hq''_top]
    rcases (((tendsto_order.1 this).2 _ hq'').and self_mem_nhdsWithin).exists with ⟨q, hq, q'q⟩
    exact ⟨⟨p'', q⟩, spq''.trans (Ioc_subset_Ioo_right q'q), hq⟩
  choose g hg using this
  have I_subset : Icc a' b ⊆ ⋃ i, Ioo (g i).1 (g i).2 :=
    calc
      Icc a' b ⊆ Ioc a b := fun x hx => ⟨aa'.trans_le hx.1, hx.2⟩
      _ = ⋃ i, s i := hs
      _ ⊆ ⋃ i, Ioo (g i).1 (g i).2 := iUnion_mono fun i => (hg i).1
  calc
    (f b - f a).toENNReal ≤ (f b - f a').toENNReal + (f a' - f a).toENNReal :=
        EReal.toENNReal_sub_le_add _ _ _
    _ ≤ ∑' i, (f (g i).2 - f (g i).1).toENNReal + ENNReal.ofReal δ := by
      refine (add_le_add (f.length_subadditive_Icc_Ioo I_subset) ?_)
      exact EReal.toENNReal_le_toENNReal ha'.le
    _ ≤ ∑' i, (f.length (s i) + ε' i) + δ :=
      (add_le_add (ENNReal.tsum_le_tsum fun i => (hg i).2.le)
        (by simp only [ENNReal.ofReal_coe_nnreal, le_rfl]))
    _ = ∑' i, f.length (s i) + ∑' i, (ε' i : ℝ≥0∞) + δ := by rw [ENNReal.tsum_add]
    _ ≤ ∑' i, f.length (s i) + δ + δ := add_le_add (add_le_add le_rfl hε.le) le_rfl
    _ = ∑' i : ℕ, f.length (s i) + ε := by simp [δ, add_assoc, ENNReal.add_halves]

theorem outer_Ioc_of_eq_bot (a b : ℝ≥0∞) (hb : f b = ⊥) : f.outer (Ioc a b) = 0 := by
  refine le_antisymm ?_ zero_le'
  suffices f.outer (Ioc a b) ≤ (f b - f a).toENNReal by simpa [hb] using this
  exact (f.length_Ioc _ _).symm ▸ outer_le_length _ _

lemma iSup_le_outer_Ioc (a b : ℝ≥0∞) :
    ⨆ c, ⨆ (_ : a < c), f.outer (Ioc c b) ≤ f.outer (Ioc a b) :=
  iSup₂_le fun _ hc ↦ f.outer_mono (Ioc_subset_Ioc hc.le le_rfl)

lemma outer_Ioc_eq_top_aux1' {a b : ℝ≥0∞} (ha : f a = ⊥) (ha' : ∀ x, a < x → f x ≠ ⊥) (hab : a < b)
    (hb : b ≠ ∞) :
    f.outer (Ioc a b) = ∞ := by
  refine eq_top_iff.mpr (le_trans ?_ (iSup_le_outer_Ioc _ _ _))
  have h_outer {b c} (hac : a < c) (hb : b ≠ ∞) : f.outer (Ioc c b) = (f b - f c).toENNReal := by
    rw [outer_Ioc_of_ne_bot _ _ _ (ha' c hac) hb]
  have : ⨆ (c : ℝ≥0∞) (_ : a < c), f.outer (Ioc c b)
      = ⨆ (c : ℝ≥0∞) (_ : a < c), (f b - f c).toENNReal := by
    congr with c
    congr with hc
    rw [h_outer hc hb]
  rw [this]
  obtain ⟨c, _, hc_gt, hc_tendsto⟩ := exists_seq_strictAnti_tendsto' hab
  have h_tendsto : Tendsto (fun n ↦ (f b - f (c n)).toENNReal) atTop (𝓝 ⊤) := by
    have hc_tendsto' : Tendsto c atTop (𝓝[≥] a) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hc_tendsto, .of_forall fun n ↦ (hc_gt n).1.le⟩
    have h'' := continuousWithinAt_const_sub_Ici f (c := f b) (a := a) ?_
    swap; · simp [ha]
    have h := h''.tendsto.comp hc_tendsto'
    have h_eq_top : f b - f a = ⊤ := by
      rw [ha, sub_eq_add_neg, EReal.neg_bot, EReal.add_top_of_ne_bot (ha' b hab)]
    rw [h_eq_top] at h
    refine (EReal.continuous_toENNReal.tendsto _).comp h
  simp only [top_le_iff]
  refine eq_top_of_forall_nnreal_le fun r ↦ ?_
  simp_rw [ENNReal.tendsto_nhds_top_iff_nnreal, eventually_atTop] at h_tendsto
  obtain ⟨n, hn⟩ := h_tendsto r
  refine (hn n le_rfl).le.trans ?_
  exact le_iSup₂ (f := fun c _ ↦ (f b - f c).toENNReal) (c n) (hc_gt n).1

lemma outer_Ioc_eq_top_aux1 {a b : ℝ≥0∞} (ha : f a = ⊥) (ha' : ∀ x, a < x → f x ≠ ⊥) (hab : a < b) :
    f.outer (Ioc a b) = ∞ := by
  by_cases hb : b = ∞
  · simp only [ne_eq, hb, Ioc_top] at *
    have : f.outer (Ioc a (a + 1)) = ∞ := by
      have ha_ne_top : a ≠ ∞ := hab.ne
      refine outer_Ioc_eq_top_aux1' f ha ha' ?_ (by simp [ha_ne_top])
      exact ENNReal.lt_add_right ha_ne_top (by simp)
    refine eq_top_iff.mpr ?_
    rw [← this]
    exact f.outer_mono Ioc_subset_Ioi_self
  · exact outer_Ioc_eq_top_aux1' f ha ha' hab hb

lemma outer_singleton_eq_top' {b : ℝ≥0∞} (hb_zero : b ≠ 0) (hb : ∀ a < b, f b - f a = ∞) :
    f.outer {b} = ∞ := by
  rw [outer_def, OuterMeasure.ofFunction_apply]
  simp only [iInf_eq_top]
  intro s' hs'
  have hb_mem' : ∃ n, b ∈ s' n := by
    rw [← mem_iUnion]
    exact hs' (mem_singleton _)
  let s := fun n ↦ s' n ∩ Ici b
  obtain ⟨n, hn⟩ : ∃ n, b ∈ s n := by simp [s, hb_mem']
  suffices ∑' n, f.length (s n) = ⊤ by
    refine eq_top_mono ?_ this
    gcongr with n
    exact f.length_mono inter_subset_left
  refine ENNReal.tsum_eq_top_of_eq_top ?_
  refine ⟨n, ?_⟩
  rw [length, if_neg]
  swap
  · simp only [subset_singleton_iff, not_forall, Classical.not_imp]
    exact ⟨b, hn, hb_zero⟩
  simp only [iInf_eq_top, EReal.toENNReal_eq_top_iff]
  refine fun i j h_subset ↦ ?_
  have hbij : b ∈ Ioc i j := h_subset hn
  refine eq_top_mono ?_ (hb i hbij.1)
  refine EReal.sub_le_sub (f.mono hbij.2) le_rfl

lemma outer_singleton_eq_top {b : ℝ≥0∞} (hb_zero : b ≠ 0) (hb : f b - leftLim f b = ∞) :
    f.outer {b} = ∞ := by
  refine outer_singleton_eq_top' f hb_zero fun a ha ↦ ?_
  exact eq_top_mono (EReal.sub_le_sub le_rfl (f.mono.le_leftLim ha)) hb

@[simp]
lemma outer_singleton_zero : f.outer {0} = 0 :=
  le_antisymm ((f.outer_le_length _).trans_eq (by simp)) zero_le'

lemma outer_singleton_aux {b : ℝ≥0∞} (hb_zero : b ≠ 0) (ha' : ∀ x < b, f x = ⊥) (hb : f b ≠ ⊥) :
    f.outer {b} = ∞ := by
  refine outer_singleton_eq_top f hb_zero ?_
  have : (𝓝[<] b).NeBot := by simp [hb_zero]
  have : leftLim f b = ⊥ := by
    refine leftLim_eq_of_tendsto NeBot.ne' ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    rw [EventuallyEq, eventually_nhdsWithin_iff]
    exact .of_forall ha'
  rw [this, sub_eq_add_neg, EReal.neg_bot, EReal.add_top_of_ne_bot hb]
  simp

lemma outer_Ioc_eq_top_aux2 {a b : ℝ≥0∞} (ha' : ∀ x < b, f x = ⊥) (hb : f b ≠ ⊥) (hab : a < b) :
    f.outer (Ioc a b) = ∞ := by
  have hb_zero : b ≠ 0 := ne_bot_of_gt hab
  exact eq_top_mono (f.outer_mono (singleton_subset_iff.mpr ⟨hab, le_rfl⟩))
    (outer_singleton_aux f hb_zero ha' hb)

theorem outer_Ioc_of_ne_top (a b : ℝ≥0∞) (hb : b ≠ ∞) :
    f.outer (Ioc a b) = (f b - f a).toENNReal := by
  by_cases ha_bot : f a = ⊥
  swap; · exact outer_Ioc_of_ne_bot f a b ha_bot hb
  simp [ha_bot, sub_eq_add_neg]
  by_cases hb : f b = ⊥
  · simp [hb, outer_Ioc_of_eq_bot]
  rw [EReal.add_top_of_ne_bot hb, EReal.toENNReal_top]
  let a' := sSup {x | f x = ⊥}
  have hb_gt x (hx : f x = ⊥) : x < b := by
    have hxb : f x < f b := by
        rw [hx, bot_lt_iff_ne_bot]
        exact hb
    by_contra h_not
    exact not_le.mpr hxb (f.mono (not_lt.mp h_not))
  have ha'_lt x (hx : x < a') : f x = ⊥ := by
    obtain ⟨x', hx'_eq : f x' = ⊥, hxx'⟩ := exists_lt_of_lt_csSup ⟨a, ha_bot⟩ hx
    exact eq_bot_mono (f.mono hxx'.le) hx'_eq
  have ha'_gt x (hx : a' < x) : f x ≠ ⊥ := by
    by_contra! h_bot
    refine not_le.mpr hx ?_
    exact le_csSup ⟨b, fun x hx ↦ (hb_gt x hx).le⟩ h_bot
  have haa' : a ≤ a' := le_csSup ⟨b, fun x hx ↦ (hb_gt x hx).le⟩ ha_bot
  by_cases hfa' : f a' = ⊥
  · suffices f.outer (Ioc a' b) = ∞ from
      eq_top_mono (f.outer_mono (Ioc_subset_Ioc haa' le_rfl)) this
    exact outer_Ioc_eq_top_aux1 f hfa' ha'_gt (hb_gt a' hfa')
  · suffices f.outer (Ioc a a') = ∞ by
      refine eq_top_mono ?_ this
      refine f.outer_mono (Ioc_subset_Ioc le_rfl ?_)
      refine csSup_le ⟨a, ha_bot⟩ fun x hx ↦ (hb_gt x hx).le
    refine outer_Ioc_eq_top_aux2 f ha'_lt hfa' ?_
    exact lt_of_le_of_ne haa' fun h_eq ↦ (h_eq ▸ hfa') ha_bot

protected theorem measurableSet_Ioi {c : ℝ≥0∞} : MeasurableSet[f.outer.caratheodory] (Ioi c) := by
  refine OuterMeasure.ofFunction_caratheodory fun t ↦ ?_
  by_cases ht : t ⊆ {0}
  · have ht_inter : t ∩ Ioi c = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hx
      have hx' : x = 0 := by simpa using ht hx
      simp [hx']
    have ht_diff : t \ Ioi c ⊆ {0} := diff_subset.trans ht
    simp [ht_inter, f.length_of_subset_singleton_zero ht_diff]
  conv_rhs => rw [length, if_neg ht]
  refine le_iInf fun a => le_iInf fun b => le_iInf fun h => ?_
  refine
    le_trans
      (add_le_add (f.length_mono <| inter_subset_inter_left _ h)
        (f.length_mono <| diff_subset_diff_left h)) ?_
  rcases le_total a c with hac | hac <;> rcases le_total b c with hbc | hbc
  · simp only [Ioc_inter_Ioi, f.length_Ioc, hac, hbc, le_refl, Ioc_eq_empty,
      max_eq_right, min_eq_left, Ioc_diff_Ioi, f.length_empty, zero_add, not_lt]
  · simp only [Ioc_inter_Ioi, hac, sup_of_le_right, length_Ioc, Ioc_diff_Ioi, hbc, min_eq_right]
    rw [EReal.toENNReal_sub_add_cancel (f.mono hac) (f.mono hbc)]
  · simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_diff_Ioi, f.length_empty,
      zero_add, or_true, le_sup_iff, f.length_Ioc, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty, not_lt]

lemma borel_le_measurable : borel ℝ≥0∞ ≤ f.outer.caratheodory := by
  rw [borel_eq_generateFrom_Ioi]
  refine MeasurableSpace.generateFrom_le fun t ⟨a, ha⟩ ↦ ?_
  rw [← ha]
  exact f.measurableSet_Ioi

protected theorem measurableSet_Iio {c : ℝ≥0∞} : MeasurableSet[f.outer.caratheodory] (Iio c) :=
  f.borel_le_measurable _ (measurableSet_Iio)

protected theorem measurableSet_Ioc {a b : ℝ≥0∞} :
    MeasurableSet[f.outer.caratheodory] (Ioc a b) :=
  f.borel_le_measurable _ (measurableSet_Ioc)

protected theorem measurableSet_Iic {a : ℝ≥0∞} :
    MeasurableSet[f.outer.caratheodory] (Iic a) :=
  f.borel_le_measurable _ (measurableSet_Iic)

@[simp]
lemma EReal.toENNReal_sub_self (a : EReal) : (a - a).toENNReal = 0 := by
  rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]

@[simp]
lemma outer_Ioo_top (a : ℝ≥0∞) : f.outer (Ioo a ∞) = (leftLim f ∞ - f a).toENNReal := by
  by_cases ha : a = ∞
  · simp only [ha, lt_self_iff_false, not_false_eq_true, Ioo_eq_empty, measure_empty]
    symm
    rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono.leftLim_le le_rfl
  have h_eq : Ioo a ∞ = ⋃ (n : ℕ), Ioc (a + n) (a + n + 1) := by
    ext x
    simp only [mem_Ioo, mem_iUnion, mem_Ioc]
    constructor
    · intro ⟨hx₁, hx₂⟩
      sorry
    · intro ⟨i, hx₁, hx₂⟩
      refine ⟨lt_of_le_of_lt (by simp) hx₁, lt_of_le_of_lt hx₂ ?_⟩
      simp [Ne.lt_top ha]
  rw [h_eq, OuterMeasure.f_iUnion f.outer]
  rotate_left
  · exact fun _ ↦ f.measurableSet_Ioc
  · intro n m hnm
    wlog hnm' : n < m
    · specialize this f a ha h_eq hnm.symm (lt_of_le_of_ne (not_lt.mp hnm') hnm.symm)
      simp only [Set.disjoint_iff] at this ⊢
      rwa [inter_comm] at this
    simp only [Ioc_disjoint_Ioc, le_sup_iff, inf_le_iff]
    right
    left
    rw [add_assoc]
    gcongr
    norm_cast
  have h_ne_top : ∀ (n : ℕ), a + n + 1 ≠ ∞ := by simp [ha]
  simp only [f.outer_Ioc_of_ne_top _ _ (h_ne_top _)]
  have h_sum n : ∑ i ∈ Finset.range n, (f (a + i + 1) - f (a + i)).toENNReal
      = (f (a + n) - f a).toENNReal := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [Finset.sum_range_succ, hn, add_comm, EReal.toENNReal_sub_add_cancel]
      · push_cast
        rw [← add_assoc]
      · exact f.mono (by simp)
      · exact f.mono (by simp)
  have h := Summable.tendsto_sum_tsum_nat (f := fun i ↦ (f (a + i + 1) - f (a + i)).toENNReal)
    ENNReal.summable
  refine tendsto_nhds_unique h ?_
  simp_rw [h_sum]
  refine (EReal.continuous_toENNReal.tendsto _).comp ?_
  refine (EReal.continuousAt_sub_const ?_).tendsto.comp ?_
  · left -- todo: split case
    sorry
  have h_tendsto : Tendsto f (𝓝[<] ∞) (𝓝 (leftLim f ∞)) := f.mono.tendsto_leftLim _
  refine h_tendsto.comp ?_
  have h_nat_tendsto : Tendsto (fun (n : ℕ) ↦ (n : ℝ≥0∞)) atTop (𝓝 ∞) :=
    ENNReal.tendsto_nat_nhds_top
  rw [tendsto_nhdsWithin_iff]
  simp only [mem_Iio, add_lt_top, natCast_lt_top, and_true, eventually_atTop, ge_iff_le]
  constructor
  · refine tendsto_nhds_top fun n ↦ ?_
    rw [tendsto_nhds_top_iff_nat] at h_nat_tendsto
    filter_upwards [h_nat_tendsto n] with m hm using hm.trans_le (by simp)
  · exact ⟨0, fun _ _ ↦ Ne.lt_top ha⟩

@[simp]
lemma outer_singleton_top : f.outer {∞} = leftLim (fun x ↦ (f ∞ - f x).toENNReal) ∞ := by
  refine le_antisymm ((f.outer_le_length _).trans_eq (by simp)) ?_
  sorry

@[simp]
theorem outer_Ioc (a b : ℝ≥0∞) : f.outer (Ioc a b) = (f b - f a).toENNReal := by
  by_cases hb : b = ∞
  swap; · exact outer_Ioc_of_ne_top f a b hb
  simp only [hb]
  by_cases ha : a = ∞
  · simp [ha]
  have : Ioc a ∞ = Ioo a ∞ ∪ {∞} := by rw [Ioo_union_right (Ne.lt_top ha)]
  rw [this]
  have : f.outer (Ioo a ⊤ ∪ {⊤}) = f.outer (Ioo a ⊤) + f.outer {∞} := by
    sorry
  rw [this, add_comm]
  simp only [outer_Ioo_top, outer_singleton_top]
  sorry

theorem outer_trim : f.outer.trim = f.outer := by
  refine le_antisymm (fun s ↦ ?_) (OuterMeasure.le_trim _)
  rw [OuterMeasure.trim_eq_iInf]
  refine le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩
  refine le_trans ?_ (add_le_add_left (le_of_lt hε) _)
  rw [← ENNReal.tsum_add]
  choose g hg using
    show ∀ i, ∃ s, t i ⊆ s ∧ MeasurableSet s
        ∧ f.outer s ≤ f.length (t i) + ENNReal.ofReal (ε' i) by
      intro i
      have hl :=
        ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_pos.2 (ε'0 i)).ne'
      conv_lhs at hl => rw [length]
      split_ifs at hl with ht_ss
      · exact ⟨{0}, ht_ss, measurableSet_singleton _, by simp⟩
      simp only [iInf_lt_iff] at hl
      rcases hl with ⟨a, b, h₁, h₂⟩
      rw [← f.outer_Ioc] at h₂
      exact ⟨_, h₁, _root_.measurableSet_Ioc, le_of_lt <| by simpa using h₂⟩
  simp only [ofReal_coe_nnreal] at hg
  apply iInf_le_of_le (iUnion g) _
  apply iInf_le_of_le (ht.trans <| iUnion_mono fun i => (hg i).1) _
  apply iInf_le_of_le (MeasurableSet.iUnion fun i => (hg i).2.1) _
  exact le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun i => (hg i).2.2)

/-! ### The measure associated to a Stieltjes function -/

/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. -/
protected irreducible_def measure : Measure ℝ≥0∞ where
  toOuterMeasure := f.outer
  m_iUnion _s hs := f.outer.iUnion_eq_of_caratheodory fun i ↦ f.borel_le_measurable _ (hs i)
  trim_le := f.outer_trim.le

@[simp]
theorem measure_Ioc (a b : ℝ≥0∞) : f.measure (Ioc a b) = (f b - f a).toENNReal := by
  rw [ERealStieltjes.measure]
  exact f.outer_Ioc a b

-- This is different from `(f a - leftLim f a).toENNReal` iff
-- `f a = ⊤ ∧ leftLim f a = ⊤ ∧ (∀ x < a, f x < ⊤)`.
@[simp]
theorem measure_singleton (a : ℝ≥0∞) :
    f.measure {a} = leftLim (fun x ↦ (f a - f x).toENNReal) a := by
  by_cases ha_zero : a = 0
  · rw [f.measure_def]
    change f.outer {a} = _
    simp only [ha_zero, outer_singleton_zero]
    rw [leftLim_eq_of_eq_bot _ (by simp)]
    simp
  have : (𝓝[<] a).NeBot := by simp [ha_zero]
  by_cases h_top : ∀ x < a, f a - f x = ⊤
  · rw [f.measure_def]
    change f.outer {a} = _
    rw [outer_singleton_eq_top' _ ha_zero]
    · symm
      refine leftLim_eq_of_tendsto NeBot.ne' ?_
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
      simp [h_top x hx]
    · convert h_top
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
      ∃ u : ℕ → ℝ≥0∞, StrictMono u ∧ (∀ n : ℕ, u n ∈ Ioo 0 a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto' (Ne.bot_lt ha_zero)
  have u_lt_a := fun n ↦ (u_lt_a n).2
  have h_anti : Antitone (fun x ↦ (f a - f x).toENNReal) := antitone_toENNReal_const_sub f a
  have hu_tendsto_sub : Tendsto (fun n ↦ (f a - f (u n)).toENNReal) atTop
      (𝓝 (leftLim (fun x ↦ (f a - f x).toENNReal) a)) := by
    have h_ll := h_anti.tendsto_leftLim a
    have u_lim' : Tendsto u atTop (𝓝[<] a) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨u_lim, .of_forall u_lt_a⟩
    exact h_ll.comp u_lim'
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine Subset.antisymm (fun x hx ↦ by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx ↦ ?_
    simp? at hx says simp only [mem_iInter, mem_Ioc] at hx
    have : a ≤ x := le_of_tendsto' u_lim fun n ↦ (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n ↦ f.measure (Ioc (u n) a)) atTop (𝓝 (f.measure {a})) := by
    rw [A]
    refine tendsto_measure_iInter_atTop (fun n ↦ nullMeasurableSet_Ioc) (fun m n hmn ↦ ?_) ?_
    · exact Ioc_subset_Ioc_left (u_mono.monotone hmn)
    · simp_rw [measure_Ioc, ne_eq, EReal.toENNReal_eq_top_iff]
      by_contra! h
      simp only [h, EReal.toENNReal_top, tendsto_const_nhds_iff] at hu_tendsto_sub
      refine h_top fun x hx ↦ ?_
      suffices (f a - f x).toENNReal = ⊤ by rwa [EReal.toENNReal_eq_top_iff] at this
      refine eq_top_mono ?_ hu_tendsto_sub.symm
      exact h_anti.leftLim_le hx
  have L2 : Tendsto (fun n ↦ f.measure (Ioc (u n) a)) atTop
      (𝓝 (leftLim (fun x ↦ (f a - f x).toENNReal) a)) := by
    simp only [measure_Ioc]
    exact hu_tendsto_sub
  exact tendsto_nhds_unique L1 L2

-- This is different from `(f b - leftLim f a).toENNReal` iff
-- `f b = ⊤ ∧ leftLim f a = ⊤ ∧ (∀ x < a, f x < ⊤)`.
@[simp]
theorem measure_Icc (a b : ℝ≥0∞) :
    f.measure (Icc a b) = leftLim (fun x ↦ (f b - f x).toENNReal) a := by
  rcases le_or_lt a b with (hab | hab)
  · have A : Disjoint {a} (Ioc a b) := by simp
    simp only [← Icc_union_Ioc_eq_Icc le_rfl hab, Icc_self, measure_union A measurableSet_Ioc,
      measure_singleton, measure_Ioc]
    rw [add_comm]
    by_cases ha_zero : a = 0
    · simp only [ha_zero]
      rw [leftLim_eq_of_eq_bot _ (by simp), leftLim_eq_of_eq_bot _ (by simp)]
      simp
    have : (𝓝[<] a).NeBot := by simp [ha_zero]
    calc (f b - f a).toENNReal + leftLim (fun x ↦ (f a - f x).toENNReal) a
    _ = leftLim (fun x ↦ (f b - f a).toENNReal + (f a - f x).toENNReal) a := by
      symm
      refine leftLim_eq_of_tendsto NeBot.ne' ?_
      refine Tendsto.const_add _ ?_
      exact (antitone_toENNReal_const_sub f a).tendsto_leftLim _
    _ = leftLim (fun x ↦ (f b - f x).toENNReal) a := by
      refine leftLim_eq_of_tendsto NeBot.ne' ?_
      have h := (antitone_toENNReal_const_sub f b).tendsto_leftLim a
      refine (tendsto_congr' ?_).mpr h
      refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
      exact EReal.toENNReal_sub_add_cancel (f.mono hx.le) (f.mono hab)
  · simp only [hab, measure_empty, Icc_eq_empty, not_le]
    symm
    have : (𝓝[<] a).NeBot := by
      have ha_zero : a ≠ 0 := ne_bot_of_gt hab
      simp [ha_zero]
    refine leftLim_eq_of_tendsto NeBot.ne' ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    have : ∀ᶠ x in 𝓝[<] a, b < x := by
      refine eventually_nhdsWithin_iff.mpr ?_
      filter_upwards [eventually_gt_nhds hab] with x hx _ using hx
    filter_upwards [this] with x hx
    rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono hx.le

@[simp]
theorem measure_Ioo {a b : ℝ≥0∞} :
    f.measure (Ioo a b) = (leftLim f b - f a).toENNReal := by
  by_cases hb_zero : b = 0
  · simp only [hb_zero, not_lt_zero', not_false_eq_true, Ioo_eq_empty, measure_empty]
    rw [leftLim_eq_of_eq_bot _ (by simp), eq_comm, EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono zero_le'
  have : (𝓝[<] b).NeBot := by simp [hb_zero]
  rw [← leftLim_toENNReal_sub_left]
  rcases le_or_lt b a with (hab | hab)
  · simp only [not_lt, hab, Ioo_eq_empty, measure_empty]
    symm
    refine leftLim_eq_of_tendsto NeBot.ne' ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
    simp only
    rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono (hx.le.trans hab)
  · obtain ⟨c, hc_mono, hc_mem, hc_tendsto⟩ := exists_seq_strictMono_tendsto' hab
    have h_iUnion : Ioo a b = ⋃ i, Ioc a (c i) := by
      ext x
      simp only [mem_Ioo, mem_iUnion, mem_Ioc, exists_and_left, and_congr_right_iff]
      refine fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · exact (Filter.Tendsto.eventually_const_le h hc_tendsto).exists
      · obtain ⟨n, hn⟩ := h
        exact hn.trans_lt (hc_mem _).2
    have h_mono : Monotone fun x ↦ (f x - f a).toENNReal :=
      fun _ _ hxy ↦ EReal.toENNReal_le_toENNReal (EReal.sub_le_sub (f.mono hxy) le_rfl)
    rw [h_iUnion, Monotone.measure_iUnion]
    · simp only [measure_Ioc]
      rw [Monotone.leftLim_eq_sSup h_mono NeBot.ne']
      apply le_antisymm
      · refine iSup_le fun n ↦ ?_
        refine le_sSup ?_
        simp only [mem_image, mem_Iio]
        exact ⟨c n, (hc_mem _).2, rfl⟩
      · refine sSup_le fun y hy ↦ ?_
        simp only [mem_image, mem_Iio] at hy
        obtain ⟨x, hx_lt, rfl⟩ := hy
        have : ∀ᶠ i in atTop, x < c i := Filter.Tendsto.eventually_const_lt hx_lt hc_tendsto
        obtain ⟨n, hn⟩ := this.exists
        exact le_iSup_of_le n (h_mono hn.le)
    · intro i j hij x
      simp only [mem_Ioc, and_imp]
      intro hax hxc
      exact ⟨hax, hxc.trans (hc_mono.monotone hij)⟩

theorem measure_Ico_of_lt {a b : ℝ≥0∞} (hab : a < b) :
    f.measure (Ico a b)
      = leftLim (fun x ↦ (f a - f x).toENNReal) a + (leftLim f b - f a).toENNReal := by
  have A : Disjoint {a} (Ioo a b) := by simp
  simp only [← Icc_union_Ioo_eq_Ico le_rfl hab, Icc_self, measure_union A measurableSet_Ioo,
    measure_singleton, measure_Ioo]

lemma measure_Ico_of_lt_of_eq_top {a b : ℝ≥0∞} (hab : a < b)
    (h : f a = ⊤ → leftLim f a = ⊤ → ∃ x < a, f x = ⊤) :
    f.measure (Ico a b) = (leftLim f b - leftLim f a).toENNReal := by
  rw [measure_Ico_of_lt _ hab, leftLim_toENNReal_sub_right f _ _ h, add_comm,
    EReal.toENNReal_sub_add_cancel (f.mono.leftLim_le le_rfl) (f.mono.le_leftLim hab)]

lemma measure_Ico_of_ge {a b : ℝ≥0∞} (hab : b ≤ a) : f.measure (Ico a b) = 0 := by simp [hab]

lemma measure_Ico_of_eq_top {a : ℝ≥0∞}
    (h : f a = ⊤ → leftLim f a = ⊤ → ∃ x < a, f x = ⊤) (b : ℝ≥0∞) :
    f.measure (Ico a b) = (leftLim f b - leftLim f a).toENNReal := by
  rcases le_or_lt b a with (hab | hab)
  · symm
    rw [measure_Ico_of_ge f hab, EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono.leftLim hab
  · rw [measure_Ico_of_lt_of_eq_top _ hab h]

@[simp]
theorem measure_Iic (x : ℝ≥0∞) : f.measure (Iic x) = (f x - f 0).toENNReal := by
  rw [← Icc_bot, measure_Icc, leftLim_eq_of_eq_bot, bot_eq_zero']
  simp

@[simp]
theorem measure_Ici (x : ℝ≥0∞) :
    f.measure (Ici x) = leftLim (fun z ↦ (f ∞ - f z).toENNReal) x := by
  rw [← Icc_top, measure_Icc]

@[simp]
lemma measure_Iio (x : ℝ≥0∞) : f.measure (Iio x) = (leftLim f x - f 0).toENNReal := by
  rw [← Ico_bot, bot_eq_zero']
  rcases le_or_lt x 0 with hx_zero | hx_pos
  · simp only [nonpos_iff_eq_zero] at hx_zero
    simp only [bot_eq_zero', hx_zero, lt_self_iff_false, not_false_eq_true, Ico_eq_empty,
      measure_empty]
    rw [leftLim_eq_of_eq_bot _ (by simp), eq_comm, EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
  rw [measure_Ico_of_lt _ hx_pos, leftLim_eq_of_eq_bot _ (by simp)]
  simp

theorem measure_univ : f.measure univ = (f ∞ - f 0).toENNReal := by
  have : (univ : Set ℝ≥0∞) = Icc 0 ∞ := by ext; simp
  rw [this, measure_Icc, leftLim_eq_of_eq_bot]
  simp

@[simp]
lemma measure_const (c : EReal) : (ERealStieltjes.const c).measure = 0 := by
  rw [← Measure.measure_univ_eq_zero, measure_univ]
  simp

@[simp]
lemma measure_zero : (0 : ERealStieltjes).measure = 0 := measure_const 0

@[simp]
lemma measure_Ioi (x : ℝ≥0∞) : f.measure (Ioi x) = (f ∞ - f x).toENNReal := by
  rw [← Ioc_top, measure_Ioc]

instance : SFinite f.measure := by
  sorry

lemma isFiniteMeasure {l u : ℝ} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    IsFiniteMeasure f.measure := by
  constructor
  simp only [f.measure_univ hfl hfu]
  rw [lt_top_iff_ne_top, ne_eq, EReal.toENNReal_eq_top_iff, ← EReal.coe_sub]
  exact EReal.coe_ne_top _

lemma isProbabilityMeasure (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    IsProbabilityMeasure f.measure := ⟨by simp [f.measure_univ hf_bot hf_top]⟩

lemma isLocallyFiniteMeasure (hf : ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤) :
    IsLocallyFiniteMeasure f.measure := by
  refine ⟨fun x ↦ ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (lt_add_one x), ?_⟩⟩
  rw [measure_Ioo, lt_top_iff_ne_top, EReal.toENNReal_ne_top_iff]
  rw [sub_eq_add_neg, EReal.add_ne_top_iff_ne_top_left]
  rotate_left
  · simp only [ne_eq, EReal.neg_eq_bot_iff]
    exact (hf _).2
  · simp only [ne_eq, EReal.neg_eq_top_iff]
    exact (hf _).1
  exact ne_top_of_le_ne_top (hf _).2 (f.mono.leftLim_le le_rfl)

lemma eq_of_measure_of_tendsto_atBot (g : ERealStieltjes) {l : ℝ}
    (hfg : f.measure = g.measure) (hfl : Tendsto f atBot (𝓝 l)) (hgl : Tendsto g atBot (𝓝 l)) :
    f = g := by
  ext x
  have hf := measure_Iic f hfl x
  rw [hfg, measure_Iic g hgl x, EReal.toENNReal_eq_toENNReal, eq_comm] at hf
  · calc f x = (f x - l) + l := by rw [sub_eq_add_neg, add_assoc, add_comm _ (l : EReal),
        ← sub_eq_add_neg, EReal.sub_self] <;> simp
    _ = (g x - l) + l := by rw [hf]
    _ = g x := by rw [sub_eq_add_neg, add_assoc, add_comm _ (l : EReal),
        ← sub_eq_add_neg, EReal.sub_self] <;> simp
  · rw [EReal.sub_nonneg (by simp) (by simp)]
    exact Monotone.le_of_tendsto g.mono hgl x
  · rw [EReal.sub_nonneg (by simp) (by simp)]
    exact Monotone.le_of_tendsto f.mono hfl x

-- this is not enough. We need to remove hf and hg and deal with those issues properly.
-- The measure is then not locally finite because of the possible infinite diracs at xmin and xmax,
-- but we can cut the measure into several pieces to isolate the difficulties.
lemma measure_add (f g : ERealStieltjes) (hf : ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤)
    (hg : ∀ x, g x ≠ ⊥ ∧ g x ≠ ⊤) :
    (f + g).measure = f.measure + g.measure := by
  have hfg x : (f + g) x ≠ ⊥ ∧ (f + g) x ≠ ⊤ := by
    rw [add_apply_of_ne_top (hf x).2 (hg x).2]
    simp only [ne_eq, EReal.add_eq_bot_iff, hf x, hg x, or_self, not_false_eq_true, true_and]
    exact EReal.add_ne_top (hf x).2 (hg x).2
  have := ERealStieltjes.isLocallyFiniteMeasure _ hfg
  refine Measure.ext_of_Ioc _ _ (fun a b h ↦ ?_)
  simp only [measure_Ioc, Pi.add_apply, Measure.coe_add]
  rw [add_apply_of_ne_top (hf b).2 (hg b).2, add_apply_of_ne_top (hf a).2 (hg a).2]
  have hfab : f a ≤ f b := f.mono h.le
  have hgab : g a ≤ g b := g.mono h.le
  lift (f a) to ℝ using (hf a).symm with fa
  lift (f b) to ℝ using (hf b).symm with fb
  lift (g a) to ℝ using (hg a).symm with ga
  lift (g b) to ℝ using (hg b).symm with gb
  norm_cast
  simp_rw [EReal.toENNReal_toEReal]
  rw [← ENNReal.ofReal_add (sub_nonneg_of_le ?_) (sub_nonneg_of_le ?_)]
  rotate_left
  · exact mod_cast hfab
  · exact mod_cast hgab
  congr 1
  ring

-- @[simp]
-- lemma measure_smul (c : ℝ≥0) (f : ERealStieltjes) : (c • f).measure = c • f.measure := by
--   refine Measure.ext_of_Ioc _ _ (fun a b _ ↦ ?_)
--   simp only [measure_Ioc, Measure.smul_apply]
--   change ofReal (c * f b - c * f a) = c • ofReal (f b - f a)
--   rw [← _root_.mul_sub, ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal, ← smul_eq_mul]
--   rfl

end ERealStieltjes
