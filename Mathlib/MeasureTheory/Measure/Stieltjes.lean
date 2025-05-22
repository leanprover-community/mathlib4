/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Order.LeftRightLim

/-!
# Stieltjes measures on the real line

Consider a function `f : ℝ → ℝ` which is monotone and right-continuous. Then one can define a
corresponding measure, giving mass `f b - f a` to the interval `(a, b]`.

## Main definitions

* `StieltjesFunction` is a structure containing a function from `ℝ → ℝ`, together with the
  assertions that it is monotone and right-continuous. To `f : StieltjesFunction`, one associates
  a Borel measure `f.measure`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = ofReal (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = ofReal (leftLim f b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
-/

noncomputable section

open Set Filter Function ENNReal NNReal Topology MeasureTheory

open ENNReal (ofReal)


/-! ### Basic properties of Stieltjes functions -/


/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure StieltjesFunction where
  toFun : ℝ → ℝ
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x

namespace StieltjesFunction

attribute [coe] toFun

instance instCoeFun : CoeFun StieltjesFunction fun _ => ℝ → ℝ :=
  ⟨toFun⟩

initialize_simps_projections StieltjesFunction (toFun → apply)

@[ext] lemma ext {f g : StieltjesFunction} (h : ∀ x, f x = g x) : f = g := by
  exact (StieltjesFunction.mk.injEq ..).mpr (funext h)

variable (f : StieltjesFunction)

theorem mono : Monotone f :=
  f.mono'

theorem right_continuous (x : ℝ) : ContinuousWithinAt f (Ici x) x :=
  f.right_continuous' x

theorem rightLim_eq (f : StieltjesFunction) (x : ℝ) : Function.rightLim f x = f x := by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq, continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x

theorem iInf_Ioi_eq (f : StieltjesFunction) (x : ℝ) : ⨅ r : Ioi x, f r = f x := by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [f.mono.rightLim_eq_sInf, sInf_image']
  rw [← neBot_iff]
  infer_instance

theorem iInf_rat_gt_eq (f : StieltjesFunction) (x : ℝ) :
    ⨅ r : { r' : ℚ // x < r' }, f r = f x := by
  rw [← iInf_Ioi_eq f x]
  refine (Real.iInf_Ioi_eq_iInf_rat_gt _ ?_ f.mono).symm
  refine ⟨f x, fun y => ?_⟩
  rintro ⟨y, hy_mem, rfl⟩
  exact f.mono (le_of_lt hy_mem)

/-- The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure. -/
@[simps]
protected def id : StieltjesFunction where
  toFun := id
  mono' _ _ := id
  right_continuous' _ := continuousWithinAt_id

@[simp]
theorem id_leftLim (x : ℝ) : leftLim StieltjesFunction.id x = x :=
  tendsto_nhds_unique (StieltjesFunction.id.mono.tendsto_leftLim x) <|
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds

instance instInhabited : Inhabited StieltjesFunction :=
  ⟨StieltjesFunction.id⟩

/-- Constant functions are Stieltjes function. -/
protected def const (c : ℝ) : StieltjesFunction where
  toFun := fun _ ↦ c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const

@[simp] lemma const_apply (c x : ℝ) : (StieltjesFunction.const c) x = c := rfl

/-- The sum of two Stieltjes functions is a Stieltjes function. -/
protected def add (f g : StieltjesFunction) : StieltjesFunction where
  toFun := fun x => f x + g x
  mono' := f.mono.add g.mono
  right_continuous' := fun x => (f.right_continuous x).add (g.right_continuous x)

instance : AddZeroClass StieltjesFunction where
  add := StieltjesFunction.add
  zero := StieltjesFunction.const 0
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _

instance : AddCommMonoid StieltjesFunction where
  nsmul n f := nsmulRec n f
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  add_comm _ _ := ext fun _ ↦ add_comm _ _
  __ := StieltjesFunction.instAddZeroClass

instance : Module ℝ≥0 StieltjesFunction where
  smul c f := {
    toFun := fun x ↦ c * f x
    mono' := f.mono.const_mul c.2
    right_continuous' := fun x ↦ (f.right_continuous x).const_smul c.1}
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul _ _ _ := ext fun _ ↦ mul_assoc _ _ _
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add _ _ _ := ext fun _ ↦ mul_add _ _ _
  add_smul _ _ _ := ext fun _ ↦ add_mul _ _ _
  zero_smul _ := ext fun _ ↦ zero_mul _

@[simp] lemma zero_apply (x : ℝ) : (0 : StieltjesFunction) x = 0 := rfl

@[simp] lemma add_apply (f g : StieltjesFunction) (x : ℝ) : (f + g) x = f x + g x := rfl

/-- If a function `f : ℝ → ℝ` is monotone, then the function mapping `x` to the right limit of `f`
at `x` is a Stieltjes function, i.e., it is monotone and right-continuous. -/
noncomputable def _root_.Monotone.stieltjesFunction {f : ℝ → ℝ} (hf : Monotone f) :
    StieltjesFunction where
  toFun := rightLim f
  mono' _ _ hxy := hf.rightLim hxy
  right_continuous' := by
    intro x s hs
    obtain ⟨l, u, hlu, lus⟩ : ∃ l u : ℝ, rightLim f x ∈ Ioo l u ∧ Ioo l u ⊆ s :=
      mem_nhds_iff_exists_Ioo_subset.1 hs
    obtain ⟨y, xy, h'y⟩ : ∃ (y : ℝ), x < y ∧ Ioc x y ⊆ f ⁻¹' Ioo l u :=
      mem_nhdsGT_iff_exists_Ioc_subset.1 (hf.tendsto_rightLim x (Ioo_mem_nhds hlu.1 hlu.2))
    change ∀ᶠ y in 𝓝[≥] x, rightLim f y ∈ s
    filter_upwards [Ico_mem_nhdsGE xy] with z hz
    apply lus
    refine ⟨hlu.1.trans_le (hf.rightLim hz.1), ?_⟩
    obtain ⟨a, za, ay⟩ : ∃ a : ℝ, z < a ∧ a < y := exists_between hz.2
    calc
      rightLim f z ≤ f a := hf.rightLim_le za
      _ < u := (h'y ⟨hz.1.trans_lt za, ay.le⟩).2

theorem _root_.Monotone.stieltjesFunction_eq {f : ℝ → ℝ} (hf : Monotone f) (x : ℝ) :
    hf.stieltjesFunction x = rightLim f x :=
  rfl

theorem countable_leftLim_ne (f : StieltjesFunction) : Set.Countable { x | leftLim f x ≠ f x } := by
  refine Countable.mono ?_ f.mono.countable_not_continuousAt
  intro x hx h'x
  apply hx
  exact tendsto_nhds_unique (f.mono.tendsto_leftLim x) (h'x.tendsto.mono_left nhdsWithin_le_nhds)

/-! ### The outer measure associated to a Stieltjes function -/


/-- Length of an interval. This is the largest monotone function which correctly measures all
intervals. -/
def length (s : Set ℝ) : ℝ≥0∞ :=
  ⨅ (a) (b) (_ : s ⊆ Ioc a b), ofReal (f b - f a)

@[simp]
theorem length_empty : f.length ∅ = 0 :=
  nonpos_iff_eq_zero.1 <| iInf_le_of_le 0 <| iInf_le_of_le 0 <| by simp

@[simp]
theorem length_Ioc (a b : ℝ) : f.length (Ioc a b) = ofReal (f b - f a) := by
  refine
    le_antisymm (iInf_le_of_le a <| iInf₂_le b Subset.rfl)
      (le_iInf fun a' => le_iInf fun b' => le_iInf fun h => ENNReal.coe_le_coe.2 ?_)
  rcases le_or_gt b a with ab | ab
  · rw [Real.toNNReal_of_nonpos (sub_nonpos.2 (f.mono ab))]
    apply zero_le
  obtain ⟨h₁, h₂⟩ := (Ioc_subset_Ioc_iff ab).1 h
  exact Real.toNNReal_le_toNNReal (sub_le_sub (f.mono h₁) (f.mono h₂))

theorem length_mono {s₁ s₂ : Set ℝ} (h : s₁ ⊆ s₂) : f.length s₁ ≤ f.length s₂ :=
  iInf_mono fun _ => biInf_mono fun _ => h.trans

open MeasureTheory

/-- The Stieltjes outer measure associated to a Stieltjes function. -/
protected def outer : OuterMeasure ℝ :=
  OuterMeasure.ofFunction f.length f.length_empty

theorem outer_le_length (s : Set ℝ) : f.outer s ≤ f.length s :=
  OuterMeasure.ofFunction_le _

/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set. -/
theorem length_subadditive_Icc_Ioo {a b : ℝ} {c d : ℕ → ℝ} (ss : Icc a b ⊆ ⋃ i, Ioo (c i) (d i)) :
    ofReal (f b - f a) ≤ ∑' i, ofReal (f (d i) - f (c i)) := by
  suffices
    ∀ (s : Finset ℕ) (b), Icc a b ⊆ (⋃ i ∈ (s : Set ℕ), Ioo (c i) (d i)) →
      (ofReal (f b - f a) : ℝ≥0∞) ≤ ∑ i ∈ s, ofReal (f (d i) - f (c i)) by
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
  · rw [ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 (f.mono ab))]
    exact zero_le _
  have := cv ⟨ab, le_rfl⟩
  simp only [Finset.mem_coe, gt_iff_lt, not_lt, mem_iUnion, mem_Ioo, exists_and_left,
    exists_prop] at this
  rcases this with ⟨i, cb, is, bd⟩
  rw [← Finset.insert_erase is] at cv ⊢
  rw [Finset.coe_insert, biUnion_insert] at cv
  rw [Finset.sum_insert (Finset.not_mem_erase _ _)]
  refine le_trans ?_ (add_le_add_left (IH _ (Finset.erase_ssubset is) (c i) ?_) _)
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
    rw [sub_add_sub_cancel]
    exact sub_le_sub_right (f.mono bd.le) _
  · rintro x ⟨h₁, h₂⟩
    exact (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left (mt And.left (not_gt_of_le h₂))

@[simp]
theorem outer_Ioc (a b : ℝ) : f.outer (Ioc a b) = ofReal (f b - f a) := by
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
  refine
    le_antisymm
      (by
        rw [← f.length_Ioc]
        apply outer_le_length)
      (le_iInf₂ fun s hs => ENNReal.le_of_forall_pos_le_add fun ε εpos h => ?_)
  let δ := ε / 2
  have δpos : 0 < (δ : ℝ≥0∞) := by simpa [δ] using εpos.ne'
  rcases ENNReal.exists_pos_sum_of_countable δpos.ne' ℕ with ⟨ε', ε'0, hε⟩
  obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a' := by
    have A : ContinuousWithinAt (fun r => f r - f a) (Ioi a) a := by
      refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
      exact (f.right_continuous a).mono Ioi_subset_Ici_self
    have B : f a - f a < δ := by rwa [sub_self, NNReal.coe_pos, ← ENNReal.coe_pos]
    exact (((tendsto_order.1 A).2 _ B).and self_mem_nhdsWithin).exists
  have : ∀ i, ∃ p : ℝ × ℝ, s i ⊆ Ioo p.1 p.2 ∧
      (ofReal (f p.2 - f p.1) : ℝ≥0∞) < f.length (s i) + ε' i := by
    intro i
    have hl :=
      ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_ne_zero.2 (ε'0 i).ne')
    conv at hl =>
      lhs
      rw [length]
    simp only [iInf_lt_iff, exists_prop] at hl
    rcases hl with ⟨p, q', spq, hq'⟩
    have : ContinuousWithinAt (fun r => ofReal (f r - f p)) (Ioi q') q' := by
      apply ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
      exact (f.right_continuous q').mono Ioi_subset_Ici_self
    rcases (((tendsto_order.1 this).2 _ hq').and self_mem_nhdsWithin).exists with ⟨q, hq, q'q⟩
    exact ⟨⟨p, q⟩, spq.trans (Ioc_subset_Ioo_right q'q), hq⟩
  choose g hg using this
  have I_subset : Icc a' b ⊆ ⋃ i, Ioo (g i).1 (g i).2 :=
    calc
      Icc a' b ⊆ Ioc a b := fun x hx => ⟨aa'.trans_le hx.1, hx.2⟩
      _ ⊆ ⋃ i, s i := hs
      _ ⊆ ⋃ i, Ioo (g i).1 (g i).2 := iUnion_mono fun i => (hg i).1
  calc
    ofReal (f b - f a) = ofReal (f b - f a' + (f a' - f a)) := by rw [sub_add_sub_cancel]
    _ ≤ ofReal (f b - f a') + ofReal (f a' - f a) := ENNReal.ofReal_add_le
    _ ≤ ∑' i, ofReal (f (g i).2 - f (g i).1) + ofReal δ :=
      (add_le_add (f.length_subadditive_Icc_Ioo I_subset) (ENNReal.ofReal_le_ofReal ha'.le))
    _ ≤ ∑' i, (f.length (s i) + ε' i) + δ :=
      (add_le_add (ENNReal.tsum_le_tsum fun i => (hg i).2.le)
        (by simp only [ENNReal.ofReal_coe_nnreal, le_rfl]))
    _ = ∑' i, f.length (s i) + ∑' i, (ε' i : ℝ≥0∞) + δ := by rw [ENNReal.tsum_add]
    _ ≤ ∑' i, f.length (s i) + δ + δ := add_le_add (add_le_add le_rfl hε.le) le_rfl
    _ = ∑' i : ℕ, f.length (s i) + ε := by simp [δ, add_assoc, ENNReal.add_halves]

theorem measurableSet_Ioi {c : ℝ} : MeasurableSet[f.outer.caratheodory] (Ioi c) := by
  refine OuterMeasure.ofFunction_caratheodory fun t => ?_
  refine le_iInf fun a => le_iInf fun b => le_iInf fun h => ?_
  refine
    le_trans
      (add_le_add (f.length_mono <| inter_subset_inter_left _ h)
        (f.length_mono <| diff_subset_diff_left h)) ?_
  rcases le_total a c with hac | hac <;> rcases le_total b c with hbc | hbc
  · simp only [Ioc_inter_Ioi, f.length_Ioc, hac, hbc, le_refl, Ioc_eq_empty,
      max_eq_right, min_eq_left, Ioc_diff_Ioi, f.length_empty, zero_add, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      ← ENNReal.ofReal_add, f.mono hac, f.mono hbc, sub_nonneg,
      sub_add_sub_cancel, le_refl,
      max_eq_right]
  · simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_diff_Ioi, f.length_empty,
      zero_add, or_true, le_sup_iff, f.length_Ioc, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty, not_lt]

theorem outer_trim : f.outer.trim = f.outer := by
  refine le_antisymm (fun s => ?_) (OuterMeasure.le_trim _)
  rw [OuterMeasure.trim_eq_iInf]
  refine le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩
  refine le_trans ?_ (add_le_add_left (le_of_lt hε) _)
  rw [← ENNReal.tsum_add]
  choose g hg using
    show ∀ i, ∃ s, t i ⊆ s ∧ MeasurableSet s ∧ f.outer s ≤ f.length (t i) + ofReal (ε' i) by
      intro i
      have hl :=
        ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_pos.2 (ε'0 i)).ne'
      conv at hl =>
        lhs
        rw [length]
      simp only [iInf_lt_iff] at hl
      rcases hl with ⟨a, b, h₁, h₂⟩
      rw [← f.outer_Ioc] at h₂
      exact ⟨_, h₁, measurableSet_Ioc, le_of_lt <| by simpa using h₂⟩
  simp only [ofReal_coe_nnreal] at hg
  apply iInf_le_of_le (iUnion g) _
  apply iInf_le_of_le (ht.trans <| iUnion_mono fun i => (hg i).1) _
  apply iInf_le_of_le (MeasurableSet.iUnion fun i => (hg i).2.1) _
  exact le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun i => (hg i).2.2)

theorem borel_le_measurable : borel ℝ ≤ f.outer.caratheodory := by
  rw [borel_eq_generateFrom_Ioi]
  refine MeasurableSpace.generateFrom_le ?_
  simp +contextual [f.measurableSet_Ioi]

/-! ### The measure associated to a Stieltjes function -/


/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. -/
protected irreducible_def measure : Measure ℝ where
  toOuterMeasure := f.outer
  m_iUnion _s hs := f.outer.iUnion_eq_of_caratheodory fun i => f.borel_le_measurable _ (hs i)
  trim_le := f.outer_trim.le

@[simp]
theorem measure_Ioc (a b : ℝ) : f.measure (Ioc a b) = ofReal (f b - f a) := by
  rw [StieltjesFunction.measure]
  exact f.outer_Ioc a b

@[simp]
theorem measure_singleton (a : ℝ) : f.measure {a} = ofReal (f a - leftLim f a) := by
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
    ∃ u : ℕ → ℝ, StrictMono u ∧ (∀ n : ℕ, u n < a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto a
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine Subset.antisymm (fun x hx => by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx => ?_
    simp? at hx says simp only [mem_iInter, mem_Ioc] at hx
    have : a ≤ x := le_of_tendsto' u_lim fun n => (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (f.measure {a})) := by
    rw [A]
    refine tendsto_measure_iInter_atTop (fun n => nullMeasurableSet_Ioc)
      (fun m n hmn => ?_) ?_
    · exact Ioc_subset_Ioc_left (u_mono.monotone hmn)
    · exact ⟨0, by simpa only [measure_Ioc] using ENNReal.ofReal_ne_top⟩
  have L2 :
      Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (ofReal (f a - leftLim f a))) := by
    simp only [measure_Ioc]
    have : Tendsto (fun n => f (u n)) atTop (𝓝 (leftLim f a)) := by
      apply (f.mono.tendsto_leftLim a).comp
      exact
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ u_lim
          (Eventually.of_forall fun n => u_lt_a n)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub this)
  exact tendsto_nhds_unique L1 L2

@[simp]
theorem measure_Icc (a b : ℝ) : f.measure (Icc a b) = ofReal (f b - leftLim f a) := by
  rcases le_or_gt a b with (hab | hab)
  · have A : Disjoint {a} (Ioc a b) := by simp
    simp [← Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ← ENNReal.ofReal_add,
      f.mono.leftLim_le, measure_union A measurableSet_Ioc, f.mono hab]
  · simp only [hab, measure_empty, Icc_eq_empty, not_le]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.le_leftLim hab]

@[simp]
theorem measure_Ioo {a b : ℝ} : f.measure (Ioo a b) = ofReal (leftLim f b - f a) := by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ioo_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim_le hab]
  · have A : Disjoint (Ioo a b) {b} := by simp
    have D : f b - f a = f b - leftLim f b + (leftLim f b - f a) := by abel
    have := f.measure_Ioc a b
    simp only [← Ioo_union_Icc_eq_Ioc hab le_rfl, measure_singleton,
      measure_union A (measurableSet_singleton b), Icc_self] at this
    rw [D, ENNReal.ofReal_add, add_comm] at this
    · simpa only [ENNReal.add_right_inj ENNReal.ofReal_ne_top]
    · simp only [f.mono.leftLim_le le_rfl, sub_nonneg]
    · simp only [f.mono.le_leftLim hab, sub_nonneg]

@[simp]
theorem measure_Ico (a b : ℝ) : f.measure (Ico a b) = ofReal (leftLim f b - leftLim f a) := by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ico_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim hab]
  · have A : Disjoint {a} (Ioo a b) := by simp
    simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, hab.ne, f.mono.leftLim_le,
      measure_union A measurableSet_Ioo, f.mono.le_leftLim hab, ← ENNReal.ofReal_add]

theorem measure_Iic {l : ℝ} (hf : Tendsto f atBot (𝓝 l)) (x : ℝ) :
    f.measure (Iic x) = ofReal (f x - l) := by
  refine tendsto_nhds_unique (tendsto_measure_Ioc_atBot _ _) ?_
  simp_rw [measure_Ioc]
  exact ENNReal.tendsto_ofReal (Tendsto.const_sub _ hf)

lemma measure_Iio {l : ℝ} (hf : Tendsto f atBot (𝓝 l)) (x : ℝ) :
    f.measure (Iio x) = ofReal (leftLim f x - l) := by
  rw [← Iic_diff_right, measure_diff _ (nullMeasurableSet_singleton x), measure_singleton,
    f.measure_Iic hf, ← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp

theorem measure_Ici {l : ℝ} (hf : Tendsto f atTop (𝓝 l)) (x : ℝ) :
    f.measure (Ici x) = ofReal (l - leftLim f x) := by
  refine tendsto_nhds_unique (tendsto_measure_Ico_atTop _ _) ?_
  simp_rw [measure_Ico]
  refine ENNReal.tendsto_ofReal (Tendsto.sub_const ?_ _)
  have h_le1 : ∀ x, f (x - 1) ≤ leftLim f x := fun x => Monotone.le_leftLim f.mono (sub_one_lt x)
  have h_le2 : ∀ x, leftLim f x ≤ f x := fun x => Monotone.leftLim_le f.mono le_rfl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hf.comp ?_) hf h_le1 h_le2
  rw [tendsto_atTop_atTop]
  exact fun y => ⟨y + 1, fun z hyz => by rwa [le_sub_iff_add_le]⟩

lemma measure_Ioi {l : ℝ} (hf : Tendsto f atTop (𝓝 l)) (x : ℝ) :
    f.measure (Ioi x) = ofReal (l - f x) := by
  rw [← Ici_diff_left, measure_diff _ (nullMeasurableSet_singleton x), measure_singleton,
    f.measure_Ici hf, ← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp

lemma measure_Ioi_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : ℝ) :
    f.measure (Ioi x) = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_atTop.mp hf (r + f x))
  exact (f.measure_Ioc x (max x N) ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
    le_tsub_of_add_le_right <| hN _ (le_max_right x N))).trans (measure_mono Ioc_subset_Ioi_self)

lemma measure_Ici_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : ℝ) :
    f.measure (Ici x) = ∞ := by
  rw [← top_le_iff, ← f.measure_Ioi_of_tendsto_atTop_atTop hf x]
  exact measure_mono Ioi_subset_Ici_self

lemma measure_Iic_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : ℝ) :
    f.measure (Iic x) = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atBot.mp (tendsto_atBot.mp hf (f x - r))
  exact (f.measure_Ioc (min x N) x ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
    le_sub_comm.mp <| hN _ (min_le_right x N))).trans (measure_mono Ioc_subset_Iic_self)

lemma measure_Iio_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : ℝ) :
    f.measure (Iio x) = ∞ := by
  rw [← top_le_iff, ← f.measure_Iic_of_tendsto_atBot_atBot hf (x - 1)]
  exact measure_mono <| Set.Iic_subset_Iio.mpr <| sub_one_lt x

theorem measure_univ {l u : ℝ} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    f.measure univ = ofReal (u - l) := by
  refine tendsto_nhds_unique (tendsto_measure_Iic_atTop _) ?_
  simp_rw [measure_Iic f hfl]
  exact ENNReal.tendsto_ofReal (Tendsto.sub_const hfu _)

lemma measure_univ_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) :
    f.measure univ = ∞ := by
  rw [← top_le_iff, ← f.measure_Ioi_of_tendsto_atTop_atTop hf 0]
  exact measure_mono (subset_univ _)

lemma measure_univ_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) :
    f.measure univ = ∞ := by
  rw [← top_le_iff, ← f.measure_Iio_of_tendsto_atBot_atBot hf 0]
  exact measure_mono (subset_univ _)

lemma isFiniteMeasure {l u : ℝ} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    IsFiniteMeasure f.measure := ⟨by simp [f.measure_univ hfl hfu]⟩

lemma isProbabilityMeasure (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    IsProbabilityMeasure f.measure := ⟨by simp [f.measure_univ hf_bot hf_top]⟩

instance instIsLocallyFiniteMeasure : IsLocallyFiniteMeasure f.measure :=
  ⟨fun x => ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), by simp⟩⟩

lemma eq_of_measure_of_tendsto_atBot (g : StieltjesFunction) {l : ℝ}
    (hfg : f.measure = g.measure) (hfl : Tendsto f atBot (𝓝 l)) (hgl : Tendsto g atBot (𝓝 l)) :
    f = g := by
  ext x
  have hf := measure_Iic f hfl x
  rw [hfg, measure_Iic g hgl x, ENNReal.ofReal_eq_ofReal_iff, eq_comm] at hf
  · simpa using hf
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto g.mono hgl x
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto f.mono hfl x

lemma eq_of_measure_of_eq (g : StieltjesFunction) {y : ℝ}
    (hfg : f.measure = g.measure) (hy : f y = g y) :
    f = g := by
  ext x
  cases le_total x y with
  | inl hxy =>
    have hf := measure_Ioc f x y
    rw [hfg, measure_Ioc g x y, ENNReal.ofReal_eq_ofReal_iff, eq_comm, hy] at hf
    · simpa using hf
    · rw [sub_nonneg]
      exact g.mono hxy
    · rw [sub_nonneg]
      exact f.mono hxy
  | inr hxy =>
    have hf := measure_Ioc f y x
    rw [hfg, measure_Ioc g y x, ENNReal.ofReal_eq_ofReal_iff, eq_comm, hy] at hf
    · simpa using hf
    · rw [sub_nonneg]
      exact g.mono hxy
    · rw [sub_nonneg]
      exact f.mono hxy

@[simp]
lemma measure_zero : StieltjesFunction.measure 0 = 0 :=
  Measure.ext_of_Ioc _ _ (by simp)

@[simp]
lemma measure_const (c : ℝ) : (StieltjesFunction.const c).measure = 0 :=
  Measure.ext_of_Ioc _ _ (by simp)

@[simp]
lemma measure_add (f g : StieltjesFunction) : (f + g).measure = f.measure + g.measure := by
  refine Measure.ext_of_Ioc _ _ (fun a b h ↦ ?_)
  simp only [measure_Ioc, add_apply, Measure.coe_add, Pi.add_apply]
  rw [← ENNReal.ofReal_add (sub_nonneg_of_le (f.mono h.le)) (sub_nonneg_of_le (g.mono h.le))]
  ring_nf

@[simp]
lemma measure_smul (c : ℝ≥0) (f : StieltjesFunction) : (c • f).measure = c • f.measure := by
  refine Measure.ext_of_Ioc _ _ (fun a b _ ↦ ?_)
  simp only [measure_Ioc, Measure.smul_apply]
  change ofReal (c * f b - c * f a) = c • ofReal (f b - f a)
  rw [← _root_.mul_sub, ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal, ← smul_eq_mul]
  rfl

end StieltjesFunction
