/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.MeasureTheory.Measure.Stieltjes.Aux
import Mathlib.MeasureTheory.Measure.Stieltjes

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

open Set Filter Function Topology MeasureTheory

open scoped ENNReal NNReal

/-! ### Basic properties of Stieltjes functions -/

/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure ERealStieltjes where
  /-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
  toFun : ℝ≥0∞ → EReal
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x

namespace ERealStieltjes

attribute [coe] toFun

instance instCoeFun : CoeFun ERealStieltjes fun _ ↦ ℝ≥0∞ → EReal where
  coe := toFun

initialize_simps_projections ERealStieltjes (toFun → apply)

@[ext] lemma ext {f g : ERealStieltjes} (h : ∀ x, f x = g x) : f = g :=
  (ERealStieltjes.mk.injEq ..).mpr (funext h)

variable (f : ERealStieltjes) {x : ℝ≥0∞}

theorem mono : Monotone f := f.mono'

theorem right_continuous (x : ℝ≥0∞) : ContinuousWithinAt f (Ici x) x := f.right_continuous' x

theorem rightLim_eq (f : ERealStieltjes) (x : ℝ≥0∞) : Function.rightLim f x = f x := by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq, continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x

-- theorem iInf_Ioi_eq (f : ERealStieltjes) (x : ℝ≥0) : ⨅ r : Ioi x, f r = f x := by
--   suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
--   rw [f.mono.rightLim_eq_sInf, sInf_image']
--   rw [← neBot_iff]
--   infer_instance

/-- Constant functions are Stieltjes function. -/
protected def const (c : EReal) : ERealStieltjes where
  toFun := fun _ ↦ c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const

@[simp] lemma const_apply (c : EReal) (x : ℝ≥0∞) : ERealStieltjes.const c x = c := rfl

instance : Zero ERealStieltjes where
  zero := ERealStieltjes.const 0

@[simp] lemma zero_apply (x : ℝ≥0∞) : (0 : ERealStieltjes) x = 0 := rfl

instance : Inhabited ERealStieltjes where
  default := 0

/-- The sum of two Stieltjes functions is a Stieltjes function. -/
protected def add (f g : ERealStieltjes) : ERealStieltjes where
  toFun := fun x ↦ -(- f x - g x) -- to ensure right continuity
  mono' x y hxy := by
    rw [EReal.neg_le_neg_iff]
    refine EReal.sub_le_sub ?_ (g.mono hxy)
    rw [EReal.neg_le_neg_iff]
    exact f.mono hxy
  right_continuous' x := by
    have hf := (f.right_continuous x).neg
    have hg := (g.right_continuous x).neg
    refine ContinuousWithinAt.neg ?_
    rw [ContinuousWithinAt] at hf hg ⊢
    simp_rw [sub_eq_add_neg]
    by_cases hf_top : f x = ⊤
    · simp only [hf_top, EReal.neg_top, EReal.bot_add]
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      have hfy : f y = ⊤ := eq_top_mono (f.mono hy) hf_top
      simp [hfy]
    by_cases hg_top : g x = ⊤
    · simp only [hg_top, EReal.neg_top, EReal.add_bot]
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      have hgy : g y = ⊤ := eq_top_mono (g.mono hy) hg_top
      simp [hgy]
    have hf_bot : - f x ≠ ⊥ := by simp [hf_top]
    have hg_bot : - g x ≠ ⊥ := by simp [hg_top]
    have h_tendsto : ContinuousAt (fun (p : EReal × EReal) ↦ p.1 + p.2) (-f x, -g x) :=
      EReal.continuousAt_add (Or.inr hg_bot) (Or.inl hf_bot)
    rw [ContinuousAt] at h_tendsto
    change Tendsto ((fun p : EReal × EReal ↦ p.1 + p.2) ∘ (fun x ↦ (-f x, -g x)))
      (𝓝[≥] x) (𝓝 (-f x + -g x))
    exact h_tendsto.comp <| Tendsto.prodMk_nhds hf hg

instance : Add ERealStieltjes where
  add := ERealStieltjes.add

lemma add_apply (f g : ERealStieltjes) (x : ℝ≥0∞) : (f + g) x = - (-f x - g x) := rfl

lemma add_apply_of_ne_top {f g : ERealStieltjes} (hfx : f x ≠ ⊤) (hgx : g x ≠ ⊤) :
    (f + g) x = f x + g x := by
  rw [add_apply, EReal.neg_sub (Or.inl _) (Or.inr hgx), neg_neg]
  simp [hfx]

lemma add_apply_of_eq_top_left {f g : ERealStieltjes} (hfx : f x = ⊤) :
    (f + g) x = ⊤ := by
  simp [add_apply, hfx]

lemma add_apply_of_eq_top_right {f g : ERealStieltjes} (hgx : g x = ⊤) :
    (f + g) x = ⊤ := by
  simp [add_apply, hgx]

instance : AddZeroClass ERealStieltjes where
  zero_add _ := by ext; simp [add_apply]
  add_zero _ := by ext; simp [add_apply]

instance : AddCommMonoid ERealStieltjes where
  nsmul n f := nsmulRec n f
  add_assoc f g h := ext fun x ↦ by
    by_cases hfx : f x = ⊤
    · rw [add_apply_of_eq_top_left, add_apply_of_eq_top_left hfx]
      rw [add_apply_of_eq_top_left hfx]
    by_cases hgx : g x = ⊤
    · rw [add_apply_of_eq_top_left, add_apply_of_eq_top_right]
      · rw [add_apply_of_eq_top_left hgx]
      · rw [add_apply_of_eq_top_right hgx]
    by_cases hhx : h x = ⊤
    · rw [add_apply_of_eq_top_right hhx, add_apply_of_eq_top_right]
      rw [add_apply_of_eq_top_right hhx]
    rw [add_apply_of_ne_top _ hhx, add_apply_of_ne_top hfx hgx, add_apply_of_ne_top hfx,
      add_apply_of_ne_top hgx hhx, add_assoc]
    · rw [add_apply_of_ne_top hgx hhx]
      exact EReal.add_ne_top hgx hhx
    · rw [add_apply_of_ne_top hfx hgx, ne_eq]
      exact EReal.add_ne_top hfx hgx
  add_comm f g := ext fun x ↦ by
    by_cases hfx : f x = ⊤
    · rw [add_apply_of_eq_top_left hfx, add_apply_of_eq_top_right hfx]
    by_cases hgx : g x = ⊤
    · rw [add_apply_of_eq_top_left hgx, add_apply_of_eq_top_right hgx]
    rw [add_apply_of_ne_top hfx hgx, add_apply_of_ne_top hgx hfx, add_comm]
  __ := ERealStieltjes.instAddZeroClass

instance : SMul ℝ≥0 ERealStieltjes where
  smul c f := {
    toFun := fun x ↦ c * f x
    mono' := by
      refine f.mono.const_mul ?_
      exact mod_cast zero_le'
    right_continuous' := fun x ↦
      EReal.continuous_coe_mul.continuousAt.comp_continuousWithinAt (f.right_continuous x) }

@[simp]
lemma smul_apply (c : ℝ≥0) (f : ERealStieltjes) : (c • f) x = c * f x := rfl

instance : Module ℝ≥0 ERealStieltjes where
  smul c f := c • f
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul a b f := ext fun x ↦ by
    simp only [smul_apply, ENNReal.coe_mul, EReal.coe_ennreal_mul]
    rw [mul_assoc]
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add c f g := ext fun x ↦ by
    simp only [smul_apply, add_apply, mul_neg, neg_inj]
    have : (c : EReal) = ((c : ℝ) : EReal) := rfl
    simp_rw [this]
    rw [sub_eq_add_neg, EReal.coe_mul_add_of_nonneg]
    swap; · exact c.2
    rw [mul_comm _ (f x), ← EReal.neg_mul, mul_comm]
    congr 1
    rw [mul_comm _ (g x), ← EReal.neg_mul, mul_comm]
  add_smul a b f := ext fun x ↦ by
    by_cases ha0 : a = 0
    · simp [ha0, add_apply]
    by_cases hfx : f x = ⊤
    · rw [smul_apply, hfx, add_apply_of_eq_top_left]
      · have : ((a + b : ℝ≥0) : EReal) = ((a + b : ℝ) : EReal) := rfl
        rw [this, EReal.coe_mul_top_of_pos]
        positivity
      · have : (a : EReal) = ((a : ℝ) : EReal) := rfl
        rw [smul_apply, hfx, this, EReal.coe_mul_top_of_pos]
        positivity
    rw [add_apply_of_ne_top]
    · simp only [smul_apply, ENNReal.coe_add, EReal.coe_ennreal_add]
      have h_eq (a : ℝ≥0) : (a : EReal) = ((a : ℝ) : EReal) := rfl
      rw [h_eq, h_eq, EReal.coe_add_mul_of_nonneg]
      · positivity
      · positivity
    · have : (a : EReal) = ((a : ℝ) : EReal) := rfl
      rw [smul_apply, this, EReal.mul_ne_top]
      simp [hfx]
    · have : (b : EReal) = ((b : ℝ) : EReal) := rfl
      rw [smul_apply, this, EReal.mul_ne_top]
      simp [hfx]
  zero_smul _ := ext fun _ ↦ zero_mul _

theorem countable_leftLim_ne (f : ERealStieltjes) : Set.Countable { x | leftLim f x ≠ f x } := by
  refine Countable.mono ?_ f.mono.countable_not_continuousAt
  intro x hx h'x
  apply hx
  by_cases hx_zero : x = 0
  · rw [leftLim_eq_of_eq_bot]
    simp [hx_zero]
  have : (𝓝[<] x).NeBot := by simp [hx_zero]
  exact tendsto_nhds_unique (f.mono.tendsto_leftLim x) (h'x.tendsto.mono_left nhdsWithin_le_nhds)

section EffectiveDomain

def xmin : ℝ≥0∞ := sInf {y | f y ≠ ⊥}

def xmax : ℝ≥0∞ := sSup {y | f y ≠ ⊤}

end EffectiveDomain

lemma continuousWithinAt_sub_const_Ici {c : EReal} {a : ℝ≥0∞} (h_bot : f a ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousWithinAt (fun x ↦ f x - c) (Ici a) a :=
  (EReal.continuousAt_sub_const h_bot).comp_continuousWithinAt (f.right_continuous a)

lemma continuousWithinAt_const_sub_Ici {c : EReal} {a : ℝ≥0∞} (h_bot : f a ≠ ⊤ ∨ c ≠ ⊤) :
    ContinuousWithinAt (fun x ↦ c - f x) (Ici a) a :=
  (EReal.continuousAt_const_sub h_bot).comp_continuousWithinAt (f.right_continuous a)

lemma continuousWithinAt_sub_const_Ioi {c : EReal} {a : ℝ≥0∞} (h_bot : f a ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousWithinAt (fun x ↦ f x - c) (Ioi a) a :=
  (f.continuousWithinAt_sub_const_Ici h_bot).mono Ioi_subset_Ici_self

lemma antitone_toENNReal_const_sub (a : ℝ≥0∞) :
    Antitone (fun x ↦ (f a - f x).toENNReal) :=
  fun _ _ hxy ↦ EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl (f.mono hxy))

lemma leftLim_toENNReal_sub_left (a b : ℝ≥0∞) :
    leftLim (fun x ↦ (f x - f a).toENNReal) b = (leftLim f b - f a).toENNReal := by
  by_cases hb_zero : b = 0
  · have : 𝓝[<] b = ⊥ := by simp [hb_zero]
    simp_rw [leftLim_eq_of_eq_bot _ this]
  have : (𝓝[<] b).NeBot := by simp [hb_zero]
  rcases le_or_lt a b with (_ | hab)
  swap
  · refine leftLim_eq_of_tendsto NeBot.ne' ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    have : ∀ᶠ x in 𝓝[<] b, x < a := by
      refine eventually_nhdsWithin_iff.mpr ?_
      filter_upwards [eventually_lt_nhds hab] with x hx _ using hx
    filter_upwards [this] with x hx
    rw [EReal.toENNReal_of_nonpos, EReal.toENNReal_of_nonpos]
    · rw [EReal.sub_nonpos]
      exact f.mono.leftLim_le hab.le
    · rw [EReal.sub_nonpos]
      exact f.mono hx.le
  by_cases hfa : f a = ⊥
  · simp [hfa, sub_eq_add_neg]
    by_cases h_lim : leftLim f b = ⊥
    · simp only [h_lim, EReal.bot_add, ne_eq, bot_ne_top, not_false_eq_true,
        EReal.toENNReal_of_ne_top, EReal.toReal_bot, ENNReal.ofReal_zero]
      have h_lt x (hxb : x < b) : f x = ⊥ := eq_bot_mono (f.mono.le_leftLim hxb) h_lim
      refine leftLim_eq_of_tendsto NeBot.ne' ?_
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
      simp [h_lt x hx]
    · rw [EReal.add_top_of_ne_bot h_lim, EReal.toENNReal_top]
      refine leftLim_eq_of_tendsto NeBot.ne' ?_
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      obtain ⟨x, hxb, hx⟩ : ∃ x < b, f x ≠ ⊥ := by
        by_contra! h_bot
        refine h_lim ?_
        refine leftLim_eq_of_tendsto NeBot.ne' ?_
        refine (tendsto_congr' ?_).mpr tendsto_const_nhds
        exact eventually_nhdsWithin_of_forall h_bot
      have : ∀ᶠ y in 𝓝[<] b, x < y := by
        refine eventually_nhdsWithin_iff.mpr ?_
        filter_upwards [eventually_gt_nhds hxb] with y hy _ using hy
      filter_upwards [this] with y hy
      rw [EReal.toENNReal_eq_top_iff, EReal.add_top_of_ne_bot]
      exact fun h_bot ↦ hx (eq_bot_mono (f.mono hy.le) h_bot)
  refine leftLim_eq_of_tendsto NeBot.ne' ?_
  have h1 := EReal.continuous_toENNReal.tendsto (leftLim f b - f a)
  have h2 := EReal.continuousAt_sub_const (c := f a) (x := leftLim f b) (Or.inr hfa)
  exact h1.comp <| h2.tendsto.comp <| f.mono.tendsto_leftLim _

lemma leftLim_toENNReal_sub_right (a : ℝ≥0∞) (c : EReal)
    (h : c = ⊤ → leftLim f a = ⊤ → ∃ x < a, f x = ⊤) :
    leftLim (fun x ↦ (c - f x).toENNReal) a = (c - leftLim f a).toENNReal := by
  by_cases ha_zero : a = 0
  · have : 𝓝[<] a = ⊥ := by simp [ha_zero]
    simp_rw [leftLim_eq_of_eq_bot _ this]
  have : (𝓝[<] a).NeBot := by simp [ha_zero]
  rcases le_or_lt (leftLim f a) c with (hab | hab)
  swap
  · refine leftLim_eq_of_tendsto NeBot.ne' ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    have : ∀ᶠ x in 𝓝[<] a, c < f x :=
      Filter.Tendsto.eventually_const_lt hab (f.mono.tendsto_leftLim _)
    filter_upwards [this] with x hx
    rw [EReal.toENNReal_of_nonpos, EReal.toENNReal_of_nonpos]
    · rw [EReal.sub_nonpos]
      exact hab.le
    · rw [EReal.sub_nonpos]
      exact hx.le
  have h1 := EReal.continuous_toENNReal.tendsto (c - leftLim f a)
  have h2 := EReal.continuousAt_const_sub (c := c) (x := leftLim f a)
  by_cases hfb : c = ⊤
  swap
  · refine leftLim_eq_of_tendsto NeBot.ne' ?_
    refine h1.comp ?_
    refine (h2 (Or.inr hfb)).tendsto.comp ?_
    exact f.mono.tendsto_leftLim _
  specialize h hfb
  by_cases h_lim : leftLim f a = ⊤
  swap
  · refine leftLim_eq_of_tendsto NeBot.ne' ?_
    refine h1.comp ?_
    refine (h2 (Or.inl h_lim)).tendsto.comp ?_
    exact f.mono.tendsto_leftLim _
  specialize h h_lim
  obtain ⟨x, hx⟩ := h
  have hfa_lim : leftLim f a = ⊤ := eq_top_mono (f.mono.le_leftLim hx.1) hx.2
  have hfb : c = ⊤ := eq_top_mono hab hfa_lim
  simp only [hfb, hfa_lim, EReal.sub_top, ne_eq, bot_ne_top, not_false_eq_true,
    EReal.toENNReal_of_ne_top, EReal.toReal_bot, ENNReal.ofReal_zero]
  refine leftLim_eq_of_tendsto NeBot.ne' ?_
  refine (tendsto_congr' ?_).mpr tendsto_const_nhds
  have : ∀ᶠ y in 𝓝[<] a, x < y := by
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [eventually_gt_nhds hx.1] with x hx _ using hx
  filter_upwards [this] with y hy
  rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos, ← eq_top_iff]
  refine eq_top_mono (f.mono hy.le) hx.2

end ERealStieltjes
