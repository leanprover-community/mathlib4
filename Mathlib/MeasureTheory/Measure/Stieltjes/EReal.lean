/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Instances.EReal.Lemmas
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

open Set Filter Function ENNReal NNReal Topology MeasureTheory

namespace EReal

@[simp]
lemma toENNReal_one : (1 : EReal).toENNReal = 1 := by
  rw [toENNReal_of_ne_top]
  · simp
  · simpa using natCast_ne_top 1

lemma toENNReal_toEReal (x : ℝ) : EReal.toENNReal x = ENNReal.ofReal x := rfl

lemma continuousAt_sub {p : EReal × EReal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊤) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊥) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 - p.2) p := by
  simp_rw [sub_eq_add_neg]
  change ContinuousAt ((fun p : EReal × EReal => p.1 + p.2) ∘ (fun p ↦ (p.1, -p.2))) p
  exact (EReal.continuousAt_add (by simp [h]) (by simp [h'])).comp (by fun_prop)

lemma continuousAt_const_sub {c x : EReal} (h' : x ≠ ⊤ ∨ c ≠ ⊤) :
    ContinuousAt (fun x : EReal ↦ c - x) x := by
  by_cases hc_top : c = ⊥
  · simpa [hc_top] using continuous_const.continuousAt
  change ContinuousAt ((fun p : EReal × EReal ↦ p.1 - p.2) ∘ (fun x ↦ (c, x))) x
  exact (EReal.continuousAt_sub h'.symm (Or.inl hc_top)).comp (by fun_prop)

lemma continuousAt_sub_const {c x : EReal} (h' : x ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousAt (fun x : EReal ↦ x - c) x := by
  by_cases hc_top : c = ⊤
  · simpa [hc_top] using continuous_const.continuousAt
  change ContinuousAt ((fun p : EReal × EReal ↦ p.1 - p.2) ∘ (fun x ↦ (x, c))) x
  exact (EReal.continuousAt_sub (Or.inr hc_top) h').comp (by fun_prop)

lemma continuous_coe_mul {c : ℝ} : Continuous (fun x : EReal ↦ c * x) := by
  by_cases hc0 : c = 0
  · simpa [hc0] using continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  have h_cont : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (c, x) := by
    refine EReal.continuousAt_mul ?_ ?_ ?_ ?_ <;> exact Or.inl (by simp [hc0])
  refine h_cont.comp ?_
  fun_prop

lemma coe_mul_add_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    x * (y + z) = x * y + x * z := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx_pos : 0 < x := hx_nonneg.lt_of_ne' hx0
  induction y
  · simp [EReal.coe_mul_bot_of_pos hx_pos]
  · induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · norm_cast
      rw [mul_add]
    · simp only [coe_add_top, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.coe_add_top]
  · simp only [EReal.coe_mul_top_of_pos hx_pos]
    induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · simp only [top_add_coe, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.top_add_coe]
    · simp [EReal.coe_mul_top_of_pos hx_pos]

lemma top_mul_add_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⊤ * (x + y) = ⊤ * x + ⊤ * y := by
  induction x, y using EReal.induction₂_symm with
  | symm h =>
    rw [add_comm, add_comm (⊤ * _)]
    exact h hy hx
  | top_top => simp
  | top_pos _ h =>
    rw [top_add_coe, top_mul_top, top_mul_of_pos, top_add_top]
    exact mod_cast h
  | top_zero => simp
  | top_neg _ h =>
    refine absurd hy ?_
    exact mod_cast h.not_le
  | top_bot => simp
  | pos_bot => simp
  | coe_coe x y =>
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have hx_pos : 0 < (x : EReal) := by
      refine hx.lt_of_ne' ?_
      exact mod_cast hx0
    have hy_pos : 0 < (y : EReal) := by
      refine hy.lt_of_ne' ?_
      exact mod_cast hy0
    rw [top_mul_of_pos hx_pos, top_mul_of_pos hy_pos, top_mul_of_pos]
    · simp
    · exact add_pos hx_pos hy_pos
  | zero_bot => simp
  | neg_bot => simp
  | bot_bot => simp

lemma mul_add_coe_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * (y + z) = x * y + x * z := by
  by_cases hx_top : x = ⊤
  · rw [hx_top]
    exact top_mul_add_of_nonneg (mod_cast hy) (mod_cast hz)
  by_cases hx_bot : x = ⊥
  · rw [hx_bot]
    by_cases hy0 : y = 0
    · simp [hy0]
    by_cases hz0 : z = 0
    · simp [hz0]
    have hy_pos : 0 < (y : EReal) := lt_of_le_of_ne' (mod_cast hy) (mod_cast hy0)
    have hz_pos : 0 < (z : EReal) := lt_of_le_of_ne' (mod_cast hz) (mod_cast hz0)
    rw [bot_mul_of_pos hy_pos, bot_mul_of_pos hz_pos, bot_mul_of_pos]
    · simp
    · exact add_pos hy_pos hz_pos
  lift x to ℝ using ⟨hx_top, hx_bot⟩
  norm_cast
  rw [mul_add]

lemma coe_add_mul_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (y + z) * x = y * x + z * x := by
  simp_rw [mul_comm _ x]
  exact EReal.mul_add_coe_of_nonneg x hy hz

lemma sub_add_sub_cancel (b a : EReal) (c : ℝ) :
    b - c + (c - a) = b - a := by
  induction a <;> induction b
  · simp
  · simp only [coe_sub_bot]
    rw [← coe_sub, coe_add_top]
  · simp
  · simp
  · norm_cast
    ring
  · simp only [top_sub_coe]
    rw [← coe_sub, top_add_coe]
  · simp
  · simp
  · simp

lemma top_sub_of_ne_top {x : EReal} (hx : x ≠ ⊤) : ⊤ - x = ⊤ := by
  induction x <;> tauto

lemma toENNReal_sub_le_add (b a c : EReal) :
    (b - a).toENNReal ≤ (b - c).toENNReal + (c - a).toENNReal := by
  by_cases hc_top : c = ⊤
  · simp only [hc_top, sub_top, ne_eq, bot_ne_top, not_false_eq_true,
      toENNReal_of_ne_top, toReal_bot, ENNReal.ofReal_zero, zero_add]
    by_cases ha : a = ⊤
    · simp [ha]
    · simp [top_sub_of_ne_top ha]
  by_cases hc_bot : c = ⊥
  · simp [hc_bot, sub_eq_add_neg]
    by_cases hb_bot : b = ⊥
    · simp [hb_bot]
    · simp [add_top_of_ne_bot hb_bot]
  refine (toENNReal_le_toENNReal ?_).trans toENNReal_add_le
  lift c to ℝ using ⟨hc_top, hc_bot⟩ with c
  rw [sub_add_sub_cancel]

lemma toENNReal_sub_add_cancel {b a c : EReal} (hac : a ≤ c) (hcb : c ≤ b) :
    (b - c).toENNReal + (c - a).toENNReal = (b - a).toENNReal := by
  induction c
  · have ha : a = ⊥ := eq_bot_iff.mpr hac
    simp [ha]
  · rw [← toENNReal_add, sub_add_sub_cancel]
    · rwa [sub_nonneg] <;> simp
    · by_cases ha : a = ⊥
      · simp [ha]
      rwa [sub_nonneg] <;> simp
  · have hb : b = ⊤ := eq_top_iff.mpr hcb
    simp [hb]

end EReal







/-! ### Basic properties of Stieltjes functions -/

/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure ERealStieltjes where
  /-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
  toFun : ℝ → EReal
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x

namespace ERealStieltjes

attribute [coe] toFun

instance instCoeFun : CoeFun ERealStieltjes fun _ ↦ ℝ → EReal where
  coe := toFun

initialize_simps_projections ERealStieltjes (toFun → apply)

@[ext] lemma ext {f g : ERealStieltjes} (h : ∀ x, f x = g x) : f = g :=
  (ERealStieltjes.mk.injEq ..).mpr (funext h)

variable (f : ERealStieltjes)

theorem mono : Monotone f := f.mono'

theorem right_continuous (x : ℝ) : ContinuousWithinAt f (Ici x) x := f.right_continuous' x

theorem rightLim_eq (f : ERealStieltjes) (x : ℝ) : Function.rightLim f x = f x := by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq, continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x

theorem iInf_Ioi_eq (f : ERealStieltjes) (x : ℝ) : ⨅ r : Ioi x, f r = f x := by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [f.mono.rightLim_eq_sInf, sInf_image']
  rw [← neBot_iff]
  infer_instance

/-- Constant functions are Stieltjes function. -/
protected def const (c : EReal) : ERealStieltjes where
  toFun := fun _ ↦ c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const

@[simp] lemma const_apply (c : EReal) (x : ℝ) : ERealStieltjes.const c x = c := rfl

instance : Zero ERealStieltjes where
  zero := ERealStieltjes.const 0

@[simp] lemma zero_apply (x : ℝ) : (0 : ERealStieltjes) x = 0 := rfl

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

lemma add_apply (f g : ERealStieltjes) (x : ℝ) : (f + g) x = - (-f x - g x) := rfl

lemma add_apply_of_ne_top {f g : ERealStieltjes} {x : ℝ} (hfx : f x ≠ ⊤) (hgx : g x ≠ ⊤) :
    (f + g) x = f x + g x := by
  rw [add_apply, EReal.neg_sub (Or.inl _) (Or.inr hgx), neg_neg]
  simp [hfx]

lemma add_apply_of_eq_top_left {f g : ERealStieltjes} {x : ℝ} (hfx : f x = ⊤) :
    (f + g) x = ⊤ := by
  simp [add_apply, hfx]

lemma add_apply_of_eq_top_right {f g : ERealStieltjes} {x : ℝ} (hgx : g x = ⊤) :
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
lemma smul_apply (c : ℝ≥0) (f : ERealStieltjes) {x : ℝ} : (c • f) x = c * f x := rfl

instance : Module ℝ≥0 ERealStieltjes where
  smul c f := c • f
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul a b f := ext fun x ↦ by
    simp only [smul_apply, coe_mul, EReal.coe_ennreal_mul]
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
    · simp only [smul_apply, coe_add, EReal.coe_ennreal_add]
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
  exact tendsto_nhds_unique (f.mono.tendsto_leftLim x) (h'x.tendsto.mono_left nhdsWithin_le_nhds)

section EffectiveDomain

def xmin : ℝ := sInf {y | f y ≠ ⊥}

def xmax : ℝ := sSup {y | f y ≠ ⊤}

end EffectiveDomain

lemma continuousWithinAt_sub_const_Ici {c : EReal} {a : ℝ} (h_bot : f a ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousWithinAt (fun x ↦ f x - c) (Ici a) a :=
  (EReal.continuousAt_sub_const h_bot).comp_continuousWithinAt (f.right_continuous a)

lemma continuousWithinAt_const_sub_Ici {c : EReal} {a : ℝ} (h_bot : f a ≠ ⊤ ∨ c ≠ ⊤) :
    ContinuousWithinAt (fun x ↦ c - f x) (Ici a) a :=
  (EReal.continuousAt_const_sub h_bot).comp_continuousWithinAt (f.right_continuous a)

lemma continuousWithinAt_sub_const_Ioi {c : EReal} {a : ℝ} (h_bot : f a ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousWithinAt (fun x ↦ f x - c) (Ioi a) a :=
  (f.continuousWithinAt_sub_const_Ici h_bot).mono Ioi_subset_Ici_self

end ERealStieltjes
