/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# L'Hôpital's rule for 0/0 indeterminate forms

In this file, we prove several forms of "L'Hôpital's rule" for computing 0/0
indeterminate forms. The proof of `HasDerivAt.lhopital_zero_right_on_Ioo`
is based on the one given in the corresponding
[Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule)
chapter, and all other statements are derived from this one by composing by
carefully chosen functions.

Note that the filter `f'/g'` tends to isn't required to be one of `𝓝 a`,
`atTop` or `atBot`. In fact, we give a slightly stronger statement by
allowing it to be any filter on `ℝ`.

Each statement is available in a `HasDerivAt` form and a `deriv` form, which
is denoted by each statement being in either the `HasDerivAt` or the `deriv`
namespace.

## Tags

L'Hôpital's rule, L'Hopital's rule
-/


open Filter Set

open scoped Filter Topology Pointwise

variable {a b : ℝ} {l : Filter ℝ} {f f' g g' : ℝ → ℝ}

/-!
## Interval-based versions

We start by proving statements where all conditions (derivability, `g' ≠ 0`) have
to be satisfied on an explicitly-provided interval.
-/


namespace HasDerivAt

theorem lhopital_zero_right_on_Ioo (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  have sub : ∀ x ∈ Ioo a b, Ioo a x ⊆ Ioo a b := fun x hx =>
    Ioo_subset_Ioo (le_refl a) (le_of_lt hx.2)
  have hg : ∀ x ∈ Ioo a b, g x ≠ 0 := by
    intro x hx h
    have : Tendsto g (𝓝[<] x) (𝓝 0) := by
      rw [← h, ← nhdsWithin_Ioo_eq_nhdsLT hx.1]
      exact ((hgg' x hx).continuousAt.continuousWithinAt.mono <| sub x hx).tendsto
    obtain ⟨y, hyx, hy⟩ : ∃ c ∈ Ioo a x, g' c = 0 :=
      exists_hasDerivAt_eq_zero' hx.1 hga this fun y hy => hgg' y <| sub x hx hy
    exact hg' y (sub x hx hyx) hy
  have : ∀ x ∈ Ioo a b, ∃ c ∈ Ioo a x, f x * g' c = g x * f' c := by
    intro x hx
    rw [← sub_zero (f x), ← sub_zero (g x)]
    exact exists_ratio_hasDerivAt_eq_ratio_slope' g g' hx.1 f f' (fun y hy => hgg' y <| sub x hx hy)
      (fun y hy => hff' y <| sub x hx hy) hga hfa
      (tendsto_nhdsWithin_of_tendsto_nhds (hgg' x hx).continuousAt.tendsto)
      (tendsto_nhdsWithin_of_tendsto_nhds (hff' x hx).continuousAt.tendsto)
  choose! c hc using this
  have : ∀ x ∈ Ioo a b, ((fun x' => f' x' / g' x') ∘ c) x = f x / g x := by
    intro x hx
    rcases hc x hx with ⟨h₁, h₂⟩
    field_simp [hg x hx, hg' (c x) ((sub x hx) h₁)]
    simp only [h₂]
    rw [mul_comm]
  have cmp : ∀ x ∈ Ioo a b, a < c x ∧ c x < x := fun x hx => (hc x hx).1
  rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
  apply tendsto_nhdsWithin_congr this
  apply hdiv.comp
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ?_ ?_) ?_
  all_goals
    apply eventually_nhdsWithin_of_forall
    intro x hx
    have := cmp x hx
    try simp
    linarith [this]

theorem lhopital_zero_right_on_Ico (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ico a b))
    (hcg : ContinuousOn g (Ico a b)) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0) (hfa : f a = 0) (hga : g a = 0)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  refine lhopital_zero_right_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto

theorem lhopital_zero_left_on_Ioo (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hfb : Tendsto f (𝓝[<] b) (𝓝 0)) (hgb : Tendsto g (𝓝[<] b) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) l) :
  Tendsto (fun x => f x / g x) (𝓝[<] b) l := by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : ∀ x ∈ -Ioo a b, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : ∀ x ∈ -Ioo a b, HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x := fun x hx =>
    comp x (hgg' (-x) hx) (hasDerivAt_neg x)
  rw [neg_Ioo] at hdnf
  rw [neg_Ioo] at hdng
  have := lhopital_zero_right_on_Ioo (neg_lt_neg hab) hdnf hdng (by
    intro x hx h
    apply hg' _ (by rw [← neg_Ioo] at hx; exact hx)
    rwa [mul_comm, ← neg_eq_neg_one_mul, neg_eq_zero] at h)
    (hfb.comp tendsto_neg_nhdsGT_neg) (hgb.comp tendsto_neg_nhdsGT_neg)
    (by
      simp only [neg_div_neg_eq, mul_one, mul_neg]
      exact (tendsto_congr fun x => rfl).mp (hdiv.comp tendsto_neg_nhdsGT_neg))
  have := this.comp tendsto_neg_nhdsLT
  unfold Function.comp at this
  simpa only [neg_neg]

theorem lhopital_zero_left_on_Ioc (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ioc a b))
    (hcg : ContinuousOn g (Ioc a b)) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0) (hfb : f b = 0) (hgb : g b = 0)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) l := by
  refine lhopital_zero_left_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcf b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto
  · rw [← hgb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcg b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto

theorem lhopital_zero_atTop_on_Ioi (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atTop l) : Tendsto (fun x => f x / g x) atTop l := by
  obtain ⟨a', haa', ha'⟩ : ∃ a', a < a' ∧ 0 < a' := ⟨1 + max a 0,
    ⟨lt_of_le_of_lt (le_max_left a 0) (lt_one_add _),
      lt_of_le_of_lt (le_max_right a 0) (lt_one_add _)⟩⟩
  have fact1 : ∀ x : ℝ, x ∈ Ioo 0 a'⁻¹ → x ≠ 0 := fun _ hx => (ne_of_lt hx.1).symm
  have fact2 (x) (hx : x ∈ Ioo 0 a'⁻¹) : a < x⁻¹ := lt_trans haa' ((lt_inv_comm₀ ha' hx.1).mpr hx.2)
  have hdnf : ∀ x ∈ Ioo 0 a'⁻¹, HasDerivAt (f ∘ Inv.inv) (f' x⁻¹ * -(x ^ 2)⁻¹) x := fun x hx =>
    comp x (hff' x⁻¹ <| fact2 x hx) (hasDerivAt_inv <| fact1 x hx)
  have hdng : ∀ x ∈ Ioo 0 a'⁻¹, HasDerivAt (g ∘ Inv.inv) (g' x⁻¹ * -(x ^ 2)⁻¹) x := fun x hx =>
    comp x (hgg' x⁻¹ <| fact2 x hx) (hasDerivAt_inv <| fact1 x hx)
  have := lhopital_zero_right_on_Ioo (inv_pos.mpr ha') hdnf hdng
    (by
      intro x hx
      refine mul_ne_zero ?_ (neg_ne_zero.mpr <| inv_ne_zero <| pow_ne_zero _ <| fact1 x hx)
      exact hg' _ (fact2 x hx))
    (hftop.comp tendsto_inv_nhdsGT_zero) (hgtop.comp tendsto_inv_nhdsGT_zero)
    (by
      refine (tendsto_congr' ?_).mp (hdiv.comp tendsto_inv_nhdsGT_zero)
      rw [eventuallyEq_iff_exists_mem]
      use Ioi 0, self_mem_nhdsWithin
      intro x hx
      unfold Function.comp
      simp only
      rw [mul_div_mul_right]
      exact neg_ne_zero.mpr (inv_ne_zero <| pow_ne_zero _ <| ne_of_gt hx))
  have := this.comp tendsto_inv_atTop_nhdsGT_zero
  unfold Function.comp at this
  simpa only [inv_inv]

theorem lhopital_zero_atBot_on_Iio (hff' : ∀ x ∈ Iio a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Iio a, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Iio a, g' x ≠ 0)
    (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atBot l) : Tendsto (fun x => f x / g x) atBot l := by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : ∀ x ∈ -Iio a, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : ∀ x ∈ -Iio a, HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x := fun x hx =>
    comp x (hgg' (-x) hx) (hasDerivAt_neg x)
  rw [neg_Iio] at hdnf
  rw [neg_Iio] at hdng
  have := lhopital_zero_atTop_on_Ioi hdnf hdng
    (by
      intro x hx h
      apply hg' _ (by rw [← neg_Iio] at hx; exact hx)
      rwa [mul_comm, ← neg_eq_neg_one_mul, neg_eq_zero] at h)
    (hfbot.comp tendsto_neg_atTop_atBot) (hgbot.comp tendsto_neg_atTop_atBot)
    (by
      simp only [mul_one, mul_neg, neg_div_neg_eq]
      exact (tendsto_congr fun x => rfl).mp (hdiv.comp tendsto_neg_atTop_atBot))
  have := this.comp tendsto_neg_atBot_atTop
  unfold Function.comp at this
  simpa only [neg_neg]

end HasDerivAt

namespace deriv

theorem lhopital_zero_right_on_Ioo (hab : a < b) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hg' : ∀ x ∈ Ioo a b, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0))
    (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  have hdf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_right_on_Ioo hab (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfa hga hdiv

theorem lhopital_zero_right_on_Ico (hab : a < b) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hcf : ContinuousOn f (Ico a b)) (hcg : ContinuousOn g (Ico a b))
    (hg' : ∀ x ∈ Ioo a b, (deriv g) x ≠ 0) (hfa : f a = 0) (hga : g a = 0)
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  refine lhopital_zero_right_on_Ioo hab hdf hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto

theorem lhopital_zero_left_on_Ioo (hab : a < b) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hg' : ∀ x ∈ Ioo a b, (deriv g) x ≠ 0) (hfb : Tendsto f (𝓝[<] b) (𝓝 0))
    (hgb : Tendsto g (𝓝[<] b) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[<] b) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) l := by
  have hdf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_left_on_Ioo hab (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfb hgb hdiv

theorem lhopital_zero_atTop_on_Ioi (hdf : DifferentiableOn ℝ f (Ioi a))
    (hg' : ∀ x ∈ Ioi a, (deriv g) x ≠ 0) (hftop : Tendsto f atTop (𝓝 0))
    (hgtop : Tendsto g atTop (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atTop l) :
    Tendsto (fun x => f x / g x) atTop l := by
  have hdf : ∀ x ∈ Ioi a, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioi_mem_nhds hx)
  have hdg : ∀ x ∈ Ioi a, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_atTop_on_Ioi (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hftop hgtop hdiv

theorem lhopital_zero_atBot_on_Iio (hdf : DifferentiableOn ℝ f (Iio a))
    (hg' : ∀ x ∈ Iio a, (deriv g) x ≠ 0) (hfbot : Tendsto f atBot (𝓝 0))
    (hgbot : Tendsto g atBot (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atBot l) :
    Tendsto (fun x => f x / g x) atBot l := by
  have hdf : ∀ x ∈ Iio a, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Iio_mem_nhds hx)
  have hdg : ∀ x ∈ Iio a, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_atBot_on_Iio (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfbot hgbot hdiv

end deriv

/-!
## Generic versions

The following statements no longer any explicit interval, as they only require
conditions holding eventually.
-/


namespace HasDerivAt

/-- L'Hôpital's rule for approaching a real from the right, `HasDerivAt` version -/
theorem lhopital_zero_nhds_right (hff' : ∀ᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[>] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[>] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ 𝓝[>] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hs
  rcases hs with ⟨u, hau, hu⟩
  refine lhopital_zero_right_on_Ioo hau ?_ ?_ ?_ hfa hga hdiv <;>
    intro x hx <;> apply_assumption <;>
    first | exact (hu hx).1.1 | exact (hu hx).1.2 | exact (hu hx).2

/-- L'Hôpital's rule for approaching a real from the left, `HasDerivAt` version -/
theorem lhopital_zero_nhds_left (hff' : ∀ᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[<] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[<] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[<] a) (𝓝 0)) (hga : Tendsto g (𝓝[<] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] a) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ 𝓝[<] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsLT_iff_exists_Ioo_subset] at hs
  rcases hs with ⟨l, hal, hl⟩
  refine lhopital_zero_left_on_Ioo hal ?_ ?_ ?_ hfa hga hdiv <;> intro x hx <;> apply_assumption <;>
    first | exact (hl hx).1.1| exact (hl hx).1.2| exact (hl hx).2

/-- L'Hôpital's rule for approaching a real from within a convex set, `HasDerivWithinAt` version.
  This does not require anything about the situation at `a` -/
theorem _root_.HasDerivWithinAt.lhopital_zero_nhdsWithin_convex {s : Set ℝ} (hs : Convex ℝ s)
    (hff' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt f (f' x) (s \ {a}) x)
    (hgg' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt g (g' x) (s \ {a}) x)
    (hg' : ∀ᶠ x in 𝓝[s \ {a}] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[s \ {a}] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[s \ {a}] a) l := by
  by_cases has : a ∈ closure s
  swap
  · rw [diff_singleton_eq_self (not_mem_subset subset_closure has),
      not_mem_closure_iff_nhdsWithin_eq_bot.1 has]
    apply tendsto_bot
  rcases Nonempty.of_closure ⟨a, has⟩ with ⟨a', ha'⟩
  rcases eq_singleton_or_nontrivial ha' with rfl | h'
  · rw [closure_singleton, mem_singleton_iff] at has
    rw [has, diff_self, nhdsWithin_empty]
    apply tendsto_bot
  replace h' := hs.interior_closure_eq_interior_of_nonempty_interior <|
    hs.nontrivial_iff_nonempty_interior.1 h'
  have h := hs.diff_singleton_eventually_mem_nhds a
  replace hff' := h.mp <| hff'.mono fun _ h ↦ h.hasDerivAt
  replace hgg' := h.mp <| hgg'.mono fun _ h ↦ h.hasDerivAt
  rw [diff_eq, ← Iio_union_Ioi, inter_union_distrib_left,
    nhdsWithin_union, tendsto_sup, eventually_sup] at *
  constructor
  · rcases eq_empty_or_nonempty (s ∩ Iio a) with hs' | ⟨b, hbs, hba⟩
    · rw [hs', nhdsWithin_empty]
      apply tendsto_bot
    have := interior_mono <| hs.closure.openSegment_subset (subset_closure hbs) has
    rw [openSegment_eq_Ioo hba, interior_Ioo, h'] at this
    rw [nhdsWithin_inter_of_mem <| mem_nhdsWithin_Iio_iff_exists_Ioo_subset.2
      ⟨b, hba, this.trans interior_subset⟩] at *
    exact lhopital_zero_nhds_left hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1
  · rcases eq_empty_or_nonempty (s ∩ Ioi a) with hs' | ⟨b, hbs, hab⟩
    · rw [hs', nhdsWithin_empty]
      apply tendsto_bot
    have := interior_mono <| hs.closure.openSegment_subset has (subset_closure hbs)
    rw [openSegment_eq_Ioo hab, interior_Ioo, h'] at this
    rw [nhdsWithin_inter_of_mem <| mem_nhdsWithin_Ioi_iff_exists_Ioo_subset.2
      ⟨b, hab, this.trans interior_subset⟩] at *
    exact lhopital_zero_nhds_right hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2

/-- L'Hôpital's rule for approaching a real, `HasDerivAt` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds' (hff' : ∀ᶠ x in 𝓝[≠] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[≠] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[≠] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[≠] a) (𝓝 0)) (hga : Tendsto g (𝓝[≠] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[≠] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) l := by
  rw [compl_eq_univ_diff] at *
  exact HasDerivWithinAt.lhopital_zero_nhdsWithin_convex convex_univ
    (hff'.mono fun _ h ↦ h.hasDerivWithinAt) (hgg'.mono fun _ h ↦ h.hasDerivWithinAt)
    hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real, `HasDerivAt` version -/
theorem lhopital_zero_nhds (hff' : ∀ᶠ x in 𝓝 a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝 a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝 a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝 a) l) : Tendsto (fun x => f x / g x) (𝓝[≠] a) l := by
  apply @lhopital_zero_nhds' _ _ _ f' _ g' <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds) <;> assumption

/-- L'Hôpital's rule for approaching +∞, `HasDerivAt` version -/
theorem lhopital_zero_atTop (hff' : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in atTop, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in atTop, g' x ≠ 0)
    (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atTop l) : Tendsto (fun x => f x / g x) atTop l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ atTop := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atTop_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' : Ioi l ⊆ s := fun x hx => hl x (le_of_lt hx)
  refine lhopital_zero_atTop_on_Ioi ?_ ?_ (fun x hx => hg' x <| (hl' hx).2) hftop hgtop hdiv <;>
    intro x hx <;> apply_assumption <;> first | exact (hl' hx).1.1| exact (hl' hx).1.2

/-- L'Hôpital's rule for approaching -∞, `HasDerivAt` version -/
theorem lhopital_zero_atBot (hff' : ∀ᶠ x in atBot, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in atBot, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in atBot, g' x ≠ 0)
    (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atBot l) : Tendsto (fun x => f x / g x) atBot l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ atBot := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atBot_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' : Iio l ⊆ s := fun x hx => hl x (le_of_lt hx)
  refine lhopital_zero_atBot_on_Iio ?_ ?_ (fun x hx => hg' x <| (hl' hx).2) hfbot hgbot hdiv <;>
    intro x hx <;> apply_assumption <;> first | exact (hl' hx).1.1| exact (hl' hx).1.2

end HasDerivAt

namespace derivWithin

/-- **L'Hôpital's rule** for approaching a real from within a convex set, `derivWithin` version -/
theorem lhopital_zero_nhdsWithin_convex {s : Set ℝ} (hs : Convex ℝ s)
    (hdf : ∀ᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt ℝ f (s \ {a}) x)
    (hg' : ∀ᶠ x in 𝓝[s \ {a}] a, derivWithin g (s \ {a}) x ≠ 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x => derivWithin f (s \ {a}) x / derivWithin g (s \ {a}) x)
      (𝓝[s \ {a}] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[s \ {a}] a) l := by
  have hdg : ∀ᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt ℝ g (s \ {a}) x :=
    hg'.mp (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (derivWithin_zero_of_not_differentiableWithinAt h))
  have hdf' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt f (derivWithin f (s \ {a}) x) (s \ {a}) x :=
    hdf.mp (Eventually.of_forall fun _ h ↦ h.hasDerivWithinAt)
  have hdg' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt g (derivWithin g (s \ {a}) x) (s \ {a}) x :=
    hdg.mp (Eventually.of_forall fun _ h => h.hasDerivWithinAt)
  exact HasDerivWithinAt.lhopital_zero_nhdsWithin_convex hs hdf' hdg' hg' hfa hga hdiv

end derivWithin

namespace deriv

/-- **L'Hôpital's rule** for approaching a real from within a convex set, `deriv` version -/
theorem lhopital_zero_nhdsWithin_convex {s : Set ℝ} (hs : Convex ℝ s)
    (hdf : ∀ᶠ x in 𝓝[s \ {a}] a, DifferentiableAt ℝ f x) (hg' : ∀ᶠ x in 𝓝[s \ {a}] a, deriv g x ≠ 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x => deriv f x / deriv g x) (𝓝[s \ {a}] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[s \ {a}] a) l := by
  refine derivWithin.lhopital_zero_nhdsWithin_convex hs
    (hdf.mono fun _ h ↦ h.differentiableWithinAt) (hg'.mp ?_) hfa hga
    (hdiv.congr' ?_)
  all_goals
    apply (hs.diff_singleton_eventually_mem_nhds a).mono
    intros
  · rwa [derivWithin_of_mem_nhds ‹_›]
  · simp only
    iterate 2 rw [derivWithin_of_mem_nhds ‹_›]

/-- **L'Hôpital's rule** for approaching a real from the right, `deriv` version -/
theorem lhopital_zero_nhds_right (hdf : ∀ᶠ x in 𝓝[>] a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝[>] a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0))
    (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  rw [← Ici_diff_left] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Ici a) hdf hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real from the left, `deriv` version -/
theorem lhopital_zero_nhds_left (hdf : ∀ᶠ x in 𝓝[<] a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝[<] a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[<] a) (𝓝 0))
    (hga : Tendsto g (𝓝[<] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[<] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] a) l := by
  rw [← Iic_diff_right] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Iic a) hdf hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real, `deriv` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds' (hdf : ∀ᶠ x in 𝓝[≠] a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝[≠] a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[≠] a) (𝓝 0))
    (hga : Tendsto g (𝓝[≠] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[≠] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) l := by
  rw [compl_eq_univ_diff] at *
  exact lhopital_zero_nhdsWithin_convex convex_univ hdf hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real, `deriv` version -/
theorem lhopital_zero_nhds (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝 a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝 a) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) l := by
  apply lhopital_zero_nhds' <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds) <;> assumption

/-- **L'Hôpital's rule** for approaching +∞, `deriv` version -/
theorem lhopital_zero_atTop (hdf : ∀ᶠ x : ℝ in atTop, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x : ℝ in atTop, deriv g x ≠ 0) (hftop : Tendsto f atTop (𝓝 0))
    (hgtop : Tendsto g atTop (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atTop l) :
    Tendsto (fun x => f x / g x) atTop l := by
  have hdg : ∀ᶠ x in atTop, DifferentiableAt ℝ g x := hg'.mp
    (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h))
  have hdf' : ∀ᶠ x in atTop, HasDerivAt f (deriv f x) x :=
    hdf.mp (Eventually.of_forall fun _ => DifferentiableAt.hasDerivAt)
  have hdg' : ∀ᶠ x in atTop, HasDerivAt g (deriv g x) x :=
    hdg.mp (Eventually.of_forall fun _ => DifferentiableAt.hasDerivAt)
  exact HasDerivAt.lhopital_zero_atTop hdf' hdg' hg' hftop hgtop hdiv

/-- **L'Hôpital's rule** for approaching -∞, `deriv` version -/
theorem lhopital_zero_atBot (hdf : ∀ᶠ x : ℝ in atBot, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x : ℝ in atBot, deriv g x ≠ 0) (hfbot : Tendsto f atBot (𝓝 0))
    (hgbot : Tendsto g atBot (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atBot l) :
    Tendsto (fun x => f x / g x) atBot l := by
  have hdg : ∀ᶠ x in atBot, DifferentiableAt ℝ g x :=
    hg'.mp (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h))
  have hdf' : ∀ᶠ x in atBot, HasDerivAt f (deriv f x) x :=
    hdf.mp (Eventually.of_forall fun _ => DifferentiableAt.hasDerivAt)
  have hdg' : ∀ᶠ x in atBot, HasDerivAt g (deriv g x) x :=
    hdg.mp (Eventually.of_forall fun _ => DifferentiableAt.hasDerivAt)
  exact HasDerivAt.lhopital_zero_atBot hdf' hdg' hg' hfbot hgbot hdiv

end deriv
