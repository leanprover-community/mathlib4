/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Signed variation

We define `variationOnFromTo f s a b : ℝ` as the signed variation of `f` between `a` and `b`, i.e.,
its variation if `a ≤ b`, and its opposite otherwise. We establish basic properties of this notion,
and use it to show that a bounded variation real function is the difference of two monotone
functions.
 -/

@[expose] public section

open scoped ENNReal Topology
open Set Filter

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/-- The **signed** variation of `f` on the interval `Icc a b` intersected with the set `s`,
squashed to a real (therefore only really meaningful if the variation is finite)
-/
noncomputable def variationOnFromTo (f : α → E) (s : Set α) (a b : α) : ℝ :=
  if a ≤ b then (eVariationOn f (s ∩ Icc a b)).toReal else -(eVariationOn f (s ∩ Icc b a)).toReal

namespace variationOnFromTo

variable (f : α → E) (s : Set α)

protected theorem self (a : α) : variationOnFromTo f s a a = 0 := by
  dsimp only [variationOnFromTo]
  rw [if_pos le_rfl, Icc_self, eVariationOn.subsingleton, ENNReal.toReal_zero]
  exact fun x hx y hy => hx.2.trans hy.2.symm

protected theorem nonneg_of_le {a b : α} (h : a ≤ b) : 0 ≤ variationOnFromTo f s a b := by
  simp only [variationOnFromTo, if_pos h, ENNReal.toReal_nonneg]

protected theorem eq_neg_swap (a b : α) :
    variationOnFromTo f s a b = -variationOnFromTo f s b a := by
  rcases lt_trichotomy a b with (ab | rfl | ba)
  · simp only [variationOnFromTo, if_pos ab.le, if_neg ab.not_ge, neg_neg]
  · simp only [variationOnFromTo.self, neg_zero]
  · simp only [variationOnFromTo, if_pos ba.le, if_neg ba.not_ge]

protected theorem nonpos_of_ge {a b : α} (h : b ≤ a) : variationOnFromTo f s a b ≤ 0 := by
  rw [variationOnFromTo.eq_neg_swap]
  exact neg_nonpos_of_nonneg (variationOnFromTo.nonneg_of_le f s h)

variable {f s} in
theorem abs_le_eVariationOn (hf : BoundedVariationOn f s) {a b : α} :
    |variationOnFromTo f s a b| ≤ (eVariationOn f s).toReal := by
  by_cases hab : a ≤ b
  · simp only [variationOnFromTo, hab, ↓reduceIte, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ inter_subset_left)
  · simp only [variationOnFromTo, hab, ↓reduceIte, abs_neg, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ inter_subset_left)

protected theorem eq_of_le {a b : α} (h : a ≤ b) :
    variationOnFromTo f s a b = (eVariationOn f (s ∩ Icc a b)).toReal :=
  if_pos h

protected theorem eq_of_ge {a b : α} (h : b ≤ a) :
    variationOnFromTo f s a b = -(eVariationOn f (s ∩ Icc b a)).toReal := by
  rw [variationOnFromTo.eq_neg_swap, neg_inj, variationOnFromTo.eq_of_le f s h]

protected theorem add {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b + variationOnFromTo f s b c = variationOnFromTo f s a c := by
  symm
  refine additive_of_total (· ≤ · : α → α → Prop) (variationOnFromTo f s) (· ∈ s) ?_ ?_ ha hb hc
  · rintro x y _xs _ys
    simp only [variationOnFromTo.eq_neg_swap f s y x, add_neg_cancel]
  · rintro x y z xy yz xs ys zs
    rw [variationOnFromTo.eq_of_le f s xy, variationOnFromTo.eq_of_le f s yz,
      variationOnFromTo.eq_of_le f s (xy.trans yz),
      ← ENNReal.toReal_add (hf x y xs ys) (hf y z ys zs), eVariationOn.Icc_add_Icc f xy yz ys]

protected theorem sub_right {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b - variationOnFromTo f s a c = variationOnFromTo f s c b := by
  rw [← variationOnFromTo.add hf ha hc hb, add_sub_cancel_left]

protected theorem sub_left {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b - variationOnFromTo f s c b = variationOnFromTo f s a c := by
  rw [← variationOnFromTo.add hf ha hc hb, add_sub_cancel_right]

variable {f s} in
protected theorem edist_zero_of_eq_zero (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : variationOnFromTo f s a b = 0) :
    edist (f a) (f b) = 0 := by
  wlog h' : a ≤ b
  · rw [edist_comm]
    apply this hf hb ha _ (le_of_not_ge h')
    rw [variationOnFromTo.eq_neg_swap, h, neg_zero]
  · rw [← nonpos_iff_eq_zero, ← ENNReal.ofReal_zero, ← h, variationOnFromTo.eq_of_le f s h',
      ENNReal.ofReal_toReal (hf a b ha hb)]
    apply eVariationOn.edist_le
    exacts [⟨ha, ⟨le_rfl, h'⟩⟩, ⟨hb, ⟨h', le_rfl⟩⟩]

protected theorem eq_left_iff {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b c : α} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b = variationOnFromTo f s a c ↔ variationOnFromTo f s b c = 0 := by
  simp only [← variationOnFromTo.add hf ha hb hc, left_eq_add]

protected theorem eq_zero_iff_of_le {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (ab : a ≤ b) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (_hx : x ∈ s ∩ Icc a b) ⦃y⦄ (_hy : y ∈ s ∩ Icc a b), edist (f x) (f y) = 0 := by
  rw [variationOnFromTo.eq_of_le _ _ ab, ENNReal.toReal_eq_zero_iff, or_iff_left (hf a b ha hb),
    eVariationOn.eq_zero_iff]

protected theorem eq_zero_iff_of_ge {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (ba : b ≤ a) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (_hx : x ∈ s ∩ Icc b a) ⦃y⦄ (_hy : y ∈ s ∩ Icc b a), edist (f x) (f y) = 0 := by
  rw [variationOnFromTo.eq_of_ge _ _ ba, neg_eq_zero, ENNReal.toReal_eq_zero_iff,
    or_iff_left (hf b a hb ha), eVariationOn.eq_zero_iff]

protected theorem eq_zero_iff {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (_hx : x ∈ s ∩ uIcc a b) ⦃y⦄ (_hy : y ∈ s ∩ uIcc a b), edist (f x) (f y) = 0 := by
  rcases le_total a b with (ab | ba)
  · rw [uIcc_of_le ab]
    exact variationOnFromTo.eq_zero_iff_of_le hf ha hb ab
  · rw [uIcc_of_ge ba]
    exact variationOnFromTo.eq_zero_iff_of_ge hf ha hb ba

variable {f} {s}

protected theorem monotoneOn (hf : LocallyBoundedVariationOn f s) {a : α} (as : a ∈ s) :
    MonotoneOn (variationOnFromTo f s a) s := by
  rintro b bs c cs bc
  rw [← variationOnFromTo.add hf as bs cs]
  exact le_add_of_nonneg_right (variationOnFromTo.nonneg_of_le f s bc)

protected theorem antitoneOn (hf : LocallyBoundedVariationOn f s) {b : α} (bs : b ∈ s) :
    AntitoneOn (fun a => variationOnFromTo f s a b) s := by
  rintro a as c cs ac
  dsimp only
  rw [← variationOnFromTo.add hf as cs bs]
  exact le_add_of_nonneg_left (variationOnFromTo.nonneg_of_le f s ac)

lemma abs_sub_le_sub_of_le {f : α → ℝ} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b c : α} (as : a ∈ s) (bs : b ∈ s) (cs : c ∈ s) (bc : b ≤ c) :
    |f c - f b| ≤ variationOnFromTo f s a c - variationOnFromTo f s a b := calc
  _ = dist (f b) (f c) := by rw [dist_comm, Real.dist_eq]
  _ ≤ variationOnFromTo f s b c := by
    rw [variationOnFromTo.eq_of_le f s bc, dist_edist]
    apply ENNReal.toReal_mono (hf b c bs cs)
    apply eVariationOn.edist_le f
    exacts [⟨bs, le_rfl, bc⟩, ⟨cs, bc, le_rfl⟩]
  _ = variationOnFromTo f s a c - variationOnFromTo f s a b := by
    rw [← variationOnFromTo.add hf as bs cs, add_sub_cancel_left]

protected theorem add_self_monotoneOn {f : α → ℝ} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a : α} (as : a ∈ s) : MonotoneOn (variationOnFromTo f s a + f) s := by
  rintro b bs c cs bc
  suffices f b - f c ≤ variationOnFromTo f s a c - variationOnFromTo f s a b by simp; linarith
  calc
    f b - f c ≤ |f c - f b| := by grw [le_abs_self (f b - f c), abs_sub_comm (f b) (f c)]
    _ ≤ variationOnFromTo f s a c - variationOnFromTo f s a b := abs_sub_le_sub_of_le hf as bs cs bc

protected theorem sub_self_monotoneOn {f : α → ℝ} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a : α} (as : a ∈ s) : MonotoneOn (variationOnFromTo f s a - f) s := by
  rintro b bs c cs bc
  rw [Pi.sub_apply, Pi.sub_apply, le_sub_iff_add_le, add_comm_sub, ← le_sub_iff_add_le']
  calc
    f c - f b ≤ |f c - f b| := le_abs_self _
    _ ≤ variationOnFromTo f s a c - variationOnFromTo f s a b := abs_sub_le_sub_of_le hf as bs cs bc

protected theorem comp_eq_of_monotoneOn {β : Type*} [LinearOrder β] (f : α → E) {t : Set β}
    (φ : β → α) (hφ : MonotoneOn φ t) {x y : β} (hx : x ∈ t) (hy : y ∈ t) :
    variationOnFromTo (f ∘ φ) t x y = variationOnFromTo f (φ '' t) (φ x) (φ y) := by
  rcases le_total x y with (h | h)
  · rw [variationOnFromTo.eq_of_le _ _ h, variationOnFromTo.eq_of_le _ _ (hφ hx hy h),
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hx hy]
  · rw [variationOnFromTo.eq_of_ge _ _ h, variationOnFromTo.eq_of_ge _ _ (hφ hy hx h),
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hy hx]

/-- The jump of `variationOnFromTo` on the left of a point is given by the distance between the
left limit and the value of the function. -/
theorem tendsto_left {E : Type*} [PseudoMetricSpace E] [TopologicalSpace α] [OrderTopology α]
    {f : α → E} {l : E} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hf : LocallyBoundedVariationOn f s) (h'f : Tendsto f (𝓝[s ∩ Iio b] b) (𝓝 l)) :
    Tendsto (variationOnFromTo f s a) (𝓝[s ∩ Iio b] b)
      (𝓝 (variationOnFromTo f s a b - dist (f b) l)) := by
  suffices H : Tendsto (fun x ↦ variationOnFromTo f s a b - variationOnFromTo f s x b)
      (𝓝[s ∩ Iio b] b) (𝓝 (variationOnFromTo f s a b - dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [variationOnFromTo.sub_left hf ha hb hx.1]
  apply Tendsto.const_sub
  suffices H : Tendsto (fun x ↦ (eVariationOn f (s ∩ Icc x b)).toReal) (𝓝[s ∩ Iio b] b)
      (𝓝 (dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx using by simp [variationOnFromTo, hx.2.le]
  rw [dist_edist]
  exact (ENNReal.tendsto_toReal (by simp)).comp (hf.tendsto_eVariationOn_Icc_left h'f hb)

/-- The jump of `variationOnFromTo` on the right of a point is given by the distance between the
right limit and the value of the function. -/
theorem tendsto_right {E : Type*} [PseudoMetricSpace E] [TopologicalSpace α] [OrderTopology α]
    {f : α → E} {l : E} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hf : LocallyBoundedVariationOn f s) (h'f : Tendsto f (𝓝[s ∩ Ioi b] b) (𝓝 l)) :
    Tendsto (variationOnFromTo f s a) (𝓝[s ∩ Ioi b] b)
      (𝓝 (variationOnFromTo f s a b + dist (f b) l)) := by
  suffices H : Tendsto (fun x ↦ variationOnFromTo f s a b + variationOnFromTo f s b x)
      (𝓝[s ∩ Ioi b] b) (𝓝 (variationOnFromTo f s a b + dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [variationOnFromTo.add hf ha hb hx.1]
  apply Tendsto.const_add
  suffices H : Tendsto (fun x ↦ (eVariationOn f (s ∩ Icc b x)).toReal) (𝓝[s ∩ Ioi b] b)
      (𝓝 (dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx using by simp [variationOnFromTo, hx.2.le]
  rw [dist_edist]
  exact (ENNReal.tendsto_toReal (by simp)).comp (hf.tendsto_eVariationOn_Icc_right h'f hb)

/-- The jump of `variationOnFromTo` on the left of a point is given by the distance between the
left limit and the value of the function. -/
theorem leftLim_eq {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]
    {f : α → E} {a b : α} (hf : BoundedVariationOn f univ) :
    (variationOnFromTo f univ a).leftLim b =
      variationOnFromTo f univ a b - dist (f b) (f.leftLim b) := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] b) with hb | hb
  · simp [leftLim_eq_of_eq_bot _ hb]
  apply leftLim_eq_of_tendsto
  have := variationOnFromTo.tendsto_left (f := f) (l := f.leftLim b) (mem_univ a) (mem_univ b)
    hf.locallyBoundedVariationOn
  simp only [univ_inter] at this
  exact this (hf.tendsto_leftLim _)

/-- The jump of `variationOnFromTo` on the right of a point is given by the distance between the
right limit and the value of the function. -/
theorem rightLim_eq {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]
    {f : α → E} {a b : α} (hf : BoundedVariationOn f univ) :
    (variationOnFromTo f univ a).rightLim b =
      variationOnFromTo f univ a b + dist (f b) (f.rightLim b) := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[>] b) with hb | hb
  · simp [rightLim_eq_of_eq_bot _ hb]
  apply rightLim_eq_of_tendsto
  have := variationOnFromTo.tendsto_right (f := f) (l := f.rightLim b) (mem_univ a) (mem_univ b)
    hf.locallyBoundedVariationOn
  simp only [univ_inter] at this
  exact this (hf.tendsto_rightLim _)

theorem _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_Ici
    [TopologicalSpace α] [OrderTopology α] (hf : BoundedVariationOn f univ) {a x : α}
    (hx : ContinuousWithinAt f (Ici x) x) :
    ContinuousWithinAt (variationOnFromTo f univ a) (Ici x) x := by
  have : variationOnFromTo f univ a =
      fun y ↦ variationOnFromTo f univ a x + variationOnFromTo f univ x y := by
    ext y
    rw [variationOnFromTo.add hf.locallyBoundedVariationOn (mem_univ _) (mem_univ _) (mem_univ _)]
  rw [this]
  apply continuousWithinAt_const.add
  suffices H : ContinuousWithinAt (fun y ↦ (eVariationOn f (univ ∩ Icc x y)).toReal) (Ici x) x from
    H.congr_of_mem (fun y hy ↦ by grind [variationOnFromTo]) self_mem_Iic
  simp only [ContinuousWithinAt, Icc_self]
  rw [eVariationOn.subsingleton _ (by grind [Set.Subsingleton])]
  apply (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
  apply Tendsto.mono_left _ (nhdsWithin_mono _ (subset_univ _))
  exact hf.tendsto_eVariationOn_Icc_zero_right _ (by simpa using hx)

theorem _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_rightLim_Ici
    [TopologicalSpace α] [OrderTopology α] [T3Space E] [CompleteSpace E]
    (hf : BoundedVariationOn f univ) {a x : α} :
    ContinuousWithinAt (variationOnFromTo f.rightLim univ a) (Ici x) x :=
  hf.rightLim.continuousWithinAt_variationOnFromTo_Ici hf.continuousWithinAt_rightLim

end variationOnFromTo

/-- If a real-valued function has bounded variation on a set, then it is a difference of monotone
functions there. Moreover, one can make sure that the two monotone functions add up to the
variation of `f`. -/
theorem LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn' {f : α → ℝ} {s : Set α}
    (h : LocallyBoundedVariationOn f s) :
    ∃ p q : α → ℝ, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q ∧
      ∀ x ∈ s, ∀ y ∈ s, (p y - p x) + (q y - q x) = variationOnFromTo f s x y := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨c, cs⟩)
  · refine ⟨f, 0, subsingleton_empty.monotoneOn _, subsingleton_empty.monotoneOn _,
      (sub_zero f).symm, fun x hx y hy ↦ by simp at hx⟩
  refine ⟨fun x ↦ (variationOnFromTo f s c x + f x) / 2,
    fun x ↦ (variationOnFromTo f s c x - f x) / 2, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    dsimp
    gcongr 1
    simpa using variationOnFromTo.add_self_monotoneOn h cs hx hy hxy
  · intro x hx y hy hxy
    dsimp
    gcongr 1
    simpa using variationOnFromTo.sub_self_monotoneOn h cs hx hy hxy
  · ext
    simp
    ring
  · intro x hx y hy
    rw [← variationOnFromTo.add h hx cs hy, variationOnFromTo.eq_neg_swap]
    ring

/-- If a real-valued function has bounded variation on a set, then it is a difference of monotone
functions there. -/
theorem LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn {f : α → ℝ} {s : Set α}
    (h : LocallyBoundedVariationOn f s) :
    ∃ p q : α → ℝ, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q := by
  rcases h.exists_monotoneOn_sub_monotoneOn' with ⟨p, q, hp, hq, h'f, -⟩
  exact ⟨p, q, hp, hq, h'f⟩
