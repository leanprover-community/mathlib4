/-
Copyright (c) 2023 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import Mathlib.Data.Set.Function
import Mathlib.Analysis.BoundedVariation

#align_import analysis.constant_speed from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Constant speed

This file defines the notion of constant (and unit) speed for a function `f : ℝ → E` with
pseudo-emetric structure on `E` with respect to a set `s : Set ℝ` and "speed" `l : ℝ≥0`, and shows
that if `f` has locally bounded variation on `s`, it can be obtained (up to distance zero, on `s`),
as a composite `φ ∘ (variationOnFromTo f s a)`, where `φ` has unit speed and `a ∈ s`.

## Main definitions

* `HasConstantSpeedOnWith f s l`, stating that the speed of `f` on `s` is `l`.
* `HasUnitSpeedOn f s`, stating that the speed of `f` on `s` is `1`.
* `naturalParameterization f s a : ℝ → E`, the unit speed reparameterization of `f` on `s` relative
  to `a`.

## Main statements

* `unique_unit_speed_on_Icc_zero` proves that if `f` and `f ∘ φ` are both naturally
  parameterized on closed intervals starting at `0`, then `φ` must be the identity on
  those intervals.
* `edist_naturalParameterization_eq_zero` proves that if `f` has locally bounded variation, then
  precomposing `naturalParameterization f s a` with `variationOnFromTo f s a` yields a function
  at distance zero from `f` on `s`.
* `has_unit_speed_naturalParameterization` proves that if `f` has locally bounded
  variation, then `naturalParameterization f s a` has unit speed on `s`.

## Tags

arc-length, parameterization
-/


open scoped NNReal ENNReal

open Set MeasureTheory Classical

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]
variable (f : ℝ → E) (s : Set ℝ) (l : ℝ≥0)

/-- `f` has constant speed `l` on `s` if the variation of `f` on `s ∩ Icc x y` is equal to
`l * (y - x)` for any `x y` in `s`.
-/
def HasConstantSpeedOnWith :=
  ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), eVariationOn f (s ∩ Icc x y) = ENNReal.ofReal (l * (y - x))
#align has_constant_speed_on_with HasConstantSpeedOnWith

variable {f s l}

theorem HasConstantSpeedOnWith.hasLocallyBoundedVariationOn (h : HasConstantSpeedOnWith f s l) :
    LocallyBoundedVariationOn f s := fun x y hx hy => by
  simp only [BoundedVariationOn, h hx hy, Ne, ENNReal.ofReal_ne_top, not_false_iff]
#align has_constant_speed_on_with.has_locally_bounded_variation_on HasConstantSpeedOnWith.hasLocallyBoundedVariationOn

theorem hasConstantSpeedOnWith_of_subsingleton (f : ℝ → E) {s : Set ℝ} (hs : s.Subsingleton)
    (l : ℝ≥0) : HasConstantSpeedOnWith f s l := by
  rintro x hx y hy; cases hs hx hy
  rw [eVariationOn.subsingleton f (fun y hy z hz => hs hy.1 hz.1 : (s ∩ Icc x x).Subsingleton)]
  simp only [sub_self, mul_zero, ENNReal.ofReal_zero]
#align has_constant_speed_on_with_of_subsingleton hasConstantSpeedOnWith_of_subsingleton

theorem hasConstantSpeedOnWith_iff_ordered :
    HasConstantSpeedOnWith f s l ↔ ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s),
      x ≤ y → eVariationOn f (s ∩ Icc x y) = ENNReal.ofReal (l * (y - x)) := by
  refine ⟨fun h x xs y ys _ => h xs ys, fun h x xs y ys => ?_⟩
  rcases le_total x y with (xy | yx)
  · exact h xs ys xy
  · rw [eVariationOn.subsingleton, ENNReal.ofReal_of_nonpos]
    · exact mul_nonpos_of_nonneg_of_nonpos l.prop (sub_nonpos_of_le yx)
    · rintro z ⟨zs, xz, zy⟩ w ⟨ws, xw, wy⟩
      cases le_antisymm (zy.trans yx) xz
      cases le_antisymm (wy.trans yx) xw
      rfl
#align has_constant_speed_on_with_iff_ordered hasConstantSpeedOnWith_iff_ordered

theorem hasConstantSpeedOnWith_iff_variationOnFromTo_eq :
    HasConstantSpeedOnWith f s l ↔ LocallyBoundedVariationOn f s ∧
      ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), variationOnFromTo f s x y = l * (y - x) := by
  constructor
  · rintro h; refine ⟨h.hasLocallyBoundedVariationOn, fun x xs y ys => ?_⟩
    rw [hasConstantSpeedOnWith_iff_ordered] at h
    rcases le_total x y with (xy | yx)
    · rw [variationOnFromTo.eq_of_le f s xy, h xs ys xy]
      exact ENNReal.toReal_ofReal (mul_nonneg l.prop (sub_nonneg.mpr xy))
    · rw [variationOnFromTo.eq_of_ge f s yx, h ys xs yx]
      have := ENNReal.toReal_ofReal (mul_nonneg l.prop (sub_nonneg.mpr yx))
      simp_all only [NNReal.val_eq_coe]; ring
  · rw [hasConstantSpeedOnWith_iff_ordered]
    rintro h x xs y ys xy
    rw [← h.2 xs ys, variationOnFromTo.eq_of_le f s xy, ENNReal.ofReal_toReal (h.1 x y xs ys)]
#align has_constant_speed_on_with_iff_variation_on_from_to_eq hasConstantSpeedOnWith_iff_variationOnFromTo_eq

theorem HasConstantSpeedOnWith.union {t : Set ℝ} (hfs : HasConstantSpeedOnWith f s l)
    (hft : HasConstantSpeedOnWith f t l) {x : ℝ} (hs : IsGreatest s x) (ht : IsLeast t x) :
    HasConstantSpeedOnWith f (s ∪ t) l := by
  rw [hasConstantSpeedOnWith_iff_ordered] at hfs hft ⊢
  rintro z (zs | zt) y (ys | yt) zy
  · have : (s ∪ t) ∩ Icc z y = s ∩ Icc z y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        · exact ⟨ws, zw, wy⟩
        · exact ⟨(le_antisymm (wy.trans (hs.2 ys)) (ht.2 wt)).symm ▸ hs.1, zw, wy⟩
      · rintro ⟨ws, zwy⟩; exact ⟨Or.inl ws, zwy⟩
    rw [this, hfs zs ys zy]
  · have : (s ∪ t) ∩ Icc z y = s ∩ Icc z x ∪ t ∩ Icc x y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        exacts [Or.inl ⟨ws, zw, hs.2 ws⟩, Or.inr ⟨wt, ht.2 wt, wy⟩]
      · rintro (⟨ws, zw, wx⟩ | ⟨wt, xw, wy⟩)
        exacts [⟨Or.inl ws, zw, wx.trans (ht.2 yt)⟩, ⟨Or.inr wt, (hs.2 zs).trans xw, wy⟩]
    rw [this, @eVariationOn.union _ _ _ _ f _ _ x, hfs zs hs.1 (hs.2 zs), hft ht.1 yt (ht.2 yt)]
    · have q := ENNReal.ofReal_add (mul_nonneg l.prop (sub_nonneg.mpr (hs.2 zs)))
        (mul_nonneg l.prop (sub_nonneg.mpr (ht.2 yt)))
      simp only [NNReal.val_eq_coe] at q
      rw [← q]
      ring_nf
    exacts [⟨⟨hs.1, hs.2 zs, le_rfl⟩, fun w ⟨_, _, wx⟩ => wx⟩,
      ⟨⟨ht.1, le_rfl, ht.2 yt⟩, fun w ⟨_, xw, _⟩ => xw⟩]
  · cases le_antisymm zy ((hs.2 ys).trans (ht.2 zt))
    simp only [Icc_self, sub_self, mul_zero, ENNReal.ofReal_zero]
    exact eVariationOn.subsingleton _ fun _ ⟨_, uz⟩ _ ⟨_, vz⟩ => uz.trans vz.symm
  · have : (s ∪ t) ∩ Icc z y = t ∩ Icc z y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        · exact ⟨le_antisymm ((ht.2 zt).trans zw) (hs.2 ws) ▸ ht.1, zw, wy⟩
        · exact ⟨wt, zw, wy⟩
      · rintro ⟨wt, zwy⟩; exact ⟨Or.inr wt, zwy⟩
    rw [this, hft zt yt zy]
#align has_constant_speed_on_with.union HasConstantSpeedOnWith.union

theorem HasConstantSpeedOnWith.Icc_Icc {x y z : ℝ} (hfs : HasConstantSpeedOnWith f (Icc x y) l)
    (hft : HasConstantSpeedOnWith f (Icc y z) l) : HasConstantSpeedOnWith f (Icc x z) l := by
  rcases le_total x y with (xy | yx)
  · rcases le_total y z with (yz | zy)
    · rw [← Set.Icc_union_Icc_eq_Icc xy yz]
      exact hfs.union hft (isGreatest_Icc xy) (isLeast_Icc yz)
    · rintro u ⟨xu, uz⟩ v ⟨xv, vz⟩
      rw [Icc_inter_Icc, sup_of_le_right xu, inf_of_le_right vz, ←
        hfs ⟨xu, uz.trans zy⟩ ⟨xv, vz.trans zy⟩, Icc_inter_Icc, sup_of_le_right xu,
        inf_of_le_right (vz.trans zy)]
  · rintro u ⟨xu, uz⟩ v ⟨xv, vz⟩
    rw [Icc_inter_Icc, sup_of_le_right xu, inf_of_le_right vz, ←
      hft ⟨yx.trans xu, uz⟩ ⟨yx.trans xv, vz⟩, Icc_inter_Icc, sup_of_le_right (yx.trans xu),
      inf_of_le_right vz]
#align has_constant_speed_on_with.Icc_Icc HasConstantSpeedOnWith.Icc_Icc

theorem hasConstantSpeedOnWith_zero_iff :
    HasConstantSpeedOnWith f s 0 ↔ ∀ᵉ (x ∈ s) (y ∈ s), edist (f x) (f y) = 0 := by
  dsimp [HasConstantSpeedOnWith]
  simp only [zero_mul, ENNReal.ofReal_zero, ← eVariationOn.eq_zero_iff]
  constructor
  · by_contra!
    obtain ⟨h, hfs⟩ := this
    simp_rw [ne_eq, eVariationOn.eq_zero_iff] at hfs h
    push_neg at hfs
    obtain ⟨x, xs, y, ys, hxy⟩ := hfs
    rcases le_total x y with (xy | yx)
    · exact hxy (h xs ys x ⟨xs, le_rfl, xy⟩ y ⟨ys, xy, le_rfl⟩)
    · rw [edist_comm] at hxy
      exact hxy (h ys xs y ⟨ys, le_rfl, yx⟩ x ⟨xs, yx, le_rfl⟩)
  · rintro h x _ y _
    refine le_antisymm ?_ zero_le'
    rw [← h]
    exact eVariationOn.mono f inter_subset_left
#align has_constant_speed_on_with_zero_iff hasConstantSpeedOnWith_zero_iff

theorem HasConstantSpeedOnWith.ratio {l' : ℝ≥0} (hl' : l' ≠ 0) {φ : ℝ → ℝ} (φm : MonotoneOn φ s)
    (hfφ : HasConstantSpeedOnWith (f ∘ φ) s l) (hf : HasConstantSpeedOnWith f (φ '' s) l') ⦃x : ℝ⦄
    (xs : x ∈ s) : EqOn φ (fun y => l / l' * (y - x) + φ x) s := by
  rintro y ys
  rw [← sub_eq_iff_eq_add, mul_comm, ← mul_div_assoc, eq_div_iff (NNReal.coe_ne_zero.mpr hl')]
  rw [hasConstantSpeedOnWith_iff_variationOnFromTo_eq] at hf
  rw [hasConstantSpeedOnWith_iff_variationOnFromTo_eq] at hfφ
  symm
  calc
    (y - x) * l = l * (y - x) := by rw [mul_comm]
    _ = variationOnFromTo (f ∘ φ) s x y := (hfφ.2 xs ys).symm
    _ = variationOnFromTo f (φ '' s) (φ x) (φ y) :=
      (variationOnFromTo.comp_eq_of_monotoneOn f φ φm xs ys)
    _ = l' * (φ y - φ x) := (hf.2 ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩)
    _ = (φ y - φ x) * l' := by rw [mul_comm]
#align has_constant_speed_on_with.ratio HasConstantSpeedOnWith.ratio

/-- `f` has unit speed on `s` if it is linearly parameterized by `l = 1` on `s`. -/
def HasUnitSpeedOn (f : ℝ → E) (s : Set ℝ) :=
  HasConstantSpeedOnWith f s 1
#align has_unit_speed_on HasUnitSpeedOn

theorem HasUnitSpeedOn.union {t : Set ℝ} {x : ℝ} (hfs : HasUnitSpeedOn f s)
    (hft : HasUnitSpeedOn f t) (hs : IsGreatest s x) (ht : IsLeast t x) :
    HasUnitSpeedOn f (s ∪ t) :=
  HasConstantSpeedOnWith.union hfs hft hs ht
#align has_unit_speed_on.union HasUnitSpeedOn.union

theorem HasUnitSpeedOn.Icc_Icc {x y z : ℝ} (hfs : HasUnitSpeedOn f (Icc x y))
    (hft : HasUnitSpeedOn f (Icc y z)) : HasUnitSpeedOn f (Icc x z) :=
  HasConstantSpeedOnWith.Icc_Icc hfs hft
#align has_unit_speed_on.Icc_Icc HasUnitSpeedOn.Icc_Icc

/-- If both `f` and `f ∘ φ` have unit speed (on `t` and `s` respectively) and `φ`
monotonically maps `s` onto `t`, then `φ` is just a translation (on `s`).
-/
theorem unique_unit_speed {φ : ℝ → ℝ} (φm : MonotoneOn φ s) (hfφ : HasUnitSpeedOn (f ∘ φ) s)
    (hf : HasUnitSpeedOn f (φ '' s)) ⦃x : ℝ⦄ (xs : x ∈ s) : EqOn φ (fun y => y - x + φ x) s := by
  dsimp only [HasUnitSpeedOn] at hf hfφ
  convert HasConstantSpeedOnWith.ratio one_ne_zero φm hfφ hf xs using 3
  norm_num
#align unique_unit_speed unique_unit_speed

/-- If both `f` and `f ∘ φ` have unit speed (on `Icc 0 t` and `Icc 0 s` respectively)
and `φ` monotonically maps `Icc 0 s` onto `Icc 0 t`, then `φ` is the identity on `Icc 0 s`
-/
theorem unique_unit_speed_on_Icc_zero {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {φ : ℝ → ℝ}
    (φm : MonotoneOn φ <| Icc 0 s) (φst : φ '' Icc 0 s = Icc 0 t)
    (hfφ : HasUnitSpeedOn (f ∘ φ) (Icc 0 s)) (hf : HasUnitSpeedOn f (Icc 0 t)) :
    EqOn φ id (Icc 0 s) := by
  rw [← φst] at hf
  convert unique_unit_speed φm hfφ hf ⟨le_rfl, hs⟩ using 1
  have : φ 0 = 0 := by
    have hm : 0 ∈ φ '' Icc 0 s := by simp only [φst, ht, mem_Icc, le_refl, and_self]
    obtain ⟨x, xs, hx⟩ := hm
    apply le_antisymm ((φm ⟨le_rfl, hs⟩ xs xs.1).trans_eq hx) _
    have := φst ▸ mapsTo_image φ (Icc 0 s)
    exact (mem_Icc.mp (@this 0 (by rw [mem_Icc]; exact ⟨le_rfl, hs⟩))).1
  simp only [tsub_zero, this, add_zero]
  rfl
#align unique_unit_speed_on_Icc_zero unique_unit_speed_on_Icc_zero

/-- The natural parameterization of `f` on `s`, which, if `f` has locally bounded variation on `s`,
* has unit speed on `s` (by `has_unit_speed_naturalParameterization`).
* composed with `variationOnFromTo f s a`, is at distance zero from `f`
  (by `edist_naturalParameterization_eq_zero`).
-/
noncomputable def naturalParameterization (f : α → E) (s : Set α) (a : α) : ℝ → E :=
  f ∘ @Function.invFunOn _ _ ⟨a⟩ (variationOnFromTo f s a) s
#align natural_parameterization naturalParameterization

theorem edist_naturalParameterization_eq_zero {f : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) {a : α} (as : a ∈ s) {b : α} (bs : b ∈ s) :
    edist (naturalParameterization f s a (variationOnFromTo f s a b)) (f b) = 0 := by
  dsimp only [naturalParameterization]
  haveI : Nonempty α := ⟨a⟩
  obtain ⟨cs, hc⟩ :=
    @Function.invFunOn_pos _ _ _ s (variationOnFromTo f s a) (variationOnFromTo f s a b)
      ⟨b, bs, rfl⟩
  rw [variationOnFromTo.eq_left_iff hf as cs bs] at hc
  apply variationOnFromTo.edist_zero_of_eq_zero hf cs bs hc
#align edist_natural_parameterization_eq_zero edist_naturalParameterization_eq_zero

theorem has_unit_speed_naturalParameterization (f : α → E) {s : Set α}
    (hf : LocallyBoundedVariationOn f s) {a : α} (as : a ∈ s) :
    HasUnitSpeedOn (naturalParameterization f s a) (variationOnFromTo f s a '' s) := by
  dsimp only [HasUnitSpeedOn]
  rw [hasConstantSpeedOnWith_iff_ordered]
  rintro _ ⟨b, bs, rfl⟩ _ ⟨c, cs, rfl⟩ h
  rcases le_total c b with (cb | bc)
  · rw [NNReal.coe_one, one_mul, le_antisymm h (variationOnFromTo.monotoneOn hf as cs bs cb),
      sub_self, ENNReal.ofReal_zero, Icc_self, eVariationOn.subsingleton]
    exact fun x hx y hy => hx.2.trans hy.2.symm
  · rw [NNReal.coe_one, one_mul, sub_eq_add_neg, variationOnFromTo.eq_neg_swap, neg_neg, add_comm,
      variationOnFromTo.add hf bs as cs, ← variationOnFromTo.eq_neg_swap f]
    rw [←
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn (naturalParameterization f s a) _
        (variationOnFromTo.monotoneOn hf as) bs cs]
    rw [@eVariationOn.eq_of_edist_zero_on _ _ _ _ _ f]
    · rw [variationOnFromTo.eq_of_le _ _ bc, ENNReal.ofReal_toReal (hf b c bs cs)]
    · rintro x ⟨xs, _, _⟩
      exact edist_naturalParameterization_eq_zero hf as xs
#align has_unit_speed_natural_parameterization has_unit_speed_naturalParameterization
