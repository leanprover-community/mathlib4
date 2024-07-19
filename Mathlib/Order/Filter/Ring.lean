/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import Mathlib.Order.Filter.Germ
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Lemmas about filters and ordered rings.
-/
namespace Filter

open Function Filter

universe u v

variable {α : Type u} {β : Type v}

theorem EventuallyLE.mul_le_mul [MulZeroClass β] [PartialOrder β] [PosMulMono β] [MulPosMono β]
    {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) (hg₀ : 0 ≤ᶠ[l] g₁)
    (hf₀ : 0 ≤ᶠ[l] f₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg, hg₀, hf₀] with x using _root_.mul_le_mul

@[to_additive EventuallyLE.add_le_add]
theorem EventuallyLE.mul_le_mul' [Mul β] [Preorder β] [CovariantClass β β (· * ·) (· ≤ ·)]
    [CovariantClass β β (swap (· * ·)) (· ≤ ·)] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β}
    (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg] with x hfx hgx using _root_.mul_le_mul' hfx hgx

theorem EventuallyLE.mul_nonneg [OrderedSemiring β] {l : Filter α} {f g : α → β} (hf : 0 ≤ᶠ[l] f)
    (hg : 0 ≤ᶠ[l] g) : 0 ≤ᶠ[l] f * g := by filter_upwards [hf, hg] with x using _root_.mul_nonneg

theorem eventually_sub_nonneg [OrderedRing β] {l : Filter α} {f g : α → β} :
    0 ≤ᶠ[l] g - f ↔ f ≤ᶠ[l] g :=
  eventually_congr <| eventually_of_forall fun _ => sub_nonneg

namespace Germ

variable {l : Filter α}

@[to_additive]
instance instOrderedCommGroup [OrderedCommGroup β] : OrderedCommGroup (Germ l β) where
  __ := instOrderedCancelCommMonoid
  __ := instCommGroup

instance instOrderedSemiring [OrderedSemiring β] : OrderedSemiring (Germ l β) where
  __ := instSemiring
  __ := instOrderedAddCommMonoid
  zero_le_one := const_le zero_le_one
  mul_le_mul_of_nonneg_left x y z := inductionOn₃ x y z fun _f _g _h hfg hh ↦ hh.mp <| hfg.mono
    fun _a ↦ mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right x y z := inductionOn₃ x y z fun _f _g _h hfg hh ↦ hh.mp <| hfg.mono
    fun _a ↦ mul_le_mul_of_nonneg_right

instance instOrderedCommSemiring [OrderedCommSemiring β] : OrderedCommSemiring (Germ l β) where
  __ := instOrderedSemiring
  __ := instCommSemiring

instance instOrderedRing [OrderedRing β] : OrderedRing (Germ l β) where
  __ := instRing
  __ := instOrderedAddCommGroup
  __ := instOrderedSemiring
  mul_nonneg x y := inductionOn₂ x y fun _f _g hf hg ↦ hg.mp <| hf.mono fun _a ↦ mul_nonneg

instance instOrderedCommRing [OrderedCommRing β] : OrderedCommRing (Germ l β) where
  __ := instOrderedRing
  __ := instOrderedCommSemiring

end Germ

end Filter
