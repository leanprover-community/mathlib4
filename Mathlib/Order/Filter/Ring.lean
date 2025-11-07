/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import Mathlib.Order.Filter.Germ.OrderedMonoid
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Lemmas about filters and ordered rings.
-/
namespace Filter

open Function Filter

universe u v

variable {α : Type u} {β : Type v}

theorem EventuallyLE.mul_le_mul [MulZeroClass β] [Preorder β] [PosMulMono β] [MulPosMono β]
    {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) (hg₀ : 0 ≤ᶠ[l] g₁)
    (hf₀ : 0 ≤ᶠ[l] f₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg, hg₀, hf₀] with x using _root_.mul_le_mul

@[to_additive EventuallyLE.add_le_add]
theorem EventuallyLE.mul_le_mul' [Mul β] [Preorder β] [MulLeftMono β]
    [MulRightMono β] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β}
    (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg] with x hfx hgx using _root_.mul_le_mul' hfx hgx

theorem EventuallyLE.mul_nonneg [Semiring β] [PartialOrder β] [IsOrderedRing β]
    {l : Filter α} {f g : α → β} (hf : 0 ≤ᶠ[l] f)
    (hg : 0 ≤ᶠ[l] g) : 0 ≤ᶠ[l] f * g := by filter_upwards [hf, hg] with x using _root_.mul_nonneg

theorem eventually_sub_nonneg [Ring β] [PartialOrder β] [IsOrderedRing β]
    {l : Filter α} {f g : α → β} :
    0 ≤ᶠ[l] g - f ↔ f ≤ᶠ[l] g :=
  eventually_congr <| Eventually.of_forall fun _ => sub_nonneg

namespace Germ

variable {l : Filter α}

instance instIsOrderedRing [Semiring β] [PartialOrder β] [IsOrderedRing β] :
    IsOrderedRing (Germ l β) where
  zero_le_one := const_le zero_le_one
  mul_le_mul_of_nonneg_left x :=
    inductionOn x fun _f hx y z ↦ inductionOn₂ y z fun _g _h hfg ↦ hx.mp <| hfg.mono
      fun _a ↦ mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right x :=
    inductionOn x fun _f hx y z ↦ inductionOn₂ y z fun _g _h hfg ↦ hx.mp <| hfg.mono
      fun _a ↦ mul_le_mul_of_nonneg_right

end Germ

end Filter
