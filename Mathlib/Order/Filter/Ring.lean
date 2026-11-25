/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Filter.Germ.OrderedMonoid

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Lemmas about filters and ordered rings.
-/

public section
namespace Filter

open Filter

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

theorem eventually_sub_nonneg [AddGroup β] [LE β] [AddRightMono β]
    {l : Filter α} {f g : α → β} :
    0 ≤ᶠ[l] g - f ↔ f ≤ᶠ[l] g :=
  eventually_congr <| Eventually.of_forall fun _ => sub_nonneg

namespace Product

variable {l : Filter α} {ε : α → Type*}

instance instIsOrderedRing [∀ i, Semiring (ε i)] [∀ i, PartialOrder (ε i)]
    [∀ i, IsOrderedRing (ε i)] : IsOrderedRing (Product l ε) where
  zero_le_one := by simp [← coe_zero, ← coe_one]
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp only [← coe_zero, ← coe_mul, coe_le, Pi.zero_apply, Pi.mul_apply] at ha hbc ⊢
    filter_upwards [ha, hbc] with x hax hbcx
    exact mul_le_mul_of_nonneg_left hbcx hax
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp only [← coe_zero, ← coe_mul, coe_le, Pi.zero_apply, Pi.mul_apply] at ha hbc ⊢
    filter_upwards [ha, hbc] with x hax hbcx
    exact mul_le_mul_of_nonneg_right hbcx hax

end Product

end Filter
