/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.IndicatorFunction

open Function Set
open scoped BigOperators

variable (𝕜 E : Type*) [OrderedSemiring 𝕜] [AddCommMonoid E] [DecidableEq E] [Module 𝕜 E]

namespace Convexity

structure ConvexSpace :=
  protected convexCombo : (E → 𝕜) → Finset E → E
  protected segmentMap : 𝕜 → 𝕜 → E → E → E
  protected convexCombo_singleton (w : E → 𝕜) (x : E) (hw : w x = 1) : convexCombo w {x} = x
  protected segmentMap_eq_convexCombo (a b : 𝕜) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (x y : E) : segmentMap a b x y = convexCombo (indicator {x} (const _ a)) {x, y}
  protected convexCombo_convexCombo (w : E → 𝕜) (w' : E → E → 𝕜) (s : Finset E)
    (hw₀ : ∀ x ∈ s, 0 ≤ w x) (hw₁ : ∑ x in s, w x = 1) (hw₀' : ∀ x ∈ s, ∀ y ∈ s, 0 ≤ w' x y)
    (hw₁' : ∀ x ∈ s, ∑ y in s, w' x y = 1) : convexSpace ()

end Convexity
