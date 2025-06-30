/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Limits.Final

/-! # Properties of the truncated simplex category

We prove that for `n > 0`, the inclusion functor from the `n`-truncated simplex category to the
untruncated simplex category, and the inclusion functor from the `n`-truncated to the `m`-truncated
simplex category, for `n ≤ m` are initial.
-/

open Simplicial CategoryTheory

namespace SimplexCategory.Truncated

/-- For `0 < n`, the inclusion functor from the `n`-truncated simplex category to the untruncated
simplex category is initial. -/
theorem initial_inclusion {n : ℕ} (hn : 0 < n) : (inclusion n).Initial := by
  constructor
  intro Δ
  have : Nonempty (CostructuredArrow (inclusion n) Δ) := ⟨⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ 0 ⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨Δ₁, hΔ₁⟩, ⟨⟨⟩⟩, f⟩ ⟨⟨Δ₂, hΔ₂⟩, ⟨⟨⟩⟩, f'⟩
  apply Zigzag.trans (j₂ := ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f 0)⟩)
    (.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0)
  by_cases hff' : f 0 ≤ f' 0
  · trans ⟨⦋1⦌ₙ, ⟨⟨⟩⟩, mkOfLe (n := Δ.len) (f 0) (f' 0) hff'⟩
    · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
    · trans ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f' 0)⟩
      · apply Zigzag.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 1
      · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
  · trans ⟨⦋1⦌ₙ, ⟨⟨⟩⟩, mkOfLe (n := Δ.len) (f' 0) (f 0) (le_of_not_ge hff')⟩
    · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 1
    · trans ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f' 0)⟩
      · apply Zigzag.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
      · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0

/-- For `0 < n ≤ m`, the inclusion functor from the `n`-truncated simplex category to the
`m`-truncated simplex category is initial. -/
theorem initial_incl {n m : ℕ} (hm : 0 < n) (hn : n ≤ m) : (incl n m).Initial := by
  constructor
  rintro ⟨Δ, hΔ⟩
  have : Nonempty (CostructuredArrow (incl n m) ⟨Δ, hΔ⟩) := ⟨⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ 0 ⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨Δ₁, hΔ₁⟩, ⟨⟨⟩⟩, f⟩ ⟨⟨Δ₂, hΔ₂⟩, ⟨⟨⟩⟩, f'⟩
  change Δ₁ ⟶ Δ at f
  change Δ₂ ⟶ Δ at f'
  apply Zigzag.trans (j₂ := ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f 0)⟩)
    (.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0)
  by_cases hff' : f 0 ≤ f' 0
  · trans ⟨⦋1⦌ₙ, ⟨⟨⟩⟩, mkOfLe (n := Δ.len) (f 0) (f' 0) hff'⟩
    · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
    · trans ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f' 0)⟩
      · apply Zigzag.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 1
      · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
  · trans ⟨⦋1⦌ₙ, ⟨⟨⟩⟩, mkOfLe (n := Δ.len) (f' 0) (f 0) (le_of_not_ge hff')⟩
    · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 1
    · trans ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f' 0)⟩
      · apply Zigzag.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
      · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0

end SimplexCategory.Truncated
