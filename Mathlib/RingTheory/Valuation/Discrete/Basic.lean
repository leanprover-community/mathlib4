/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Valuation.Basic

/-!
# Discrete Valuations

A valuation `v : A → ℤₘ₀` on a ring `A` is said to be a (normalized) discrete valuation if
`ofAdd (-1 : ℤ)` belongs to the image of `v`. Note that valuations in Mathlib are multiplicative;
if `a : A → ℤ ∪ {infty}` is the additive valuation associated to `v`, this is equivalent to asking
that `1 : ℤ` belongs to the image of `a`.

## Main Definitions
* `IsDiscrete`: We define a valuation to be discrete if it is `ℤₘ₀`-valued and `ofAdd (-1 : ℤ)`
  belongs to the image.

## TODO
* Define (pre)uniformizers for nontrivial `ℤₘ₀`-valued valuations.
* Relate discrete valuations and discrete valuation rings.

-/

namespace Valuation

open Function Multiplicative Set WithZero

variable {A : Type*} [Ring A]

/-- A valuation `v` on a ring `A` is (normalized) discrete if it is `ℤₘ₀`-valued and
`WithZero.exp (-1)` belongs to the image. Note that the latter is equivalent to asking that `1 : ℤ`
belongs to the image of the corresponding additive valuation. -/
class IsDiscrete (v : Valuation A ℤₘ₀) : Prop where
  exp_neg_one_mem_range : exp (-1) ∈ range v

variable {K : Type*} [Field K]

/-- A discrete valuation on a field `K` is surjective. -/
lemma IsDiscrete.surj (v : Valuation K ℤₘ₀) [hv : IsDiscrete v] : Surjective v := by
  obtain ⟨π, hπ⟩ := hv
  rintro (_ | ⟨(c : ℤ)⟩)
  · exact ⟨0, map_zero _⟩
  · exact ⟨π ^ (-c), show _ = exp c by simp [hπ, ← exp_zsmul]⟩

/-- A `ℤₘ₀`-valued valuation on a field `K` is discrete if and only if it is surjective. -/
lemma isDiscrete_iff_surjective (v : Valuation K ℤₘ₀) :
    IsDiscrete v ↔ Surjective v :=
  ⟨fun _ ↦ IsDiscrete.surj v, fun hv ↦ ⟨hv _⟩⟩

end Valuation
