/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Algebra.GroupWithZero.Int

/-!
# Discrete Valuations

A valuation `v : A → ℤₘ₀` is said to be a (normalized) discrete valuation if
`Multiplicative.ofAdd (- 1 : ℤ)` belongs to the image of `v`.

## Main Definitions
* `IsDiscrete`: We define a valuation to be discrete if it is `ℤₘ₀`-valued and
  `Multiplicative.ofAdd (- 1 : ℤ)` belongs to the image.

## TODO
* Define (pre)uniformizers for nontrivial `ℤₘ₀`-valued valuations.
* Relate discrete valuations and discrete valuation rings.

-/

namespace Valuation

open Function Multiplicative Set

variable {A : Type*} [Ring A]

/-- A valuation `v` on a ring `A` is (normalized) discrete if it is `ℤₘ₀`-valued and
  `Multiplicative.ofAdd (- 1 : ℤ)` belongs to the image. -/
class IsDiscrete (v : Valuation A ℤₘ₀) : Prop where
  one_mem_range : (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀) ∈ range v

/-- A discrete valuation on a field `K` is surjective. -/
lemma IsDiscrete.surj {K : Type*} [Field K] (v : Valuation K ℤₘ₀) [hv : IsDiscrete v] :
    Surjective v := by
  intro c
  refine WithOne.cases_on c ⟨0, map_zero _⟩ ?_
  obtain ⟨π, hπ⟩ := hv
  intro a
  use π ^ (- a.toAdd)
  rw [map_zpow₀, hπ]
  simp only [ofAdd_neg, WithZero.coe_inv, zpow_neg, inv_zpow', inv_inv, ← WithZero.ofAdd_zpow]
  rfl

/-- A `ℤₘ₀`-valued valuation on a field `K` is discrete if and only if it is surjective. -/
lemma isDiscrete_iff_surjective {K : Type*} [Field K] (v : Valuation K ℤₘ₀) :
    IsDiscrete v ↔ Surjective v :=
  ⟨fun _ ↦ IsDiscrete.surj v, fun hv ↦ ⟨hv (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀)⟩⟩

end Valuation
