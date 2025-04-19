/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Int
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

open Function Multiplicative Set

variable {A : Type*} [Ring A]

/-- A valuation `v` on a ring `A` is (normalized) discrete if it is `ℤₘ₀`-valued and
  `ofAdd (-1 : ℤ)` belongs to the image. Note that the latter is equivalent to
  asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsDiscrete (v : Valuation A ℤₘ₀) : Prop where
  one_mem_range : (↑(ofAdd (-1 : ℤ)) : ℤₘ₀) ∈ range v

variable {K : Type*} [Field K]

/-- A discrete valuation on a field `K` is surjective. -/
lemma IsDiscrete.surj (v : Valuation K ℤₘ₀) [hv : IsDiscrete v] :
    Surjective v := by
  intro c
  obtain ⟨π, hπ⟩ := hv
  refine WithZero.cases_on c ⟨0, map_zero _⟩ fun a ↦ ⟨π ^ (-a.toAdd), ?_⟩
  simp [hπ, ← WithZero.ofAdd_zpow]

/-- A `ℤₘ₀`-valued valuation on a field `K` is discrete if and only if it is surjective. -/
lemma isDiscrete_iff_surjective (v : Valuation K ℤₘ₀) :
    IsDiscrete v ↔ Surjective v :=
  ⟨fun _ ↦ IsDiscrete.surj v, fun hv ↦ ⟨hv _⟩⟩

end Valuation
