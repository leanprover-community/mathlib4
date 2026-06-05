/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Graded coalgebras

A coalgebra `A` over `R` is *graded* by a family of submodules `𝒜 : ι → Submodule R A` if both
the comultiplication and counit respect the grading: `Δ(𝒜 n) ⊆ ⨆_{p+q=n} 𝒜 p ⊗ 𝒜 q` and
`ε(𝒜 n) = 0` for `n ≠ 0`.
-/

public section

variable {R A ι : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [Coalgebra R A] [AddMonoid ι]

/-- A coalgebra is *graded* by `𝒜 : ι → Submodule R A` if both the comultiplication and counit
respect the grading: `Δ(𝒜 n) ⊆ ⨆_{p+q=n} 𝒜 p ⊗ 𝒜 q` and `ε(𝒜 n) = 0` for `n ≠ 0`. -/
class GradedCoalgebra (𝒜 : ι → Submodule R A) : Prop where
  /-- The comultiplication takes degree-`n` elements to the sum of `𝒜 p ⊗ 𝒜 q` over `p + q = n`. -/
  comul_mem : ∀ {n : ι} {x : A}, x ∈ 𝒜 n →
    Coalgebra.comul x ∈
      ⨆ p : ι, ⨆ q : ι, ⨆ (_ : p + q = n),
        LinearMap.range (TensorProduct.map (𝒜 p).subtype (𝒜 q).subtype)
  /-- The counit vanishes on elements of nonzero degree. -/
  counit_eq_zero_of_ne_zero : ∀ {n : ι} {x : A}, n ≠ 0 → x ∈ 𝒜 n →
    Coalgebra.counit (R := R) x = 0
