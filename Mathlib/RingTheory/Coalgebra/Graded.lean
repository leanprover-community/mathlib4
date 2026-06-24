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

## Main definitions

* `GradedCoalgebra 𝒜`: the comultiplication and counit respect the grading `𝒜`.

## Main results

* `apply_mem_of_mem_bigradedPart`: a linear map out of `A ⊗[R] A` that sends each homogeneous
  pure tensor of total degree `n` into a submodule `S` sends the whole degree-`n` part into `S`.
  This is the bookkeeping lemma for working with `GradedCoalgebra.comul_mem`.
-/

public section

open scoped TensorProduct

variable {R A ι : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]

/-- A linear map on `A ⊗[R] A` that carries each pure tensor `a ⊗ₜ b` with `a ∈ 𝒜 p`, `b ∈ 𝒜 q`,
`p + q = n` into a submodule `S` carries the whole degree-`n` part `⨆_{p+q=n} 𝒜 p ⊗ 𝒜 q` into `S`.
This is the membership companion to `GradedCoalgebra.comul_mem`. -/
theorem apply_mem_of_mem_bigradedPart [Add ι] {M : Type*} [AddCommMonoid M] [Module R M]
    (𝒜 : ι → Submodule R A) (f : A ⊗[R] A →ₗ[R] M) (S : Submodule R M) {n : ι}
    (h : ∀ p q, p + q = n → ∀ a ∈ 𝒜 p, ∀ b ∈ 𝒜 q, f (a ⊗ₜ[R] b) ∈ S) {z : A ⊗[R] A}
    (hz : z ∈ ⨆ (p : ι) (q : ι) (_ : p + q = n),
      Submodule.map₂ (TensorProduct.mk R A A) (𝒜 p) (𝒜 q)) :
    f z ∈ S :=
  Submodule.mem_comap.mp <| (iSup_le fun p => iSup_le fun q => iSup_le fun hpq =>
    Submodule.map₂_le.2 fun a ha b hb => h p q hpq a ha b hb) hz

variable [Coalgebra R A] [Add ι] [Zero ι]

/-- A coalgebra is *graded* by `𝒜 : ι → Submodule R A` if both the comultiplication and counit
respect the grading: `Δ(𝒜 n) ⊆ ⨆_{p+q=n} 𝒜 p ⊗ 𝒜 q` and `ε(𝒜 n) = 0` for `n ≠ 0`. -/
class GradedCoalgebra (𝒜 : ι → Submodule R A) : Prop where
  /-- The comultiplication takes degree-`n` elements to the sum of `𝒜 p ⊗ 𝒜 q` over `p + q = n`. -/
  comul_mem : ∀ {n : ι} {x : A}, x ∈ 𝒜 n →
    Coalgebra.comul x ∈
      ⨆ (p : ι) (q : ι) (_ : p + q = n), Submodule.map₂ (TensorProduct.mk R A A) (𝒜 p) (𝒜 q)
  /-- The counit vanishes on elements of nonzero degree. -/
  counit_eq_zero_of_ne_zero : ∀ {n : ι} {x : A}, n ≠ 0 → x ∈ 𝒜 n →
    Coalgebra.counit (R := R) x = 0
