/-
Copyright (c) 2026 Alex Ibarra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ibarra
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Gram completeness: equal Gram matrices are related by a unitary

This file proves *Gram completeness*: in a finite-dimensional inner product space, two finite
families of vectors with equal Gram matrices are related by a single global unitary (a linear
isometric automorphism of the whole space).

## Main results

* `LinearIsometryEquiv.exists_of_gram_eq`: given `v w : ι → E` over a finite index type with
  `⟪v i, v j⟫ = ⟪w i, w j⟫` for all `i j`, there is a `U : E ≃ₗᵢ[𝕜] E` with `U (v i) = w i`
  for every `i`.
* `LinearIsometryEquiv.exists_of_gram_matrix_eq`: the same statement phrased through
  `Matrix.gram`.
* `eq_of_isometryInvariant_of_gram_eq`: any function of a family that is invariant under the
  diagonal unitary action agrees on families with equal Gram matrices — i.e. it factors through
  the Gram matrix. The Gram entries `⟪v i, v j⟫` are thus a complete set of separating invariants
  of the unitary action.

## Implementation notes

The proof factors the linear-combination map `Finsupp.linearCombination 𝕜 v` through its range:
equal Gram matrices force the kernels of the two linear-combination maps to coincide, so the map
`v i ↦ w i` is well defined on `span 𝕜 (range v)` and, by the Gram hypothesis, an isometry there.
`LinearIsometry.extend` promotes this isometry of a subspace to a global isometry of `E`, which is
surjective (hence a `LinearIsometryEquiv`) because `E` is finite-dimensional.

This is the geometric core of the First Fundamental Theorem of classical invariant theory for the
unitary group `U(n)` (and `GL(n, ℂ)`): the Gram entries are a complete invariant of a tuple up to
the diagonal unitary action.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open Finsupp LinearMap

namespace LinearIsometryEquiv

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [Finite ι]

/-! ### Inner products of linear combinations through the Gram entries -/

omit [Finite ι] in
/-- The inner product of two linear combinations of a family expands through its Gram entries:
`⟪∑ cᵢ vᵢ, ∑ dⱼ vⱼ⟫ = ∑ᵢ ∑ⱼ conj (cᵢ) * dⱼ * ⟪vᵢ, vⱼ⟫`. -/
theorem inner_linearCombination_linearCombination [Fintype ι] (v : ι → E) (c d : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 v c, Finsupp.linearCombination 𝕜 v d⟫_𝕜
      = ∑ i, ∑ j, conj (c i) * d j * ⟪v i, v j⟫_𝕜 := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp), sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

variable {v w : ι → E}

/-- If two families have equal Gram matrices, the inner products of corresponding linear
combinations agree. -/
theorem inner_linearCombination_eq_of_gram_eq
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) (c d : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 v c, Finsupp.linearCombination 𝕜 v d⟫_𝕜
      = ⟪Finsupp.linearCombination 𝕜 w c, Finsupp.linearCombination 𝕜 w d⟫_𝕜 := by
  have := Fintype.ofFinite ι
  rw [inner_linearCombination_linearCombination, inner_linearCombination_linearCombination]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [h i j]

/-- Equal Gram matrices force the linear-combination maps to share a kernel: if `∑ cᵢ vᵢ = 0`
then `∑ cᵢ wᵢ = 0`. -/
theorem linearCombination_eq_zero_of_gram_eq
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) (c : ι →₀ 𝕜)
    (hc : Finsupp.linearCombination 𝕜 v c = 0) :
    Finsupp.linearCombination 𝕜 w c = 0 := by
  rw [← inner_self_eq_zero (𝕜 := 𝕜), ← inner_linearCombination_eq_of_gram_eq h c c, hc,
    inner_zero_left]

theorem ker_linearCombination_le_of_gram_eq (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) :
    LinearMap.ker (Finsupp.linearCombination 𝕜 v)
      ≤ LinearMap.ker (Finsupp.linearCombination 𝕜 w) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  exact linearCombination_eq_zero_of_gram_eq h c hc

/-! ### The Gram-preserving map between the spans

From `ker Lv ≤ ker Lw` we factor `Lw` through `range Lv = span 𝕜 (range v)`, obtaining a linear
map sending each `v i` to `w i`. Equal Gram matrices make it inner-product-preserving. -/

variable (v w) in
/-- The linear map `range (linearCombination 𝕜 v) →ₗ E` factoring the linear-combination map of
`w` through the range of that of `v`; on a generator it sends `v i ↦ w i`. Requires only that
the kernel of the first map is contained in the kernel of the second. -/
noncomputable def gramFactor
    (hle : LinearMap.ker (Finsupp.linearCombination 𝕜 v)
      ≤ LinearMap.ker (Finsupp.linearCombination 𝕜 w)) :
    LinearMap.range (Finsupp.linearCombination 𝕜 v) →ₗ[𝕜] E :=
  ((LinearMap.ker (Finsupp.linearCombination 𝕜 v)).liftQ
      (Finsupp.linearCombination 𝕜 w) hle).comp
    (LinearMap.quotKerEquivRange (Finsupp.linearCombination 𝕜 v)).symm.toLinearMap

omit [Finite ι] in
variable (v w) in
/-- On a linear combination, `gramFactor` returns the same combination of the `w`s. -/
theorem gramFactor_linearCombination
    (hle : LinearMap.ker (Finsupp.linearCombination 𝕜 v)
      ≤ LinearMap.ker (Finsupp.linearCombination 𝕜 w)) (c : ι →₀ 𝕜) :
    gramFactor v w hle ⟨Finsupp.linearCombination 𝕜 v c, LinearMap.mem_range_self _ c⟩
      = Finsupp.linearCombination 𝕜 w c := by
  have hsymm : (LinearMap.quotKerEquivRange (Finsupp.linearCombination 𝕜 v)).symm
      ⟨Finsupp.linearCombination 𝕜 v c, LinearMap.mem_range_self _ c⟩
        = Submodule.Quotient.mk c := by
    apply (LinearMap.quotKerEquivRange (Finsupp.linearCombination 𝕜 v)).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
  simp only [gramFactor, LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm, Submodule.liftQ_apply]

omit [Finite ι] in
variable (v w) in
/-- `gramFactor` sends the generator `v i` (in the range) to `w i`. -/
theorem gramFactor_apply_gen
    (hle : LinearMap.ker (Finsupp.linearCombination 𝕜 v)
      ≤ LinearMap.ker (Finsupp.linearCombination 𝕜 w)) (i : ι)
    (hvi : v i ∈ LinearMap.range (Finsupp.linearCombination 𝕜 v)) :
    gramFactor v w hle ⟨v i, hvi⟩ = w i := by
  have hc : Finsupp.linearCombination 𝕜 v (Finsupp.single i 1) = v i := by
    rw [Finsupp.linearCombination_single, one_smul]
  have hd : Finsupp.linearCombination 𝕜 w (Finsupp.single i 1) = w i := by
    rw [Finsupp.linearCombination_single, one_smul]
  have := gramFactor_linearCombination v w hle (Finsupp.single i 1)
  rw [hd] at this
  rw [← this]
  exact congrArg _ (Subtype.ext hc.symm)

variable (v w) in
/-- `gramFactor` preserves the inner product when the two families have equal Gram matrices. -/
theorem inner_gramFactor (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜)
    (x y : LinearMap.range (Finsupp.linearCombination 𝕜 v)) :
    ⟪gramFactor v w (ker_linearCombination_le_of_gram_eq h) x,
        gramFactor v w (ker_linearCombination_le_of_gram_eq h) y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  rw [LinearMap.mem_range] at hx hy
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := hy
  rw [gramFactor_linearCombination, gramFactor_linearCombination, Submodule.coe_inner]
  exact (inner_linearCombination_eq_of_gram_eq h c d).symm

variable [FiniteDimensional 𝕜 E]

variable (v w) in
/-- The Gram-preserving map packaged as a linear isometry from `span 𝕜 (range v)` into `E`. -/
noncomputable def gramIsometry (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) :
    LinearMap.range (Finsupp.linearCombination 𝕜 v) →ₗᵢ[𝕜] E where
  toLinearMap := gramFactor v w (ker_linearCombination_le_of_gram_eq h)
  norm_map' x := (LinearMap.norm_map_iff_inner_map_map _).mpr (inner_gramFactor v w h) x

/-! ### Gram completeness -/

variable (v w)

/-- **Gram completeness.** Two finite families of vectors in a finite-dimensional inner product
space with equal Gram matrices `⟪v i, v j⟫ = ⟪w i, w j⟫` are related by a single global unitary
(a linear isometric automorphism) `U` with `U (v i) = w i`.

This is the geometric core of the First Fundamental Theorem for the unitary group: the Gram
entries form a complete invariant of a family up to the diagonal unitary action. -/
theorem exists_of_gram_eq (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) :
    ∃ U : E ≃ₗᵢ[𝕜] E, ∀ i, U (v i) = w i := by
  refine ⟨LinearIsometryEquiv.ofSurjective (gramIsometry v w h).extend
    ((gramIsometry v w h).extend.toLinearMap.surjective_of_injective
      (gramIsometry v w h).extend.injective), fun i => ?_⟩
  have hvi : v i ∈ LinearMap.range (Finsupp.linearCombination 𝕜 v) :=
    ⟨Finsupp.single i 1, by rw [Finsupp.linearCombination_single, one_smul]⟩
  rw [LinearIsometryEquiv.coe_ofSurjective]
  have hext : (gramIsometry v w h).extend
      (⟨v i, hvi⟩ : LinearMap.range (Finsupp.linearCombination 𝕜 v))
        = gramIsometry v w h ⟨v i, hvi⟩ := LinearIsometry.extend_apply _ _
  rw [show ((⟨v i, hvi⟩ : LinearMap.range (Finsupp.linearCombination 𝕜 v)) : E) = v i from rfl]
    at hext
  rw [hext]
  exact gramFactor_apply_gen v w (ker_linearCombination_le_of_gram_eq h) i hvi

/-- **Gram completeness, through `Matrix.gram`.** Two finite families of vectors in a
finite-dimensional inner product space with equal Gram matrices are related by a global unitary
`U` with `U (v i) = w i`. -/
theorem exists_of_gram_matrix_eq (h : Matrix.gram 𝕜 v = Matrix.gram 𝕜 w) :
    ∃ U : E ≃ₗᵢ[𝕜] E, ∀ i, U (v i) = w i :=
  exists_of_gram_eq v w fun i j => by
    simpa only [Matrix.gram_apply] using congrFun (congrFun h i) j

end LinearIsometryEquiv

/-- **Function-level First Fundamental Theorem (separation).** Any function of a family that is
invariant under the diagonal action of all unitaries takes equal values on families with equal
Gram matrices — i.e. it factors through the Gram matrix. Hence the Gram entries `⟪v i, v j⟫` form
a complete set of separating invariants of the unitary action. -/
theorem eq_of_isometryInvariant_of_gram_eq {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {ι : Type*} [Finite ι]
    {α : Type*} (v w : ι → E) (f : (ι → E) → α)
    (hf : ∀ (U : E ≃ₗᵢ[𝕜] E) (u : ι → E), f (fun i => U (u i)) = f u)
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) :
    f v = f w := by
  obtain ⟨U, hU⟩ := LinearIsometryEquiv.exists_of_gram_eq v w h
  have hfv : f (fun i => U (v i)) = f v := hf U v
  rw [show (fun i => U (v i)) = w from funext hU] at hfv
  exact hfv.symm
