/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber, Jon Crall
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Gram Matrices

This file defines Gram matrices and proves their positive semidefiniteness. It also
shows that a finite family of vectors is determined, up to a linear isometry, by
its pairwise inner products (equivalently, by its Gram matrix): if two families
have equal pairwise inner products, the map sending one to the other extends to a
linear isometry. In the language of finite frames, two frames are equivalent under
a linear isometry (a unitary or orthogonal map) iff their Gram matrices coincide;
this is also the exact (noise-free) case of the Procrustes alignment problem.
Results require `RCLike 𝕜`.

## Main definition

* `Matrix.gram` : the `Matrix n n 𝕜` with `⟪v i, v j⟫` at `i j : n`, where `v : n → E` for an
  `Inner 𝕜 E`.

## Main results

* `Matrix.posSemidef_gram`: Gram matrices are positive semidefinite.
* `Matrix.posDef_gram_iff_linearIndependent`: Linear independence of `v` is
  equivalent to positive definiteness of `gram 𝕜 v`.
* `exists_linearIsometryEquiv_span_map_eq_of_inner_eq`: two families `φ`, `ψ` (in
  possibly different inner product spaces) with equal pairwise inner products are
  related by a linear isometry equivalence of their spans, `span 𝕜 (range φ) ≃ₗᵢ
  span 𝕜 (range ψ)`, sending `φ i` to `ψ i`.
* `exists_linearIsometryEquiv_map_eq_of_inner_eq`: in finite dimension, this
  extends to a linear isometry equivalence of the ambient space.
* `Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq`: in finite
  dimension, two families have equal Gram matrices iff a linear isometry
  equivalence of the ambient space maps one to the other.

## References

* [R. A. Horn, C. R. Johnson, *Matrix Analysis*][horn_johnson_2013]
* [P. H. Schönemann, *A generalized solution of the orthogonal Procrustes
  problem*][schonemann1966]
* [T.-Y. Chien, S. Waldron, *A Characterization of Projective Unitary Equivalence
  of Finite Frames and Applications*][chien_waldron_2016]
-/

@[expose] public section

open RCLike Real Matrix

open scoped InnerProductSpace ComplexOrder ComplexConjugate

variable {E n α 𝕜 : Type*}
namespace Matrix

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
def gram (𝕜 : Type*) [Inner 𝕜 E] (v : n → E) : Matrix n n 𝕜 := of fun i j ↦ ⟪v i, v j⟫_𝕜

@[simp]
lemma gram_apply [Inner 𝕜 E] (v : n → E) (i j : n) :
    (gram 𝕜 v) i j = ⟪v i, v j⟫_𝕜 := rfl

variable [RCLike 𝕜]

section SemiInnerProductSpace
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

@[simp]
lemma gram_zero : gram 𝕜 (0 : n → E) = 0 := Matrix.ext fun _ _ ↦ inner_zero_left _

@[simp]
lemma gram_single [DecidableEq n] (i : n) (x : E) :
    gram 𝕜 (Pi.single i x) = Matrix.single i i ⟪x, x⟫_𝕜 := by
  ext j k
  obtain hij | rfl := ne_or_eq i j
  · simp [hij]
  obtain hik | rfl := ne_or_eq i k
  · simp [hik]
  simp

lemma submatrix_gram (v : n → E) {m : Set n} (f : m → n) :
    (gram 𝕜 v).submatrix f f = gram 𝕜 (v ∘ f) := rfl

variable (𝕜) in
/-- A Gram matrix is Hermitian. -/
lemma isHermitian_gram (v : n → E) : (gram 𝕜 v).IsHermitian :=
  Matrix.ext fun _ _ ↦ inner_conj_symm _ _

theorem star_dotProduct_gram_mulVec [Fintype n] (v : n → E) (x y : n → 𝕜) :
    star x ⬝ᵥ (gram 𝕜 v) *ᵥ y = ⟪∑ i, x i • v i, ∑ i, y i • v i⟫_𝕜 := by
  trans ∑ i, ∑ j, conj (x i) * y j * ⟪v i, v j⟫_𝕜
  · simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm, ← star_def,
      gram_apply, Pi.star_apply]
  · simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]

variable [Finite n]

variable (𝕜) in
/-- A Gram matrix is positive semidefinite. -/
theorem posSemidef_gram (v : n → E) :
    PosSemidef (gram 𝕜 v) := by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_gram _ _) fun x ↦ ?_
  rw [star_dotProduct_gram_mulVec, le_iff_re_im]
  simp

/-- In a normed space, positive definiteness of `gram 𝕜 v` implies linear independence of `v`. -/
theorem linearIndependent_of_posDef_gram {v : n → E} (h_gram : PosDef (gram 𝕜 v)) :
    LinearIndependent 𝕜 v := by
  have := Fintype.ofFinite n
  rw [Fintype.linearIndependent_iff]
  intro y hy
  have := h_gram.dotProduct_mulVec_pos (x := y)
  simp_all [star_dotProduct_gram_mulVec]

omit [Finite n] in
theorem linearIndependent_of_det_gram_ne_zero [Fintype n] [DecidableEq n] {v : n → E}
    (h : (gram 𝕜 v).det ≠ 0) : LinearIndependent 𝕜 v :=
  linearIndependent_of_posDef_gram <| (posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero.mpr h

end SemiInnerProductSpace

section NormedInnerProductSpace
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Finite n]

/-- In a normed space, linear independence of `v` implies positive definiteness of `gram 𝕜 v`. -/
theorem posDef_gram_of_linearIndependent
    {v : n → E} (h_li : LinearIndependent 𝕜 v) : PosDef (gram 𝕜 v) := by
  have := Fintype.ofFinite n
  rw [Fintype.linearIndependent_iff] at h_li
  refine .of_dotProduct_mulVec_pos (isHermitian_gram _ _) fun x hx ↦
    ((posSemidef_gram ..).dotProduct_mulVec_nonneg _).lt_of_ne' ?_
  rw [star_dotProduct_gram_mulVec, inner_self_eq_zero.ne]
  exact mt (h_li x) (mt funext hx)

/-- In a normed space, linear independence of `v` is equivalent to positive definiteness of
`gram 𝕜 v`. -/
theorem posDef_gram_iff_linearIndependent {v : n → E} :
    PosDef (gram 𝕜 v) ↔ LinearIndependent 𝕜 v :=
  ⟨linearIndependent_of_posDef_gram, posDef_gram_of_linearIndependent⟩

omit [Finite n] in
theorem det_gram_ne_zero_iff_linearIndependent [Fintype n] [DecidableEq n] {v : n → E} :
    (gram 𝕜 v).det ≠ 0 ↔ LinearIndependent 𝕜 v := by
  rw [← posDef_gram_iff_linearIndependent, (posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero]

omit [Finite n] in
theorem gram_eq_conjTranspose_mul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (v : n → E) :
    letI m := of fun i j ↦ b.repr (v j) i
    gram 𝕜 v = mᴴ * m := by
  ext i j
  simp [mul_apply, b.repr_apply_apply, b.sum_inner_mul_inner]

omit [Finite n] in
/-- Inequality `‖f x‖ ≤ ‖f‖ * ‖x‖` lifted to Gram matrices. -/
theorem posSemidef_opNorm_smul_gram_sub_gram {F} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (v : n → E) (f : E →L[𝕜] F) : (‖f‖ ^ 2 • gram 𝕜 v - gram 𝕜 (f ∘ v)).PosSemidef := by
  refine ⟨(isHermitian_gram 𝕜 v).smul (((Pi.isSelfAdjoint.mpr (congrFun rfl)).apply f).pow 2)
    |>.sub (isHermitian_gram 𝕜 (f ∘ v)), fun c ↦ ?_⟩
  simp_rw [Finsupp.sum, Matrix.sub_apply, Matrix.smul_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib, sub_nonneg]
  calc
    ∑ x ∈ c.support, ∑ y ∈ c.support, star (c x) * gram 𝕜 (f ∘ v) x y * c y
    _ = (‖f (∑ x ∈ c.support, c x • v x)‖ : 𝕜) ^ 2 := ?h1
    _ ≤ ‖f‖ ^ 2 • (‖∑ i ∈ c.support, c i • v i‖ : 𝕜) ^ 2 := by
      norm_cast
      grw [f.le_opNorm _, smul_eq_mul, ← mul_pow]
    _ = ∑ x ∈ c.support, ∑ y ∈ c.support, star (c x) * ‖f‖ ^ 2 • gram 𝕜 v x y * c y := ?h2
  all_goals
    rw [Finset.sum_comm]
    simp [← inner_self_eq_norm_sq_to_K, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
      Finset.mul_sum, Finset.smul_sum, RCLike.real_smul_eq_coe_mul]
    grind

end NormedInnerProductSpace

end Matrix

/-! ### Isometries from equal inner products

Two families of vectors with equal pairwise inner products are related by a linear
isometry: the map `φ i ↦ ψ i` extends to a linear isometry equivalence of their
spans, in finite dimension to a linear isometry equivalence of the ambient space,
and the hypothesis can be packaged as equality of `Matrix.gram` matrices. This is
the exact case of the Procrustes alignment problem. -/

section Rigidity

variable {F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

section
variable {φ : ι → E} {ψ : ι → F} (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜)
include h

/-- For families `φ`, `ψ` with equal pairwise inner products, the maps of linear combinations
`∑ cᵢ • φ i` and `∑ cᵢ • ψ i` have equal pairwise inner products. -/
theorem inner_linearCombination_eq_of_inner_eq (c c' : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 φ c, Finsupp.linearCombination 𝕜 φ c'⟫_𝕜
      = ⟪Finsupp.linearCombination 𝕜 ψ c, Finsupp.linearCombination 𝕜 ψ c'⟫_𝕜 := by
  simp [inner_linearCombination_linearCombination, h]

/-- Families with equal pairwise inner products have linear-combination maps with equal kernels:
`∑ cᵢ • φ i = 0 ↔ ∑ cᵢ • ψ i = 0`. -/
theorem ker_linearCombination_eq_of_inner_eq :
    LinearMap.ker (Finsupp.linearCombination 𝕜 φ)
      = LinearMap.ker (Finsupp.linearCombination 𝕜 ψ) := by
  ext c
  rw [LinearMap.mem_ker, LinearMap.mem_ker,
    ← inner_self_eq_zero (𝕜 := 𝕜) (x := Finsupp.linearCombination 𝕜 φ c),
    inner_linearCombination_eq_of_inner_eq h c c, inner_self_eq_zero]

/-- The (unique) linear isometry equivalence `span 𝕜 (range φ) ≃ₗᵢ span 𝕜 (range ψ)` sending each
`φ i` to `ψ i`, when the families `φ`, `ψ` (in possibly different inner product spaces over `𝕜`)
have equal pairwise inner products.  It is the map of linear combinations `∑ cᵢ • φ i ↦ ∑ cᵢ • ψ i`
(well defined since the two linear-combination maps have equal kernels), transported to the spans
and upgraded to an isometry via `LinearEquiv.isometryOfInner`.  No finiteness is required, and the
ambient spaces need not coincide.

It is the unique such isometry: a linear isometry equivalence of the spans sending `φ i ↦ ψ i` is
determined on the spanning family `φ` (`LinearMap.eqOn_span`). -/
noncomputable def linearIsometryEquivSpanOfInnerEq :
    (Submodule.span 𝕜 (Set.range φ)) ≃ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)) :=
  (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜)).symm.trans
    ((((Finsupp.linearCombination 𝕜 φ).quotKerEquivRange.symm.trans
        ((Submodule.quotEquivOfEq _ _ (ker_linearCombination_eq_of_inner_eq h)).trans
          (Finsupp.linearCombination 𝕜 ψ).quotKerEquivRange)).isometryOfInner fun x y => by
        obtain ⟨_, c, rfl⟩ := x
        obtain ⟨_, c', rfl⟩ := y
        simp only [LinearEquiv.trans_apply, LinearMap.quotKerEquivRange_symm_apply_image,
          Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk,
          Submodule.coe_inner]
        exact (inner_linearCombination_eq_of_inner_eq h c c').symm).trans
      (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜)))

@[simp]
theorem linearIsometryEquivSpanOfInnerEq_apply (i : ι) :
    (linearIsometryEquivSpanOfInnerEq h ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ : F) = ψ i := by
  simp only [linearIsometryEquivSpanOfInnerEq, LinearIsometryEquiv.trans_apply]
  rw [show ((LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜 (v := φ))).symm
        ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ :
        LinearMap.range (Finsupp.linearCombination 𝕜 φ))
      = ⟨Finsupp.linearCombination 𝕜 φ (Finsupp.single i 1), LinearMap.mem_range_self _ _⟩
      from Subtype.ext (by simp)]
  simp only [LinearEquiv.coe_isometryOfInner, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivRange_apply_mk, LinearIsometryEquiv.coe_ofEq_apply]
  simp [Finsupp.linearCombination_single]

/-- If a family `φ : ι → E` and a family `ψ : ι → F`
in two inner product spaces over `𝕜` have equal pairwise inner products, then the
map `φ i ↦ ψ i` extends to a linear isometry equivalence of the span of the `φ i`
onto the span of the `ψ i`. No finiteness is required, and the ambient spaces need
not coincide. See `linearIsometryEquivSpanOfInnerEq` for the construction. -/
theorem exists_linearIsometryEquiv_span_map_eq_of_inner_eq :
    ∃ L :
      (Submodule.span 𝕜 (Set.range φ)) ≃ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)),
      ∀ i, (L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ : F) = ψ i :=
  ⟨linearIsometryEquivSpanOfInnerEq h, linearIsometryEquivSpanOfInnerEq_apply h⟩

end

/-- If two families `φ ψ : ι → E` in a
finite-dimensional inner product space have equal pairwise inner products, then
there is a linear isometry equivalence `W` of `E` with `W (φ i) = ψ i` for every
`i`. The span-level equivalence is extended to the whole space by
`LinearIsometry.extend` and bundled as an equivalence by finite dimensionality
(`LinearIsometry.toLinearIsometryEquiv`). -/
theorem exists_linearIsometryEquiv_map_eq_of_inner_eq [FiniteDimensional 𝕜 E] {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  obtain ⟨L, hL⟩ := exists_linearIsometryEquiv_span_map_eq_of_inner_eq h
  -- Extend the span-to-ambient isometry to `E`, then bundle it as an equivalence.
  set L' : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] E :=
    (Submodule.span 𝕜 (Set.range ψ)).subtypeₗᵢ.comp L.toLinearIsometry with hL'
  refine ⟨L'.extend.toLinearIsometryEquiv rfl, fun i => ?_⟩
  rw [LinearIsometry.coe_toLinearIsometryEquiv,
    show φ i = ((⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ :
      Submodule.span 𝕜 (Set.range φ)) : E) from rfl, L'.extend_apply]
  exact hL i

namespace Matrix

/-- Two families of vectors in a
finite-dimensional inner product space have equal Gram matrices if and only if a
linear isometry equivalence of the ambient space maps one family to the other. -/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq [FiniteDimensional 𝕜 E]
    {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  constructor
  · intro hg
    refine exists_linearIsometryEquiv_map_eq_of_inner_eq fun i j => ?_
    simpa only [gram_apply] using congrFun₂ hg i j
  · rintro ⟨W, hW⟩
    ext i j
    simp [gram_apply, ← hW i, ← hW j, LinearIsometryEquiv.inner_map_map]

end Matrix

end Rigidity
