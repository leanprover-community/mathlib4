/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Inner product space structure on exterior powers

Given a real inner product space `E`, we construct a canonical inner product on `⋀[ℝ]^n E`
via the Gram determinant formula: on decomposable elements,
`⟪v₁ ∧ ⋯ ∧ vₙ, w₁ ∧ ⋯ ∧ wₙ⟫ = det (⟪vⱼ, wᵢ⟫)ᵢⱼ`.

## Main results

- `exteriorPower.inner_ιMulti_ιMulti`: The inner product on decomposable elements equals the
  Gram determinant.
- `exteriorPower.inner_ιMulti_self`: `⟪v₁ ∧ ⋯ ∧ vₙ, v₁ ∧ ⋯ ∧ vₙ⟫ = det (gram ℝ d)`.
- `OrthonormalBasis.exteriorPower`: An orthonormal basis of `E` induces an orthonormal basis
  of `⋀[ℝ]^n E`.

## Future work

Generalize to `[RCLike 𝕜]`. To define `innerProductForm`, we would probably
want a semilinear generalization of `exteriorPower.map`, which in turn requires
generalizing `AlternatingMap` to the semilinear setting.

-/

@[expose] public noncomputable section

namespace exteriorPower

open RealInnerProductSpace Matrix

/-- The inner product on `⋀[ℝ]^n E` as a bilinear map. This is an implementation detail
for constructing the `InnerProductSpace` instance. Do not use this directly; use `⟪·, ·⟫_ℝ`
(or `⟪·, ·⟫` with `open RealInnerProductSpace`) instead. -/
def innerProductForm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} :
    ⋀[ℝ]^n E →ₗ[ℝ] ⋀[ℝ]^n E →ₗ[ℝ] ℝ :=
  pairingDual ℝ E n ∘ₗ map n (innerₗ E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

lemma innerProductForm_ιMulti_ιMulti (x y : Fin n → E) :
    innerProductForm (ιMulti ℝ n x) (ιMulti ℝ n y) = det (of fun i j ↦ ⟪x j, y i⟫) := by
  simp [innerProductForm]

@[simp]
lemma innerProductForm_ιMulti_self (x : Fin n → E) :
    innerProductForm (ιMulti ℝ n x) (ιMulti ℝ n x) = det (gram ℝ x) := by
  simp [gram, innerProductForm_ιMulti_ιMulti, real_inner_comm]

lemma flip_innerProductForm :
    LinearMap.flip (innerProductForm (E := E) (n := n)) = innerProductForm := by
  apply linearMap_ext
  ext
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.flip_apply,
    innerProductForm_ιMulti_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext
  exact real_inner_comm _ _

lemma innerProductForm_symm (x y : ⋀[ℝ]^n E) : innerProductForm x y = innerProductForm y x :=
  congr($flip_innerProductForm y x)

@[simp]
lemma innerProductForm_ιMulti_family_of_orthonormal {ι : Type*} [LinearOrder ι] {v : ι → E}
    (hv : Orthonormal ℝ v) (s t : Set.powersetCard ι n) :
    innerProductForm (ιMulti_family ℝ n v s) (ιMulti_family ℝ n v t) = if s = t then 1 else 0 := by
  simp only [ιMulti_family]
  split_ifs with h
  · subst h
    simp [gram_orthonormal (hv.comp _ (RelEmbedding.injective _))]
  · rw [innerProductForm_ιMulti_ιMulti]
    have : ¬t.1 ⊆ s.1 := fun H ↦ Ne.symm h <|
      Subtype.val_injective (Finset.eq_of_subset_of_card_le H (s.2.le.trans t.2.ge))
    rw [Finset.not_subset] at this
    obtain ⟨x, hxt, hxs⟩ := this
    simp only [Set.powersetCard.mem_coe_iff, Set.mem_range, not_exists,
      ← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem] at hxs hxt
    obtain ⟨i, hi⟩ := hxt
    exact det_eq_zero_of_row_eq_zero i (fun j ↦ hv.inner_eq_zero (hi ▸ hxs j))

lemma innerProductForm_eq_sum {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι ℝ E) (x y : ⋀[ℝ]^n E) :
    innerProductForm x y =
      ∑ s, (b.toBasis.exteriorPower n).repr y s * (b.toBasis.exteriorPower n).repr x s := by
  conv_lhs =>
    rw [← (b.toBasis.exteriorPower n).sum_repr x, ← (b.toBasis.exteriorPower n).sum_repr y]
  simp

lemma innerProductForm_self (x : ⋀[ℝ]^n E) {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι ℝ E) :
    innerProductForm x x = ∑ s, (b.toBasis.exteriorPower n).repr x s ^ 2 := by
  simp_rw [innerProductForm_eq_sum b, pow_two]

instance [FiniteDimensional ℝ E] : InnerProductSpace.Core ℝ (⋀[ℝ]^n E) where
  inner x y := innerProductForm x y
  conj_inner_symm x y := innerProductForm_symm y x
  add_left := by simp
  smul_left := by simp
  re_inner_nonneg x := by
    rw [RCLike.re_to_real, innerProductForm_self x (stdOrthonormalBasis ℝ E)]
    exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  definite x h := by
    rw [innerProductForm_self x (stdOrthonormalBasis ℝ E),
      Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)] at h
    apply Module.Basis.ext_elem ((stdOrthonormalBasis ℝ E).toBasis.exteriorPower n)
    simpa using h

instance [FiniteDimensional ℝ E] : NormedAddCommGroup (⋀[ℝ]^n E) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance [FiniteDimensional ℝ E] : InnerProductSpace ℝ (⋀[ℝ]^n E) :=
  InnerProductSpace.ofCore _

/-- The inner product on `⋀[ℝ]^n E` equals the Gram determinant on decomposable elements. -/
lemma inner_ιMulti_ιMulti [FiniteDimensional ℝ E] (x y : Fin n → E) :
    ⟪ιMulti ℝ n x, ιMulti ℝ n y⟫ = det (of fun i j ↦ ⟪x j, y i⟫) :=
  innerProductForm_ιMulti_ιMulti x y

/-- The self-inner-product on `⋀[ℝ]^n E` equals `det (gram ℝ v)` on decomposable elements. -/
@[simp]
lemma inner_ιMulti_self [FiniteDimensional ℝ E] (x : Fin n → E) :
    ⟪ιMulti ℝ n x, ιMulti ℝ n x⟫ = det (gram ℝ x) :=
  innerProductForm_ιMulti_self x

end exteriorPower

section OrthonormalBasis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I] [LinearOrder I]

/-- An orthonormal basis of a finite-dimensional real inner product space `E` induces an
orthonormal basis of `⋀[ℝ]^n E`, indexed by `n`-element subsets of the index type. -/
def OrthonormalBasis.exteriorPower (b : OrthonormalBasis I ℝ E) (n : ℕ) :
    OrthonormalBasis (Set.powersetCard I n) ℝ (⋀[ℝ]^n E) :=
  (b.toBasis.exteriorPower n).toOrthonormalBasis <| by
    rw [orthonormal_iff_ite]
    intro i j
    rw [exteriorPower.coe_basis, OrthonormalBasis.coe_toBasis]
    exact exteriorPower.innerProductForm_ιMulti_family_of_orthonormal b.orthonormal i j

@[simp]
lemma OrthonormalBasis.toBasis_exteriorPower (b : OrthonormalBasis I ℝ E) (n : ℕ) :
    (b.exteriorPower n).toBasis = b.toBasis.exteriorPower n :=
  (b.toBasis.exteriorPower n).toBasis_toOrthonormalBasis _

end OrthonormalBasis
