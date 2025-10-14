/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.TensorProduct.Finite

/-!

# Inner product space structure on tensor product spaces

This file provides the inner product space structure on tensor product spaces.

We define the inner product on `E ⊗ F` by `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`, when `E` and `F` are
inner product spaces.

## Main definitions:

* `TensorProduct.instNormedAddCommGroup`: the normed additive group structure on tensor products,
where `‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`.
* `TensorProduct.instInnerProductSpace`: the inner product space structure on tensor products, where
`⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`.
* `TensorProduct.mapInclLinearIsometry`: the linear isometry version of `TensorProduct.mapIncl`.
* `TensorProduct.commLinearIsometryEquiv`: the linear isometry version of `TensorProduct.comm`.
* `TensorProduct.lidLinearIsometryEquiv`: the linear isometry version of `TensorProduct.lid`.
* `TensorProduct.assocLinearIsometryEquiv`: the linear isometry version of `TensorProduct.assoc`.
* `OrthonormalBasis.tensorProduct`: the orthonormal basis of the tensor product of two orthonormal
bases.

## TODO:

* Define the continuous linear map version of `TensorProduct.map`.
* Complete space of tensor products.
* Define the normed space without needing inner products, this should be analogous to
`Mathlib/Analysis/NormedSpace/PiTensorProduct/InjectiveSeminorm.lean`.

-/

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

open scoped TensorProduct

namespace TensorProduct

/-- Bilinear map for the inner product on tensor products. -/
private abbrev inner_ :=
  (lift <| mapBilinear 𝕜 E F 𝕜 𝕜).compr₂ (LinearMap.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)

instance instInner : Inner 𝕜 (E ⊗[𝕜] F) := ⟨fun x y => inner_ x y⟩

private lemma inner_def (x y : E ⊗[𝕜] F) : inner 𝕜 x y = inner_ x y := rfl

@[simp] theorem inner_tmul (x x' : E) (y y' : F) :
    inner 𝕜 (x ⊗ₜ[𝕜] y) (x' ⊗ₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y' := rfl

lemma inner_mapIncl_mapIncl (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) (x y : E' ⊗[𝕜] F') :
    inner 𝕜 (mapIncl E' F' x) (mapIncl E' F' y) = inner 𝕜 x y :=
  x.induction_on (by simp [inner_def]) (y.induction_on (by simp [inner_def]) (by simp)
    (by simp_all [inner_def])) (by simp_all [inner_def])

open scoped ComplexOrder
open Module

private theorem inner_definite (x : E ⊗[𝕜] F) (hx : inner 𝕜 x x = 0) : x = 0 := by
  /-
  The way we prove this is by first noting that every element of a tensor product lies
  in the tensor product of some finite submodules.
  So for `x : E ⊗ F`, there exists finite submodules `E', F'` such that `x ∈ mapIncl E' F'`.
  Let `y : E' ⊗ F'` such that `x = mapIncl E' F' y`.
  Let `e` be the orthonormal basis of `E'` and `f` be the orthonomal basis of `F'`.
  Then it is easy to see that because `⟪x, x⟫ = 0`, we get
  `(e.toBasis.tensorProduct f.toBasis).repr y (i, j) = 0` for all `i, j`. Which means `y = 0`.
  And so `x = 0`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  rw [Set.singleton_subset_iff] at hz
  rw [← hz.choose_spec, inner_mapIncl_mapIncl] at hx
  set y := hz.choose
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  rw [y.basis_sum_repr e.toBasis f.toBasis] at hx
  simp only [OrthonormalBasis.coe_toBasis, inner_def] at hx
  simp only [map_smulₛₗ, map_sum, LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply,
    ← inner_def, inner_tmul, smul_eq_mul, OrthonormalBasis.inner_eq_ite, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hx
  simp only [RCLike.mul_conj, ← Finset.sum_product', Finset.univ_product_univ, Prod.mk.eta] at hx
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by simp)] at hx
  simp only [Finset.mem_univ, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    map_eq_zero, norm_eq_zero, forall_const, Prod.forall] at hx
  have : y = 0 := by
    rw [Basis.ext_elem_iff (e.toBasis.tensorProduct f.toBasis)]
    simp only [hx, map_zero, Finsupp.coe_zero, Pi.zero_apply, implies_true]
  rw [← hz.choose_spec, (by rfl : hz.choose = y), this, map_zero]

private protected theorem re_inner_self_nonneg (x : E ⊗[𝕜] F) :
    0 ≤ RCLike.re (inner 𝕜 x x) := by
  /-
  Similarly to the above proof, for `x : E ⊗ F`, there exists finite submodules `E', F'` such that
  `x ∈ mapIncl E' F'`.
  Let `y : E' ⊗ F'` such that `x = mapIncl E' F' y`.
  Let `e` be the orthonormal basis of `E'` and `f` be the orthonomal basis of `F'`.
  Then it is easy to see that
  `⟪x, x⟫ = ∑ i j, ‖(e.toBasis.tensorProduct f.toBasis).repr y (i, j)‖ ^ 2`,
  which is clearly nonnegative.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  rw [Set.singleton_subset_iff] at hz
  rw [← hz.choose_spec, inner_mapIncl_mapIncl]
  set y := hz.choose
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  rw [y.basis_sum_repr e.toBasis f.toBasis]
  simp only [OrthonormalBasis.coe_toBasis, inner_def, map_sum, LinearMap.sum_apply, map_smulₛₗ]
  simp only [LinearMap.smul_apply, RingHom.id_apply, ← inner_def, inner_tmul, smul_eq_mul,
    OrthonormalBasis.inner_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, ← Finset.sum_product', RCLike.mul_conj]
  apply Finset.sum_nonneg
  intro i hi
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]
  exact sq_nonneg _

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (E ⊗[𝕜] F) :=
  letI : InnerProductSpace.Core 𝕜 (E ⊗[𝕜] F) :=
  { conj_inner_symm x y :=
      x.induction_on (by simp [inner]) (y.induction_on (by simp [inner]) (fun x y => by simp)
        (fun x y hx hy a b => by simp_all [inner])) (fun x y hx hy => by simp_all [inner])
    add_left _ _ _ := by simp [inner]
    smul_left _ _ _ := by simp [inner]
    definite := TensorProduct.inner_definite
    re_inner_nonneg := TensorProduct.re_inner_self_nonneg }
  this.toNormedAddCommGroup

instance instInnerProductSpace : InnerProductSpace 𝕜 (E ⊗[𝕜] F) := .ofCore _

@[simp] theorem norm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖ = ‖x‖ * ‖y‖ := by
  simp [norm_eq_sqrt_re_inner (𝕜 := 𝕜), Real.sqrt_mul inner_self_nonneg]

@[simp] theorem nnnorm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖₊ = ‖x‖₊ * ‖y‖₊ := by simp [← NNReal.coe_inj]

@[simp] theorem enorm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖ₑ = ‖x‖ₑ * ‖y‖ₑ := ENNReal.coe_inj.mpr <| by simp

theorem dist_tmul_le (x x' : E) (y y' : F) :
    dist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖ * ‖y‖ + ‖x'‖ * ‖y'‖ := by
  grw [dist_eq_norm, norm_sub_le]; simp

theorem nndist_tmul_le (x x' : E) (y y' : F) :
    nndist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖₊ * ‖y‖₊ + ‖x'‖₊ * ‖y'‖₊ := by
  grw [nndist_eq_nnnorm, nnnorm_sub_le]; simp

theorem edist_tmul_le (x x' : E) (y y' : F) :
    edist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖ₑ * ‖y‖ₑ + ‖x'‖ₑ * ‖y'‖ₑ := by
  grw [edist_eq_enorm_sub, enorm_sub_le]; simp

/-- In `ℝ` or `ℂ` fields, the inner product on tensor products is essentially just the inner product
with multiplication instead of tensors, i.e., `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a * b, c * d⟫`. -/
theorem _root_.RCLike.inner_tmul_eq (a b c d : 𝕜) :
    inner 𝕜 (a ⊗ₜ[𝕜] b) (c ⊗ₜ[𝕜] d) = inner 𝕜 (a * b) (c * d) := by
  simp; ring

/-- Given `x, y : E ⊗ F`, `x = y` iff `⟪x, a ⊗ₜ b⟫ = ⟪y, a ⊗ₜ b⟫` for all `a, b`. -/
protected theorem ext_inner_right_iff {x y : E ⊗[𝕜] F} :
    x = y ↔ ∀ a b, inner 𝕜 x (a ⊗ₜ[𝕜] b) = inner 𝕜 y (a ⊗ₜ[𝕜] b) := by
  rw [_root_.ext_inner_right_iff 𝕜]
  refine ⟨fun h a b => by rw [h], fun h v => ?_⟩
  exact v.induction_on (by simp) h (fun c d hc hd => by simp [inner_add_right, hc, hd])

/-- Given `x, y : E ⊗ F ⊗ G`, `x = y` iff `⟪x, a ⊗ₜ b ⊗ₜ c⟫ = ⟪y, a ⊗ₜ b ⊗ₜ c⟫` for all `a, b, c`.

See also `ext_inner_right_threefold_iff'` for when `x, y : E ⊗ (F ⊗ G)`. -/
theorem ext_inner_right_threefold_iff {x y : E ⊗[𝕜] F ⊗[𝕜] G} :
    x = y ↔ ∀ a b c, inner 𝕜 x (a ⊗ₜ[𝕜] b ⊗ₜ[𝕜] c) = inner 𝕜 y (a ⊗ₜ[𝕜] b ⊗ₜ[𝕜] c) := by
  simp_rw [← @sub_eq_zero 𝕜 _ _ (inner _ _ _), ← inner_sub_left]
  rw [← sub_eq_zero]
  exact ⟨fun h a b => by simp [h, inner_zero_left], fun h => TensorProduct.ext_inner_right_iff.mpr
    fun z b => z.induction_on (by simp) (by simp [h])
    fun c d hc hd => by simp [add_tmul, inner_add_right, hc, hd]⟩

section isometry

/-- The linear isometry version of `TensorProduct.mapIncl`. -/
def mapInclLinearIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    E' ⊗[𝕜] F' →ₗᵢ[𝕜] E ⊗[𝕜] F where
  toLinearMap := mapIncl E' F'
  norm_map' x := by simp_rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), inner_mapIncl_mapIncl]

@[simp] lemma mapInclLinearIsometry_apply (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
    (x : E' ⊗[𝕜] F') : mapInclLinearIsometry E' F' x = mapIncl E' F' x := rfl

@[simp] lemma toLinearMap_mapInclLinearIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    (mapInclLinearIsometry E' F').toLinearMap = mapIncl E' F' := rfl

@[simp] theorem inner_comm_comm (x y : E ⊗[𝕜] F) :
    inner 𝕜 (TensorProduct.comm 𝕜 E F x) (TensorProduct.comm 𝕜 E F y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ => y.induction_on (by simp) (by simp [mul_comm])
    (fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2]))
    (fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2])

variable (𝕜 E F) in
/-- The linear isometry equivalence version of `TensorProduct.comm`. -/
def commLinearIsometryEquiv : E ⊗[𝕜] F ≃ₗᵢ[𝕜] F ⊗[𝕜] E where
  toLinearEquiv := TensorProduct.comm 𝕜 E F
  norm_map' _ := by simp_rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), inner_comm_comm]

@[simp] lemma commLinearIsometryEquiv_apply (x : E ⊗[𝕜] F) :
    commLinearIsometryEquiv 𝕜 E F x = TensorProduct.comm 𝕜 E F x := rfl
lemma commLinearIsometryEquiv_symm :
    (commLinearIsometryEquiv 𝕜 E F).symm = commLinearIsometryEquiv 𝕜 F E := rfl

@[simp] lemma toLinearEquiv_commLinearIsometryEquiv :
    (commLinearIsometryEquiv 𝕜 E F).toLinearEquiv = TensorProduct.comm 𝕜 E F := rfl

@[simp] theorem inner_lid_lid (x y : 𝕜 ⊗[𝕜] E) :
    inner 𝕜 (TensorProduct.lid 𝕜 E x) (TensorProduct.lid 𝕜 E y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ => y.induction_on (by simp)
    (by simp [inner_smul_left, inner_smul_right, mul_assoc])
    (fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2]))
    (fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2])

variable (𝕜 E) in
/-- The linear isometry equivalence version of `TensorProduct.lid`. -/
def lidLinearIsometryEquiv : 𝕜 ⊗[𝕜] E ≃ₗᵢ[𝕜] E where
  toLinearEquiv := TensorProduct.lid 𝕜 E
  norm_map' _ := by simp_rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), inner_lid_lid]

@[simp] lemma lidLinearIsometryEquiv_apply (x : 𝕜 ⊗[𝕜] E) :
    lidLinearIsometryEquiv 𝕜 E x = TensorProduct.lid 𝕜 E x := rfl
@[simp] lemma lidLinearIsometryEquiv_symm_apply (x : E) :
    (lidLinearIsometryEquiv 𝕜 E).symm x = 1 ⊗ₜ x := rfl

@[simp] lemma toLinearEquiv_lidLinearIsometryEquiv :
    (lidLinearIsometryEquiv 𝕜 E).toLinearEquiv = TensorProduct.lid 𝕜 E := rfl

@[simp] theorem inner_assoc_assoc (x y : E ⊗[𝕜] F ⊗[𝕜] G) :
    inner 𝕜 (TensorProduct.assoc 𝕜 E F G x) (TensorProduct.assoc 𝕜 E F G y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun a b =>
    y.induction_on (by simp) (fun c d =>
      a.induction_on (by simp) (fun e f =>
        c.induction_on (by simp) (by simp [mul_assoc])
        (fun _ _ h1 h2 => by simp only [add_tmul, inner_add_right, map_add, h1, h2]))
      (fun _ _ h1 h2 => by simp only [add_tmul, inner_add_left, map_add, h1, h2]))
    (fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2]))
  (fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2])

variable (𝕜 E F G) in
/-- The linear isometry equivalence version of `TensorProduct.lid`. -/
def assocLinearIsometryEquiv : E ⊗[𝕜] F ⊗[𝕜] G ≃ₗᵢ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G) where
  toLinearEquiv := TensorProduct.assoc 𝕜 E F G
  norm_map' _ := by simp_rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), inner_assoc_assoc]

@[simp] lemma assocLinearIsometryEquiv_apply (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    assocLinearIsometryEquiv 𝕜 E F G x = TensorProduct.assoc 𝕜 E F G x := rfl
@[simp] lemma assocLinearIsometryEquiv_symm_apply (x : E ⊗[𝕜] (F ⊗[𝕜] G)) :
    (assocLinearIsometryEquiv 𝕜 E F G).symm x = (TensorProduct.assoc 𝕜 E F G).symm x := rfl

@[simp] lemma toLinearEquiv_assocLinearIsometryEquiv :
    (assocLinearIsometryEquiv 𝕜 E F G).toLinearEquiv = TensorProduct.assoc 𝕜 E F G := rfl

end isometry

-- TODO: upgrade `map` to a `ContinuousLinearMap`
@[simp] theorem adjoint_map {A : Type*} [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
    [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (f : A →ₗ[𝕜] G) (g : E →ₗ[𝕜] F) :
    LinearMap.adjoint (map f g) = map (LinearMap.adjoint f) (LinearMap.adjoint g) :=
  ext' fun x y => by simp [TensorProduct.ext_inner_right_iff, LinearMap.adjoint_inner_left]

/-- Given `x, y : E ⊗ (F ⊗ G)`, `x = y` iff `⟪x, a ⊗ₜ (b ⊗ₜ c)⟫ = ⟪y, a ⊗ₜ (b ⊗ₜ c)⟫` for all
`a, b, c`.

See also `ext_inner_right_threefold_iff` for when `x, y : E ⊗ F ⊗ G`. -/
theorem ext_inner_right_threefold_iff' {x y : E ⊗[𝕜] (F ⊗[𝕜] G)} :
    x = y ↔ ∀ a b c, inner 𝕜 x (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) = inner 𝕜 y (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) := by
  simp only [← (assocLinearIsometryEquiv 𝕜 E F G).symm.injective.eq_iff,
    ext_inner_right_threefold_iff, LinearIsometryEquiv.inner_map_eq_flip]
  simp

end TensorProduct

section onb
variable {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]

open Module

/-- The tensor product of two orthonormal vectors is orthonormal. -/
theorem Orthonormal.tensorProduct
    {b₁ : ι₁ → E} {b₂ : ι₂ → F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 fun i : ι₁ × ι₂ ↦ b₁ i.1 ⊗ₜ[𝕜] b₂ i.2 :=
  orthonormal_iff_ite.mpr fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    simp [orthonormal_iff_ite.mp, hb₁, hb₂, ← ite_and, and_comm]

/-- The tensor product of two orthonormal bases is orthonormal. -/
theorem Orthonormal.basisTensorProduct
    {b₁ : Basis ι₁ 𝕜 E} {b₂ : Basis ι₂ 𝕜 F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 (b₁.tensorProduct b₂) := b₁.coe_tensorProduct b₂ ▸ hb₁.tensorProduct hb₂

namespace OrthonormalBasis
variable [Fintype ι₁] [Fintype ι₂]

/-- The orthonormal basis of the tensor product of two orthonormal bases. -/
protected noncomputable def tensorProduct
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    OrthonormalBasis (ι₁ × ι₂) 𝕜 (E ⊗[𝕜] F) :=
  (b₁.toBasis.tensorProduct b₂.toBasis).toOrthonormalBasis
    (b₁.orthonormal.basisTensorProduct b₂.orthonormal)

@[simp]
lemma tensorProduct_apply
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁) (j : ι₂) :
    b₁.tensorProduct b₂ (i, j) = b₁ i ⊗ₜ[𝕜] b₂ j := by simp [OrthonormalBasis.tensorProduct]

lemma tensorProduct_apply'
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁ × ι₂) :
    b₁.tensorProduct b₂ i = b₁ i.1 ⊗ₜ[𝕜] b₂ i.2 := tensorProduct_apply _ _ _ _

@[simp]
lemma tensorProduct_repr_tmul_apply (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
    (x : E) (y : F) (i : ι₁) (j : ι₂) :
    (b₁.tensorProduct b₂).repr (x ⊗ₜ[𝕜] y) (i, j) = b₂.repr y j * b₁.repr x i := by
  simp [OrthonormalBasis.tensorProduct]

lemma tensorProduct_repr_tmul_apply'
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (x : E) (y : F) (i : ι₁ × ι₂) :
    (b₁.tensorProduct b₂).repr (x ⊗ₜ[𝕜] y) i = b₂.repr y i.2 * b₁.repr x i.1 :=
  tensorProduct_repr_tmul_apply _ _ _ _ _ _

@[simp]
lemma toBasis_tensorProduct (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    (b₁.tensorProduct b₂).toBasis = b₁.toBasis.tensorProduct b₂.toBasis := by
  simp [OrthonormalBasis.tensorProduct]

@[simp]
lemma coe_tensorProduct (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    ⇑(b₁.tensorProduct b₂) = fun i : ι₁ × ι₂ ↦ b₁ i.1 ⊗ₜ b₂ i.2 := by
  ext; rw [tensorProduct_apply']

end OrthonormalBasis
end onb
