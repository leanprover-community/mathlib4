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
* `TensorProduct.mapIsometry`: the linear isometry version of `TensorProduct.map f g` when
  `f` and `g` are linear isometries.
* `TensorProduct.congrIsometry`: the linear isometry equivalence version of
  `TensorProduct.congr f g` when `f` and `g` are linear isometry equivalences.
* `TensorProduct.mapInclIsometry`: the linear isometry version of `TensorProduct.mapIncl`.
* `TensorProduct.commIsometry`: the linear isometry version of `TensorProduct.comm`.
* `TensorProduct.lidIsometry`: the linear isometry version of `TensorProduct.lid`.
* `TensorProduct.assocIsometry`: the linear isometry version of `TensorProduct.assoc`.
* `OrthonormalBasis.tensorProduct`: the orthonormal basis of the tensor product of two orthonormal
  bases.

## TODO:

* Define the continuous linear map version of `TensorProduct.map`.
* Complete space of tensor products.
* Define the normed space without needing inner products, this should be analogous to
  `Mathlib/Analysis/NormedSpace/PiTensorProduct/InjectiveSeminorm.lean`.

-/

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open scoped TensorProduct

namespace TensorProduct

/-- Bilinear map for the inner product on tensor products.
On pure tensors: `inner_ (a ⊗ₜ b) (c ⊗ₜ d) = ⟪a, c⟫ * ⟪b, d⟫`. -/
private abbrev inner_ : E ⊗[𝕜] F →ₗ⋆[𝕜] E ⊗[𝕜] F →ₗ[𝕜] 𝕜 :=
  (lift <| mapBilinear 𝕜 E F 𝕜 𝕜).compr₂ (LinearMap.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)

instance instInner : Inner 𝕜 (E ⊗[𝕜] F) := ⟨fun x y => inner_ x y⟩

private lemma inner_def (x y : E ⊗[𝕜] F) : inner 𝕜 x y = inner_ x y := rfl

@[simp] theorem inner_tmul (x x' : E) (y y' : F) :
    inner 𝕜 (x ⊗ₜ[𝕜] y) (x' ⊗ₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y' := rfl

@[simp] lemma inner_map_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x y : E ⊗[𝕜] F) :
    inner 𝕜 (map f.toLinearMap g.toLinearMap x) (map f.toLinearMap g.toLinearMap y) = inner 𝕜 x y :=
  x.induction_on (by simp [inner_def]) (y.induction_on (by simp [inner_def]) (by simp)
    (by simp_all [inner_def])) (by simp_all [inner_def])

lemma inner_mapIncl_mapIncl (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) (x y : E' ⊗[𝕜] F') :
    inner 𝕜 (mapIncl E' F' x) (mapIncl E' F' y) = inner 𝕜 x y :=
  inner_map_map E'.subtypeₗᵢ F'.subtypeₗᵢ x y

open scoped ComplexOrder
open Module

private theorem inner_definite (x : E ⊗[𝕜] F) (hx : inner 𝕜 x x = 0) : x = 0 := by
  /-
  The way we prove this is by first noting that every element of a tensor product lies
  in the tensor product of some finite submodules.
  So for `x : E ⊗ F`, there exists finite submodules `E', F'` such that `x ∈ mapIncl E' F'`.
  Let `y : E' ⊗ F'` such that `x = mapIncl E' F' y`.
  Let `e` be an orthonormal basis of `E'` and `f` be an orthonormal basis of `F'`.
  Then it is easy to see that because `⟪x, x⟫ = 0`, we get
  `(e.toBasis.tensorProduct f.toBasis).repr y (i, j) = 0` for all `i, j`. Which means `y = 0`.
  And so `x = 0`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hz
  rw [inner_mapIncl_mapIncl] at hx
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
  rw [this, map_zero]

private protected theorem re_inner_self_nonneg (x : E ⊗[𝕜] F) :
    0 ≤ RCLike.re (inner 𝕜 x x) := by
  /-
  Similarly to the above proof, for `x : E ⊗ F`, there exists finite submodules `E', F'` such that
  `x ∈ mapIncl E' F'`.
  Let `y : E' ⊗ F'` such that `x = mapIncl E' F' y`.
  Let `e` be an orthonormal basis of `E'` and `f` be an orthonormal basis of `F'`.
  Then it is easy to see that
  `⟪x, x⟫ = ∑ i j, ‖(e.toBasis.tensorProduct f.toBasis).repr y (i, j)‖ ^ 2`,
  which is clearly nonnegative.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hz
  rw [inner_mapIncl_mapIncl]
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
protected theorem ext_iff_inner_right {x y : E ⊗[𝕜] F} :
    x = y ↔ ∀ a b, inner 𝕜 x (a ⊗ₜ[𝕜] b) = inner 𝕜 y (a ⊗ₜ[𝕜] b) := by
  rw [← innerSL_inj (𝕜 := 𝕜), ← ContinuousLinearMap.coe_inj, TensorProduct.ext_iff]
  simp [LinearMap.ext_iff]

/-- Given `x, y : E ⊗ F`, `x = y` iff `⟪a ⊗ₜ b, x⟫ = ⟪a ⊗ₜ b, y⟫` for all `a, b`. -/
protected theorem ext_iff_inner_left {x y : E ⊗[𝕜] F} :
    x = y ↔ ∀ a b, inner 𝕜 (a ⊗ₜ b) x = inner 𝕜 (a ⊗ₜ b) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    TensorProduct.ext_iff_inner_right (x := x) (y := y)

/-- Given `x, y : E ⊗ F ⊗ G`, `x = y` iff `⟪x, a ⊗ₜ b ⊗ₜ c⟫ = ⟪y, a ⊗ₜ b ⊗ₜ c⟫` for all `a, b, c`.

See also `ext_iff_inner_right_threefold'` for when `x, y : E ⊗ (F ⊗ G)`. -/
theorem ext_iff_inner_right_threefold {x y : E ⊗[𝕜] F ⊗[𝕜] G} :
    x = y ↔ ∀ a b c, inner 𝕜 x (a ⊗ₜ[𝕜] b ⊗ₜ[𝕜] c) = inner 𝕜 y (a ⊗ₜ[𝕜] b ⊗ₜ[𝕜] c) :=
  ⟨fun h _ _ _ ↦ h ▸ rfl, fun h ↦ innerSL_inj.mp (ContinuousLinearMap.coe_inj.mp (ext_threefold h))⟩

/-- Given `x, y : E ⊗ F ⊗ G`, `x = y` iff `⟪a ⊗ₜ b ⊗ₜ c, x⟫ = ⟪a ⊗ₜ b ⊗ₜ c, y⟫` for all `a, b, c`.

See also `ext_iff_inner_left_threefold'` for when `x, y : E ⊗ (F ⊗ G)`. -/
theorem ext_iff_inner_left_threefold {x y : E ⊗[𝕜] F ⊗[𝕜] G} :
    x = y ↔ ∀ a b c, inner 𝕜 (a ⊗ₜ b ⊗ₜ c) x = inner 𝕜 (a ⊗ₜ b ⊗ₜ c) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold (x := x) (y := y)

section isometry

/-- The tensor product map of two linear isometries is a linear isometry. In particular, this is
the linear isometry version of `TensorProduct.map f g` when `f` and `g` are linear isometries. -/
def mapIsometry (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) :
    E ⊗[𝕜] F →ₗᵢ[𝕜] G ⊗[𝕜] H :=
  map f.toLinearMap g.toLinearMap |>.isometryOfInner <| inner_map_map _ _

@[simp] lemma mapIsometry_apply (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    mapIsometry f g x = map f.toLinearMap g.toLinearMap x := rfl

@[simp] lemma toLinearMap_mapIsometry (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) :
    (mapIsometry f g).toLinearMap = map f.toLinearMap g.toLinearMap := rfl

@[simp] lemma norm_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    ‖map f.toLinearMap g.toLinearMap x‖ = ‖x‖ := mapIsometry f g |>.norm_map x
@[simp] lemma nnnorm_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    ‖map f.toLinearMap g.toLinearMap x‖₊ = ‖x‖₊ := mapIsometry f g |>.nnnorm_map x
@[simp] lemma enorm_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    ‖map f.toLinearMap g.toLinearMap x‖ₑ = ‖x‖ₑ := mapIsometry f g |>.enorm_map x

/-- The tensor product of two linear isometry equivalences is a linear isometry equivalence.
In particular, this is the linear isometry equivalence version of `TensorProduct.congr f g` when `f`
and `g` are linear isometry equivalences. -/
def congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    E ⊗[𝕜] F ≃ₗᵢ[𝕜] G ⊗[𝕜] H :=
  congr f.toLinearEquiv g.toLinearEquiv |>.isometryOfInner <|
    inner_map_map f.toLinearIsometry g.toLinearIsometry

@[simp] lemma congrIsometry_apply (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    congrIsometry f g x = congr f g x := rfl

lemma congrIsometry_symm (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometry f g).symm = congrIsometry f.symm g.symm := rfl

@[simp] lemma toLinearEquiv_congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometry f g).toLinearEquiv = congr f.toLinearEquiv g.toLinearEquiv := rfl

/-- The linear isometry version of `TensorProduct.mapIncl`. -/
def mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    E' ⊗[𝕜] F' →ₗᵢ[𝕜] E ⊗[𝕜] F :=
  mapIsometry E'.subtypeₗᵢ F'.subtypeₗᵢ

@[simp] lemma mapInclIsometry_apply (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
    (x : E' ⊗[𝕜] F') : mapInclIsometry E' F' x = mapIncl E' F' x := rfl

@[simp] lemma toLinearMap_mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    (mapInclIsometry E' F').toLinearMap = mapIncl E' F' := rfl

@[simp] theorem inner_comm_comm (x y : E ⊗[𝕜] F) :
    inner 𝕜 (TensorProduct.comm 𝕜 E F x) (TensorProduct.comm 𝕜 E F y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ => y.induction_on (by simp) (by simp [mul_comm])
    (fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2]))
    (fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2])

variable (𝕜 E F) in
/-- The linear isometry equivalence version of `TensorProduct.comm`. -/
def commIsometry : E ⊗[𝕜] F ≃ₗᵢ[𝕜] F ⊗[𝕜] E :=
  TensorProduct.comm 𝕜 E F |>.isometryOfInner inner_comm_comm

@[simp] lemma commIsometry_apply (x : E ⊗[𝕜] F) :
    commIsometry 𝕜 E F x = TensorProduct.comm 𝕜 E F x := rfl
lemma commIsometry_symm :
    (commIsometry 𝕜 E F).symm = commIsometry 𝕜 F E := rfl

@[simp] lemma toLinearEquiv_commIsometry :
    (commIsometry 𝕜 E F).toLinearEquiv = TensorProduct.comm 𝕜 E F := rfl

@[simp] lemma norm_comm (x : E ⊗[𝕜] F) :
    ‖TensorProduct.comm 𝕜 E F x‖ = ‖x‖ := commIsometry 𝕜 E F |>.norm_map x
@[simp] lemma nnnorm_comm (x : E ⊗[𝕜] F) :
    ‖TensorProduct.comm 𝕜 E F x‖₊ = ‖x‖₊ := commIsometry 𝕜 E F |>.nnnorm_map x
@[simp] lemma enorm_comm (x : E ⊗[𝕜] F) :
    ‖TensorProduct.comm 𝕜 E F x‖ₑ = ‖x‖ₑ := commIsometry 𝕜 E F |>.toLinearIsometry.enorm_map x

@[simp] theorem inner_lid_lid (x y : 𝕜 ⊗[𝕜] E) :
    inner 𝕜 (TensorProduct.lid 𝕜 E x) (TensorProduct.lid 𝕜 E y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ => y.induction_on (by simp)
    (by simp [inner_smul_left, inner_smul_right, mul_assoc])
    (fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2]))
    (fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2])

variable (𝕜 E) in
/-- The linear isometry equivalence version of `TensorProduct.lid`. -/
def lidIsometry : 𝕜 ⊗[𝕜] E ≃ₗᵢ[𝕜] E :=
  TensorProduct.lid 𝕜 E |>.isometryOfInner inner_lid_lid

@[simp] lemma lidIsometry_apply (x : 𝕜 ⊗[𝕜] E) :
    lidIsometry 𝕜 E x = TensorProduct.lid 𝕜 E x := rfl
@[simp] lemma lidIsometry_symm_apply (x : E) :
    (lidIsometry 𝕜 E).symm x = 1 ⊗ₜ x := rfl

@[simp] lemma toLinearEquiv_lidIsometry :
    (lidIsometry 𝕜 E).toLinearEquiv = TensorProduct.lid 𝕜 E := rfl

@[simp] lemma norm_lid (x : 𝕜 ⊗[𝕜] E) :
    ‖TensorProduct.lid 𝕜 E x‖ = ‖x‖ := lidIsometry 𝕜 E |>.norm_map x
@[simp] lemma nnnorm_lid (x : 𝕜 ⊗[𝕜] E) :
    ‖TensorProduct.lid 𝕜 E x‖₊ = ‖x‖₊ := lidIsometry 𝕜 E |>.nnnorm_map x
@[simp] lemma enorm_lid (x : 𝕜 ⊗[𝕜] E) :
    ‖TensorProduct.lid 𝕜 E x‖ₑ = ‖x‖ₑ := lidIsometry 𝕜 E |>.toLinearIsometry.enorm_map x

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
/-- The linear isometry equivalence version of `TensorProduct.assoc`. -/
def assocIsometry : E ⊗[𝕜] F ⊗[𝕜] G ≃ₗᵢ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G) :=
  TensorProduct.assoc 𝕜 E F G |>.isometryOfInner inner_assoc_assoc

@[simp] lemma assocIsometry_apply (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    assocIsometry 𝕜 E F G x = TensorProduct.assoc 𝕜 E F G x := rfl
@[simp] lemma assocIsometry_symm_apply (x : E ⊗[𝕜] (F ⊗[𝕜] G)) :
    (assocIsometry 𝕜 E F G).symm x = (TensorProduct.assoc 𝕜 E F G).symm x := rfl

@[simp] lemma toLinearEquiv_assocIsometry :
    (assocIsometry 𝕜 E F G).toLinearEquiv = TensorProduct.assoc 𝕜 E F G := rfl

@[simp] lemma norm_assoc (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    ‖TensorProduct.assoc 𝕜 E F G x‖ = ‖x‖ := assocIsometry 𝕜 E F G |>.norm_map x
@[simp] lemma nnnorm_assoc (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    ‖TensorProduct.assoc 𝕜 E F G x‖₊ = ‖x‖₊ := assocIsometry 𝕜 E F G |>.nnnorm_map x
@[simp] lemma enorm_assoc (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    ‖TensorProduct.assoc 𝕜 E F G x‖ₑ = ‖x‖ₑ := assocIsometry 𝕜 E F G |>.toLinearIsometry.enorm_map x

end isometry

-- TODO: upgrade `map` to a `ContinuousLinearMap`
@[simp] theorem adjoint_map [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →ₗ[𝕜] F) (g : G →ₗ[𝕜] H) :
    LinearMap.adjoint (map f g) = map (LinearMap.adjoint f) (LinearMap.adjoint g) :=
  ext' fun x y => by simp [TensorProduct.ext_iff_inner_right, LinearMap.adjoint_inner_left]

/-- Given `x, y : E ⊗ (F ⊗ G)`, `x = y` iff `⟪x, a ⊗ₜ (b ⊗ₜ c)⟫ = ⟪y, a ⊗ₜ (b ⊗ₜ c)⟫` for all
`a, b, c`.

See also `ext_iff_inner_right_threefold` for when `x, y : E ⊗ F ⊗ G`. -/
theorem ext_iff_inner_right_threefold' {x y : E ⊗[𝕜] (F ⊗[𝕜] G)} :
    x = y ↔ ∀ a b c, inner 𝕜 x (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) = inner 𝕜 y (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) := by
  simp only [← (assocIsometry 𝕜 E F G).symm.injective.eq_iff,
    ext_iff_inner_right_threefold, LinearIsometryEquiv.inner_map_eq_flip]
  simp

/-- Given `x, y : E ⊗ (F ⊗ G)`, `x = y` iff `⟪a ⊗ₜ (b ⊗ₜ c), x⟫ = ⟪a ⊗ₜ (b ⊗ₜ c), y⟫` for all
`a, b, c`.

See also `ext_iff_inner_left_threefold` for when `x, y : E ⊗ F ⊗ G`. -/
theorem ext_iff_inner_left_threefold' {x y : E ⊗[𝕜] (F ⊗[𝕜] G)} :
    x = y ↔ ∀ a b c, inner 𝕜 (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) x = inner 𝕜 (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold' (x := x) (y := y)

end TensorProduct

section orthonormal
variable {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]

open Module

/-- The tensor product of two orthonormal vectors is orthonormal. -/
theorem Orthonormal.tmul
    {b₁ : ι₁ → E} {b₂ : ι₂ → F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 fun i : ι₁ × ι₂ ↦ b₁ i.1 ⊗ₜ[𝕜] b₂ i.2 :=
  orthonormal_iff_ite.mpr fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    simp [orthonormal_iff_ite.mp, hb₁, hb₂, ← ite_and, and_comm]

/-- The tensor product of two orthonormal bases is orthonormal. -/
theorem Orthonormal.basisTensorProduct
    {b₁ : Basis ι₁ 𝕜 E} {b₂ : Basis ι₂ 𝕜 F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 (b₁.tensorProduct b₂) := b₁.coe_tensorProduct b₂ ▸ hb₁.tmul hb₂

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

lemma coe_tensorProduct (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    ⇑(b₁.tensorProduct b₂) = fun i : ι₁ × ι₂ ↦ b₁ i.1 ⊗ₜ b₂ i.2 := by
  ext; rw [tensorProduct_apply']

end OrthonormalBasis
end orthonormal
