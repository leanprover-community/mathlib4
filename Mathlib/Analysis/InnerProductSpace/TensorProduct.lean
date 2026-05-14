/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

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

@[expose] public section

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open scoped TensorProduct

namespace TensorProduct

set_option backward.privateInPublic true in
/-- Bilinear map for the inner product on tensor products.
On pure tensors: `inner_ (a ⊗ₜ b) (c ⊗ₜ d) = ⟪a, c⟫ * ⟪b, d⟫`. -/
private abbrev inner_ : E ⊗[𝕜] F →ₗ⋆[𝕜] E ⊗[𝕜] F →ₗ[𝕜] 𝕜 :=
  (lift <| mapBilinear (.id 𝕜) E F 𝕜 𝕜).compr₂ (LinearMap.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance instInner : Inner 𝕜 (E ⊗[𝕜] F) := ⟨fun x y => inner_ x y⟩

private lemma inner_def (x y : E ⊗[𝕜] F) : inner 𝕜 x y = inner_ x y := rfl

variable (𝕜) in
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

/- This holds in any inner product space, but we need this to set up the instance.
This is a helper lemma for showing that this inner product is positive definite. -/
private theorem inner_self {ι ι' : Type*} [Fintype ι] [Fintype ι'] (x : E ⊗[𝕜] F)
    (e : OrthonormalBasis ι 𝕜 E) (f : OrthonormalBasis ι' 𝕜 F) :
    inner 𝕜 x x = ∑ i, ‖(e.toBasis.tensorProduct f.toBasis).repr x i‖ ^ 2 := by
  classical
  have : x = ∑ i : ι, ∑ j : ι', (e.toBasis.tensorProduct f.toBasis).repr x (i, j) • e i ⊗ₜ f j := by
    conv_lhs => rw [← (e.toBasis.tensorProduct f.toBasis).sum_repr x]
    simp [← Finset.sum_product', Basis.tensorProduct_apply']
  conv_lhs => rw [this]
  simp only [inner_def, map_sum, LinearMap.sum_apply]
  simp [OrthonormalBasis.inner_eq_ite, ← Finset.sum_product', RCLike.mul_conj]

set_option backward.privateInPublic true in
private theorem inner_definite (x : E ⊗[𝕜] F) (hx : inner 𝕜 x x = 0) : x = 0 := by
  /-
  The way we prove this is by noting that every element of a tensor product lies
  in the tensor product of some finite submodules.
  So for `x : E ⊗ F`, there exists finite submodules `E', F'` such that `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl_mapIncl` and `inner_self`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y : E' ⊗ F', rfl : mapIncl E' F' y = x⟩ := Set.singleton_subset_iff.mp hz
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  have (i) (j) : (e.toBasis.tensorProduct f.toBasis).repr y (i, j) = 0 := by
    rw [inner_mapIncl_mapIncl, inner_self y e f, RCLike.ofReal_eq_zero,
      Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at hx
    simpa using hx (i, j)
  have : y = 0 := by simp [(e.toBasis.tensorProduct f.toBasis).ext_elem_iff, this]
  rw [this, map_zero]

set_option backward.privateInPublic true in
private protected theorem re_inner_self_nonneg (x : E ⊗[𝕜] F) :
    0 ≤ RCLike.re (inner 𝕜 x x) := by
  /-
  Similarly to the above proof, for `x : E ⊗ F`, there exists finite submodules `E', F'` such that
  `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl_mapIncl` and `inner_self`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hz
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  rw [inner_mapIncl_mapIncl, inner_self y e f, RCLike.ofReal_re]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (E ⊗[𝕜] F) :=
  letI : InnerProductSpace.Core 𝕜 (E ⊗[𝕜] F) :=
  { conj_inner_symm x y :=
      x.induction_on (by simp [inner]) (y.induction_on (by simp [inner]) (by simp)
        (by simp_all [inner])) (by simp_all [inner])
    add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
    smul_left _ _ _ := LinearMap.map_smulₛₗ₂ _ _ _ _
    definite := TensorProduct.inner_definite
    re_inner_nonneg := TensorProduct.re_inner_self_nonneg }
  this.toNormedAddCommGroup

instance instInnerProductSpace : InnerProductSpace 𝕜 (E ⊗[𝕜] F) := .ofCore _

@[simp] theorem norm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖ = ‖x‖ * ‖y‖ := by
  simpa using congr(√(RCLike.re $(inner_tmul 𝕜 x x y y)))

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
    x = y ↔ ∀ a b, inner 𝕜 x (a ⊗ₜ[𝕜] b) = inner 𝕜 y (a ⊗ₜ[𝕜] b) :=
  ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ innerSL_inj.mp <| ContinuousLinearMap.coe_inj.mp <| ext' h⟩

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
noncomputable def mapIsometry (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) :
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

@[simp] lemma mapIsometry_id_id :
    mapIsometry (.id : E →ₗᵢ[𝕜] E) (.id : F →ₗᵢ[𝕜] F) = .id := by ext; simp

variable (E) in
/-- This is the natural linear isometry induced by `f : F ≃ₗᵢ G`. -/
noncomputable def _root_.LinearIsometry.lTensor (f : F →ₗᵢ[𝕜] G) :
    E ⊗[𝕜] F →ₗᵢ[𝕜] E ⊗[𝕜] G := mapIsometry .id f

variable (G) in
/-- This is the natural linear isometry induced by `f : E ≃ₗᵢ F`. -/
noncomputable def _root_.LinearIsometry.rTensor (f : E →ₗᵢ[𝕜] F) :
    E ⊗[𝕜] G →ₗᵢ[𝕜] F ⊗[𝕜] G := mapIsometry f .id

lemma _root_.LinearIsometry.lTensor_def (f : F →ₗᵢ[𝕜] G) :
    f.lTensor E = mapIsometry .id f := rfl

lemma _root_.LinearIsometry.rTensor_def (f : E →ₗᵢ[𝕜] F) :
    f.rTensor G = mapIsometry f .id := rfl

@[simp] lemma _root_.LinearIsometry.toLinearMap_lTensor (f : F →ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearMap = f.toLinearMap.lTensor E := rfl

@[simp] lemma _root_.LinearIsometry.toLinearMap_rTensor (f : E →ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearMap = f.toLinearMap.rTensor G := rfl

@[simp] lemma _root_.LinearIsometry.lTensor_apply (f : F →ₗᵢ[𝕜] G) (x : E ⊗[𝕜] F) :
    f.lTensor E x = f.toLinearMap.lTensor E x := rfl

@[simp] lemma _root_.LinearIsometry.rTensor_apply (f : E →ₗᵢ[𝕜] F) (x : E ⊗[𝕜] G) :
    f.rTensor G x = f.toLinearMap.rTensor G x := rfl

/-- The tensor product of two linear isometry equivalences is a linear isometry equivalence.
In particular, this is the linear isometry equivalence version of `TensorProduct.congr f g` when `f`
and `g` are linear isometry equivalences. -/
noncomputable def congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    E ⊗[𝕜] F ≃ₗᵢ[𝕜] G ⊗[𝕜] H :=
  congr f.toLinearEquiv g.toLinearEquiv |>.isometryOfInner <|
    inner_map_map f.toLinearIsometry g.toLinearIsometry

@[simp] lemma congrIsometry_apply (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    congrIsometry f g x = congr (σ₁₂ := .id _) f g x := rfl

lemma congrIsometry_symm (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometry f g).symm = congrIsometry f.symm g.symm := rfl

@[simp] lemma toLinearEquiv_congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometry f g).toLinearEquiv = congr f.toLinearEquiv g.toLinearEquiv := rfl

@[simp] lemma congrIsometry_refl_refl :
    congrIsometry (.refl 𝕜 E) (.refl 𝕜 F) = .refl 𝕜 (E ⊗ F) :=
  LinearIsometryEquiv.toLinearEquiv_inj.mp <| LinearEquiv.toLinearMap_inj.mp <| by ext; simp

variable (E) in
/-- This is the natural linear isometric equivalence induced by `f : F ≃ₗᵢ G`. -/
noncomputable def _root_.LinearIsometryEquiv.lTensor (f : F ≃ₗᵢ[𝕜] G) :
    E ⊗[𝕜] F ≃ₗᵢ[𝕜] E ⊗[𝕜] G := congrIsometry (.refl 𝕜 E) f

variable (G) in
/-- This is the natural linear isometric equivalence induced by `f : E ≃ₗᵢ F`. -/
noncomputable def _root_.LinearIsometryEquiv.rTensor (f : E ≃ₗᵢ[𝕜] F) :
    E ⊗[𝕜] G ≃ₗᵢ[𝕜] F ⊗[𝕜] G := congrIsometry f (.refl 𝕜 G)

lemma _root_.LinearIsometryEquiv.lTensor_def (f : F ≃ₗᵢ[𝕜] G) :
    f.lTensor E = congrIsometry (.refl 𝕜 E) f := rfl

lemma _root_.LinearIsometryEquiv.rTensor_def (f : E ≃ₗᵢ[𝕜] F) :
    f.rTensor G = congrIsometry f (.refl 𝕜 G) := rfl

lemma _root_.LinearIsometryEquiv.symm_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).symm = f.symm.lTensor E := rfl

lemma _root_.LinearIsometryEquiv.symm_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).symm = f.symm.rTensor G := rfl

@[simp] lemma _root_.LinearIsometryEquiv.toLinearEquiv_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearEquiv = f.toLinearEquiv.lTensor E := rfl

@[simp] lemma _root_.LinearIsometryEquiv.toLinearIsometry_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearIsometry = f.toLinearIsometry.lTensor E := rfl

@[simp] lemma _root_.LinearIsometryEquiv.toLinearEquiv_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearEquiv = f.toLinearEquiv.rTensor G := rfl

@[simp] lemma _root_.LinearIsometryEquiv.toLinearIsometry_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearIsometry = f.toLinearIsometry.rTensor G := rfl

@[simp] lemma _root_.LinearIsometryEquiv.lTensor_apply (f : F ≃ₗᵢ[𝕜] G) (x : E ⊗[𝕜] F) :
    f.lTensor E x = f.toLinearEquiv.lTensor E x := rfl

@[simp] lemma _root_.LinearIsometryEquiv.rTensor_apply (f : E ≃ₗᵢ[𝕜] F) (x : E ⊗[𝕜] G) :
    f.rTensor G x = f.toLinearEquiv.rTensor G x := rfl

/-- The linear isometry version of `TensorProduct.mapIncl`. -/
noncomputable def mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    E' ⊗[𝕜] F' →ₗᵢ[𝕜] E ⊗[𝕜] F :=
  mapIsometry E'.subtypeₗᵢ F'.subtypeₗᵢ

@[simp] lemma mapInclIsometry_apply (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
    (x : E' ⊗[𝕜] F') : mapInclIsometry E' F' x = mapIncl E' F' x := rfl

@[simp] lemma toLinearMap_mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    (mapInclIsometry E' F').toLinearMap = mapIncl E' F' := rfl

@[simp] theorem inner_comm_comm (x y : E ⊗[𝕜] F) :
    inner 𝕜 (TensorProduct.comm 𝕜 E F x) (TensorProduct.comm 𝕜 E F y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [mul_comm])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E F) in
/-- The linear isometry equivalence version of `TensorProduct.comm`. -/
noncomputable def commIsometry : E ⊗[𝕜] F ≃ₗᵢ[𝕜] F ⊗[𝕜] E :=
  TensorProduct.comm 𝕜 E F |>.isometryOfInner inner_comm_comm

@[simp] lemma commIsometry_apply (x : E ⊗[𝕜] F) :
    commIsometry 𝕜 E F x = TensorProduct.comm 𝕜 E F x := rfl
@[simp] lemma commIsometry_symm :
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
  x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [inner_smul_left, inner_smul_right, mul_assoc])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E) in
/-- The linear isometry equivalence version of `TensorProduct.lid`. -/
noncomputable def lidIsometry : 𝕜 ⊗[𝕜] E ≃ₗᵢ[𝕜] E :=
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
  x.induction_on (by simp) (fun a _ =>
    y.induction_on (by simp) (fun c _ =>
      a.induction_on (by simp) (fun _ _ =>
        c.induction_on (by simp) (by simp [mul_assoc])
        fun _ _ h1 h2 => by simp only [add_tmul, inner_add_right, map_add, h1, h2])
      fun _ _ h1 h2 => by simp only [add_tmul, inner_add_left, map_add, h1, h2])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E F G) in
/-- The linear isometry equivalence version of `TensorProduct.assoc`. -/
noncomputable def assocIsometry : E ⊗[𝕜] F ⊗[𝕜] G ≃ₗᵢ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G) :=
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
  ext' fun _ _ => by simp [TensorProduct.ext_iff_inner_right, LinearMap.adjoint_inner_left]

open LinearMap

@[simp] theorem _root_.LinearMap.adjoint_rTensor [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] (f : E →ₗ[𝕜] F) :
    adjoint (rTensor G f) = rTensor G f.adjoint := by simp [rTensor]

@[simp] theorem _root_.LinearMap.adjoint_lTensor [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] (f : E →ₗ[𝕜] F) :
    adjoint (lTensor G f) = lTensor G f.adjoint := by simp [lTensor]

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
variable {ι₁ ι₂ : Type*}

open Module

/-- The tensor product of two orthonormal vectors is orthonormal. -/
theorem Orthonormal.tmul
    {b₁ : ι₁ → E} {b₂ : ι₂ → F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 fun i : ι₁ × ι₂ ↦ b₁ i.1 ⊗ₜ[𝕜] b₂ i.2 := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [orthonormal_iff_ite.mp, hb₁, hb₂, ← ite_and, and_comm]

/-- The tensor product of two orthonormal bases is orthonormal. -/
theorem Orthonormal.basisTensorProduct
    {b₁ : Basis ι₁ 𝕜 E} {b₂ : Basis ι₂ 𝕜 F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 (b₁.tensorProduct b₂) := by
  convert hb₁.tmul hb₂
  exact b₁.tensorProduct_apply' b₂ _

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

end OrthonormalBasis
end orthonormal
