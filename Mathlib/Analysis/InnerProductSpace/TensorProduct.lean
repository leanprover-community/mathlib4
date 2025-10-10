/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!

# Inner product space structure on tensor product spaces

This file provides an inner product space structure on tensor product spaces.

-/

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

open scoped TensorProduct

namespace TensorProduct

instance instInner : Inner 𝕜 (E ⊗[𝕜] F) := ⟨fun x y =>
  ((lift (mapBilinear 𝕜 E F 𝕜 𝕜)).compr₂ (LinearMap.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x y⟩

@[simp]
theorem inner_tmul (x x' : E) (y y' : F) :
    inner 𝕜 (x ⊗ₜ[𝕜] y) (x' ⊗ₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y' := rfl

section move

lemma mem_finiteDimensional_range_mapIncl {K V V' : Type*} [Field K] [AddCommGroup V]
    [AddCommGroup V'] [Module K V] [Module K V'] (z : V ⊗[K] V') :
    ∃ (E' : Submodule K V) (F' : Submodule K V')
    (_ : FiniteDimensional K E') (_ : FiniteDimensional K F'),
    z ∈ LinearMap.range (mapIncl E' F') :=
  z.induction_on
  ⟨⊥, ⊥, finiteDimensional_bot K V, finiteDimensional_bot K V', Submodule.zero_mem _⟩
  fun e f => by
    rcases Module.mem_finiteDimensional_submodule K e with ⟨E', iE', he⟩
    rcases Module.mem_finiteDimensional_submodule K f with ⟨F', iF', hf⟩
    exact ⟨E', F', iE', iF', ⟨⟨e, he⟩ ⊗ₜ ⟨f, hf⟩, rfl⟩⟩
  fun _ _ ih₁ ih₂ => by
    rcases ih₁ with ⟨E1, F1, _, _, ⟨z1, rfl⟩⟩
    rcases ih₂ with ⟨E2, F2, _, _, ⟨z2, rfl⟩⟩
    exact ⟨E1 ⊔ E2, F1 ⊔ F2, E1.finiteDimensional_sup _, F1.finiteDimensional_sup _,
      Submodule.add_mem _
      ((range_mapIncl_mono le_sup_left (le_refl _)).trans
        (range_mapIncl_mono (le_refl _) le_sup_left) ⟨z1, rfl⟩)
      ((range_mapIncl_mono le_sup_right (le_refl _)).trans
        (range_mapIncl_mono (le_refl _) le_sup_right) ⟨z2, rfl⟩)⟩

end move

private lemma inner_coe_of_eq {E' : Submodule 𝕜 E} {F' : Submodule 𝕜 F} {x y : E' ⊗[𝕜] F'} :
    inner 𝕜 x y = inner 𝕜 (mapIncl E' F' x) (mapIncl E' F' y) :=
  x.induction_on (by simp [inner])
  (y.induction_on (by simp [inner]) (by simp) (by simp_all [inner])) (by simp_all [inner])

private lemma inner_coe_of_eq' {x y : E ⊗[𝕜] F}
    {E' : Submodule 𝕜 E} {F' : Submodule 𝕜 F} {x' y' : E' ⊗[𝕜] F'}
    (hx : x = mapIncl E' F' x') (hy : y = mapIncl E' F' y') :
    inner 𝕜 x' y' = inner 𝕜 x y :=
  hx ▸ hy ▸ inner_coe_of_eq

private lemma inner_coe_of_mem_range {x y : E ⊗[𝕜] F} {E' : Submodule 𝕜 E} {F' : Submodule 𝕜 F}
    (hx : x ∈ LinearMap.range (mapIncl E' F')) (hy : y ∈ LinearMap.range (mapIncl E' F')) :
    inner 𝕜 hx.choose hy.choose = inner 𝕜 x y :=
  TensorProduct.inner_coe_of_eq' hx.choose_spec.symm hy.choose_spec.symm

open scoped ComplexOrder
open Module

private theorem inner_definite (x : E ⊗[𝕜] F) (hx : inner 𝕜 x x = 0) : x = 0 := by
  obtain ⟨E', F', iE', iF', hz⟩ := x.mem_finiteDimensional_range_mapIncl
  rw [← inner_coe_of_mem_range hz hz] at hx
  let y := hz.choose
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  have hy : y = hz.choose := rfl
  rw [← hy] at hx
  rw [y.basis_sum_repr e.toBasis f.toBasis] at hx
  simp only [OrthonormalBasis.coe_toBasis] at hx
  simp only [inner, map_smulₛₗ, map_sum, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, RingHom.id_apply] at hx
  simp only [LinearMap.coe_comp, Function.comp_apply, map_tmul, LinearMap.compr₂_apply,
    lift.tmul, mapBilinear_apply, innerₛₗ_apply, OrthonormalBasis.inner_eq_ite,
    LinearMap.mul'_apply, mul_ite, mul_one, mul_zero, smul_eq_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at hx
  simp only [RCLike.mul_conj, ← Finset.sum_product', Finset.univ_product_univ, Prod.mk.eta] at hx
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by simp)] at hx
  simp only [Finset.mem_univ, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    map_eq_zero, norm_eq_zero, forall_const, Prod.forall] at hx
  have : y = 0 := by
    rw [Basis.ext_elem_iff (e.toBasis.tensorProduct f.toBasis)]
    simp only [hx, map_zero, Finsupp.coe_zero, Pi.zero_apply, implies_true]
  rw [← hz.choose_spec, ← hy, this, map_zero]

private protected theorem re_inner_self_nonneg (x : E ⊗[𝕜] F) :
    0 ≤ RCLike.re (inner 𝕜 x x) := by
  obtain ⟨E', F', iE', iF', hz⟩ := x.mem_finiteDimensional_range_mapIncl
  rw [← inner_coe_of_mem_range hz hz]
  let y := hz.choose
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  have hy : y = hz.choose := rfl
  rw [← hy]
  rw [y.basis_sum_repr e.toBasis f.toBasis]
  simp only [OrthonormalBasis.coe_toBasis, inner, LinearMap.comp_apply,
    map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply]
  simp only [RingHom.id_apply, map_tmul, LinearMap.compr₂_apply, lift.tmul, mapBilinear_apply,
    innerₛₗ_apply, LinearMap.mul'_apply, smul_eq_mul]
  simp only [OrthonormalBasis.inner_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
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

instance instInnerProductSpace : InnerProductSpace 𝕜 (E ⊗[𝕜] F) :=
  InnerProductSpace.ofCore _

@[simp]
theorem norm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖ = ‖x‖ * ‖y‖ := by
  rw [@norm_eq_sqrt_re_inner (𝕜 := 𝕜)]
  simp [Real.sqrt_mul inner_self_nonneg, ← norm_eq_sqrt_re_inner]

theorem dist_tmul_le (x x' : E) (y y' : F) :
    dist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖ * ‖y‖ + ‖x'‖ * ‖y'‖ :=
  calc ‖x ⊗ₜ[𝕜] y - x' ⊗ₜ[𝕜] y'‖ ≤ ‖x ⊗ₜ[𝕜] y‖ + ‖x' ⊗ₜ[𝕜] y'‖ := norm_sub_le _ _
    _ = ‖x‖ * ‖y‖ + ‖x'‖ * ‖y'‖ := by simp

theorem _root_.RCLike.inner_tmul_eq (a b c d : 𝕜) :
    inner 𝕜 (a ⊗ₜ[𝕜] b) (c ⊗ₜ[𝕜] d) = inner 𝕜 (a * b) (c * d) := by
  simp; ring

theorem inner_ext_iff (x y : E ⊗[𝕜] F) :
    x = y ↔ ∀ (a : E) (b : F), inner 𝕜 x (a ⊗ₜ[𝕜] b) = inner 𝕜 y (a ⊗ₜ[𝕜] b) := by
  simp_rw [← @sub_eq_zero 𝕜 _ _ (inner _ _ _), ← inner_sub_left]
  rw [← sub_eq_zero]
  refine ⟨fun h a b => by rw [h, inner_zero_left], fun h => ext_inner_right 𝕜 fun y => ?_⟩
  exact y.induction_on (inner_zero_right _) h (fun c d hc hd => by simp [inner_add_right, hc, hd])

theorem inner_ext_threefold_iff {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (x y : E ⊗[𝕜] F ⊗[𝕜] G) :
    x = y ↔ ∀ (a : E) (b : F) (c : G),
      inner 𝕜 x (a ⊗ₜ[𝕜] b ⊗ₜ[𝕜] c) = inner 𝕜 y (a ⊗ₜ[𝕜] b ⊗ₜ[𝕜] c) := by
  simp_rw [← @sub_eq_zero 𝕜 _ _ (inner _ _ _), ← inner_sub_left]
  rw [← sub_eq_zero]
  refine ⟨fun h a b => by simp [h, inner_zero_left], fun h => (inner_ext_iff _ _).mpr fun z b => ?_⟩
  exact z.induction_on (by simp) (by simp [h]) (fun c d hc hd => by
    simp [add_tmul, inner_add_right, hc, hd])

theorem inner_ext_threefold'_iff {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (x y : (E ⊗[𝕜] F) ⊗[𝕜] G) :
    x = y ↔ ∀ (a : E) (b : F) (c : G),
      inner 𝕜 x ((a ⊗ₜ[𝕜] b) ⊗ₜ[𝕜] c) = inner 𝕜 y ((a ⊗ₜ[𝕜] b) ⊗ₜ[𝕜] c) := by
  simp_rw [← @sub_eq_zero 𝕜 _ _ (inner _ _ _), ← inner_sub_left]
  rw [← sub_eq_zero]
  refine ⟨fun h a b => by simp [h, inner_zero_left], fun h => (inner_ext_iff _ _).mpr fun z b => ?_⟩
  exact z.induction_on (by simp) (by simp [h]) (fun c d hc hd => by
    simp [add_tmul, inner_add_right, hc, hd])

section FiniteDimensional
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

theorem comm_adjoint :
    LinearMap.adjoint (TensorProduct.comm 𝕜 E F).toLinearMap =
      (TensorProduct.comm 𝕜 E F).symm.toLinearMap := TensorProduct.ext' fun x y => by
  simp [inner_ext_iff, LinearMap.adjoint_inner_left, mul_comm]

theorem map_adjoint {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B]
    [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] (f : A →ₗ[𝕜] B) (g : E →ₗ[𝕜] F) :
    LinearMap.adjoint (TensorProduct.map f g)
      = TensorProduct.map (LinearMap.adjoint f) (LinearMap.adjoint g) :=
  TensorProduct.ext' fun x y => by simp [inner_ext_iff, LinearMap.adjoint_inner_left]

theorem lid_adjoint :
    LinearMap.adjoint (TensorProduct.lid 𝕜 E).toLinearMap
      = (TensorProduct.lid 𝕜 E).symm.toLinearMap := by
  simp [LinearMap.ext_iff, inner_ext_iff, LinearMap.adjoint_inner_left, inner_smul_right]

theorem assoc_adjoint {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G] :
    LinearMap.adjoint (TensorProduct.assoc 𝕜 E F G).toLinearMap
      = (TensorProduct.assoc 𝕜 E F G).symm.toLinearMap := by
  apply TensorProduct.ext_threefold'
  simp [TensorProduct.inner_ext_threefold'_iff, LinearMap.adjoint_inner_left, mul_assoc]

end FiniteDimensional

end TensorProduct

section OrthonormalBasis
variable {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]

open Module

theorem Basis.tensorProduct_orthonormal
    {b₁ : Basis ι₁ 𝕜 E} {b₂ : Basis ι₂ 𝕜 F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 (b₁.tensorProduct b₂) := orthonormal_iff_ite.mpr fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
  simp [orthonormal_iff_ite.mp, hb₁, hb₂, ← ite_and, and_comm]

variable [Fintype ι₁] [Fintype ι₂]

/-- The orthonormal basis of the tensor product of two orthonormal bases. -/
noncomputable def OrthonormalBasis.tensorProduct
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    OrthonormalBasis (ι₁ × ι₂) 𝕜 (E ⊗[𝕜] F) :=
  (b₁.toBasis.tensorProduct b₂.toBasis).toOrthonormalBasis
    (Basis.tensorProduct_orthonormal b₁.orthonormal b₂.orthonormal)

@[simp]
lemma OrthonormalBasis.tensorProduct_apply
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁) (j : ι₂) :
    b₁.tensorProduct b₂ (i, j) = b₁ i ⊗ₜ[𝕜] b₂ j := by simp [tensorProduct]

lemma OrthonormalBasis.tensorProduct_apply'
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁ × ι₂) :
    b₁.tensorProduct b₂ i = b₁ i.1 ⊗ₜ[𝕜] b₂ i.2 := tensorProduct_apply _ _ _ _

@[simp]
lemma OrthonormalBasis.tensorProduct_repr_tmul_apply
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
    (x : E) (y : F) (i : ι₁) (j : ι₂) :
    ((b₁.tensorProduct b₂).repr (x ⊗ₜ[𝕜] y)) (i, j) = (b₂.repr y j) * (b₁.repr x i) := by
  simp [tensorProduct]

lemma OrthonormalBasis.tensorProduct_repr_tmul_apply'
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (x : E) (y : F) (i : ι₁ × ι₂) :
    ((b₁.tensorProduct b₂).repr (x ⊗ₜ[𝕜] y)) i = (b₂.repr y i.2) * (b₁.repr x i.1) :=
  tensorProduct_repr_tmul_apply _ _ _ _ _ _

lemma OrthonormalBasis.tensorProduct_toBasis
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    (b₁.tensorProduct b₂).toBasis = b₁.toBasis.tensorProduct b₂.toBasis := by simp [tensorProduct]

end OrthonormalBasis
