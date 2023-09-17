/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Character
import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

#align_import algebra.lie.weights from "leanprover-community/mathlib"@"6b0169218d01f2837d79ea2784882009a0da1aa1"

/-!
# Weights and roots of Lie modules and Lie algebras

Just as a key tool when studying the behaviour of a linear operator is to decompose the space on
which it acts into a sum of (generalised) eigenspaces, a key tool when studying a representation `M`
of Lie algebra `L` is to decompose `M` into a sum of simultaneous eigenspaces of `x` as `x` ranges
over `L`. These simultaneous generalised eigenspaces are known as the weight spaces of `M`.

When `L` is nilpotent, it follows from the binomial theorem that weight spaces are Lie submodules.
Even when `L` is not nilpotent, it may be useful to study its representations by restricting them
to a nilpotent subalgebra (e.g., a Cartan subalgebra). In the particular case when we view `L` as a
module over itself via the adjoint action, the weight spaces of `L` restricted to a nilpotent
subalgebra are known as root spaces.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `LieModule.weightSpace`
  * `LieModule.IsWeight`
  * `LieAlgebra.rootSpace`
  * `LieAlgebra.IsRoot`
  * `LieAlgebra.rootSpaceWeightSpaceProduct`
  * `LieAlgebra.rootSpaceProduct`
  * `LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan`

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b)

## Tags

lie character, eigenvalue, eigenspace, weight, weight vector, root, root vector
-/


universe u v w w₁ w₂ w₃

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

variable (H : LieSubalgebra R L) [LieAlgebra.IsNilpotent R H]

variable (M : Type w) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

open LieAlgebra

open TensorProduct

open TensorProduct.LieModule

open scoped BigOperators

open scoped TensorProduct

/-- Given a Lie module `M` over a Lie algebra `L`, the pre-weight space of `M` with respect to a
map `χ : L → R` is the simultaneous generalized eigenspace of the action of all `x : L` on `M`,
with eigenvalues `χ x`.

See also `LieModule.weightSpace`. -/
def preWeightSpace (χ : L → R) : Submodule R M :=
  ⨅ x : L, (toEndomorphism R L M x).maximalGeneralizedEigenspace (χ x)
#align lie_module.pre_weight_space LieModule.preWeightSpace

theorem mem_preWeightSpace (χ : L → R) (m : M) :
    m ∈ preWeightSpace M χ ↔
    ∀ x, ∃ k : ℕ, ((toEndomorphism R L M x - χ x • ↑1) ^ k) m = 0 := by
  simp [preWeightSpace]
#align lie_module.mem_pre_weight_space LieModule.mem_preWeightSpace

variable (R)

theorem exists_preWeightSpace_zero_le_ker_of_isNoetherian [IsNoetherian R M] (x : L) :
    ∃ k : ℕ, preWeightSpace M (0 : L → R) ≤ LinearMap.ker (toEndomorphism R L M x ^ k) := by
  use (toEndomorphism R L M x).maximalGeneralizedEigenspaceIndex 0
  simp only [← Module.End.generalizedEigenspace_zero, preWeightSpace, Pi.zero_apply, iInf_le,
    ← (toEndomorphism R L M x).maximalGeneralizedEigenspace_eq]
#align lie_module.exists_pre_weight_space_zero_le_ker_of_is_noetherian LieModule.exists_preWeightSpace_zero_le_ker_of_isNoetherian

variable {R} (L)

/-- See also `bourbaki1975b` Chapter VII §1.1, Proposition 2 (ii). -/
protected theorem weight_vector_multiplication (M₁ : Type w₁) (M₂ : Type w₂) (M₃ : Type w₃)
    [AddCommGroup M₁] [Module R M₁] [LieRingModule L M₁] [LieModule R L M₁] [AddCommGroup M₂]
    [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂] [AddCommGroup M₃] [Module R M₃]
    [LieRingModule L M₃] [LieModule R L M₃] (g : M₁ ⊗[R] M₂ →ₗ⁅R,L⁆ M₃) (χ₁ χ₂ : L → R) :
    LinearMap.range ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp
    (mapIncl (preWeightSpace M₁ χ₁) (preWeightSpace M₂ χ₂))) ≤
      preWeightSpace M₃ (χ₁ + χ₂) := by
  -- Unpack the statement of the goal.
  intro m₃
  simp only [LieModuleHom.coe_toLinearMap, Pi.add_apply, Function.comp_apply, mem_preWeightSpace,
    LinearMap.coe_comp, TensorProduct.mapIncl, exists_imp, LinearMap.mem_range]
  rintro t rfl x
  -- Set up some notation.
  let F : Module.End R M₃ := toEndomorphism R L M₃ x - (χ₁ x + χ₂ x) • ↑1
  -- The goal is linear in `t` so use induction to reduce to the case that `t` is a pure tensor.
  refine t.induction_on ?_ ?_ ?_
  · use 0; simp only [LinearMap.map_zero, LieModuleHom.map_zero]
  swap
  · rintro t₁ t₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩; use max k₁ k₂
    simp only [LieModuleHom.map_add, LinearMap.map_add,
      LinearMap.pow_map_zero_of_le (le_max_left k₁ k₂) hk₁,
      LinearMap.pow_map_zero_of_le (le_max_right k₁ k₂) hk₂, add_zero]
  -- Now the main argument: pure tensors.
  rintro ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩
--  change ∃ k, (F ^ k) ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃) (m₁ ⊗ₜ m₂)) = 0
  -- Eliminate `g` from the picture.
  let f₁ : Module.End R (M₁ ⊗[R] M₂) := (toEndomorphism R L M₁ x - χ₁ x • ↑1).rTensor M₂
  let f₂ : Module.End R (M₁ ⊗[R] M₂) := (toEndomorphism R L M₂ x - χ₂ x • ↑1).lTensor M₁
  have h_comm_square : F ∘ₗ ↑g = (g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp (f₁ + f₂) := by
    ext m₁ m₂;
    simp only [← g.map_lie x (m₁ ⊗ₜ m₂), add_smul, sub_tmul, tmul_sub, smul_tmul, lie_tmul_right,
      tmul_smul, toEndomorphism_apply_apply, LieModuleHom.map_smul, LinearMap.one_apply,
      LieModuleHom.coe_toLinearMap, LinearMap.smul_apply, Function.comp_apply, LinearMap.coe_comp,
      LinearMap.rTensor_tmul, LieModuleHom.map_add, LinearMap.add_apply, LieModuleHom.map_sub,
      LinearMap.sub_apply, LinearMap.lTensor_tmul, AlgebraTensorModule.curry_apply,
      curry_apply, LinearMap.toFun_eq_coe, LinearMap.coe_restrictScalars]
    abel
  rsuffices ⟨k, hk⟩ : ∃ k : ℕ, ((f₁ + f₂) ^ k) (m₁ ⊗ₜ m₂) = 0
  · use k
    change (F ^ k) (g.toLinearMap (m₁ ⊗ₜ[R] m₂)) = 0
    rw [← LinearMap.comp_apply, LinearMap.commute_pow_left_of_commute h_comm_square,
      LinearMap.comp_apply, hk, LinearMap.map_zero]
  -- Unpack the information we have about `m₁`, `m₂`.
  simp only [mem_preWeightSpace] at hm₁ hm₂
  obtain ⟨k₁, hk₁⟩ := hm₁ x
  obtain ⟨k₂, hk₂⟩ := hm₂ x
  have hf₁ : (f₁ ^ k₁) (m₁ ⊗ₜ m₂) = 0 := by
    simp only [hk₁, zero_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_pow]
  have hf₂ : (f₂ ^ k₂) (m₁ ⊗ₜ m₂) = 0 := by
    simp only [hk₂, tmul_zero, LinearMap.lTensor_tmul, LinearMap.lTensor_pow]
  -- It's now just an application of the binomial theorem.
  use k₁ + k₂ - 1
  have hf_comm : Commute f₁ f₂ := by
    ext m₁ m₂
    simp only [LinearMap.mul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      AlgebraTensorModule.curry_apply, LinearMap.toFun_eq_coe, LinearMap.lTensor_tmul,
      curry_apply, LinearMap.coe_restrictScalars]
  rw [hf_comm.add_pow']
  simp only [TensorProduct.mapIncl, Submodule.subtype_apply, Finset.sum_apply, Submodule.coe_mk,
    LinearMap.coeFn_sum, TensorProduct.map_tmul, LinearMap.smul_apply]
  -- The required sum is zero because each individual term is zero.
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  -- Eliminate the binomial coefficients from the picture.
  suffices (f₁ ^ i * f₂ ^ j) (m₁ ⊗ₜ m₂) = 0 by rw [this]; apply smul_zero
  -- Finish off with appropriate case analysis.
  cases' Nat.le_or_le_of_add_eq_add_pred (Finset.Nat.mem_antidiagonal.mp hij) with hi hj
  · rw [(hf_comm.pow_pow i j).eq, LinearMap.mul_apply, LinearMap.pow_map_zero_of_le hi hf₁,
      LinearMap.map_zero]
  · rw [LinearMap.mul_apply, LinearMap.pow_map_zero_of_le hj hf₂, LinearMap.map_zero]
#align lie_module.weight_vector_multiplication LieModule.weight_vector_multiplication

variable {L M}

theorem lie_mem_preWeightSpace_of_mem_preWeightSpace {χ₁ χ₂ : L → R} {x : L} {m : M}
    (hx : x ∈ preWeightSpace L χ₁) (hm : m ∈ preWeightSpace M χ₂) :
    ⁅x, m⁆ ∈ preWeightSpace M (χ₁ + χ₂) := by
  apply LieModule.weight_vector_multiplication L L M M (toModuleHom R L M) χ₁ χ₂
  simp only [LieModuleHom.coe_toLinearMap, Function.comp_apply, LinearMap.coe_comp,
    TensorProduct.mapIncl, LinearMap.mem_range]
  use ⟨x, hx⟩ ⊗ₜ ⟨m, hm⟩
  simp only [Submodule.subtype_apply, toModuleHom_apply, TensorProduct.map_tmul]
#align lie_module.lie_mem_pre_weight_space_of_mem_pre_weight_space LieModule.lie_mem_preWeightSpace_of_mem_preWeightSpace

variable (M)

/-- If a Lie algebra is nilpotent, then pre-weight spaces are Lie submodules. -/
def weightSpace [LieAlgebra.IsNilpotent R L] (χ : L → R) : LieSubmodule R L M :=
  { preWeightSpace M χ with
    lie_mem := fun hm => by
      dsimp only
      rw [← zero_add χ]
      refine lie_mem_preWeightSpace_of_mem_preWeightSpace ?_ hm
      suffices preWeightSpace L (0 : L → R) = ⊤ by simp only [this, Submodule.mem_top]
      exact LieAlgebra.iInf_max_gen_zero_eigenspace_eq_top_of_nilpotent R L }
#align lie_module.weight_space LieModule.weightSpace

theorem mem_weightSpace [LieAlgebra.IsNilpotent R L] (χ : L → R) (m : M) :
    m ∈ weightSpace M χ ↔ m ∈ preWeightSpace M χ := Iff.rfl
#align lie_module.mem_weight_space LieModule.mem_weightSpace

/-- See also the more useful form `LieModule.zero_weightSpace_eq_top_of_nilpotent`. -/
@[simp]
theorem zero_weightSpace_eq_top_of_nilpotent' [LieAlgebra.IsNilpotent R L] [IsNilpotent R L M] :
    weightSpace M (0 : L → R) = ⊤ := by
  rw [← LieSubmodule.coe_toSubmodule_eq_iff, LieSubmodule.top_coeSubmodule]
  exact iInf_max_gen_zero_eigenspace_eq_top_of_nilpotent R L M
#align lie_module.zero_weight_space_eq_top_of_nilpotent' LieModule.zero_weightSpace_eq_top_of_nilpotent'

theorem coe_weightSpace_of_top [LieAlgebra.IsNilpotent R L] (χ : L → R) :
    (weightSpace M (χ ∘ (⊤ : LieSubalgebra R L).incl) : Submodule R M) = weightSpace M χ := by
  ext m
  simp only [weightSpace, LieSubmodule.coe_toSubmodule_mk, LieSubalgebra.coe_bracket_of_module,
    Function.comp_apply, mem_preWeightSpace]
  constructor <;> intro h x
  · obtain ⟨k, hk⟩ := h ⟨x, Set.mem_univ x⟩; use k; exact hk
  · obtain ⟨k, hk⟩ := h x; use k; exact hk
#align lie_module.coe_weight_space_of_top LieModule.coe_weightSpace_of_top

@[simp]
theorem zero_weightSpace_eq_top_of_nilpotent [LieAlgebra.IsNilpotent R L] [IsNilpotent R L M] :
    weightSpace M (0 : (⊤ : LieSubalgebra R L) → R) = ⊤ := by
  /- We use `coe_weightSpace_of_top` as a trick to circumvent the fact that we don't (yet) know
      `IsNilpotent R (⊤ : LieSubalgebra R L) M` is equivalent to `IsNilpotent R L M`. -/
  have h₀ : (0 : L → R) ∘ (⊤ : LieSubalgebra R L).incl = 0 := by ext; rfl
  rw [← LieSubmodule.coe_toSubmodule_eq_iff, LieSubmodule.top_coeSubmodule, ← h₀,
    coe_weightSpace_of_top, ← iInf_max_gen_zero_eigenspace_eq_top_of_nilpotent R L M]
  rfl
#align lie_module.zero_weight_space_eq_top_of_nilpotent LieModule.zero_weightSpace_eq_top_of_nilpotent

/-- Given a Lie module `M` of a Lie algebra `L`, a weight of `M` with respect to a nilpotent
subalgebra `H ⊆ L` is a Lie character whose corresponding weight space is non-empty. -/
def IsWeight (χ : LieCharacter R H) : Prop :=
  weightSpace M χ ≠ ⊥
#align lie_module.is_weight LieModule.IsWeight

/-- For a non-trivial nilpotent Lie module over a nilpotent Lie algebra, the zero character is a
weight with respect to the `⊤` Lie subalgebra. -/
theorem isWeight_zero_of_nilpotent [Nontrivial M] [LieAlgebra.IsNilpotent R L] [IsNilpotent R L M] :
    IsWeight (⊤ : LieSubalgebra R L) M 0 := by
  rw [IsWeight, LieHom.coe_zero, zero_weightSpace_eq_top_of_nilpotent]; exact top_ne_bot
#align lie_module.is_weight_zero_of_nilpotent LieModule.isWeight_zero_of_nilpotent

/-- A (nilpotent) Lie algebra acts nilpotently on the zero weight space of a Noetherian Lie
module. -/
theorem isNilpotent_toEndomorphism_weightSpace_zero [LieAlgebra.IsNilpotent R L] [IsNoetherian R M]
    (x : L) : _root_.IsNilpotent <| toEndomorphism R L (weightSpace M (0 : L → R)) x := by
  obtain ⟨k, hk⟩ := exists_preWeightSpace_zero_le_ker_of_isNoetherian R M x
  use k
  ext ⟨m, hm⟩
  rw [LinearMap.zero_apply, LieSubmodule.coe_zero, Submodule.coe_eq_zero, ←
    LieSubmodule.toEndomorphism_restrict_eq_toEndomorphism, LinearMap.pow_restrict, ←
    SetLike.coe_eq_coe, LinearMap.restrict_apply, Submodule.coe_mk, Submodule.coe_zero]
  exact hk hm
#align lie_module.is_nilpotent_to_endomorphism_weight_space_zero LieModule.isNilpotent_toEndomorphism_weightSpace_zero

/-- By Engel's theorem, when the Lie algebra is Noetherian, the zero weight space of a Noetherian
Lie module is nilpotent. -/
instance [LieAlgebra.IsNilpotent R L] [IsNoetherian R L] [IsNoetherian R M] :
    IsNilpotent R L (weightSpace M (0 : L → R)) :=
  isNilpotent_iff_forall.mpr <| isNilpotent_toEndomorphism_weightSpace_zero M

end LieModule

namespace LieAlgebra

open scoped TensorProduct

open TensorProduct.LieModule

open LieModule

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of a map `χ : H → R` is the weight
space of `L` regarded as a module of `H` via the adjoint action. -/
abbrev rootSpace (χ : H → R) : LieSubmodule R H L :=
  weightSpace L χ
#align lie_algebra.root_space LieAlgebra.rootSpace

-- @[simp] -- Porting note: simp can prove this
theorem zero_rootSpace_eq_top_of_nilpotent [IsNilpotent R L] :
    rootSpace (⊤ : LieSubalgebra R L) 0 = ⊤ :=
  zero_weightSpace_eq_top_of_nilpotent L
#align lie_algebra.zero_root_space_eq_top_of_nilpotent LieAlgebra.zero_rootSpace_eq_top_of_nilpotent

/-- A root of a Lie algebra `L` with respect to a nilpotent subalgebra `H ⊆ L` is a weight of `L`,
regarded as a module of `H` via the adjoint action. -/
abbrev IsRoot :=
  IsWeight H L
#align lie_algebra.is_root LieAlgebra.IsRoot

@[simp]
theorem rootSpace_comap_eq_weightSpace (χ : H → R) :
    (rootSpace H χ).comap H.incl' = weightSpace H χ := by
  ext x
  let f : H → Module.End R L := fun y => toEndomorphism R H L y - χ y • ↑1
  let g : H → Module.End R H := fun y => toEndomorphism R H H y - χ y • ↑1
  suffices
    (∀ y : H, ∃ k : ℕ, (f y ^ k).comp (H.incl : H →ₗ[R] L) x = 0) ↔
      ∀ y : H, ∃ k : ℕ, (H.incl : H →ₗ[R] L).comp (g y ^ k) x = 0 by
    simp only [LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, Function.comp_apply,
      LinearMap.coe_comp, Submodule.coe_eq_zero] at this
    simp only [mem_weightSpace, mem_preWeightSpace, LieSubalgebra.coe_incl',
      LieSubmodule.mem_comap, this]
  have hfg : ∀ y : H, (f y).comp (H.incl : H →ₗ[R] L) = (H.incl : H →ₗ[R] L).comp (g y) := by
    rintro ⟨y, hy⟩; ext ⟨z, _⟩
    simp only [Submodule.coe_sub, toEndomorphism_apply_apply, LieHom.coe_toLinearMap,
      LinearMap.one_apply, LieSubalgebra.coe_incl, LieSubalgebra.coe_bracket_of_module,
      LieSubalgebra.coe_bracket, LinearMap.smul_apply, Function.comp_apply,
      Submodule.coe_smul_of_tower, LinearMap.coe_comp, LinearMap.sub_apply]
  simp_rw [LinearMap.commute_pow_left_of_commute (hfg _)]
#align lie_algebra.root_space_comap_eq_weight_space LieAlgebra.rootSpace_comap_eq_weightSpace

variable {H M}

theorem lie_mem_weightSpace_of_mem_weightSpace {χ₁ χ₂ : H → R} {x : L} {m : M}
    (hx : x ∈ rootSpace H χ₁) (hm : m ∈ weightSpace M χ₂) : ⁅x, m⁆ ∈ weightSpace M (χ₁ + χ₂) := by
  apply LieModule.weight_vector_multiplication H L M M ((toModuleHom R L M).restrictLie H) χ₁ χ₂
  simp only [LieModuleHom.coe_toLinearMap, Function.comp_apply, LinearMap.coe_comp,
    TensorProduct.mapIncl, LinearMap.mem_range]
  use ⟨x, hx⟩ ⊗ₜ ⟨m, hm⟩
  simp only [Submodule.subtype_apply, toModuleHom_apply, Submodule.coe_mk,
    LieModuleHom.coe_restrictLie, TensorProduct.map_tmul]
#align lie_algebra.lie_mem_weight_space_of_mem_weight_space LieAlgebra.lie_mem_weightSpace_of_mem_weightSpace

variable (R L H M)

/-- Auxiliary definition for `rootSpaceWeightSpaceProduct`,
which is close to the deterministic timeout limit.
-/
def rootSpaceWeightSpaceProductAux {χ₁ χ₂ χ₃ : H → R} (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ →ₗ[R] weightSpace M χ₂ →ₗ[R] weightSpace M χ₃ where
  toFun x :=
    { toFun := fun m =>
        ⟨⁅(x : L), (m : M)⁆, hχ ▸ lie_mem_weightSpace_of_mem_weightSpace x.property m.property⟩
      map_add' := fun m n => by simp only [LieSubmodule.coe_add, lie_add]; rfl
      map_smul' := fun t m => by
        dsimp only
        conv_lhs =>
          congr
          rw [LieSubmodule.coe_smul, lie_smul] }
  map_add' x y := by
    ext m
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, add_lie, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply, AddSubmonoid.mk_add_mk]
  map_smul' t x := by
    simp only [RingHom.id_apply]
    ext m
    simp only [SetLike.val_smul, smul_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      SetLike.mk_smul_mk]
#align lie_algebra.root_space_weight_space_product_aux LieAlgebra.rootSpaceWeightSpaceProductAux

-- Porting note: this def is _really_ slow
-- See https://github.com/leanprover-community/mathlib4/issues/5028
/-- Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is a natural
`R`-bilinear product of root vectors and weight vectors, compatible with the actions of `H`. -/
def rootSpaceWeightSpaceProduct (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ ⊗[R] weightSpace M χ₂ →ₗ⁅R,H⁆ weightSpace M χ₃ :=
  liftLie R H (rootSpace H χ₁) (weightSpace M χ₂) (weightSpace M χ₃)
    { toLinearMap := rootSpaceWeightSpaceProductAux R L H M hχ
      map_lie' := fun {x y} => by
        ext m
        simp only [rootSpaceWeightSpaceProductAux, LieSubmodule.coe_bracket,
          LieSubalgebra.coe_bracket_of_module, lie_lie, LinearMap.coe_mk, AddHom.coe_mk,
          Subtype.coe_mk, LieHom.lie_apply, LieSubmodule.coe_sub] }
#align lie_algebra.root_space_weight_space_product LieAlgebra.rootSpaceWeightSpaceProduct

@[simp]
theorem coe_rootSpaceWeightSpaceProduct_tmul (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃)
    (x : rootSpace H χ₁) (m : weightSpace M χ₂) :
    (rootSpaceWeightSpaceProduct R L H M χ₁ χ₂ χ₃ hχ (x ⊗ₜ m) : M) = ⁅(x : L), (m : M)⁆ := by
  simp only [rootSpaceWeightSpaceProduct, rootSpaceWeightSpaceProductAux, coe_liftLie_eq_lift_coe,
    AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, lift_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_mk]
#align lie_algebra.coe_root_space_weight_space_product_tmul LieAlgebra.coe_rootSpaceWeightSpaceProduct_tmul

/-- Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is a natural
`R`-bilinear product of root vectors, compatible with the actions of `H`. -/
def rootSpaceProduct (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ ⊗[R] rootSpace H χ₂ →ₗ⁅R,H⁆ rootSpace H χ₃ :=
  rootSpaceWeightSpaceProduct R L H L χ₁ χ₂ χ₃ hχ
#align lie_algebra.root_space_product LieAlgebra.rootSpaceProduct

@[simp]
theorem rootSpaceProduct_def : rootSpaceProduct R L H = rootSpaceWeightSpaceProduct R L H L := rfl
#align lie_algebra.root_space_product_def LieAlgebra.rootSpaceProduct_def

theorem rootSpaceProduct_tmul (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) (x : rootSpace H χ₁)
    (y : rootSpace H χ₂) : (rootSpaceProduct R L H χ₁ χ₂ χ₃ hχ (x ⊗ₜ y) : L) = ⁅(x : L), (y : L)⁆ :=
  by simp only [rootSpaceProduct_def, coe_rootSpaceWeightSpaceProduct_tmul]
#align lie_algebra.root_space_product_tmul LieAlgebra.rootSpaceProduct_tmul

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of the zero map `0 : H → R` is a Lie
subalgebra of `L`. -/
def zeroRootSubalgebra : LieSubalgebra R L :=
  { (rootSpace H 0 : Submodule R L) with
    lie_mem' := fun {x y hx hy} => by
      let xy : rootSpace H 0 ⊗[R] rootSpace H 0 := ⟨x, hx⟩ ⊗ₜ ⟨y, hy⟩
      suffices (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy : L) ∈ rootSpace H 0 by
        rwa [rootSpaceProduct_tmul, Subtype.coe_mk, Subtype.coe_mk] at this
      exact (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy).property }
#align lie_algebra.zero_root_subalgebra LieAlgebra.zeroRootSubalgebra

@[simp]
theorem coe_zeroRootSubalgebra : (zeroRootSubalgebra R L H : Submodule R L) = rootSpace H 0 := rfl
#align lie_algebra.coe_zero_root_subalgebra LieAlgebra.coe_zeroRootSubalgebra

theorem mem_zeroRootSubalgebra (x : L) :
    x ∈ zeroRootSubalgebra R L H ↔ ∀ y : H, ∃ k : ℕ, (toEndomorphism R H L y ^ k) x = 0 := by
  rw [zeroRootSubalgebra]
  -- Porting note: added the following `change` otherwise the `simp` fails
  -- See https://github.com/leanprover-community/mathlib4/issues/5026
  change x ∈ rootSpace H 0 ↔ _
  simp only [mem_weightSpace, mem_preWeightSpace, Pi.zero_apply, zero_smul, sub_zero]
#align lie_algebra.mem_zero_root_subalgebra LieAlgebra.mem_zeroRootSubalgebra

theorem toLieSubmodule_le_rootSpace_zero : H.toLieSubmodule ≤ rootSpace H 0 := by
  intro x hx
  simp only [LieSubalgebra.mem_toLieSubmodule] at hx
  simp only [mem_weightSpace, mem_preWeightSpace, Pi.zero_apply, sub_zero, zero_smul]
  intro y
  obtain ⟨k, hk⟩ := (inferInstance : IsNilpotent R H)
  use k
  let f : Module.End R H := toEndomorphism R H H y
  let g : Module.End R L := toEndomorphism R H L y
  have hfg : g.comp (H : Submodule R L).subtype = (H : Submodule R L).subtype.comp f := by
    ext z
    simp only [toEndomorphism_apply_apply, Submodule.subtype_apply,
      LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket, Function.comp_apply,
      LinearMap.coe_comp]
    rfl
  change (g ^ k).comp (H : Submodule R L).subtype ⟨x, hx⟩ = 0
  rw [LinearMap.commute_pow_left_of_commute hfg k]
  have h := iterate_toEndomorphism_mem_lowerCentralSeries R H H y ⟨x, hx⟩ k
  rw [hk, LieSubmodule.mem_bot] at h
  simp only [Submodule.subtype_apply, Function.comp_apply, LinearMap.pow_apply, LinearMap.coe_comp,
    Submodule.coe_eq_zero]
  exact h
#align lie_algebra.to_lie_submodule_le_root_space_zero LieAlgebra.toLieSubmodule_le_rootSpace_zero

theorem le_zeroRootSubalgebra : H ≤ zeroRootSubalgebra R L H := by
  rw [← LieSubalgebra.coe_submodule_le_coe_submodule, ← H.coe_toLieSubmodule,
    coe_zeroRootSubalgebra, LieSubmodule.coeSubmodule_le_coeSubmodule]
  exact toLieSubmodule_le_rootSpace_zero R L H
#align lie_algebra.le_zero_root_subalgebra LieAlgebra.le_zeroRootSubalgebra

@[simp]
theorem zeroRootSubalgebra_normalizer_eq_self :
    (zeroRootSubalgebra R L H).normalizer = zeroRootSubalgebra R L H := by
  refine' le_antisymm _ (LieSubalgebra.le_normalizer _)
  intro x hx
  rw [LieSubalgebra.mem_normalizer_iff] at hx
  rw [mem_zeroRootSubalgebra]
  rintro ⟨y, hy⟩
  specialize hx y (le_zeroRootSubalgebra R L H hy)
  rw [mem_zeroRootSubalgebra] at hx
  obtain ⟨k, hk⟩ := hx ⟨y, hy⟩
  rw [← lie_skew, LinearMap.map_neg, neg_eq_zero] at hk
  use k + 1
  rw [LinearMap.iterate_succ, LinearMap.coe_comp, Function.comp_apply, toEndomorphism_apply_apply,
    LieSubalgebra.coe_bracket_of_module, Submodule.coe_mk, hk]
#align lie_algebra.zero_root_subalgebra_normalizer_eq_self LieAlgebra.zeroRootSubalgebra_normalizer_eq_self

/-- If the zero root subalgebra of a nilpotent Lie subalgebra `H` is just `H` then `H` is a Cartan
subalgebra.

When `L` is Noetherian, it follows from Engel's theorem that the converse holds. See
`LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan` -/
theorem is_cartan_of_zeroRootSubalgebra_eq (h : zeroRootSubalgebra R L H = H) :
    H.IsCartanSubalgebra :=
  { nilpotent := inferInstance
    self_normalizing := by rw [← h]; exact zeroRootSubalgebra_normalizer_eq_self R L H }
#align lie_algebra.is_cartan_of_zero_root_subalgebra_eq LieAlgebra.is_cartan_of_zeroRootSubalgebra_eq

@[simp]
theorem zeroRootSubalgebra_eq_of_is_cartan (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
    [IsNoetherian R L] : zeroRootSubalgebra R L H = H := by
  refine' le_antisymm _ (le_zeroRootSubalgebra R L H)
  suffices rootSpace H 0 ≤ H.toLieSubmodule by exact fun x hx => this hx
  obtain ⟨k, hk⟩ := (rootSpace H 0).isNilpotent_iff_exists_self_le_ucs.mp (by infer_instance)
  exact hk.trans (LieSubmodule.ucs_le_of_normalizer_eq_self (by simp) k)
#align lie_algebra.zero_root_subalgebra_eq_of_is_cartan LieAlgebra.zeroRootSubalgebra_eq_of_is_cartan

theorem zeroRootSubalgebra_eq_iff_is_cartan [IsNoetherian R L] :
    zeroRootSubalgebra R L H = H ↔ H.IsCartanSubalgebra :=
  ⟨is_cartan_of_zeroRootSubalgebra_eq R L H, by intros; simp⟩
#align lie_algebra.zero_root_subalgebra_eq_iff_is_cartan LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan

end LieAlgebra

namespace LieModule

open LieAlgebra

variable {H}

/-- A priori, weight spaces are Lie submodules over the Lie subalgebra `H` used to define them.
However they are naturally Lie submodules over the (in general larger) Lie subalgebra
`zeroRootSubalgebra R L H`. Even though it is often the case that
`zeroRootSubalgebra R L H = H`, it is likely to be useful to have the flexibility not to have
to invoke this equality (as well as to work more generally). -/
def weightSpace' (χ : H → R) : LieSubmodule R (zeroRootSubalgebra R L H) M :=
  { (weightSpace M χ : Submodule R M) with
    lie_mem := fun {x m hm} => by
      have hx : (x : L) ∈ rootSpace H 0 := by
        rw [← LieSubmodule.mem_coeSubmodule, ← coe_zeroRootSubalgebra]; exact x.prop
      dsimp only
      rw [← zero_add χ]
      exact lie_mem_weightSpace_of_mem_weightSpace hx hm }
#align lie_module.weight_space' LieModule.weightSpace'

@[simp]
theorem coe_weightSpace' (χ : H → R) : (weightSpace' M χ : Submodule R M) = weightSpace M χ := rfl
#align lie_module.coe_weight_space' LieModule.coe_weightSpace'

end LieModule
