/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Ring.Divisibility.Lemmas
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Engel
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Artinian

#align_import algebra.lie.weights from "leanprover-community/mathlib"@"6b0169218d01f2837d79ea2784882009a0da1aa1"

/-!
# Weight spaces of Lie modules of nilpotent Lie algebras

Just as a key tool when studying the behaviour of a linear operator is to decompose the space on
which it acts into a sum of (generalised) eigenspaces, a key tool when studying a representation `M`
of Lie algebra `L` is to decompose `M` into a sum of simultaneous eigenspaces of `x` as `x` ranges
over `L`. These simultaneous generalised eigenspaces are known as the weight spaces of `M`.

When `L` is nilpotent, it follows from the binomial theorem that weight spaces are Lie submodules.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `LieModule.weightSpaceOf`
  * `LieModule.weightSpace`
  * `LieModule.posFittingCompOf`
  * `LieModule.posFittingComp`
  * `LieModule.iSup_ucs_eq_weightSpace_zero`
  * `LieModule.iInf_lowerCentralSeries_eq_posFittingComp`

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b)

## Tags

lie character, eigenvalue, eigenspace, weight, weight vector, root, root vector
-/

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieAlgebra.IsNilpotent R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

open LieAlgebra TensorProduct TensorProduct.LieModule
open scoped BigOperators TensorProduct

section notation_weight_space_of

/-- Until we define `LieModule.weightSpaceOf`, it is useful to have some notation as follows: -/
local notation3 (prettyPrint := false) "𝕎("M"," χ"," x")" =>
  (toEndomorphism R L M x).maximalGeneralizedEigenspace χ

/-- See also `bourbaki1975b` Chapter VII §1.1, Proposition 2 (ii). -/
protected theorem weight_vector_multiplication (M₁ M₂ M₃ : Type*)
    [AddCommGroup M₁] [Module R M₁] [LieRingModule L M₁] [LieModule R L M₁] [AddCommGroup M₂]
    [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂] [AddCommGroup M₃] [Module R M₃]
    [LieRingModule L M₃] [LieModule R L M₃] (g : M₁ ⊗[R] M₂ →ₗ⁅R,L⁆ M₃) (χ₁ χ₂ : R) (x : L) :
    LinearMap.range ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp (mapIncl 𝕎(M₁, χ₁, x) 𝕎(M₂, χ₂, x))) ≤
      𝕎(M₃, χ₁ + χ₂, x) := by
  -- Unpack the statement of the goal.
  intro m₃
  simp only [TensorProduct.mapIncl, LinearMap.mem_range, LinearMap.coe_comp,
    LieModuleHom.coe_toLinearMap, Function.comp_apply, Pi.add_apply, exists_imp,
    Module.End.mem_maximalGeneralizedEigenspace]
  rintro t rfl
  -- Set up some notation.
  let F : Module.End R M₃ := toEndomorphism R L M₃ x - (χ₁ + χ₂) • ↑1
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
  change ∃ k, (F ^ k) ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃) (m₁ ⊗ₜ m₂)) = (0 : M₃)
  -- Eliminate `g` from the picture.
  let f₁ : Module.End R (M₁ ⊗[R] M₂) := (toEndomorphism R L M₁ x - χ₁ • ↑1).rTensor M₂
  let f₂ : Module.End R (M₁ ⊗[R] M₂) := (toEndomorphism R L M₂ x - χ₂ • ↑1).lTensor M₁
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
  simp only [Module.End.mem_maximalGeneralizedEigenspace] at hm₁ hm₂
  obtain ⟨k₁, hk₁⟩ := hm₁
  obtain ⟨k₂, hk₂⟩ := hm₂
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

lemma lie_mem_maxGenEigenspace_toEndomorphism
    {χ₁ χ₂ : R} {x y : L} {m : M} (hy : y ∈ 𝕎(L, χ₁, x)) (hm : m ∈ 𝕎(M, χ₂, x)) :
    ⁅y, m⁆ ∈ 𝕎(M, χ₁ + χ₂, x) := by
  apply LieModule.weight_vector_multiplication L M M (toModuleHom R L M) χ₁ χ₂
  simp only [LieModuleHom.coe_toLinearMap, Function.comp_apply, LinearMap.coe_comp,
    TensorProduct.mapIncl, LinearMap.mem_range]
  use ⟨y, hy⟩ ⊗ₜ ⟨m, hm⟩
  simp only [Submodule.subtype_apply, toModuleHom_apply, TensorProduct.map_tmul]

variable (M)

/-- If `M` is a representation of a nilpotent Lie algebra `L`, `χ` is a scalar, and `x : L`, then
`weightSpaceOf M χ x` is the maximal generalized `χ`-eigenspace of the action of `x` on `M`.

It is a Lie submodule because `L` is nilpotent. -/
def weightSpaceOf (χ : R) (x : L) : LieSubmodule R L M :=
  { 𝕎(M, χ, x) with
    lie_mem := by
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid] at hm ⊢
      rw [← zero_add χ]
      exact lie_mem_maxGenEigenspace_toEndomorphism (by simp) hm }

theorem mem_weightSpaceOf (χ : R) (x : L) (m : M) :
    m ∈ weightSpaceOf M χ x ↔ ∃ k : ℕ, ((toEndomorphism R L M x - χ • ↑1) ^ k) m = 0 := by
  simp [weightSpaceOf]

end notation_weight_space_of

variable (M)

/-- If `M` is a representation of a nilpotent Lie algebra `L` and `χ : L → R` is a family of
scalars, then `weightSpace M χ` is the intersection of the maximal generalized `χ x`-eigenspaces of
the action of `x` on `M` as `x` ranges over `L`.

It is a Lie submodule because `L` is nilpotent. -/
def weightSpace (χ : L → R) : LieSubmodule R L M :=
  ⨅ x, weightSpaceOf M (χ x) x

theorem mem_weightSpace (χ : L → R) (m : M) :
    m ∈ weightSpace M χ ↔ ∀ x, ∃ k : ℕ, ((toEndomorphism R L M x - χ x • ↑1) ^ k) m = 0 := by
  simp [weightSpace, mem_weightSpaceOf]

/-- See also the more useful form `LieModule.zero_weightSpace_eq_top_of_nilpotent`. -/
@[simp]
theorem zero_weightSpace_eq_top_of_nilpotent' [IsNilpotent R L M] :
    weightSpace M (0 : L → R) = ⊤ := by
  ext
  simp [weightSpace, weightSpaceOf]
#align lie_module.zero_weight_space_eq_top_of_nilpotent' LieModule.zero_weightSpace_eq_top_of_nilpotent'

theorem coe_weightSpace_of_top (χ : L → R) :
    (weightSpace M (χ ∘ (⊤ : LieSubalgebra R L).incl) : Submodule R M) = weightSpace M χ := by
  ext m
  simp only [mem_weightSpace, LieSubmodule.mem_coeSubmodule, Subtype.forall]
  apply forall_congr'
  simp
#align lie_module.coe_weight_space_of_top LieModule.coe_weightSpace_of_top

@[simp]
theorem zero_weightSpace_eq_top_of_nilpotent [IsNilpotent R L M] :
    weightSpace M (0 : (⊤ : LieSubalgebra R L) → R) = ⊤ := by
  ext m
  simp only [mem_weightSpace, Pi.zero_apply, zero_smul, sub_zero, Subtype.forall, forall_true_left,
    LieSubalgebra.toEndomorphism_mk, LieSubalgebra.mem_top, LieSubmodule.mem_top, iff_true]
  intro x
  obtain ⟨k, hk⟩ := exists_forall_pow_toEndomorphism_eq_zero R L M
  exact ⟨k, by simp [hk x]⟩
#align lie_module.zero_weight_space_eq_top_of_nilpotent LieModule.zero_weightSpace_eq_top_of_nilpotent

variable (R) in
theorem exists_weightSpace_zero_le_ker_of_isNoetherian
    [IsNoetherian R M] (x : L) :
    ∃ k : ℕ, weightSpace M (0 : L → R) ≤ LinearMap.ker (toEndomorphism R L M x ^ k) := by
  use (toEndomorphism R L M x).maximalGeneralizedEigenspaceIndex 0
  simp only [weightSpace, weightSpaceOf, LieSubmodule.iInf_coe_toSubmodule, Pi.zero_apply, iInf_le,
    ← Module.End.generalizedEigenspace_zero,
    ← (toEndomorphism R L M x).maximalGeneralizedEigenspace_eq]

/-- A (nilpotent) Lie algebra acts nilpotently on the zero weight space of a Noetherian Lie
module. -/
theorem isNilpotent_toEndomorphism_weightSpace_zero [IsNoetherian R M]
    (x : L) : _root_.IsNilpotent <| toEndomorphism R L (weightSpace M (0 : L → R)) x := by
  obtain ⟨k, hk⟩ := exists_weightSpace_zero_le_ker_of_isNoetherian R M x
  use k
  ext ⟨m, hm⟩
  rw [LinearMap.zero_apply, LieSubmodule.coe_zero, Submodule.coe_eq_zero, ←
    LieSubmodule.toEndomorphism_restrict_eq_toEndomorphism, LinearMap.pow_restrict, ←
    SetLike.coe_eq_coe, LinearMap.restrict_apply, Submodule.coe_mk, Submodule.coe_zero]
  exact hk hm
#align lie_module.is_nilpotent_to_endomorphism_weight_space_zero LieModule.isNilpotent_toEndomorphism_weightSpace_zero

/-- By Engel's theorem, the zero weight space of a Noetherian Lie module is nilpotent. -/
instance [IsNoetherian R M] :
    IsNilpotent R L (weightSpace M (0 : L → R)) :=
  isNilpotent_iff_forall'.mpr <| isNilpotent_toEndomorphism_weightSpace_zero M

variable (R L)

@[simp]
lemma weightSpace_zero_normalizer_eq_self :
    (weightSpace M (0 : L → R)).normalizer = weightSpace M 0 := by
  refine' le_antisymm _ (LieSubmodule.le_normalizer _)
  intro m hm
  rw [LieSubmodule.mem_normalizer] at hm
  simp only [mem_weightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm ⊢
  intro y
  obtain ⟨k, hk⟩ := hm y y
  use k + 1
  simpa [pow_succ', LinearMap.mul_eq_comp]

lemma iSup_ucs_le_weightSpace_zero :
    ⨆ k, (⊥ : LieSubmodule R L M).ucs k ≤ weightSpace M (0 : L → R) := by
  simpa using LieSubmodule.ucs_le_of_normalizer_eq_self (weightSpace_zero_normalizer_eq_self R L M)

/-- See also `LieModule.iInf_lowerCentralSeries_eq_posFittingComp`. -/
lemma iSup_ucs_eq_weightSpace_zero [IsNoetherian R M] :
    ⨆ k, (⊥ : LieSubmodule R L M).ucs k = weightSpace M (0 : L → R) := by
  obtain ⟨k, hk⟩ := (LieSubmodule.isNilpotent_iff_exists_self_le_ucs
    <| weightSpace M (0 : L → R)).mp inferInstance
  refine le_antisymm (iSup_ucs_le_weightSpace_zero R L M) (le_trans hk ?_)
  exact le_iSup (fun k ↦ (⊥ : LieSubmodule R L M).ucs k) k

variable {L}

/-- If `M` is a representation of a nilpotent Lie algebra `L`, and `x : L`, then
`posFittingCompOf R M x` is the infimum of the decreasing system
`range φₓ ⊇ range φₓ² ⊇ range φₓ³ ⊇ ⋯` where `φₓ : End R M := toEndomorphism R L M x`. We call this
the "positive Fitting component" because with appropriate assumptions (e.g., `R` is a field and
`M` is finite-dimensional) `φₓ` induces the so-called Fitting decomposition: `M = M₀ ⊕ M₁` where
`M₀ = weightSpaceOf M 0 x` and `M₁ = posFittingCompOf R M x`.

It is a Lie submodule because `L` is nilpotent. -/
def posFittingCompOf (x : L) : LieSubmodule R L M :=
  { toSubmodule := ⨅ k, LinearMap.range (toEndomorphism R L M x ^ k)
    lie_mem := by
      set φ := toEndomorphism R L M x
      intros y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Submodule.mem_iInf, LinearMap.mem_range] at hm ⊢
      intro k
      obtain ⟨N, hN⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra R L
      obtain ⟨m, rfl⟩ := hm (N + k)
      let f₁ : Module.End R (L ⊗[R] M) := (LieAlgebra.ad R L x).rTensor M
      let f₂ : Module.End R (L ⊗[R] M) := φ.lTensor L
      replace hN : f₁ ^ N = 0 := by ext; simp [hN]
      have h₁ : Commute f₁ f₂ := by ext; simp
      have h₂ : φ ∘ₗ toModuleHom R L M = toModuleHom R L M ∘ₗ (f₁ + f₂) := by ext; simp
      obtain ⟨q, hq⟩ := h₁.add_pow_dvd_pow_of_pow_eq_zero_right (N + k).le_succ hN
      use toModuleHom R L M (q (y ⊗ₜ m))
      change (φ ^ k).comp ((toModuleHom R L M : L ⊗[R] M →ₗ[R] M)) _ = _
      simp [LinearMap.commute_pow_left_of_commute h₂, LinearMap.comp_apply (g := (f₁ + f₂) ^ k),
        ← LinearMap.comp_apply (g := q), ← LinearMap.mul_eq_comp, ← hq] }

variable {M} in
lemma mem_posFittingCompOf (x : L) (m : M) :
    m ∈ posFittingCompOf R M x ↔ ∀ (k : ℕ), ∃ n, (toEndomorphism R L M x ^ k) n = m := by
  simp [posFittingCompOf]

@[simp] lemma posFittingCompOf_le_lowerCentralSeries (x : L) (k : ℕ) :
    posFittingCompOf R M x ≤ lowerCentralSeries R L M k := by
  suffices : ∀ m l, (toEndomorphism R L M x ^ l) m ∈ lowerCentralSeries R L M l
  · intro m hm
    obtain ⟨n, rfl⟩ := (mem_posFittingCompOf R x m).mp hm k
    exact this n k
  intro m l
  induction' l with l ih; simp
  simp only [lowerCentralSeries_succ, pow_succ, LinearMap.mul_apply]
  exact LieSubmodule.lie_mem_lie _ ⊤ (LieSubmodule.mem_top x) ih

@[simp] lemma posFittingCompOf_eq_bot_of_isNilpotent
    [IsNilpotent R L M] (x : L) :
    posFittingCompOf R M x = ⊥ := by
  simp_rw [eq_bot_iff, ← iInf_lowerCentralSeries_eq_bot_of_isNilpotent, le_iInf_iff,
    posFittingCompOf_le_lowerCentralSeries, forall_const]

variable (L)

/-- If `M` is a representation of a nilpotent Lie algebra `L` with coefficients in `R`, then
`posFittingComp R L M` is the span of the positive Fitting components of the action of `x` on `M`,
as `x` ranges over `L`.

It is a Lie submodule because `L` is nilpotent. -/
def posFittingComp : LieSubmodule R L M :=
  ⨆ x, posFittingCompOf R M x

lemma mem_posFittingComp (m : M) :
    m ∈ posFittingComp R L M ↔ m ∈ ⨆ (x : L), posFittingCompOf R M x := by
  rfl

lemma posFittingCompOf_le_posFittingComp (x : L) :
    posFittingCompOf R M x ≤ posFittingComp R L M := by
  rw [posFittingComp]; exact le_iSup (posFittingCompOf R M) x

lemma posFittingComp_le_iInf_lowerCentralSeries :
    posFittingComp R L M ≤ ⨅ k, lowerCentralSeries R L M k := by
  simp [posFittingComp]

/-- See also `LieModule.iSup_ucs_eq_weightSpace_zero`. -/
@[simp] lemma iInf_lowerCentralSeries_eq_posFittingComp
    [IsNoetherian R M] [IsArtinian R M] :
    ⨅ k, lowerCentralSeries R L M k = posFittingComp R L M := by
  refine le_antisymm ?_ (posFittingComp_le_iInf_lowerCentralSeries R L M)
  apply iInf_lcs_le_of_isNilpotent_quot
  rw [LieModule.isNilpotent_iff_forall']
  intro x
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (toEndomorphism R L M x).eventually_iInf_range_pow_eq
  use k
  ext ⟨m⟩
  set F := posFittingComp R L M
  replace hk : (toEndomorphism R L M x ^ k) m ∈ F := by
    apply posFittingCompOf_le_posFittingComp R L M x
    simp_rw [← LieSubmodule.mem_coeSubmodule, posFittingCompOf, hk k (le_refl k)]
    apply LinearMap.mem_range_self
  suffices (toEndomorphism R L (M ⧸ F) x ^ k) (LieSubmodule.Quotient.mk (N := F) m) =
    LieSubmodule.Quotient.mk (N := F) ((toEndomorphism R L M x ^ k) m) by simpa [this]
  have := LinearMap.congr_fun (LinearMap.commute_pow_left_of_commute
    (LieSubmodule.Quotient.toEndomorphism_comp_mk' F x) k) m
  simpa using this

@[simp] lemma posFittingComp_eq_bot_of_isNilpotent
    [IsNilpotent R L M] :
    posFittingComp R L M = ⊥ := by
  simp [posFittingComp]

end LieModule
