/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Ring.Divisibility.Lemmas
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Engel
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.Artinian
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FreeModule.PID

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
  * `LieModule.Weight`
  * `LieModule.posFittingCompOf`
  * `LieModule.posFittingComp`
  * `LieModule.iSup_ucs_eq_weightSpace_zero`
  * `LieModule.iInf_lowerCentralSeries_eq_posFittingComp`
  * `LieModule.isCompl_weightSpace_zero_posFittingComp`
  * `LieModule.independent_weightSpace`
  * `LieModule.iSup_weightSpace_eq_top`

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b)

## Tags

lie character, eigenvalue, eigenspace, weight, weight vector, root, root vector
-/

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieAlgebra.IsNilpotent R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

open Set Function LieAlgebra TensorProduct TensorProduct.LieModule
open scoped TensorProduct

section notation_weightSpaceOf

/-- Until we define `LieModule.weightSpaceOf`, it is useful to have some notation as follows: -/
local notation3 "𝕎("M", " χ", " x")" => (toEnd R L M x).maxGenEigenspace χ

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
    Module.End.mem_maxGenEigenspace]
  rintro t rfl
  -- Set up some notation.
  let F : Module.End R M₃ := toEnd R L M₃ x - (χ₁ + χ₂) • ↑1
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
  let f₁ : Module.End R (M₁ ⊗[R] M₂) := (toEnd R L M₁ x - χ₁ • ↑1).rTensor M₂
  let f₂ : Module.End R (M₁ ⊗[R] M₂) := (toEnd R L M₂ x - χ₂ • ↑1).lTensor M₁
  have h_comm_square : F ∘ₗ ↑g = (g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp (f₁ + f₂) := by
    ext m₁ m₂;
    simp only [f₁, f₂, F, ← g.map_lie x (m₁ ⊗ₜ m₂), add_smul, sub_tmul, tmul_sub, smul_tmul,
      lie_tmul_right, tmul_smul, toEnd_apply_apply, LieModuleHom.map_smul,
      LinearMap.one_apply, LieModuleHom.coe_toLinearMap, LinearMap.smul_apply, Function.comp_apply,
      LinearMap.coe_comp, LinearMap.rTensor_tmul, LieModuleHom.map_add, LinearMap.add_apply,
      LieModuleHom.map_sub, LinearMap.sub_apply, LinearMap.lTensor_tmul,
      AlgebraTensorModule.curry_apply, TensorProduct.curry_apply, LinearMap.toFun_eq_coe,
      LinearMap.coe_restrictScalars]
    abel
  rsuffices ⟨k, hk⟩ : ∃ k : ℕ, ((f₁ + f₂) ^ k) (m₁ ⊗ₜ m₂) = 0
  · use k
    change (F ^ k) (g.toLinearMap (m₁ ⊗ₜ[R] m₂)) = 0
    rw [← LinearMap.comp_apply, LinearMap.commute_pow_left_of_commute h_comm_square,
      LinearMap.comp_apply, hk, LinearMap.map_zero]
  -- Unpack the information we have about `m₁`, `m₂`.
  simp only [Module.End.mem_maxGenEigenspace] at hm₁ hm₂
  obtain ⟨k₁, hk₁⟩ := hm₁
  obtain ⟨k₂, hk₂⟩ := hm₂
  have hf₁ : (f₁ ^ k₁) (m₁ ⊗ₜ m₂) = 0 := by
    simp only [f₁, hk₁, zero_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_pow]
  have hf₂ : (f₂ ^ k₂) (m₁ ⊗ₜ m₂) = 0 := by
    simp only [f₂, hk₂, tmul_zero, LinearMap.lTensor_tmul, LinearMap.lTensor_pow]
  -- It's now just an application of the binomial theorem.
  use k₁ + k₂ - 1
  have hf_comm : Commute f₁ f₂ := by
    ext m₁ m₂
    simp only [f₁, f₂, LinearMap.mul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      AlgebraTensorModule.curry_apply, LinearMap.toFun_eq_coe, LinearMap.lTensor_tmul,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars]
  rw [hf_comm.add_pow']
  simp only [TensorProduct.mapIncl, Submodule.subtype_apply, Finset.sum_apply, Submodule.coe_mk,
    LinearMap.coeFn_sum, TensorProduct.map_tmul, LinearMap.smul_apply]
  -- The required sum is zero because each individual term is zero.
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  -- Eliminate the binomial coefficients from the picture.
  suffices (f₁ ^ i * f₂ ^ j) (m₁ ⊗ₜ m₂) = 0 by rw [this]; apply smul_zero
  -- Finish off with appropriate case analysis.
  cases' Nat.le_or_le_of_add_eq_add_pred (Finset.mem_antidiagonal.mp hij) with hi hj
  · rw [(hf_comm.pow_pow i j).eq, LinearMap.mul_apply, LinearMap.pow_map_zero_of_le hi hf₁,
      LinearMap.map_zero]
  · rw [LinearMap.mul_apply, LinearMap.pow_map_zero_of_le hj hf₂, LinearMap.map_zero]

lemma lie_mem_maxGenEigenspace_toEnd
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
      exact lie_mem_maxGenEigenspace_toEnd (by simp) hm }

end notation_weightSpaceOf

variable (M)

theorem mem_weightSpaceOf (χ : R) (x : L) (m : M) :
    m ∈ weightSpaceOf M χ x ↔ ∃ k : ℕ, ((toEnd R L M x - χ • ↑1) ^ k) m = 0 := by
  simp [weightSpaceOf]

theorem coe_weightSpaceOf_zero (x : L) :
    ↑(weightSpaceOf M (0 : R) x) = ⨆ k, LinearMap.ker (toEnd R L M x ^ k) := by
  simp [weightSpaceOf, Module.End.maxGenEigenspace]

/-- If `M` is a representation of a nilpotent Lie algebra `L` and `χ : L → R` is a family of
scalars, then `weightSpace M χ` is the intersection of the maximal generalized `χ x`-eigenspaces of
the action of `x` on `M` as `x` ranges over `L`.

It is a Lie submodule because `L` is nilpotent. -/
def weightSpace (χ : L → R) : LieSubmodule R L M :=
  ⨅ x, weightSpaceOf M (χ x) x

theorem mem_weightSpace (χ : L → R) (m : M) :
    m ∈ weightSpace M χ ↔ ∀ x, ∃ k : ℕ, ((toEnd R L M x - χ x • ↑1) ^ k) m = 0 := by
  simp [weightSpace, mem_weightSpaceOf]

lemma weightSpace_le_weightSpaceOf (x : L) (χ : L → R) :
    weightSpace M χ ≤ weightSpaceOf M (χ x) x :=
  iInf_le _ x

variable (R L) in
/-- A weight of a Lie module is a map `L → R` such that the corresponding weight space is
non-trivial. -/
structure Weight where
  /-- The family of eigenvalues corresponding to a weight. -/
  toFun : L → R
  weightSpace_ne_bot' : weightSpace M toFun ≠ ⊥

namespace Weight

instance instFunLike : FunLike (Weight R L M) L R where
  coe χ := χ.1
  coe_injective' χ₁ χ₂ h := by cases χ₁; cases χ₂; simp_all

@[simp] lemma coe_weight_mk (χ : L → R) (h) :
    (↑(⟨χ, h⟩ : Weight R L M) : L → R) = χ :=
  rfl

lemma weightSpace_ne_bot (χ : Weight R L M) : weightSpace M χ ≠ ⊥ := χ.weightSpace_ne_bot'

variable {M}

@[ext] lemma ext {χ₁ χ₂ : Weight R L M} (h : ∀ x, χ₁ x = χ₂ x) : χ₁ = χ₂ := by
  cases' χ₁ with f₁ _; cases' χ₂ with f₂ _; aesop

lemma ext_iff {χ₁ χ₂ : Weight R L M} : (χ₁ : L → R) = χ₂ ↔ χ₁ = χ₂ := by aesop

lemma exists_ne_zero (χ : Weight R L M) :
    ∃ x ∈ weightSpace M χ, x ≠ 0 := by
  simpa [LieSubmodule.eq_bot_iff] using χ.weightSpace_ne_bot

instance [Subsingleton M] : IsEmpty (Weight R L M) :=
  ⟨fun h ↦ h.2 (Subsingleton.elim _ _)⟩

instance [Nontrivial (weightSpace M (0 : L → R))] : Zero (Weight R L M) :=
  ⟨0, fun e ↦ not_nontrivial (⊥ : LieSubmodule R L M) (e ▸ ‹_›)⟩

@[simp]
lemma coe_zero [Nontrivial (weightSpace M (0 : L → R))] : ((0 : Weight R L M) : L → R) = 0 := rfl

lemma zero_apply [Nontrivial (weightSpace M (0 : L → R))] (x) : (0 : Weight R L M) x = 0 := rfl

/-- The proposition that a weight of a Lie module is zero.

We make this definition because we cannot define a `Zero (Weight R L M)` instance since the weight
space of the zero function can be trivial. -/
def IsZero (χ : Weight R L M) := (χ : L → R) = 0

@[simp] lemma IsZero.eq {χ : Weight R L M} (hχ : χ.IsZero) : (χ : L → R) = 0 := hχ

@[simp] lemma coe_eq_zero_iff (χ : Weight R L M) : (χ : L → R) = 0 ↔ χ.IsZero := Iff.rfl

lemma isZero_iff_eq_zero [Nontrivial (weightSpace M (0 : L → R))] {χ : Weight R L M} :
    χ.IsZero ↔ χ = 0 := ext_iff (χ₂ := 0)

lemma isZero_zero [Nontrivial (weightSpace M (0 : L → R))] : IsZero (0 : Weight R L M) := rfl

/-- The proposition that a weight of a Lie module is non-zero. -/
abbrev IsNonZero (χ : Weight R L M) := ¬ IsZero (χ : Weight R L M)

lemma isNonZero_iff_ne_zero [Nontrivial (weightSpace M (0 : L → R))] {χ : Weight R L M} :
    χ.IsNonZero ↔ χ ≠ 0 := isZero_iff_eq_zero.not

variable (R L M) in
/-- The set of weights is equivalent to a subtype. -/
def equivSetOf : Weight R L M ≃ {χ : L → R | weightSpace M χ ≠ ⊥} where
  toFun w := ⟨w.1, w.2⟩
  invFun w := ⟨w.1, w.2⟩
  left_inv w := by simp
  right_inv w := by simp

lemma weightSpaceOf_ne_bot (χ : Weight R L M) (x : L) :
    weightSpaceOf M (χ x) x ≠ ⊥ := by
  have : ⨅ x, weightSpaceOf M (χ x) x ≠ ⊥ := χ.weightSpace_ne_bot
  contrapose! this
  rw [eq_bot_iff]
  exact le_of_le_of_eq (iInf_le _ _) this

lemma hasEigenvalueAt (χ : Weight R L M) (x : L) :
    (toEnd R L M x).HasEigenvalue (χ x) := by
  obtain ⟨k : ℕ, hk : (toEnd R L M x).genEigenspace (χ x) k ≠ ⊥⟩ := by
    simpa [Module.End.maxGenEigenspace, weightSpaceOf] using χ.weightSpaceOf_ne_bot x
  exact Module.End.hasEigenvalue_of_hasGenEigenvalue hk

lemma apply_eq_zero_of_isNilpotent [NoZeroSMulDivisors R M] [IsReduced R]
    (x : L) (h : _root_.IsNilpotent (toEnd R L M x)) (χ : Weight R L M) :
    χ x = 0 :=
  ((χ.hasEigenvalueAt x).isNilpotent_of_isNilpotent h).eq_zero

end Weight

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
    LieSubalgebra.toEnd_mk, LieSubalgebra.mem_top, LieSubmodule.mem_top, iff_true]
  intro x
  obtain ⟨k, hk⟩ := exists_forall_pow_toEnd_eq_zero R L M
  exact ⟨k, by simp [hk x]⟩
#align lie_module.zero_weight_space_eq_top_of_nilpotent LieModule.zero_weightSpace_eq_top_of_nilpotent

theorem exists_weightSpace_le_ker_of_isNoetherian [IsNoetherian R M] (χ : L → R) (x : L) :
    ∃ k : ℕ,
      weightSpace M χ ≤ LinearMap.ker ((toEnd R L M x - algebraMap R _ (χ x)) ^ k) := by
  use (toEnd R L M x).maxGenEigenspaceIndex (χ x)
  intro m hm
  replace hm : m ∈ (toEnd R L M x).maxGenEigenspace (χ x) :=
    weightSpace_le_weightSpaceOf M x χ hm
  rwa [Module.End.maxGenEigenspace_eq] at hm

variable (R) in
theorem exists_weightSpace_zero_le_ker_of_isNoetherian
    [IsNoetherian R M] (x : L) :
    ∃ k : ℕ, weightSpace M (0 : L → R) ≤ LinearMap.ker (toEnd R L M x ^ k) := by
  simpa using exists_weightSpace_le_ker_of_isNoetherian M (0 : L → R) x

lemma isNilpotent_toEnd_sub_algebraMap [IsNoetherian R M] (χ : L → R) (x : L) :
    _root_.IsNilpotent <| toEnd R L (weightSpace M χ) x - algebraMap R _ (χ x) := by
  have : toEnd R L (weightSpace M χ) x - algebraMap R _ (χ x) =
      (toEnd R L M x - algebraMap R _ (χ x)).restrict
        (fun m hm ↦ sub_mem (LieSubmodule.lie_mem _ hm) (Submodule.smul_mem _ _ hm)) := by
    rfl
  obtain ⟨k, hk⟩ := exists_weightSpace_le_ker_of_isNoetherian M χ x
  use k
  ext ⟨m, hm⟩
  simpa [this, LinearMap.pow_restrict _, LinearMap.restrict_apply] using hk hm

/-- A (nilpotent) Lie algebra acts nilpotently on the zero weight space of a Noetherian Lie
module. -/
theorem isNilpotent_toEnd_weightSpace_zero [IsNoetherian R M] (x : L) :
    _root_.IsNilpotent <| toEnd R L (weightSpace M (0 : L → R)) x := by
  simpa using isNilpotent_toEnd_sub_algebraMap M (0 : L → R) x
#align lie_module.is_nilpotent_to_endomorphism_weight_space_zero LieModule.isNilpotent_toEnd_weightSpace_zero

/-- By Engel's theorem, the zero weight space of a Noetherian Lie module is nilpotent. -/
instance [IsNoetherian R M] :
    IsNilpotent R L (weightSpace M (0 : L → R)) :=
  isNilpotent_iff_forall'.mpr <| isNilpotent_toEnd_weightSpace_zero M

variable (R L)

@[simp]
lemma weightSpace_zero_normalizer_eq_self :
    (weightSpace M (0 : L → R)).normalizer = weightSpace M 0 := by
  refine le_antisymm ?_ (LieSubmodule.le_normalizer _)
  intro m hm
  rw [LieSubmodule.mem_normalizer] at hm
  simp only [mem_weightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm ⊢
  intro y
  obtain ⟨k, hk⟩ := hm y y
  use k + 1
  simpa [pow_succ, LinearMap.mul_eq_comp]

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
`range φₓ ⊇ range φₓ² ⊇ range φₓ³ ⊇ ⋯` where `φₓ : End R M := toEnd R L M x`. We call this
the "positive Fitting component" because with appropriate assumptions (e.g., `R` is a field and
`M` is finite-dimensional) `φₓ` induces the so-called Fitting decomposition: `M = M₀ ⊕ M₁` where
`M₀ = weightSpaceOf M 0 x` and `M₁ = posFittingCompOf R M x`.

It is a Lie submodule because `L` is nilpotent. -/
def posFittingCompOf (x : L) : LieSubmodule R L M :=
  { toSubmodule := ⨅ k, LinearMap.range (toEnd R L M x ^ k)
    lie_mem := by
      set φ := toEnd R L M x
      intros y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Submodule.mem_iInf, LinearMap.mem_range] at hm ⊢
      intro k
      obtain ⟨N, hN⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra R L
      obtain ⟨m, rfl⟩ := hm (N + k)
      let f₁ : Module.End R (L ⊗[R] M) := (LieAlgebra.ad R L x).rTensor M
      let f₂ : Module.End R (L ⊗[R] M) := φ.lTensor L
      replace hN : f₁ ^ N = 0 := by ext; simp [f₁, hN]
      have h₁ : Commute f₁ f₂ := by ext; simp [f₁, f₂]
      have h₂ : φ ∘ₗ toModuleHom R L M = toModuleHom R L M ∘ₗ (f₁ + f₂) := by ext; simp [φ, f₁, f₂]
      obtain ⟨q, hq⟩ := h₁.add_pow_dvd_pow_of_pow_eq_zero_right (N + k).le_succ hN
      use toModuleHom R L M (q (y ⊗ₜ m))
      change (φ ^ k).comp ((toModuleHom R L M : L ⊗[R] M →ₗ[R] M)) _ = _
      simp [φ,  f₁, f₂, LinearMap.commute_pow_left_of_commute h₂,
        LinearMap.comp_apply (g := (f₁ + f₂) ^ k), ← LinearMap.comp_apply (g := q),
        ← LinearMap.mul_eq_comp, ← hq] }

variable {M} in
lemma mem_posFittingCompOf (x : L) (m : M) :
    m ∈ posFittingCompOf R M x ↔ ∀ (k : ℕ), ∃ n, (toEnd R L M x ^ k) n = m := by
  simp [posFittingCompOf]

@[simp] lemma posFittingCompOf_le_lowerCentralSeries (x : L) (k : ℕ) :
    posFittingCompOf R M x ≤ lowerCentralSeries R L M k := by
  suffices ∀ m l, (toEnd R L M x ^ l) m ∈ lowerCentralSeries R L M l by
    intro m hm
    obtain ⟨n, rfl⟩ := (mem_posFittingCompOf R x m).mp hm k
    exact this n k
  intro m l
  induction' l with l ih
  · simp
  simp only [lowerCentralSeries_succ, pow_succ', LinearMap.mul_apply]
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
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (toEnd R L M x).eventually_iInf_range_pow_eq
  use k
  ext ⟨m⟩
  set F := posFittingComp R L M
  replace hk : (toEnd R L M x ^ k) m ∈ F := by
    apply posFittingCompOf_le_posFittingComp R L M x
    simp_rw [← LieSubmodule.mem_coeSubmodule, posFittingCompOf, hk k (le_refl k)]
    apply LinearMap.mem_range_self
  suffices (toEnd R L (M ⧸ F) x ^ k) (LieSubmodule.Quotient.mk (N := F) m) =
    LieSubmodule.Quotient.mk (N := F) ((toEnd R L M x ^ k) m) by simpa [this]
  have := LinearMap.congr_fun (LinearMap.commute_pow_left_of_commute
    (LieSubmodule.Quotient.toEnd_comp_mk' F x) k) m
  simpa using this

@[simp] lemma posFittingComp_eq_bot_of_isNilpotent
    [IsNilpotent R L M] :
    posFittingComp R L M = ⊥ := by
  simp [posFittingComp]

section map_comap

variable {R L M}
variable
  {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
  {χ : L → R} (f : M →ₗ⁅R,L⁆ M₂)

lemma map_posFittingComp_le :
    (posFittingComp R L M).map f ≤ posFittingComp R L M₂ := by
  rw [posFittingComp, posFittingComp, LieSubmodule.map_iSup]
  refine iSup_mono fun y ↦ LieSubmodule.map_le_iff_le_comap.mpr fun m hm ↦ ?_
  simp only [mem_posFittingCompOf] at hm
  simp only [LieSubmodule.mem_comap, mem_posFittingCompOf]
  intro k
  obtain ⟨n, hn⟩ := hm k
  use f n
  rw [LieModule.toEnd_pow_apply_map, hn]

lemma map_weightSpace_le :
    (weightSpace M χ).map f ≤ weightSpace M₂ χ := by
  rw [LieSubmodule.map_le_iff_le_comap]
  intro m hm
  simp only [LieSubmodule.mem_comap, mem_weightSpace]
  intro x
  have : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f = f ∘ₗ (toEnd R L M x - χ x • ↑1) := by
    ext; simp
  obtain ⟨k, h⟩ := (mem_weightSpace _ _ _).mp hm x
  exact ⟨k, by simpa [h] using LinearMap.congr_fun (LinearMap.commute_pow_left_of_commute this k) m⟩

variable {f}

lemma comap_weightSpace_eq_of_injective (hf : Injective f) :
    (weightSpace M₂ χ).comap f = weightSpace M χ := by
  refine le_antisymm (fun m hm ↦ ?_) ?_
  · simp only [LieSubmodule.mem_comap, mem_weightSpace] at hm
    simp only [mem_weightSpace]
    intro x
    have h : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f =
             f ∘ₗ (toEnd R L M x - χ x • ↑1) := by ext; simp
    obtain ⟨k, hk⟩ := hm x
    use k
    suffices f (((toEnd R L M x - χ x • ↑1) ^ k) m) = 0 by
      rw [← f.map_zero] at this; exact hf this
    simpa [hk] using (LinearMap.congr_fun (LinearMap.commute_pow_left_of_commute h k) m).symm
  · rw [← LieSubmodule.map_le_iff_le_comap]
    exact map_weightSpace_le f

lemma map_weightSpace_eq_of_injective (hf : Injective f) :
    (weightSpace M χ).map f = weightSpace M₂ χ ⊓ f.range := by
  refine le_antisymm (le_inf_iff.mpr ⟨map_weightSpace_le f, LieSubmodule.map_le_range f⟩) ?_
  rintro - ⟨hm, ⟨m, rfl⟩⟩
  simp only [← comap_weightSpace_eq_of_injective hf, LieSubmodule.mem_map, LieSubmodule.mem_comap]
  exact ⟨m, hm, rfl⟩

lemma map_weightSpace_eq (e : M ≃ₗ⁅R,L⁆ M₂) :
    (weightSpace M χ).map e = weightSpace M₂ χ := by
  simp [map_weightSpace_eq_of_injective e.injective]

lemma map_posFittingComp_eq (e : M ≃ₗ⁅R,L⁆ M₂) :
    (posFittingComp R L M).map e = posFittingComp R L M₂ := by
  refine le_antisymm (map_posFittingComp_le _) ?_
  suffices posFittingComp R L M₂ = ((posFittingComp R L M₂).map (e.symm : M₂ →ₗ⁅R,L⁆ M)).map e by
    rw [this]
    exact LieSubmodule.map_mono (map_posFittingComp_le _)
  rw [← LieSubmodule.map_comp]
  convert LieSubmodule.map_id
  ext
  simp

lemma posFittingComp_map_incl_sup_of_codisjoint [IsNoetherian R M] [IsArtinian R M]
    {N₁ N₂ : LieSubmodule R L M} (h : Codisjoint N₁ N₂) :
    (posFittingComp R L N₁).map N₁.incl ⊔ (posFittingComp R L N₂).map N₂.incl =
    posFittingComp R L M := by
  obtain ⟨l, hl⟩ := Filter.eventually_atTop.mp <|
    (eventually_iInf_lowerCentralSeries_eq R L N₁).and <|
    (eventually_iInf_lowerCentralSeries_eq R L N₂).and
    (eventually_iInf_lowerCentralSeries_eq R L M)
  obtain ⟨hl₁, hl₂, hl₃⟩ := hl l (le_refl _)
  simp_rw [← iInf_lowerCentralSeries_eq_posFittingComp, hl₁, hl₂, hl₃,
    LieSubmodule.lowerCentralSeries_map_eq_lcs, ← LieSubmodule.lcs_sup, lowerCentralSeries,
    h.eq_top]

lemma weightSpace_weightSpaceOf_map_incl (x : L) (χ : L → R) :
    (weightSpace (weightSpaceOf M (χ x) x) χ).map (weightSpaceOf M (χ x) x).incl =
    weightSpace M χ := by
  simpa [map_weightSpace_eq_of_injective (weightSpaceOf M (χ x) x).injective_incl]
    using weightSpace_le_weightSpaceOf M x χ

end map_comap

section fitting_decomposition

variable [IsNoetherian R M] [IsArtinian R M]

lemma isCompl_weightSpaceOf_zero_posFittingCompOf (x : L) :
    IsCompl (weightSpaceOf M 0 x) (posFittingCompOf R M x) := by
  simpa only [isCompl_iff, codisjoint_iff, disjoint_iff, ← LieSubmodule.coe_toSubmodule_eq_iff,
    LieSubmodule.sup_coe_toSubmodule, LieSubmodule.inf_coe_toSubmodule,
    LieSubmodule.top_coeSubmodule, LieSubmodule.bot_coeSubmodule, coe_weightSpaceOf_zero] using
    (toEnd R L M x).isCompl_iSup_ker_pow_iInf_range_pow

/-- This lemma exists only to simplify the proof of
`LieModule.isCompl_weightSpace_zero_posFittingComp`. -/
private lemma isCompl_weightSpace_zero_posFittingComp_aux
    (h : ∀ N < (⊤ : LieSubmodule R L M), IsCompl (weightSpace N 0) (posFittingComp R L N)) :
    IsCompl (weightSpace M 0) (posFittingComp R L M) := by
  set M₀ := weightSpace M (0 : L → R)
  set M₁ := posFittingComp R L M
  rcases forall_or_exists_not (fun (x : L) ↦ weightSpaceOf M (0 : R) x = ⊤)
    with h | ⟨x, hx : weightSpaceOf M (0 : R) x ≠ ⊤⟩
  · suffices IsNilpotent R L M by simp [M₀, M₁, isCompl_top_bot]
    replace h : M₀ = ⊤ := by simpa [M₀, weightSpace]
    rw [← LieModule.isNilpotent_of_top_iff', ← h]
    infer_instance
  · set M₀ₓ := weightSpaceOf M (0 : R) x
    set M₁ₓ := posFittingCompOf R M x
    set M₀ₓ₀ := weightSpace M₀ₓ (0 : L → R)
    set M₀ₓ₁ := posFittingComp R L M₀ₓ
    have h₁ : IsCompl M₀ₓ M₁ₓ := isCompl_weightSpaceOf_zero_posFittingCompOf R L M x
    have h₂ : IsCompl M₀ₓ₀ M₀ₓ₁ := h M₀ₓ hx.lt_top
    have h₃ : M₀ₓ₀.map M₀ₓ.incl = M₀ := by
      rw [map_weightSpace_eq_of_injective M₀ₓ.injective_incl, inf_eq_left, LieSubmodule.range_incl]
      exact iInf_le _ x
    have h₄ : M₀ₓ₁.map M₀ₓ.incl ⊔ M₁ₓ = M₁ := by
      apply le_antisymm <| sup_le_iff.mpr
        ⟨map_posFittingComp_le _, posFittingCompOf_le_posFittingComp R L M x⟩
      rw [← posFittingComp_map_incl_sup_of_codisjoint h₁.codisjoint]
      exact sup_le_sup_left LieSubmodule.map_incl_le _
    rw [← h₃, ← h₄]
    apply Disjoint.isCompl_sup_right_of_isCompl_sup_left
    · rw [disjoint_iff, ← LieSubmodule.map_inf M₀ₓ.injective_incl, h₂.inf_eq_bot,
        LieSubmodule.map_bot]
    · rwa [← LieSubmodule.map_sup, h₂.sup_eq_top, LieModuleHom.map_top, LieSubmodule.range_incl]

/-- This is the Fitting decomposition of the Lie module `M`. -/
lemma isCompl_weightSpace_zero_posFittingComp :
    IsCompl (weightSpace M 0) (posFittingComp R L M) := by
  let P : LieSubmodule R L M → Prop := fun N ↦ IsCompl (weightSpace N 0) (posFittingComp R L N)
  suffices P ⊤ by
    let e := LieModuleEquiv.ofTop R L M
    rw [← map_weightSpace_eq e, ← map_posFittingComp_eq e]
    exact (LieSubmodule.orderIsoMapComap e).isCompl_iff.mp this
  refine (LieSubmodule.wellFounded_of_isArtinian R L M).induction (C := P) _ fun N hN ↦ ?_
  refine isCompl_weightSpace_zero_posFittingComp_aux R L N fun N' hN' ↦ ?_
  suffices IsCompl (weightSpace (N'.map N.incl) 0) (posFittingComp R L (N'.map N.incl)) by
    let e := LieSubmodule.equivMapOfInjective N' N.injective_incl
    rw [← map_weightSpace_eq e, ← map_posFittingComp_eq e] at this
    exact (LieSubmodule.orderIsoMapComap e).isCompl_iff.mpr this
  exact hN _ (LieSubmodule.map_incl_lt_iff_lt_top.mpr hN')

end fitting_decomposition

lemma disjoint_weightSpaceOf [NoZeroSMulDivisors R M] {x : L} {φ₁ φ₂ : R} (h : φ₁ ≠ φ₂) :
    Disjoint (weightSpaceOf M φ₁ x) (weightSpaceOf M φ₂ x) := by
  rw [LieSubmodule.disjoint_iff_coe_toSubmodule]
  exact Module.End.disjoint_iSup_genEigenspace _ h

lemma disjoint_weightSpace [NoZeroSMulDivisors R M] {χ₁ χ₂ : L → R} (h : χ₁ ≠ χ₂) :
    Disjoint (weightSpace M χ₁) (weightSpace M χ₂) := by
  obtain ⟨x, hx⟩ : ∃ x, χ₁ x ≠ χ₂ x := Function.ne_iff.mp h
  exact (disjoint_weightSpaceOf R L M hx).mono
    (weightSpace_le_weightSpaceOf M x χ₁) (weightSpace_le_weightSpaceOf M x χ₂)

lemma injOn_weightSpace [NoZeroSMulDivisors R M] :
    InjOn (fun (χ : L → R) ↦ weightSpace M χ) {χ | weightSpace M χ ≠ ⊥} := by
  rintro χ₁ _ χ₂ hχ₂ (hχ₁₂ : weightSpace M χ₁ = weightSpace M χ₂)
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_weightSpace R L M hχ₂

/-- Lie module weight spaces are independent.

See also `LieModule.independent_weightSpace'`. -/
lemma independent_weightSpace [NoZeroSMulDivisors R M] :
    CompleteLattice.Independent fun (χ : L → R) ↦ weightSpace M χ := by
  classical
  suffices ∀ χ (s : Finset (L → R)) (_ : χ ∉ s),
      Disjoint (weightSpace M χ) (s.sup fun (χ : L → R) ↦ weightSpace M χ) by
    simpa only [CompleteLattice.independent_iff_supIndep_of_injOn (injOn_weightSpace R L M),
      Finset.supIndep_iff_disjoint_erase] using fun s χ _ ↦ this _ _ (s.not_mem_erase χ)
  intro χ₁ s
  induction' s using Finset.induction_on with χ₂ s _ ih
  · simp
  intro hχ₁₂
  obtain ⟨hχ₁₂ : χ₁ ≠ χ₂, hχ₁ : χ₁ ∉ s⟩ := by rwa [Finset.mem_insert, not_or] at hχ₁₂
  specialize ih hχ₁
  rw [Finset.sup_insert, disjoint_iff, LieSubmodule.eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  simp only [SetLike.mem_coe, LieSubmodule.mem_coeSubmodule] at hx hx'
  suffices x ∈ weightSpace M χ₂ by
    rw [← LieSubmodule.mem_bot (R := R) (L := L), ← (disjoint_weightSpace R L M hχ₁₂).eq_bot]
    exact ⟨hx, this⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := (LieSubmodule.mem_sup _ _ _).mp hx'; clear hx'
  suffices ∀ l, ∃ (k : ℕ),
      ((toEnd R L M l - algebraMap R (Module.End R M) (χ₂ l)) ^ k) (y + z) ∈
      weightSpace M χ₁ ⊓ Finset.sup s fun χ ↦ weightSpace M χ by
    simpa only [ih.eq_bot, LieSubmodule.mem_bot, mem_weightSpace] using this
  intro l
  let g : Module.End R M := toEnd R L M l - algebraMap R (Module.End R M) (χ₂ l)
  obtain ⟨k, hk : (g ^ k) y = 0⟩ := (mem_weightSpace _ _ _).mp hy l
  refine ⟨k, (LieSubmodule.mem_inf _ _ _).mp ⟨?_, ?_⟩⟩
  · exact LieSubmodule.mapsTo_pow_toEnd_sub_algebraMap _ hx
  · rw [map_add, hk, zero_add]
    suffices (s.sup fun χ ↦ weightSpace M χ : Submodule R M).map (g ^ k) ≤
        s.sup fun χ ↦ weightSpace M χ by
      refine this (Submodule.mem_map_of_mem ?_)
      simp_rw [← LieSubmodule.mem_coeSubmodule, Finset.sup_eq_iSup,
        LieSubmodule.iSup_coe_toSubmodule, ← Finset.sup_eq_iSup] at hz
      exact hz
    simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup (ι := L → R), Submodule.map_iSup (ι := _ ∈ s),
      LieSubmodule.iSup_coe_toSubmodule]
    refine iSup₂_mono fun χ _ ↦ ?_
    rintro - ⟨u, hu, rfl⟩
    exact LieSubmodule.mapsTo_pow_toEnd_sub_algebraMap _ hu

lemma independent_weightSpace' [NoZeroSMulDivisors R M] :
    CompleteLattice.Independent fun χ : Weight R L M ↦ weightSpace M χ :=
  (independent_weightSpace R L M).comp <|
    Subtype.val_injective.comp (Weight.equivSetOf R L M).injective

lemma independent_weightSpaceOf [NoZeroSMulDivisors R M] (x : L) :
    CompleteLattice.Independent fun (χ : R) ↦ weightSpaceOf M χ x := by
  rw [LieSubmodule.independent_iff_coe_toSubmodule]
  exact (toEnd R L M x).independent_genEigenspace

lemma finite_weightSpaceOf_ne_bot [NoZeroSMulDivisors R M] [IsNoetherian R M] (x : L) :
    {χ : R | weightSpaceOf M χ x ≠ ⊥}.Finite :=
  CompleteLattice.WellFounded.finite_ne_bot_of_independent
    (LieSubmodule.wellFounded_of_noetherian R L M) (independent_weightSpaceOf R L M x)

lemma finite_weightSpace_ne_bot [NoZeroSMulDivisors R M] [IsNoetherian R M] :
    {χ : L → R | weightSpace M χ ≠ ⊥}.Finite :=
  CompleteLattice.WellFounded.finite_ne_bot_of_independent
    (LieSubmodule.wellFounded_of_noetherian R L M) (independent_weightSpace R L M)

instance Weight.instFinite [NoZeroSMulDivisors R M] [IsNoetherian R M] :
    Finite (Weight R L M) := by
  have : Finite {χ : L → R | weightSpace M χ ≠ ⊥} := finite_weightSpace_ne_bot R L M
  exact Finite.of_injective (equivSetOf R L M) (equivSetOf R L M).injective

noncomputable instance Weight.instFintype [NoZeroSMulDivisors R M] [IsNoetherian R M] :
    Fintype (Weight R L M) :=
  Fintype.ofFinite _

/-- A Lie module `M` of a Lie algebra `L` is triangularizable if the endomorhpism of `M` defined by
any `x : L` is triangularizable. -/
class IsTriangularizable : Prop :=
  iSup_eq_top : ∀ x, ⨆ φ, ⨆ k, (toEnd R L M x).genEigenspace φ k = ⊤

@[simp]
lemma iSup_weightSpaceOf_eq_top [IsTriangularizable R L M] (x : L) :
    ⨆ (φ : R), weightSpaceOf M φ x = ⊤ := by
  rw [← LieSubmodule.coe_toSubmodule_eq_iff, LieSubmodule.iSup_coe_toSubmodule,
    LieSubmodule.top_coeSubmodule]
  exact IsTriangularizable.iSup_eq_top x

open LinearMap FiniteDimensional in
@[simp]
lemma trace_toEnd_weightSpace [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R M] [Module.Finite R M] (χ : L → R) (x : L) :
    trace R _ (toEnd R L (weightSpace M χ) x) = finrank R (weightSpace M χ) • χ x := by
  suffices _root_.IsNilpotent ((toEnd R L (weightSpace M χ) x) - χ x • LinearMap.id) by
    replace this := (isNilpotent_trace_of_isNilpotent this).eq_zero
    rwa [map_sub, map_smul, trace_id, sub_eq_zero, smul_eq_mul, mul_comm,
      ← nsmul_eq_mul] at this
  rw [← Module.algebraMap_end_eq_smul_id]
  exact isNilpotent_toEnd_sub_algebraMap M χ x

section field

open FiniteDimensional

variable (K)
variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [LieAlgebra.IsNilpotent K L]
  [FiniteDimensional K M]

instance instIsTriangularizableOfIsAlgClosed [IsAlgClosed K] : IsTriangularizable K L M :=
  ⟨fun _ ↦ Module.End.iSup_genEigenspace_eq_top _⟩

instance (N : LieSubmodule K L M) [IsTriangularizable K L M] : IsTriangularizable K L N := by
  refine ⟨fun y ↦ ?_⟩
  rw [← N.toEnd_restrict_eq_toEnd y]
  exact Module.End.iSup_genEigenspace_restrict_eq_top _ (IsTriangularizable.iSup_eq_top y)

/-- For a triangularizable Lie module in finite dimensions, the weight spaces span the entire space.

See also `LieModule.iSup_weightSpace_eq_top'`. -/
lemma iSup_weightSpace_eq_top [IsTriangularizable K L M] :
    ⨆ χ : L → K, weightSpace M χ = ⊤ := by
  clear! R -- cf https://github.com/leanprover/lean4/issues/2452
  induction' h_dim : finrank K M using Nat.strong_induction_on with n ih generalizing M
  obtain h' | ⟨y : L, hy : ¬ ∃ φ, weightSpaceOf M φ y = ⊤⟩ :=
    forall_or_exists_not (fun (x : L) ↦ ∃ (φ : K), weightSpaceOf M φ x = ⊤)
  · choose χ hχ using h'
    replace hχ : weightSpace M χ = ⊤ := by simpa only [weightSpace, hχ] using iInf_top
    exact eq_top_iff.mpr <| hχ ▸ le_iSup (weightSpace M) χ
  · replace hy : ∀ φ, finrank K (weightSpaceOf M φ y) < n := fun φ ↦ by
      simp_rw [not_exists, ← lt_top_iff_ne_top] at hy; exact h_dim ▸ Submodule.finrank_lt (hy φ)
    replace ih : ∀ φ, ⨆ χ : L → K, weightSpace (weightSpaceOf M φ y) χ = ⊤ :=
      fun φ ↦ ih _ (hy φ) (weightSpaceOf M φ y) rfl
    replace ih : ∀ φ, ⨆ (χ : L → K) (_ : χ y = φ), weightSpace (weightSpaceOf M φ y) χ = ⊤ := by
      intro φ
      suffices ∀ χ : L → K, χ y ≠ φ → weightSpace (weightSpaceOf M φ y) χ = ⊥ by
        specialize ih φ; rw [iSup_split, biSup_congr this] at ih; simpa using ih
      intro χ hχ
      rw [eq_bot_iff, ← (weightSpaceOf M φ y).ker_incl, LieModuleHom.ker,
        ← LieSubmodule.map_le_iff_le_comap, map_weightSpace_eq_of_injective
        (weightSpaceOf M φ y).injective_incl, LieSubmodule.range_incl, ← disjoint_iff_inf_le]
      exact (disjoint_weightSpaceOf K L M hχ).mono_left (weightSpace_le_weightSpaceOf M y χ)
    replace ih : ∀ φ, ⨆ (χ : L → K) (_ : χ y = φ), weightSpace M χ = weightSpaceOf M φ y := by
      intro φ
      have : ∀ (χ : L → K) (_ : χ y = φ), weightSpace M χ =
          (weightSpace (weightSpaceOf M φ y) χ).map (weightSpaceOf M φ y).incl := fun χ hχ ↦ by
        rw [← hχ, weightSpace_weightSpaceOf_map_incl]
      simp_rw [biSup_congr this, ← LieSubmodule.map_iSup, ih, LieModuleHom.map_top,
        LieSubmodule.range_incl]
    simpa only [← ih, iSup_comm (ι := K), iSup_iSup_eq_right] using
      iSup_weightSpaceOf_eq_top K L M y

lemma iSup_weightSpace_eq_top' [IsTriangularizable K L M] :
    ⨆ χ : Weight K L M, weightSpace M χ = ⊤ := by
  have := iSup_weightSpace_eq_top K L M
  erw [← iSup_ne_bot_subtype, ← (Weight.equivSetOf K L M).iSup_comp] at this
  exact this

end field

end LieModule
