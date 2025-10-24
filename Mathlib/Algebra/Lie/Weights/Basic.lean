/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Ring.Divisibility.Lemmas
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Engel
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Weight spaces of Lie modules of nilpotent Lie algebras

Just as a key tool when studying the behaviour of a linear operator is to decompose the space on
which it acts into a sum of (generalised) eigenspaces, a key tool when studying a representation `M`
of Lie algebra `L` is to decompose `M` into a sum of simultaneous eigenspaces of `x` as `x` ranges
over `L`. These simultaneous generalised eigenspaces are known as the weight spaces of `M`.

When `L` is nilpotent, it follows from the binomial theorem that weight spaces are Lie submodules.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `LieModule.genWeightSpaceOf`
  * `LieModule.genWeightSpace`
  * `LieModule.Weight`
  * `LieModule.posFittingCompOf`
  * `LieModule.posFittingComp`
  * `LieModule.iSup_ucs_eq_genWeightSpace_zero`
  * `LieModule.iInf_lowerCentralSeries_eq_posFittingComp`
  * `LieModule.isCompl_genWeightSpace_zero_posFittingComp`
  * `LieModule.iSupIndep_genWeightSpace`
  * `LieModule.iSup_genWeightSpace_eq_top`

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b)

## Tags

lie character, eigenvalue, eigenspace, weight, weight vector, root, root vector
-/

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

open Set Function TensorProduct LieModule

variable (M) in
/-- If `M` is a representation of a Lie algebra `L` and `χ : L → R` is a family of scalars,
then `weightSpace M χ` is the intersection of the `χ x`-eigenspaces
of the action of `x` on `M` as `x` ranges over `L`. -/
def weightSpace (χ : L → R) : LieSubmodule R L M where
  __ := ⨅ x : L, (toEnd R L M x).eigenspace (χ x)
  lie_mem {x m} hm := by simp_all [smul_comm (χ x)]

lemma mem_weightSpace (χ : L → R) (m : M) : m ∈ weightSpace M χ ↔ ∀ x, ⁅x, m⁆ = χ x • m := by
  simp [weightSpace]

section notation_genWeightSpaceOf

/-- Until we define `LieModule.genWeightSpaceOf`, it is useful to have some notation as follows: -/
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
    LieModuleHom.coe_toLinearMap, Function.comp_apply, exists_imp, Module.End.mem_maxGenEigenspace]
  rintro t rfl
  -- Set up some notation.
  let F : Module.End R M₃ := toEnd R L M₃ x - (χ₁ + χ₂) • ↑1
  -- The goal is linear in `t` so use induction to reduce to the case that `t` is a pure tensor.
  refine t.induction_on ?_ ?_ ?_
  · use 0; simp only [map_zero]
  swap
  · rintro t₁ t₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩; use max k₁ k₂
    simp only [map_add, Module.End.pow_map_zero_of_le (le_max_left k₁ k₂) hk₁,
      Module.End.pow_map_zero_of_le (le_max_right k₁ k₂) hk₂, add_zero]
  -- Now the main argument: pure tensors.
  rintro ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩
  change ∃ k, (F ^ k) ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃) (m₁ ⊗ₜ m₂)) = (0 : M₃)
  -- Eliminate `g` from the picture.
  let f₁ : Module.End R (M₁ ⊗[R] M₂) := (toEnd R L M₁ x - χ₁ • ↑1).rTensor M₂
  let f₂ : Module.End R (M₁ ⊗[R] M₂) := (toEnd R L M₂ x - χ₂ • ↑1).lTensor M₁
  have h_comm_square : F ∘ₗ ↑g = (g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp (f₁ + f₂) := by
    ext m₁ m₂
    simp only [f₁, f₂, F, ← g.map_lie x (m₁ ⊗ₜ m₂), add_smul, sub_tmul, tmul_sub, smul_tmul,
      lie_tmul_right, tmul_smul, toEnd_apply_apply, map_smul, Module.End.one_apply,
      LieModuleHom.coe_toLinearMap, LinearMap.smul_apply, Function.comp_apply, LinearMap.coe_comp,
      LinearMap.rTensor_tmul, map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply,
      LinearMap.lTensor_tmul, AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars]
    abel
  rsuffices ⟨k, hk⟩ : ∃ k : ℕ, ((f₁ + f₂) ^ k) (m₁ ⊗ₜ m₂) = 0
  · use k
    change (F ^ k) (g.toLinearMap (m₁ ⊗ₜ[R] m₂)) = 0
    rw [← LinearMap.comp_apply, Module.End.commute_pow_left_of_commute h_comm_square,
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
    simp only [f₁, f₂, Module.End.mul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      AlgebraTensorModule.curry_apply, LinearMap.lTensor_tmul, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars]
  rw [hf_comm.add_pow']
  simp only [Finset.sum_apply, LinearMap.coeFn_sum, LinearMap.smul_apply]
  -- The required sum is zero because each individual term is zero.
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  -- Eliminate the binomial coefficients from the picture.
  suffices (f₁ ^ i * f₂ ^ j) (m₁ ⊗ₜ m₂) = 0 by rw [this]; apply smul_zero
  -- Finish off with appropriate case analysis.
  rcases Nat.le_or_le_of_add_eq_add_pred (Finset.mem_antidiagonal.mp hij) with hi | hj
  · rw [(hf_comm.pow_pow i j).eq, Module.End.mul_apply, Module.End.pow_map_zero_of_le hi hf₁,
      LinearMap.map_zero]
  · rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le hj hf₂, LinearMap.map_zero]

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
`genWeightSpaceOf M χ x` is the maximal generalized `χ`-eigenspace of the action of `x` on `M`.

It is a Lie submodule because `L` is nilpotent. -/
def genWeightSpaceOf [LieRing.IsNilpotent L] (χ : R) (x : L) : LieSubmodule R L M :=
  { 𝕎(M, χ, x) with
    lie_mem := by
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid] at hm ⊢
      rw [← zero_add χ]
      exact lie_mem_maxGenEigenspace_toEnd (by simp) hm }

end notation_genWeightSpaceOf

variable (M)
variable [LieRing.IsNilpotent L]

theorem mem_genWeightSpaceOf (χ : R) (x : L) (m : M) :
    m ∈ genWeightSpaceOf M χ x ↔ ∃ k : ℕ, ((toEnd R L M x - χ • ↑1) ^ k) m = 0 := by
  simp [genWeightSpaceOf]

theorem coe_genWeightSpaceOf_zero (x : L) :
    ↑(genWeightSpaceOf M (0 : R) x) = ⨆ k, LinearMap.ker (toEnd R L M x ^ k) := by
  simp [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq]

/-- If `M` is a representation of a nilpotent Lie algebra `L`
and `χ : L → R` is a family of scalars,
then `genWeightSpace M χ` is the intersection of the maximal generalized `χ x`-eigenspaces
of the action of `x` on `M` as `x` ranges over `L`.

It is a Lie submodule because `L` is nilpotent. -/
def genWeightSpace (χ : L → R) : LieSubmodule R L M :=
  ⨅ x, genWeightSpaceOf M (χ x) x

theorem mem_genWeightSpace (χ : L → R) (m : M) :
    m ∈ genWeightSpace M χ ↔ ∀ x, ∃ k : ℕ, ((toEnd R L M x - χ x • ↑1) ^ k) m = 0 := by
  simp [genWeightSpace, mem_genWeightSpaceOf]

lemma genWeightSpace_le_genWeightSpaceOf (x : L) (χ : L → R) :
    genWeightSpace M χ ≤ genWeightSpaceOf M (χ x) x :=
  iInf_le _ x

lemma weightSpace_le_genWeightSpace (χ : L → R) :
    weightSpace M χ ≤ genWeightSpace M χ := by
  apply le_iInf
  intro x
  rw [← (LieSubmodule.toSubmodule_orderEmbedding R L M).le_iff_le]
  apply (iInf_le _ x).trans
  exact ((toEnd R L M x).genEigenspace (χ x)).monotone le_top

variable (R L) in
/-- A weight of a Lie module is a map `L → R` such that the corresponding weight space is
non-trivial. -/
structure Weight where
  /-- The family of eigenvalues corresponding to a weight. -/
  toFun : L → R
  genWeightSpace_ne_bot' : genWeightSpace M toFun ≠ ⊥

namespace Weight

instance instFunLike : FunLike (Weight R L M) L R where
  coe χ := χ.1
  coe_injective' χ₁ χ₂ h := by cases χ₁; cases χ₂; simp_all

@[simp] lemma coe_weight_mk (χ : L → R) (h) :
    (↑(⟨χ, h⟩ : Weight R L M) : L → R) = χ :=
  rfl

lemma genWeightSpace_ne_bot (χ : Weight R L M) : genWeightSpace M χ ≠ ⊥ := χ.genWeightSpace_ne_bot'

variable {M}

@[ext] lemma ext {χ₁ χ₂ : Weight R L M} (h : ∀ x, χ₁ x = χ₂ x) : χ₁ = χ₂ := by
  obtain ⟨f₁, _⟩ := χ₁; obtain ⟨f₂, _⟩ := χ₂; aesop

lemma ext_iff' {χ₁ χ₂ : Weight R L M} : (χ₁ : L → R) = χ₂ ↔ χ₁ = χ₂ := by simp

lemma exists_ne_zero (χ : Weight R L M) :
    ∃ x ∈ genWeightSpace M χ, x ≠ 0 := by
  simpa [LieSubmodule.eq_bot_iff] using χ.genWeightSpace_ne_bot

instance [Subsingleton M] : IsEmpty (Weight R L M) :=
  ⟨fun h ↦ h.2 (Subsingleton.elim _ _)⟩

instance [Nontrivial (genWeightSpace M (0 : L → R))] : Zero (Weight R L M) :=
  ⟨0, fun e ↦ not_nontrivial (⊥ : LieSubmodule R L M) (e ▸ ‹_›)⟩

@[simp]
lemma coe_zero [Nontrivial (genWeightSpace M (0 : L → R))] : ((0 : Weight R L M) : L → R) = 0 := rfl

lemma zero_apply [Nontrivial (genWeightSpace M (0 : L → R))] (x) : (0 : Weight R L M) x = 0 := rfl

/-- The proposition that a weight of a Lie module is zero.

We make this definition because we cannot define a `Zero (Weight R L M)` instance since the weight
space of the zero function can be trivial. -/
def IsZero (χ : Weight R L M) := (χ : L → R) = 0

@[simp] lemma IsZero.eq {χ : Weight R L M} (hχ : χ.IsZero) : (χ : L → R) = 0 := hχ

@[simp] lemma coe_eq_zero_iff (χ : Weight R L M) : (χ : L → R) = 0 ↔ χ.IsZero := Iff.rfl

lemma isZero_iff_eq_zero [Nontrivial (genWeightSpace M (0 : L → R))] {χ : Weight R L M} :
    χ.IsZero ↔ χ = 0 := Weight.ext_iff' (χ₂ := 0)

lemma isZero_zero [Nontrivial (genWeightSpace M (0 : L → R))] : IsZero (0 : Weight R L M) := rfl

/-- The proposition that a weight of a Lie module is non-zero. -/
abbrev IsNonZero (χ : Weight R L M) := ¬ IsZero (χ : Weight R L M)

lemma isNonZero_iff_ne_zero [Nontrivial (genWeightSpace M (0 : L → R))] {χ : Weight R L M} :
    χ.IsNonZero ↔ χ ≠ 0 := isZero_iff_eq_zero.not

noncomputable instance : DecidablePred (IsNonZero (R := R) (L := L) (M := M)) := Classical.decPred _

variable (R L M) in
/-- The set of weights is equivalent to a subtype. -/
def equivSetOf : Weight R L M ≃ {χ : L → R | genWeightSpace M χ ≠ ⊥} where
  toFun w := ⟨w.1, w.2⟩
  invFun w := ⟨w.1, w.2⟩
  left_inv w := by simp
  right_inv w := by simp

lemma genWeightSpaceOf_ne_bot (χ : Weight R L M) (x : L) :
    genWeightSpaceOf M (χ x) x ≠ ⊥ := by
  have : ⨅ x, genWeightSpaceOf M (χ x) x ≠ ⊥ := χ.genWeightSpace_ne_bot
  contrapose! this
  rw [eq_bot_iff]
  exact le_of_le_of_eq (iInf_le _ _) this

lemma hasEigenvalueAt (χ : Weight R L M) (x : L) :
    (toEnd R L M x).HasEigenvalue (χ x) := by
  obtain ⟨k : ℕ, hk : (toEnd R L M x).genEigenspace (χ x) k ≠ ⊥⟩ := by
    simpa [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq] using χ.genWeightSpaceOf_ne_bot x
  exact Module.End.hasEigenvalue_of_hasGenEigenvalue hk

lemma apply_eq_zero_of_isNilpotent [NoZeroSMulDivisors R M] [IsReduced R]
    (x : L) (h : _root_.IsNilpotent (toEnd R L M x)) (χ : Weight R L M) :
    χ x = 0 :=
  ((χ.hasEigenvalueAt x).isNilpotent_of_isNilpotent h).eq_zero

end Weight

/-- See also the more useful form `LieModule.zero_genWeightSpace_eq_top_of_nilpotent`. -/
@[simp]
theorem zero_genWeightSpace_eq_top_of_nilpotent' [IsNilpotent L M] :
    genWeightSpace M (0 : L → R) = ⊤ := by
  simp [genWeightSpace, genWeightSpaceOf]

theorem coe_genWeightSpace_of_top (χ : L → R) :
    (genWeightSpace M (χ ∘ (⊤ : LieSubalgebra R L).incl) : Submodule R M) = genWeightSpace M χ := by
  ext m
  simp only [mem_genWeightSpace, LieSubmodule.mem_toSubmodule, Subtype.forall]
  apply forall_congr'
  simp

@[simp]
theorem zero_genWeightSpace_eq_top_of_nilpotent [IsNilpotent L M] :
    genWeightSpace M (0 : (⊤ : LieSubalgebra R L) → R) = ⊤ := by
  simp_all

theorem exists_genWeightSpace_le_ker_of_isNoetherian [IsNoetherian R M] (χ : L → R) (x : L) :
    ∃ k : ℕ,
      genWeightSpace M χ ≤ LinearMap.ker ((toEnd R L M x - algebraMap R _ (χ x)) ^ k) := by
  use (toEnd R L M x).maxGenEigenspaceIndex (χ x)
  intro m hm
  replace hm : m ∈ (toEnd R L M x).maxGenEigenspace (χ x) :=
    genWeightSpace_le_genWeightSpaceOf M x χ hm
  rwa [Module.End.maxGenEigenspace_eq, Module.End.genEigenspace_nat] at hm

variable (R) in
theorem exists_genWeightSpace_zero_le_ker_of_isNoetherian
    [IsNoetherian R M] (x : L) :
    ∃ k : ℕ, genWeightSpace M (0 : L → R) ≤ LinearMap.ker (toEnd R L M x ^ k) := by
  simpa using exists_genWeightSpace_le_ker_of_isNoetherian M (0 : L → R) x

lemma isNilpotent_toEnd_sub_algebraMap [IsNoetherian R M] (χ : L → R) (x : L) :
    _root_.IsNilpotent <| toEnd R L (genWeightSpace M χ) x - algebraMap R _ (χ x) := by
  have : toEnd R L (genWeightSpace M χ) x - algebraMap R _ (χ x) =
      (toEnd R L M x - algebraMap R _ (χ x)).restrict
        (fun m hm ↦ sub_mem (LieSubmodule.lie_mem _ hm) (Submodule.smul_mem _ _ hm)) := by
    rfl
  obtain ⟨k, hk⟩ := exists_genWeightSpace_le_ker_of_isNoetherian M χ x
  use k
  ext ⟨m, hm⟩
  simp only [this, Module.End.pow_restrict _, LinearMap.zero_apply, ZeroMemClass.coe_zero,
    ZeroMemClass.coe_eq_zero]
  exact ZeroMemClass.coe_eq_zero.mp (hk hm)

/-- A (nilpotent) Lie algebra acts nilpotently on the zero weight space of a Noetherian Lie
module. -/
theorem isNilpotent_toEnd_genWeightSpace_zero [IsNoetherian R M] (x : L) :
    _root_.IsNilpotent <| toEnd R L (genWeightSpace M (0 : L → R)) x := by
  simpa using isNilpotent_toEnd_sub_algebraMap M (0 : L → R) x

/-- By Engel's theorem, the zero weight space of a Noetherian Lie module is nilpotent. -/
instance [IsNoetherian R M] :
    IsNilpotent L (genWeightSpace M (0 : L → R)) :=
  isNilpotent_iff_forall'.mpr <| isNilpotent_toEnd_genWeightSpace_zero M

variable (R L)

@[simp]
lemma genWeightSpace_zero_normalizer_eq_self :
    (genWeightSpace M (0 : L → R)).normalizer = genWeightSpace M 0 := by
  refine le_antisymm ?_ (LieSubmodule.le_normalizer _)
  intro m hm
  rw [LieSubmodule.mem_normalizer] at hm
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm ⊢
  intro y
  obtain ⟨k, hk⟩ := hm y y
  use k + 1
  simpa [pow_succ, Module.End.mul_eq_comp]

lemma iSup_ucs_le_genWeightSpace_zero :
    ⨆ k, (⊥ : LieSubmodule R L M).ucs k ≤ genWeightSpace M (0 : L → R) := by
  simpa using
    LieSubmodule.ucs_le_of_normalizer_eq_self (genWeightSpace_zero_normalizer_eq_self R L M)

/-- See also `LieModule.iInf_lowerCentralSeries_eq_posFittingComp`. -/
lemma iSup_ucs_eq_genWeightSpace_zero [IsNoetherian R M] :
    ⨆ k, (⊥ : LieSubmodule R L M).ucs k = genWeightSpace M (0 : L → R) := by
  obtain ⟨k, hk⟩ := (LieSubmodule.isNilpotent_iff_exists_self_le_ucs
    <| genWeightSpace M (0 : L → R)).mp inferInstance
  refine le_antisymm (iSup_ucs_le_genWeightSpace_zero R L M) (le_trans hk ?_)
  exact le_iSup (fun k ↦ (⊥ : LieSubmodule R L M).ucs k) k

variable {L}

/-- If `M` is a representation of a nilpotent Lie algebra `L`, and `x : L`, then
`posFittingCompOf R M x` is the infimum of the decreasing system
`range φₓ ⊇ range φₓ² ⊇ range φₓ³ ⊇ ⋯` where `φₓ : End R M := toEnd R L M x`. We call this
the "positive Fitting component" because with appropriate assumptions (e.g., `R` is a field and
`M` is finite-dimensional) `φₓ` induces the so-called Fitting decomposition: `M = M₀ ⊕ M₁` where
`M₀ = genWeightSpaceOf M 0 x` and `M₁ = posFittingCompOf R M x`.

It is a Lie submodule because `L` is nilpotent. -/
def posFittingCompOf (x : L) : LieSubmodule R L M :=
  { toSubmodule := ⨅ k, LinearMap.range (toEnd R L M x ^ k)
    lie_mem := by
      set φ := toEnd R L M x
      intro y m hm
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
      simp [φ, f₁, f₂, Module.End.commute_pow_left_of_commute h₂,
        LinearMap.comp_apply (g := (f₁ + f₂) ^ k), ← LinearMap.comp_apply (g := q),
        ← Module.End.mul_eq_comp, ← hq] }

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
  induction l with
  | zero => simp
  | succ l ih =>
    simp only [lowerCentralSeries_succ, pow_succ', Module.End.mul_apply]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ih

@[simp] lemma posFittingCompOf_eq_bot_of_isNilpotent
    [IsNilpotent L M] (x : L) :
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

/-- See also `LieModule.iSup_ucs_eq_genWeightSpace_zero`. -/
@[simp] lemma iInf_lowerCentralSeries_eq_posFittingComp
    [IsNoetherian R M] [IsArtinian R M] :
    ⨅ k, lowerCentralSeries R L M k = posFittingComp R L M := by
  refine le_antisymm ?_ (posFittingComp_le_iInf_lowerCentralSeries R L M)
  apply iInf_lcs_le_of_isNilpotent_quot
  rw [LieModule.isNilpotent_iff_forall' (R := R)]
  intro x
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (toEnd R L M x).eventually_iInf_range_pow_eq
  use k
  ext ⟨m⟩
  set F := posFittingComp R L M
  replace hk : (toEnd R L M x ^ k) m ∈ F := by
    apply posFittingCompOf_le_posFittingComp R L M x
    simp_rw [← LieSubmodule.mem_toSubmodule, posFittingCompOf, hk k (le_refl k)]
    apply LinearMap.mem_range_self
  suffices (toEnd R L (M ⧸ F) x ^ k) (LieSubmodule.Quotient.mk (N := F) m) =
    LieSubmodule.Quotient.mk (N := F) ((toEnd R L M x ^ k) m)
      by simpa [Submodule.Quotient.quot_mk_eq_mk, this]
  have := LinearMap.congr_fun (Module.End.commute_pow_left_of_commute
    (LieSubmodule.Quotient.toEnd_comp_mk' F x) k) m
  simpa using this

@[simp] lemma posFittingComp_eq_bot_of_isNilpotent
    [IsNilpotent L M] :
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

lemma map_genWeightSpace_le :
    (genWeightSpace M χ).map f ≤ genWeightSpace M₂ χ := by
  rw [LieSubmodule.map_le_iff_le_comap]
  intro m hm
  simp only [LieSubmodule.mem_comap, mem_genWeightSpace]
  intro x
  have : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f = f ∘ₗ (toEnd R L M x - χ x • ↑1) := by
    ext; simp
  obtain ⟨k, h⟩ := (mem_genWeightSpace _ _ _).mp hm x
  refine ⟨k, ?_⟩
  simpa [h] using LinearMap.congr_fun (Module.End.commute_pow_left_of_commute this k) m

variable {f}

lemma comap_genWeightSpace_eq_of_injective (hf : Injective f) :
    (genWeightSpace M₂ χ).comap f = genWeightSpace M χ := by
  refine le_antisymm (fun m hm ↦ ?_) ?_
  · simp only [LieSubmodule.mem_comap, mem_genWeightSpace] at hm
    simp only [mem_genWeightSpace]
    intro x
    have h : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f =
             f ∘ₗ (toEnd R L M x - χ x • ↑1) := by ext; simp
    obtain ⟨k, hk⟩ := hm x
    use k
    suffices f (((toEnd R L M x - χ x • ↑1) ^ k) m) = 0 by
      rw [← map_zero f] at this; exact hf this
    simpa [hk] using (LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h k) m).symm
  · rw [← LieSubmodule.map_le_iff_le_comap]
    exact map_genWeightSpace_le f

lemma map_genWeightSpace_eq_of_injective (hf : Injective f) :
    (genWeightSpace M χ).map f = genWeightSpace M₂ χ ⊓ f.range := by
  refine le_antisymm (le_inf_iff.mpr ⟨map_genWeightSpace_le f, LieSubmodule.map_le_range f⟩) ?_
  rintro - ⟨hm, ⟨m, rfl⟩⟩
  simp only [← comap_genWeightSpace_eq_of_injective hf, LieSubmodule.mem_map,
    LieSubmodule.mem_comap]
  exact ⟨m, hm, rfl⟩

lemma map_genWeightSpace_eq (e : M ≃ₗ⁅R,L⁆ M₂) :
    (genWeightSpace M χ).map e = genWeightSpace M₂ χ := by
  simp [map_genWeightSpace_eq_of_injective e.injective]

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

lemma genWeightSpace_genWeightSpaceOf_map_incl (x : L) (χ : L → R) :
    (genWeightSpace (genWeightSpaceOf M (χ x) x) χ).map (genWeightSpaceOf M (χ x) x).incl =
    genWeightSpace M χ := by
  simpa [map_genWeightSpace_eq_of_injective (genWeightSpaceOf M (χ x) x).injective_incl]
    using genWeightSpace_le_genWeightSpaceOf M x χ

end map_comap

section fitting_decomposition

variable [IsNoetherian R M] [IsArtinian R M]

lemma isCompl_genWeightSpaceOf_zero_posFittingCompOf (x : L) :
    IsCompl (genWeightSpaceOf M 0 x) (posFittingCompOf R M x) := by
  simpa only [isCompl_iff, codisjoint_iff, disjoint_iff, ← LieSubmodule.toSubmodule_inj,
    LieSubmodule.sup_toSubmodule, LieSubmodule.inf_toSubmodule,
    LieSubmodule.top_toSubmodule, LieSubmodule.bot_toSubmodule, coe_genWeightSpaceOf_zero] using
    (toEnd R L M x).isCompl_iSup_ker_pow_iInf_range_pow

/-- This lemma exists only to simplify the proof of
`LieModule.isCompl_genWeightSpace_zero_posFittingComp`. -/
private lemma isCompl_genWeightSpace_zero_posFittingComp_aux
    (h : ∀ N < (⊤ : LieSubmodule R L M), IsCompl (genWeightSpace N 0) (posFittingComp R L N)) :
    IsCompl (genWeightSpace M 0) (posFittingComp R L M) := by
  set M₀ := genWeightSpace M (0 : L → R)
  set M₁ := posFittingComp R L M
  rcases forall_or_exists_not (fun (x : L) ↦ genWeightSpaceOf M (0 : R) x = ⊤)
    with h | ⟨x, hx : genWeightSpaceOf M (0 : R) x ≠ ⊤⟩
  · suffices IsNilpotent L M by simp [M₀, M₁, isCompl_top_bot]
    replace h : M₀ = ⊤ := by simpa [M₀, genWeightSpace]
    rw [← LieModule.isNilpotent_of_top_iff' (R := R), ← h]
    infer_instance
  · set M₀ₓ := genWeightSpaceOf M (0 : R) x
    set M₁ₓ := posFittingCompOf R M x
    set M₀ₓ₀ := genWeightSpace M₀ₓ (0 : L → R)
    set M₀ₓ₁ := posFittingComp R L M₀ₓ
    have h₁ : IsCompl M₀ₓ M₁ₓ := isCompl_genWeightSpaceOf_zero_posFittingCompOf R L M x
    have h₂ : IsCompl M₀ₓ₀ M₀ₓ₁ := h M₀ₓ hx.lt_top
    have h₃ : M₀ₓ₀.map M₀ₓ.incl = M₀ := by
      rw [map_genWeightSpace_eq_of_injective M₀ₓ.injective_incl, inf_eq_left,
        LieSubmodule.range_incl]
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
lemma isCompl_genWeightSpace_zero_posFittingComp :
    IsCompl (genWeightSpace M 0) (posFittingComp R L M) := by
  let P : LieSubmodule R L M → Prop := fun N ↦ IsCompl (genWeightSpace N 0) (posFittingComp R L N)
  suffices P ⊤ by
    let e := LieModuleEquiv.ofTop R L M
    rw [← map_genWeightSpace_eq e, ← map_posFittingComp_eq e]
    exact (LieSubmodule.orderIsoMapComap e).isCompl_iff.mp this
  refine (LieSubmodule.wellFoundedLT_of_isArtinian R L M).induction (C := P) _ fun N hN ↦ ?_
  refine isCompl_genWeightSpace_zero_posFittingComp_aux R L N fun N' hN' ↦ ?_
  suffices IsCompl (genWeightSpace (N'.map N.incl) 0) (posFittingComp R L (N'.map N.incl)) by
    let e := LieSubmodule.equivMapOfInjective N' N.injective_incl
    rw [← map_genWeightSpace_eq e, ← map_posFittingComp_eq e] at this
    exact (LieSubmodule.orderIsoMapComap e).isCompl_iff.mpr this
  exact hN _ (LieSubmodule.map_incl_lt_iff_lt_top.mpr hN')

end fitting_decomposition

lemma disjoint_genWeightSpaceOf [NoZeroSMulDivisors R M] {x : L} {φ₁ φ₂ : R} (h : φ₁ ≠ φ₂) :
    Disjoint (genWeightSpaceOf M φ₁ x) (genWeightSpaceOf M φ₂ x) := by
  rw [← LieSubmodule.disjoint_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact Module.End.disjoint_genEigenspace _ h _ _

lemma disjoint_genWeightSpace [NoZeroSMulDivisors R M] {χ₁ χ₂ : L → R} (h : χ₁ ≠ χ₂) :
    Disjoint (genWeightSpace M χ₁) (genWeightSpace M χ₂) := by
  obtain ⟨x, hx⟩ : ∃ x, χ₁ x ≠ χ₂ x := Function.ne_iff.mp h
  exact (disjoint_genWeightSpaceOf R L M hx).mono
    (genWeightSpace_le_genWeightSpaceOf M x χ₁) (genWeightSpace_le_genWeightSpaceOf M x χ₂)

lemma injOn_genWeightSpace [NoZeroSMulDivisors R M] :
    InjOn (fun (χ : L → R) ↦ genWeightSpace M χ) {χ | genWeightSpace M χ ≠ ⊥} := by
  rintro χ₁ _ χ₂ hχ₂ (hχ₁₂ : genWeightSpace M χ₁ = genWeightSpace M χ₂)
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_genWeightSpace R L M hχ₂

/-- Lie module weight spaces are independent.

See also `LieModule.iSupIndep_genWeightSpace'`. -/
lemma iSupIndep_genWeightSpace [NoZeroSMulDivisors R M] :
    iSupIndep fun χ : L → R ↦ genWeightSpace M χ := by
  simp only [← LieSubmodule.iSupIndep_toSubmodule, genWeightSpace,
    LieSubmodule.iInf_toSubmodule]
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (toEnd R L M)
    (fun x y φ z ↦ (genWeightSpaceOf M φ y).lie_mem)

lemma iSupIndep_genWeightSpace' [NoZeroSMulDivisors R M] :
    iSupIndep fun χ : Weight R L M ↦ genWeightSpace M χ :=
  (iSupIndep_genWeightSpace R L M).comp <|
    Subtype.val_injective.comp (Weight.equivSetOf R L M).injective

lemma iSupIndep_genWeightSpaceOf [NoZeroSMulDivisors R M] (x : L) :
    iSupIndep fun (χ : R) ↦ genWeightSpaceOf M χ x := by
  rw [← LieSubmodule.iSupIndep_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact (toEnd R L M x).independent_genEigenspace _

lemma finite_genWeightSpaceOf_ne_bot [NoZeroSMulDivisors R M] [IsNoetherian R M] (x : L) :
    {χ : R | genWeightSpaceOf M χ x ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_genWeightSpaceOf R L M x)

lemma finite_genWeightSpace_ne_bot [NoZeroSMulDivisors R M] [IsNoetherian R M] :
    {χ : L → R | genWeightSpace M χ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_genWeightSpace R L M)

instance Weight.instFinite [NoZeroSMulDivisors R M] [IsNoetherian R M] :
    Finite (Weight R L M) := by
  have : Finite {χ : L → R | genWeightSpace M χ ≠ ⊥} := finite_genWeightSpace_ne_bot R L M
  exact Finite.of_injective (equivSetOf R L M) (equivSetOf R L M).injective

noncomputable instance Weight.instFintype [NoZeroSMulDivisors R M] [IsNoetherian R M] :
    Fintype (Weight R L M) :=
  Fintype.ofFinite _

/-- A Lie module `M` of a Lie algebra `L` is triangularizable if the endomorphism of `M` defined by
any `x : L` is triangularizable. -/
class IsTriangularizable : Prop where
  maxGenEigenspace_eq_top : ∀ x, ⨆ φ, (toEnd R L M x).maxGenEigenspace φ = ⊤

instance (L' : LieSubalgebra R L) [IsTriangularizable R L M] : IsTriangularizable R L' M where
  maxGenEigenspace_eq_top x := IsTriangularizable.maxGenEigenspace_eq_top (x : L)

instance (I : LieIdeal R L) [IsTriangularizable R L M] : IsTriangularizable R I M where
  maxGenEigenspace_eq_top x := IsTriangularizable.maxGenEigenspace_eq_top (x : L)

instance [IsTriangularizable R L M] : IsTriangularizable R (LieModule.toEnd R L M).range M where
  maxGenEigenspace_eq_top := by
    rintro ⟨-, x, rfl⟩
    exact IsTriangularizable.maxGenEigenspace_eq_top x

@[simp]
lemma iSup_genWeightSpaceOf_eq_top [IsTriangularizable R L M] (x : L) :
    ⨆ (φ : R), genWeightSpaceOf M φ x = ⊤ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.top_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact IsTriangularizable.maxGenEigenspace_eq_top x

open LinearMap Module in
@[simp]
lemma trace_toEnd_genWeightSpace [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R M] [Module.Finite R M] (χ : L → R) (x : L) :
    trace R _ (toEnd R L (genWeightSpace M χ) x) = finrank R (genWeightSpace M χ) • χ x := by
  suffices _root_.IsNilpotent ((toEnd R L (genWeightSpace M χ) x) - χ x • LinearMap.id) by
    replace this := (isNilpotent_trace_of_isNilpotent this).eq_zero
    rwa [map_sub, map_smul, trace_id, sub_eq_zero, smul_eq_mul, mul_comm,
      ← nsmul_eq_mul] at this
  rw [← Module.algebraMap_end_eq_smul_id]
  exact isNilpotent_toEnd_sub_algebraMap M χ x

section field

open Module

variable (K)
variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]

instance instIsTriangularizableOfIsAlgClosed [IsAlgClosed K] : IsTriangularizable K L M :=
  ⟨fun _ ↦ Module.End.iSup_maxGenEigenspace_eq_top _⟩

instance (N : LieSubmodule K L M) [IsTriangularizable K L M] : IsTriangularizable K L N := by
  refine ⟨fun y ↦ ?_⟩
  rw [← N.toEnd_restrict_eq_toEnd y]
  exact Module.End.genEigenspace_restrict_eq_top _ (IsTriangularizable.maxGenEigenspace_eq_top y)

/-- For a triangularizable Lie module in finite dimensions, the weight spaces span the entire space.

See also `LieModule.iSup_genWeightSpace_eq_top'`. -/
lemma iSup_genWeightSpace_eq_top [IsTriangularizable K L M] :
    ⨆ χ : L → K, genWeightSpace M χ = ⊤ := by
  simp only [← LieSubmodule.toSubmodule_inj, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.iInf_toSubmodule, LieSubmodule.top_toSubmodule, genWeightSpace]
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (toEnd K L M)
    (fun x y φ z ↦ (genWeightSpaceOf M φ y).lie_mem) ?_
  apply IsTriangularizable.maxGenEigenspace_eq_top

lemma iSup_genWeightSpace_eq_top' [IsTriangularizable K L M] :
    ⨆ χ : Weight K L M, genWeightSpace M χ = ⊤ := by
  have := iSup_genWeightSpace_eq_top K L M
  erw [← iSup_ne_bot_subtype, ← (Weight.equivSetOf K L M).iSup_comp] at this
  exact this

end field

end LieModule
