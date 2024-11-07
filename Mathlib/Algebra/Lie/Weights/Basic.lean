/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Weights.Defs
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

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
  * `LieModule.independent_genWeightSpace`
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

namespace Weight

instance [Subsingleton M] : IsEmpty (Weight R L M) :=
  ⟨fun h ↦ h.2.choose_spec.1 (Subsingleton.elim _ _)⟩

instance [Nontrivial (weightSpace M (0 : L → R))] : Zero (Weight R L M) :=
  ⟨0, by simpa [mem_weightSpace, and_comm] using exists_ne (0 : weightSpace M (0 : L → R))⟩

@[simp]
lemma coe_zero [Nontrivial (weightSpace M (0 : L → R))] : ((0 : Weight R L M) : L → R) = 0 := rfl

lemma zero_apply [Nontrivial (weightSpace M (0 : L → R))] (x) : (0 : Weight R L M) x = 0 := rfl

lemma isZero_iff_eq_zero [Nontrivial (weightSpace M (0 : L → R))] {χ : Weight R L M} :
    χ.IsZero ↔ χ = 0 := Weight.ext_iff' (χ₂ := 0)

lemma isZero_zero [Nontrivial (weightSpace M (0 : L → R))] : IsZero (0 : Weight R L M) := rfl

/-- The proposition that a weight of a Lie module is non-zero. -/
abbrev IsNonZero (χ : Weight R L M) := ¬ IsZero (χ : Weight R L M)

lemma isNonZero_iff_ne_zero [Nontrivial (weightSpace M (0 : L → R))] {χ : Weight R L M} :
    χ.IsNonZero ↔ χ ≠ 0 := isZero_iff_eq_zero.not

noncomputable instance : DecidablePred (IsNonZero (R := R) (L := L) (M := M)) := Classical.decPred _

instance weightSpace_nontrivial (χ : Weight R L M) : Nontrivial (weightSpace M χ) := by
  obtain ⟨m, hm0, hm⟩ := χ.exists_lie_eq_smul'
  exact nontrivial_of_ne ⟨m, by simpa [mem_weightSpace] using hm⟩ 0 <| by simpa using hm0

lemma weightSpace_ne_bot (χ : Weight R L M) : weightSpace M χ ≠ ⊥ := by
  intro h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := exists_pair_ne (weightSpace M χ)
  rw [h] at hx hy
  simp_all

lemma hasEigenvalueAt (χ : Weight R L M) (x : L) :
    (toEnd R L M x).HasEigenvalue (χ x) := by
  obtain ⟨m, hm0, hm⟩ := χ.exists_lie_eq_smul'
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := m)
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  exact ⟨hm x, hm0⟩

lemma apply_eq_zero_of_isNilpotent [NoZeroSMulDivisors R M] [IsReduced R]
    (x : L) (h : _root_.IsNilpotent (toEnd R L M x)) (χ : Weight R L M) :
    χ x = 0 :=
  ((χ.hasEigenvalueAt x).isNilpotent_of_isNilpotent h).eq_zero

end Weight

theorem coe_weightSpace_of_top (χ : L → R) :
    (weightSpace M (χ ∘ (⊤ : LieSubalgebra R L).incl) : Submodule R M) = weightSpace M χ := by
  ext m
  simp only [mem_weightSpace, LieSubmodule.mem_coeSubmodule, Subtype.forall]
  apply forall_congr'
  simp

section map_comap

variable
  {M₁ M₂ : Type*}
  [AddCommGroup M₁] [Module R M₁] [LieRingModule L M₁] [LieModule R L M₁]
  [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
  {χ : L → R} (f : M₁ →ₗ⁅R,L⁆ M₂)

lemma map_weightSpace_le : (weightSpace M₁ χ).map f ≤ weightSpace M₂ χ := by
  rw [LieSubmodule.map_le_iff_le_comap]
  intro m hm
  rw [mem_weightSpace] at hm
  simp only [LieSubmodule.mem_comap, mem_weightSpace, ← f.map_lie, hm, f.map_smul, implies_true]

variable {f}

lemma comap_weightSpace_eq_of_injective (hf : Injective f) :
    (weightSpace M₂ χ).comap f = weightSpace M₁ χ := by
  refine le_antisymm (fun m hm ↦ ?_) ?_
  · simp only [LieSubmodule.mem_comap, mem_weightSpace] at hm
    simp only [mem_weightSpace]
    intro x
    apply hf
    simpa using hm x
  · rw [← LieSubmodule.map_le_iff_le_comap]
    exact map_weightSpace_le f

lemma map_weightSpace_eq_of_injective (hf : Injective f) :
    (weightSpace M₁ χ).map f = weightSpace M₂ χ ⊓ f.range := by
  refine le_antisymm (le_inf_iff.mpr ⟨map_weightSpace_le f, LieSubmodule.map_le_range f⟩) ?_
  rintro - ⟨hm, ⟨m, rfl⟩⟩
  simp only [← comap_weightSpace_eq_of_injective hf, LieSubmodule.mem_map,
    LieSubmodule.mem_comap]
  exact ⟨m, hm, rfl⟩

lemma map_weightSpace_eq (e : M ≃ₗ⁅R,L⁆ M₂) :
    (weightSpace M χ).map e = weightSpace M₂ χ := by
  simp [map_weightSpace_eq_of_injective e.injective]

end map_comap

variable (M) in
lemma disjoint_weightSpace [NoZeroSMulDivisors R M] {χ₁ χ₂ : L → R} (h : χ₁ ≠ χ₂) :
    Disjoint (weightSpace M χ₁) (weightSpace M χ₂) := by
  obtain ⟨x, hx⟩ : ∃ x, χ₁ x ≠ χ₂ x := Function.ne_iff.mp h
  apply Disjoint.of_orderEmbedding (LieSubmodule.toSubmodule_orderEmbedding R L M)
  have := (toEnd R L M x).disjoint_genEigenspace hx 1 1
  apply this.mono <;> apply iInf_le

variable (R L M) in
lemma injOn_weightSpace [NoZeroSMulDivisors R M] :
    InjOn (fun (χ : L → R) ↦ weightSpace M χ) {χ | weightSpace M χ ≠ ⊥} := by
  rintro χ₁ _ χ₂ hχ₂ (hχ₁₂ : weightSpace M χ₁ = weightSpace M χ₂)
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_weightSpace M hχ₂

instance (L' : LieSubalgebra R L) [IsTriangularizable R L M] : IsTriangularizable R L' M where
  maxGenEigenspace_eq_top x := IsTriangularizable.maxGenEigenspace_eq_top (x : L)

instance (I : LieIdeal R L) [IsTriangularizable R L M] : IsTriangularizable R I M where
  maxGenEigenspace_eq_top x := IsTriangularizable.maxGenEigenspace_eq_top (x : L)

instance [IsTriangularizable R L M] : IsTriangularizable R (LieModule.toEnd R L M).range M where
  maxGenEigenspace_eq_top := by
    rintro ⟨-, x, rfl⟩
    exact IsTriangularizable.maxGenEigenspace_eq_top x

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

end field

end LieModule
