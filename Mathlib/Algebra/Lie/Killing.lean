/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Semisimple
import Mathlib.Algebra.Lie.TraceForm

/-!
# Lie algebras with non-degenerate Killing forms.

In characteristic zero, the following three conditions are equivalent:
 1. The solvable radical of a Lie algebra is trivial
 2. A Lie algebra is a direct sum of its simple ideals
 3. A Lie algebra has non-degenerate Killing form

In positive characteristic, it is still true that 3 implies 2, and that 2 implies 1, but there are
counterexamples to the remaining implications. Thus condition 3 is the strongest assumption.
Furthermore, much of the Cartan-Killing classification of semisimple Lie algebras in characteristic
zero, continues to hold in positive characteristic (over a perfect field) if the Lie algebra has a
non-degenerate Killing form.

This file contains basic definitions and results for such Lie algebras.

## Main definitions
 * `LieAlgebra.IsKilling`: a typeclass encoding the fact that a Lie algebra has a non-singular
   Killing form.
 * `LieAlgebra.IsKilling.instHasTrivialRadical`: if a Lie algebra has non-singular Killing form
   then it has trivial radical.

## TODO

 * Prove that in characteristic zero, a semisimple Lie algebra has non-singular Killing form.

-/

variable (R K L M : Type*) [CommRing R] [Field K] [LieRing L] [LieAlgebra R L] [LieAlgebra K L]

namespace LieAlgebra

/-- We say a Lie algebra is Killing if its Killing form is non-singular.

NB: This is not standard terminology (the literature does not seem to name Lie algebras with this
property). -/
class IsKilling : Prop :=
  /-- We say a Lie algebra is Killing if its Killing form is non-singular. -/
  killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥

attribute [simp] IsKilling.killingCompl_top_eq_bot

namespace IsKilling

variable [Module.Free R L] [Module.Finite R L] [IsKilling R L]

@[simp] lemma ker_killingForm_eq_bot :
    LinearMap.ker (killingForm R L) = ⊥ := by
  simp [← LieIdeal.coe_killingCompl_top, killingCompl_top_eq_bot]

lemma killingForm_nondegenerate :
    (killingForm R L).Nondegenerate := by
  simp [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]

/-- The converse of this is true over a field of characteristic zero. There are counterexamples
over fields with positive characteristic. -/
instance instHasTrivialRadical [IsDomain R] [IsPrincipalIdealRing R] : HasTrivialRadical R L := by
  refine' (hasTrivialRadical_iff_no_abelian_ideals R L).mpr fun I hI ↦ _
  rw [eq_bot_iff, ← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian

end IsKilling

section LieEquiv

variable {R L}
variable {L' : Type*} [LieRing L'] [LieAlgebra R L']

/-- Given an equivalence `e` of Lie algebras from `L` to `L'`, and elements `x y : L`, the
respective Killing forms of `L` and `L'` satisfy `κ'(e x, e y) = κ(x, y)`. -/
@[simp] lemma killingForm_of_equiv_apply (e : L ≃ₗ⁅R⁆ L') (x y : L) :
    killingForm R L' (e x) (e y) = killingForm R L x y := by
  simp_rw [killingForm_apply_apply, ← LieAlgebra.conj_ad_apply, ← LinearEquiv.conj_comp,
    LinearMap.trace_conj']

/-- Given a Killing Lie algebra `L`, if `L'` is isomorphic to `L`, then `L'` is Killing too. -/
lemma isKilling_of_equiv [IsKilling R L] (e : L ≃ₗ⁅R⁆ L') : IsKilling R L' := by
  constructor
  ext x'
  simp_rw [LieIdeal.mem_killingCompl, LieModule.traceForm_comm]
  refine ⟨fun hx' ↦ ?_, fun hx y _ ↦ hx ▸ LinearMap.map_zero₂ (killingForm R L') y⟩
  suffices e.symm x' ∈ LinearMap.ker (killingForm R L) by
    rw [IsKilling.ker_killingForm_eq_bot] at this
    simpa using (e : L ≃ₗ[R] L').congr_arg this
  ext y
  replace hx' : ∀ y', killingForm R L' x' y' = 0 := by simpa using hx'
  specialize hx' (e y)
  rwa [← e.apply_symm_apply x', killingForm_of_equiv_apply] at hx'

alias _root_.LieEquiv.isKilling := LieAlgebra.isKilling_of_equiv

end LieEquiv

section IsSemisimple

/-!
We follow the short and excellent paper

    Dieudonné, Jean (1953), "On semi-simple Lie algebras",
    Proceedings of the American Mathematical Society, 4 (6): 931–932,
    doi:10.2307/2031832, ISSN 0002-9939, JSTOR 2031832, MR 0059262

-/

variable {R K L M}

section ring

variable (hL : ∀ I : LieIdeal R L, IsAtom I → ¬IsLieAbelian I)
variable (Φ : LinearMap.BilinForm R L) (hΦ_inv : ∀ x y z, Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆)
variable (hΦ_nondeg : Φ.Nondegenerate)

-- move this to `Mathlib.Algebra.Lie.Abelian`
lemma perfect_of_isAtom (I : LieIdeal R L) (hI : IsAtom I) : ⁅I, I⁆ = I := by
  rw [← hI.le_iff_eq]
  · exact LieSubmodule.lie_le_right I I
  · intro h
    rw [LieSubmodule.lie_eq_bot_iff] at h
    apply hL I hI
    constructor
    simpa only [LieIdeal.coe_bracket_of_module, Subtype.ext_iff, LieSubmodule.coe_bracket,
      ZeroMemClass.coe_zero, Subtype.forall, LieSubmodule.mem_coeSubmodule] using h

-- move this to `Mathlib.Algebra.Lie.TraceForm`?
@[simps!]
def orthogonalLieIdeal (I : LieIdeal R L) : LieIdeal R L where
  __ := Φ.orthogonal I
  lie_mem {x y} := by
    suffices (∀ n ∈ I, Φ n y = 0) → ∀ n ∈ I, Φ n ⁅x, y⁆ = 0 by
      simpa only [LinearMap.BilinForm.isOrtho_def, -- and some default simp lemmas
        LieIdeal.coe_to_lieSubalgebra_to_submodule, AddSubsemigroup.mem_carrier,
        AddSubmonoid.mem_toSubsemigroup, Submodule.mem_toAddSubmonoid,
        LinearMap.BilinForm.mem_orthogonal_iff, LieSubmodule.mem_coeSubmodule]
    intro H a ha
    rw [← hΦ_inv]
    apply H
    apply lie_mem_left
    apply ha

-- move this to `Mathlib.Algebra.Lie.TraceForm`?
@[simp]
lemma orthogonalLieIdeal_toSubmodule (I : LieIdeal R L) :
    (orthogonalLieIdeal Φ hΦ_inv I).toSubmodule = Φ.orthogonal I.toSubmodule := rfl

-- move this to `Mathlib.Algebra.Lie.TraceForm`?
lemma mem_orthogonalLieIdeal (I : LieIdeal R L) (x : L) :
    x ∈ orthogonalLieIdeal Φ hΦ_inv I ↔ ∀ n ∈ I, Φ n x = 0 := by
  simp [orthogonalLieIdeal, LinearMap.BilinForm.isOrtho_def, LinearMap.BilinForm.mem_orthogonal_iff]

lemma orthogonalLieIdeal_disjoint (I : LieIdeal R L) (hI : IsAtom I) :
    Disjoint I (orthogonalLieIdeal  Φ hΦ_inv I) := by
  rw [disjoint_iff, ← hI.lt_iff, lt_iff_le_and_ne]
  suffices ¬I ≤ orthogonalLieIdeal  Φ hΦ_inv I by
    simpa only [inf_le_left, ne_eq, inf_eq_left, true_and]
  intro contra
  apply hI.1
  rw [eq_bot_iff, ← perfect_of_isAtom hL I hI,
      LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [LieSubmodule.bot_coe, Set.mem_singleton_iff]
  apply hΦ_nondeg
  intro z
  rw [hΦ_inv]
  have hyz : ⁅(y : L), z⁆ ∈ I := lie_mem_left _ _ _ _ _ y.2
  exact contra hyz x x.2

end ring

section field

-- move this
open FiniteDimensional Submodule in
lemma exists_atom_le_of_finite
    [AddCommGroup M] [Module K M] [Module.Finite K M] [LieRingModule L M] :
    ∀ (N : LieSubmodule K L M), N ≠ ⊥ → ∃ a : LieSubmodule K L M, IsAtom a ∧ a ≤ N := by
  intro N hN
  by_cases H : ∀ b, b < N → b = ⊥
  · exact ⟨N, ⟨hN, H⟩, le_rfl⟩
  push_neg at H
  obtain ⟨b, hbN, hb⟩ := H
  obtain ⟨a, ha, hab⟩ := exists_atom_le_of_finite b hb
  exact ⟨a, ha, hab.trans hbN.le⟩
termination_by N => finrank K N
decreasing_by exact finrank_lt_finrank_of_lt hbN

-- move this
instance [AddCommGroup M] [Module K M] [Module.Finite K M] [LieRingModule L M] :
    IsAtomic (LieSubmodule K L M) := by
  constructor
  intro N
  rw [or_iff_not_imp_left]
  exact exists_atom_le_of_finite N

variable [Module.Finite K L]
variable (hL : ∀ I : LieIdeal K L, IsAtom I → ¬IsLieAbelian I)
variable (Φ : LinearMap.BilinForm K L) (hΦ_inv : ∀ x y z, Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆)
variable (hΦ_nondeg : Φ.Nondegenerate) (hΦ_refl : Φ.IsRefl)

open FiniteDimensional Submodule in
lemma orthogonalLieIdeal_isCompl_submodule (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I.toSubmodule (orthogonalLieIdeal Φ hΦ_inv I).toSubmodule := by
  have := (orthogonalLieIdeal_disjoint hL Φ hΦ_inv hΦ_nondeg I hI).eq_bot
  apply_fun LieSubmodule.toSubmodule at this
  simp only [LieSubmodule.inf_coe_toSubmodule, LieSubmodule.bot_coeSubmodule,
    orthogonalLieIdeal_toSubmodule] at this ⊢
  refine IsCompl.of_eq this ?_
  apply (eq_top_of_finrank_eq <| (finrank_le _).antisymm _)
  conv_rhs => rw [← add_zero (finrank K _)]
  rw [← finrank_bot K L, ← this, finrank_sup_add_finrank_inf_eq]
  erw [LinearMap.BilinForm.finrank_add_finrank_orthogonal hΦ_refl (W := I)]
  exact le_self_add

-- move this
lemma _root_.LieSubmodule.toSubmodule_injective
    {R L M : Type*} [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M] :
    Function.Injective (LieSubmodule.toSubmodule : LieSubmodule R L M → Submodule R M) := by
  rintro ⟨I, hI⟩ ⟨J, hJ⟩ h
  congr

open FiniteDimensional Submodule in
lemma orthogonalLieIdeal_isCompl (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I (orthogonalLieIdeal Φ hΦ_inv I) := by
  apply IsCompl.of_eq
  · apply LieSubmodule.toSubmodule_injective
    simpa using (orthogonalLieIdeal_isCompl_submodule hL Φ hΦ_inv hΦ_nondeg hΦ_refl I hI).inf_eq_bot
  · apply LieSubmodule.toSubmodule_injective
    simpa using (orthogonalLieIdeal_isCompl_submodule hL Φ hΦ_inv hΦ_nondeg hΦ_refl I hI).sup_eq_top

lemma restrict_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict I).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  exact orthogonalLieIdeal_isCompl_submodule hL Φ hΦ_inv hΦ_nondeg hΦ_refl I hI

-- move this
open FiniteDimensional Submodule in
lemma _root_.LinearMap.BilinForm.orthogonal_top
    {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (hB₀ : B.IsRefl) (hB : B.Nondegenerate) :
    B.orthogonal ⊤ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  apply hB
  intro y
  exact hB₀ _ _ (hx y mem_top)

-- move this
open FiniteDimensional Submodule in
lemma _root_.LinearMap.BilinForm.finrank_orthogonal
    {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (hB₀ : B.IsRefl) (hB : B.Nondegenerate) (W : Submodule K V) :
    finrank K (B.orthogonal W) = finrank K V - finrank K W := by
  have := LinearMap.BilinForm.finrank_add_finrank_orthogonal hB₀ (W := W)
  rw [B.orthogonal_top hB₀ hB, inf_bot_eq, finrank_bot, add_zero] at this
  have : finrank K W ≤ finrank K V := finrank_le W
  omega

-- move this
open FiniteDimensional Submodule in
lemma _root_.LinearMap.BilinForm.orthogonal_orthogonal
    {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (hB₀ : B.IsRefl) (hB : B.Nondegenerate) (W : Submodule K V) :
    B.orthogonal (B.orthogonal W) = W := by
  apply (eq_of_le_of_finrank_le (LinearMap.BilinForm.le_orthogonal_orthogonal hB₀) _).symm
  simp only [B.finrank_orthogonal hB₀ hB]
  have : finrank K W ≤ finrank K V := finrank_le W
  omega

lemma restrict_orthogonal_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    LinearMap.BilinForm.Nondegenerate (Φ.restrict (orthogonalLieIdeal Φ hΦ_inv I)) := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  simp only [LieIdeal.coe_to_lieSubalgebra_to_submodule, orthogonalLieIdeal_toSubmodule,
    Φ.orthogonal_orthogonal hΦ_refl hΦ_nondeg]
  exact (orthogonalLieIdeal_isCompl_submodule hL Φ hΦ_inv hΦ_nondeg hΦ_refl I hI).symm

open FiniteDimensional Submodule in
lemma atomistic : ∀ I : LieIdeal K L, sSup {J : LieIdeal K L | IsAtom J ∧ J ≤ I} = I := by
  intro I
  apply le_antisymm
  · apply sSup_le
    rintro J ⟨-, hJ'⟩
    exact hJ'
  by_cases hI : I = ⊥
  · exact hI.le.trans bot_le
  obtain ⟨J, hJ, hJI⟩ := exists_atom_le_of_finite I hI
  let J' := orthogonalLieIdeal Φ hΦ_inv J
  suffices I ≤ J ⊔ (J' ⊓ I) by
    refine this.trans ?_
    apply sup_le
    · exact le_sSup ⟨hJ, hJI⟩
    rw [← atomistic (J' ⊓ I)]
    apply sSup_le_sSup
    simp only [le_inf_iff, Set.setOf_subset_setOf, and_imp]
    tauto
  suffices J ⊔ J' = ⊤ by rw [← sup_inf_assoc_of_le _ hJI, this, top_inf_eq]
  exact (orthogonalLieIdeal_isCompl hL Φ hΦ_inv hΦ_nondeg hΦ_refl J hJ).codisjoint.eq_top
termination_by I => finrank K I
decreasing_by
  apply finrank_lt_finrank_of_lt
  suffices ¬I ≤ J' by simpa
  intro hIJ'
  apply hJ.1
  rw [eq_bot_iff]
  exact orthogonalLieIdeal_disjoint hL Φ hΦ_inv hΦ_nondeg J hJ le_rfl (hJI.trans hIJ')

theorem isSemisimple_of_nondegenerate_invariant_form : IsSemisimple K L := by
  refine ⟨?_, ?_, hL⟩
  · simpa using atomistic hL Φ hΦ_inv hΦ_nondeg hΦ_refl ⊤
  intro J hJ
  sorry

end field

end IsSemisimple

end LieAlgebra
