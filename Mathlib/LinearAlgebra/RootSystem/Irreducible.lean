/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.RepresentationTheory.Submodule

/-!
# Irreducible root pairings

This file contains basic definitions and results about irreducible root systems.

## Main definitions / results:
* `RootPairing.isSimpleModule_weylGroupRootRep_iff`: a criterion for the representation of the Weyl
  group on root space to be irreducible.
* `RootPairing.IsIrreducible`: a typeclass encoding the fact that a root pairing is irreducible.
* `RootPairing.IsIrreducible.mk'`: an alternative constructor for irreducibility when the
  coefficients are a field.

-/

open Function Set
open Submodule (span span_le)
open LinearMap (ker)
open MulAction (orbit mem_orbit_self mem_orbit_iff)
open Module.End (invtSubmodule)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

namespace RootPairing

/-- The sublattice of invariant submodules of the root space. -/
def invtRootSubmodule : Sublattice (Submodule R M) :=
  ⨅ i, invtSubmodule (P.reflection i)

lemma mem_invtRootSubmodule_iff {q : Submodule R M} :
    q ∈ P.invtRootSubmodule ↔ ∀ i, q ∈ Module.End.invtSubmodule (P.reflection i) := by
  simp [invtRootSubmodule]

@[simp] protected lemma invtRootSubmodule.top_mem : ⊤ ∈ P.invtRootSubmodule := by
  simp [invtRootSubmodule]

@[simp] protected lemma invtRootSubmodule.bot_mem : ⊥ ∈ P.invtRootSubmodule := by
  simp [invtRootSubmodule]

instance : BoundedOrder P.invtRootSubmodule where
  top := ⟨⊤, invtRootSubmodule.top_mem P⟩
  bot := ⟨⊥, invtRootSubmodule.bot_mem P⟩
  le_top := fun ⟨p, hp⟩ ↦ by simp
  bot_le := fun ⟨p, hp⟩ ↦ by simp

instance [Nontrivial M] : Nontrivial P.invtRootSubmodule where
  exists_pair_ne := ⟨⊥, ⊤, by rw [ne_eq, Subtype.ext_iff]; exact bot_ne_top⟩

lemma isSimpleModule_weylGroupRootRep_iff [Nontrivial M] :
    IsSimpleModule (MonoidAlgebra R P.weylGroup) P.weylGroupRootRep.asModule ↔
    ∀ (q : Submodule R M), (∀ i, q ∈ invtSubmodule (P.reflection i)) → q ≠ ⊥ → q = ⊤ := by
  rw [IsSimpleModule, ← P.weylGroupRootRep.mapSubmodule.isSimpleOrder_iff]
  refine ⟨fun h q hq₁ hq₂ ↦ ?_, fun h ↦ ⟨fun q ↦ ?_⟩⟩
  · suffices ∀ g : P.weylGroup, q ∈ invtSubmodule (P.weylGroupRootRep g) by
      let q' : P.weylGroupRootRep.invtSubmodule :=
        ⟨q, (Representation.mem_invtSubmodule P.weylGroupRootRep).mpr this⟩
      suffices q' = ⊤ by simpa [q']
      apply (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
      simpa [q']
    rintro ⟨g, hg⟩
    induction hg using weylGroup.induction with
    | mem i => exact hq₁ i
    | one => simp [← Submonoid.one_def]
    | mul x y hx hy hx' hy' => apply invtSubmodule.comp <;> assumption
  · rcases eq_or_ne q ⊥ with rfl | hq; · tauto
    suffices (q : Submodule R M) = ⊤ by right; simpa using this
    refine h q (fun i ↦ ?_) (by simpa using hq)
    exact P.weylGroupRootRep.mem_invtSubmodule.mp q.property ⟨_, P.reflection_mem_weylGroup i⟩

/-- A root pairing is irreducible if it is non-trivial and contains no proper invariant submodules.
-/
@[mk_iff] class IsIrreducible : Prop where
  nontrivial  : Nontrivial M
  nontrivial' : Nontrivial N
  eq_top_of_invtSubmodule_reflection (q : Submodule R M) :
    (∀ i, q ∈ invtSubmodule (P.reflection i)) → q ≠ ⊥ → q = ⊤
  eq_top_of_invtSubmodule_coreflection (q : Submodule R N) :
    (∀ i, q ∈ invtSubmodule (P.coreflection i)) → q ≠ ⊥ → q = ⊤

instance [P.IsIrreducible] : P.flip.IsIrreducible where
  nontrivial := IsIrreducible.nontrivial' P
  nontrivial' := IsIrreducible.nontrivial P
  eq_top_of_invtSubmodule_reflection := IsIrreducible.eq_top_of_invtSubmodule_coreflection (P := P)
  eq_top_of_invtSubmodule_coreflection := IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P)

lemma isSimpleModule_weylGroupRootRep [P.IsIrreducible] :
    IsSimpleModule (MonoidAlgebra R P.weylGroup) P.weylGroupRootRep.asModule :=
  have := IsIrreducible.nontrivial P
  P.isSimpleModule_weylGroupRootRep_iff.mpr IsIrreducible.eq_top_of_invtSubmodule_reflection

/-- A nonempty irreducible root pairing is a root system. -/
def toRootSystem [Nonempty ι] [NeZero (2 : R)] [P.IsIrreducible] : RootSystem ι R M N :=
  { toRootPairing := P
    span_root_eq_top := IsIrreducible.eq_top_of_invtSubmodule_reflection
      (P.rootSpan R) P.rootSpan_mem_invtSubmodule_reflection (P.rootSpan_ne_bot R)
    span_coroot_eq_top := IsIrreducible.eq_top_of_invtSubmodule_coreflection
      (P.corootSpan R) P.corootSpan_mem_invtSubmodule_coreflection (P.corootSpan_ne_bot R) }

lemma invtSubmodule_reflection_of_invtSubmodule_coreflection (i : ι) (q : Submodule R N)
    (hq : q ∈ invtSubmodule (P.coreflection i)) :
    q.dualAnnihilator.map P.toDualLeft.symm ∈ invtSubmodule (P.reflection i) := by
  rw [LinearEquiv.map_mem_invtSubmodule_iff, LinearEquiv.symm_symm, toDualLeft_conj_reflection,
    Module.End.mem_invtSubmodule, ← Submodule.map_le_iff_le_comap]
  exact (Submodule.dualAnnihilator_map_dualMap_le _ _).trans <| Submodule.dualAnnihilator_anti hq

/-- When the coefficients are a field, the coroot conditions for irreducibility follow from those
for the roots. -/
lemma IsIrreducible.mk' {K : Type*} [Field K] [Module K M] [Module K N] [Nontrivial M]
    (P : RootPairing ι K M N)
    (h : ∀ (q : Submodule K M), (∀ i, q ∈ invtSubmodule (P.reflection i)) → q ≠ ⊥ → q = ⊤) :
    P.IsIrreducible where
  nontrivial := inferInstance
  nontrivial' := (Module.nontrivial_dual_iff K).mp P.toDualLeft.symm.nontrivial
  eq_top_of_invtSubmodule_reflection := h
  eq_top_of_invtSubmodule_coreflection q stab ne_bot := by
    specialize h (q.dualAnnihilator.map P.toDualLeft.symm)
      fun i ↦ invtSubmodule_reflection_of_invtSubmodule_coreflection P i q (stab i)
    rw [Submodule.map_eq_top_iff, not_imp_comm] at h
    replace ne_bot : q.dualAnnihilator ≠ ⊤ := by simpa
    simpa using h ne_bot

lemma isIrreducible_iff_invtRootSubmodule
    {K : Type*} [Field K] [Module K M] [Module K N] [Nontrivial M] (P : RootPairing ι K M N) :
    P.IsIrreducible ↔ IsSimpleOrder P.invtRootSubmodule := by
  refine ⟨fun h ↦ ⟨fun ⟨q, hq⟩ ↦ ?_⟩, fun h ↦ IsIrreducible.mk' P fun q hq hq' ↦ ?_⟩
  · simp only [invtRootSubmodule.bot_mem,  invtRootSubmodule.top_mem, Subtype.mk_eq_bot_iff,
      Subtype.mk_eq_top_iff]
    rw [mem_invtRootSubmodule_iff] at hq
    have := IsIrreducible.eq_top_of_invtSubmodule_reflection q hq
    tauto
  · let q' : P.invtRootSubmodule := ⟨q, P.mem_invtRootSubmodule_iff.mpr hq⟩
    replace hq' : ⊥ < q' := by simpa [q', bot_lt_iff_ne_bot]
    suffices q' = ⊤ by simpa [q'] using this
    exact IsSimpleOrder.eq_top_of_lt hq'

lemma exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule
    [NeZero (2 : R)] [NoZeroSMulDivisors R M] (q : Submodule R M)
    (hq : ∀ i, q ∈ invtSubmodule (P.reflection i)) :
    ∃ Φ : Set ι, (∀ i ∈ Φ, ¬ Disjoint q (R ∙ P.root i)) ∧ (∀ i ∉ Φ, q ≤ ker (P.coroot' i)) := by
  refine ⟨{i | ¬ Disjoint q (R ∙ P.root i)}, by simp, fun i hi ↦ ?_⟩
  simp only [mem_setOf_eq, not_not] at hi
  rw [← Submodule.mem_invtSubmodule_reflection_iff (by simp) hi]
  exact hq i

variable [NeZero (2 : R)] [P.IsIrreducible]

lemma span_orbit_eq_top (i : ι) :
    span R (orbit P.weylGroup (P.root i)) = ⊤ := by
  refine IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P) _ (fun j ↦ ?_) ?_
  · let g : P.weylGroup := ⟨Equiv.reflection P j, P.reflection_mem_weylGroup j⟩
    exact Module.End.span_orbit_mem_invtSubmodule R (P.root i) g
  · simpa using ⟨P.root i, mem_orbit_self _, P.ne_zero i⟩

lemma exists_form_eq_form_and_form_ne_zero (B : P.InvariantForm) (i j : ι) :
    ∃ k, B.form (P.root k) (P.root k) = B.form (P.root j) (P.root j) ∧
         B.form (P.root i) (P.root k) ≠ 0 := by
  by_contra! contra
  suffices span R (orbit P.weylGroup (P.root j)) ≤ ker (B.form (P.root i)) from
    B.apply_root_ne_zero i <| by simpa [span_orbit_eq_top] using this
  refine span_le.mpr fun v hv ↦ ?_
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hv
  simp only [P.weylGroup_apply_root, SetLike.mem_coe, LinearMap.mem_ker]
  apply contra
  simp [← Subgroup.smul_def g]

lemma span_root_image_eq_top_of_forall_orthogonal (s : Set ι)
    (hne : s.Nonempty) (h : ∀ j, P.root j ∉ span R (P.root '' s) → ∀ i ∈ s, P.IsOrthogonal j i) :
    span R (P.root '' s) = ⊤ := by
  have hq (j : ι) : span R (P.root '' s) ∈ Module.End.invtSubmodule (P.reflection j) := by
    by_cases hj : P.root j ∈ span R (P.root '' s)
    · exact Submodule.mem_invtSubmodule_reflection_of_mem _ _ hj
    · refine (Module.End.mem_invtSubmodule _).mpr fun x hx ↦ ?_
      rwa [Submodule.mem_comap, LinearEquiv.coe_coe,
        (isFixedPt_reflection_of_isOrthogonal (h _ hj) hx).eq]
  apply IsIrreducible.eq_top_of_invtSubmodule_reflection _ hq
  simpa using ⟨hne.choose, hne.choose_spec, P.ne_zero _⟩

end RootPairing

namespace RootSystem

/-
Note that this actually holds for `RootPairing` provided we:
* assume `RootPairing.IsBalanced`,
* replace the assumption `q ≠ ⊥` with `¬ Disjoint P.rootSpan q`,
* replace the conclusion `q = ⊤` with `P.rootSpan ≤ q`.
-/
lemma eq_top_of_mem_invtSubmodule_of_forall_eq_univ
    {K : Type*} [Field K] [NeZero (2 : K)] [Module K M] [Module K N]
    (P : RootSystem ι K M N)
    (q : Submodule K M)
    (h₀ : q ≠ ⊥)
    (h₁ : ∀ i, q ∈ invtSubmodule (P.reflection i))
    (h₂ : ∀ Φ, Φ.Nonempty → P.root '' Φ ⊆ q → (∀ i ∉ Φ, q ≤ ker (P.coroot' i)) → Φ = univ) :
    q = ⊤ := by
  obtain ⟨Φ, b, c⟩ := P.exist_set_root_not_disjoint_and_le_ker_coroot'_of_invtSubmodule q h₁
  rcases Φ.eq_empty_or_nonempty with rfl | hΦ
  · replace c : q ≤ ⨅ i, LinearMap.ker (P.coroot' i) := by simpa using c
    simp [h₀, ← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'] at c
  · replace b : P.root '' Φ ⊆ q := by
      simpa [Submodule.disjoint_span_singleton' (P.ne_zero _)] using b
    simpa [h₂ Φ hΦ b c, ← span_le] using b

end RootSystem
