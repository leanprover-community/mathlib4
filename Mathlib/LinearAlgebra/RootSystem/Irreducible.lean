/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.RepresentationTheory.Submodule
import LeanCopilot

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
      P.rootSpan P.rootSpan_mem_invtSubmodule_reflection P.rootSpan_ne_bot
    span_coroot_eq_top := IsIrreducible.eq_top_of_invtSubmodule_coreflection
      P.corootSpan P.corootSpan_mem_invtSubmodule_coreflection P.corootSpan_ne_bot }

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

lemma root_mem_or_subset_ker_coroot {K : Type*} [Field K] [Module K M] [Module K N]
    (q : Submodule K M) (P : RootPairing ι K M N) (i : ι)
    (hi : q ∈ invtSubmodule (P.reflection i)) :
    P.root i ∈ q ∨ q ≤ ker (P.coroot' i) := by
  by_cases h_root : P.root i ∈ q
  · left
    exact h_root
  right
  intro v hv
  by_cases h_zero : v = 0
  · subst h_zero
    simp only [Submodule.zero_mem]
  have : (P.coroot' i) v • P.root i ∈ q := by
    simpa using (Submodule.sub_mem_iff_right q hv).mp (hi hv)
  by_contra h_ne
  have : P.root i ∈ q := by
    have := Submodule.smul_mem q (((P.coroot' i) v)⁻¹) this
    rwa [inv_smul_smul₀ h_ne] at this
  contradiction

lemma root_subset_characterization {K : Type*} [Field K] [Module K M] [Module K N]
    (q : Submodule K M) (P : RootPairing ι K M N)
    (h₁ : ∀ i, q ∈ invtSubmodule (P.reflection i)) :
    ∃ (Φ : Set ι), (∀ i ∈ Φ, P.root i ∈ q) ∧ (∀ i ∉ Φ, q ≤ ker (P.coroot' i)) := by
  use {i | P.root i ∈ q}
  constructor
  · exact fun _ => id
  · intro i hi
    exact (root_mem_or_subset_ker_coroot q P i (h₁ i)).resolve_left hi

lemma span_coroot_eq_top' {K : Type*} [Field K] [Module K M] [Module K N]
    (P : RootSystem ι K M N) : span K (range P.coroot') = ⊤ := by
  have key (d : Module.Dual K M) :
      d ∈ span K (range fun i ↦ P.flip.toDualLeft (P.flip.root i)) := by
    simp only [PerfectPairing.toDualLeft_apply]
    rw [range_comp' P.flip.toPerfectPairing P.flip.root]
    have h₁ := Submodule.apply_mem_span_image_iff_mem_span (s := (range fun i ↦ (P.flip.root i)))
      (x := (P.flip.toDualLeft.invFun d)) P.flip.toDualLeft.injective
    have h₂: P.flip.toDualLeft.symm d ∈ span K (range fun i ↦ (P.flip.root i)) := by
      simp only [Submodule.mem_top, RootSystem.span_root_eq_top]
    have h₃ : P.flip.toDualLeft (P.flip.toDualLeft.invFun d) = d := by
      exact (LinearEquiv.eq_symm_apply P.flip.toDualLeft).mp rfl
    have := h₁.mpr h₂
    rw [h₃] at this
    exact this
  exact Submodule.eq_top_iff'.mpr key

lemma aux {K : Type*} [Field K] [Module K M] [Module K N]
    (P : RootSystem ι K M N) (v : M) (h₁ : ∀ (i : ι), v ∈ ker (P.coroot' i))
    (d : Module.Dual K M) : d v = 0 := by
  have : d ∈ span K (range P.coroot') := by
    simp only [Submodule.mem_top, span_coroot_eq_top' P]
  induction this using Submodule.span_induction with
  | mem x hx' =>
    rcases hx' with ⟨w, h⟩
    subst h
    exact h₁ w
  | zero => simp only [Submodule.mem_top, LinearMap.zero_apply]
  | add _ _ _ _ a₁ a₂ => rw [LinearMap.add_apply, a₁, a₂, add_zero]
  | smul _ _ _ m => rw [LinearMap.smul_apply, smul_eq_mul, m, mul_zero]

lemma l3 {K : Type*} [Field K] [Module K M] [Module K N]
    (P : RootSystem ι K M N) (q : Submodule K M) (h₁ : ∀ i, q ∈ invtSubmodule (P.reflection i))
    (h_bot: q ≠ ⊥) (h_top: q ≠ ⊤) :
    ∃ (Φ : Set ι), (∀ i ∈ Φ, P.root i ∈ q) ∧ (∀ i ∉ Φ, q ≤ LinearMap.ker (P.coroot' i)) ∧
    Φ ≠ univ ∧ Φ ≠ ∅ := by
  obtain ⟨Φ, b, c⟩ := root_subset_characterization q P.toRootPairing h₁
  use Φ
  constructor
  · exact b
  constructor
  · exact c
  constructor
  · by_contra hu
    have lll (i : ι) : P.root i ∈ q := by
      subst hu
      simp_all only [ne_eq, mem_univ, forall_const, not_true_eq_false, IsEmpty.forall_iff,
        implies_true]
    have : span K (P.root '' univ) ≤ q := by
      subst hu
      simp_all only [ne_eq, mem_univ, implies_true, forall_const, not_true_eq_false,
        IsEmpty.forall_iff, image_univ]
      rw [span_le]
      exact range_subset_iff.mpr b
    have : span K (P.root '' univ) = ⊤ := by
      subst hu
      simp_all only [ne_eq, mem_univ, implies_true, image_univ, RootSystem.span_root_eq_top,
        top_le_iff]
    have : q = ⊤ := by
      subst hu
      simp_all only [ne_eq, mem_univ, implies_true, image_univ, RootSystem.span_root_eq_top,
        top_le_iff]
    · contradiction
  by_contra hn
  have lll (i : ι) : q ≤ ker (P.coroot' i) := by
    subst hn
    simp_all only [ne_eq, mem_empty_iff_false, IsEmpty.forall_iff, implies_true, not_false_eq_true,
      forall_const]
  have : ∃ v ∈ q, v ≠ 0 := by
    exact (Submodule.ne_bot_iff q).1 h_bot
  obtain ⟨v1, ⟨v21, v22⟩⟩ := this
  have xxx (i : ι) : v1 ∈ ker (P.coroot' i) := by
    subst hn
    simp_all only [ne_eq, mem_empty_iff_false, not_false_eq_true, implies_true, IsEmpty.forall_iff,
      forall_const, LinearMap.mem_ker, PerfectPairing.flip_apply_apply]
    apply c
    simp_all only
  have help (d : Module.Dual K M) : d v1 = 0 := by
    exact aux P v1 xxx d
  have : q.dualAnnihilator ≠ ⊤ := by
    subst hn
    simp_all only [ne_eq, mem_empty_iff_false, not_false_eq_true, implies_true, LinearMap.mem_ker,
      image_univ, RootSystem.span_coroot_eq_top, IsEmpty.forall_iff, forall_const,
        Submodule.dualAnnihilator_eq_top_iff]
  have := (Module.forall_dual_apply_eq_zero_iff K v1).1 help
  contradiction

lemma invtsubmodule_to_root_subset {K : Type*} [Field K] [Module K M] [Module K N]
    (P : RootSystem ι K M N)
    (q : Submodule K M)
    (h₀ : q ≠ ⊥)
    (h₁ : ∀ i, q ∈ invtSubmodule (P.reflection i))
    (h₂ : ∀ Φ, Φ.Nonempty → P.root '' Φ ⊆ q → (∀ i ∉ Φ, q ≤ ker (P.coroot' i)) → Φ = univ) :
    q = ⊤ := by
  by_contra ntop
  have := l3 P q h₁ h₀ ntop
  obtain ⟨Φ, b, c, d, e⟩ := this
  have rr : Φ.Nonempty := by
    exact nonempty_iff_ne_empty.mpr e
  have ss :  P.root '' Φ ⊆ q := by
    exact image_subset_iff.mpr b
  have s2 := h₂ Φ rr ss c
  contradiction

end RootPairing
