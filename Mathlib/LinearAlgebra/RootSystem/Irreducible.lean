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

lemma span_root_image_eq_top_of_forall_orthogonal [Invertible (2 : R)] (s : Set ι)
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

lemma l1 {K : Type*} [Field K] [Module K M] [Module K N]
    (P : RootPairing ι K M N) (q : Submodule K M) (i : ι)
      (hq : q ∈ invtSubmodule (P.reflection i)) :
        P.root i ∈ q ∨ q ≤ LinearMap.ker (P.coroot' i) := by
  by_cases h₀ : P.root i ∈ q
  · simp_all only [PerfectPairing.flip_apply_apply, Subtype.forall, true_or]
  right
  intro v
  intro v1
  by_cases h₁ : v = 0
  · subst h₁
    simp_all only [Submodule.zero_mem]
  simp_all
  have ttt : ((P.reflection i) v) ∈ q := by
    have xxx := (Module.End.mem_invtSubmodule (R := K) (M := M) (P.reflection i) (p := q)).1 hq
    simp at xxx
    exact xxx v1
  have x := (P.reflection_apply i) v
  rw [x] at ttt
  simp_all
  have rrr : (P.coroot' i) v • P.root i ∈ q := by
    have h3 : - (v - (P.coroot' i) v • P.root i) ∈ q := Submodule.neg_mem q ttt
    have h4 : (P.coroot' i) v • P.root i - v ∈ q := by rwa [neg_sub] at h3
    have h5 : ((P.coroot' i) v • P.root i - v) + v ∈ q := Submodule.add_mem q h4 v1
    simp at h5
    simp
    exact h5
  simp at rrr
  by_contra h_ne_zero
  have : IsUnit ((P.coroot' i) v) := by
    simp_all only [ne_eq, PerfectPairing.flip_apply_apply, isUnit_iff_ne_zero, not_false_eq_true]
  have a_inv : ((P.coroot' i) v)⁻¹ * ((P.coroot' i) v) = 1 := by
    simp_all only [ne_eq, PerfectPairing.flip_apply_apply,
      isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel]
  have : P.root i ∈ q := by
    have := Submodule.smul_mem (M := M) q (((P.coroot' i) v)⁻¹) rrr
    simp at this
    simp_all only [ne_eq, PerfectPairing.flip_apply_apply,
      isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel,
      inv_smul_smul₀]
  contradiction

lemma l2 {K : Type*} [Field K] [Module K M] [Module K N]
    (P : RootPairing ι K M N) (q : Submodule K M) (ha : ∀ i, q ∈ invtSubmodule (P.reflection i)):
      ∃ (Φ : Set ι), (∀ i ∈ Φ, P.root i ∈ q) ∧ (∀ i ∉ Φ, q ≤ LinearMap.ker (P.coroot' i)) := by
  let Φ := {i | P.root i ∈ q}
  use Φ
  constructor
  · intro i hi
    exact hi
  · intro i hi
    cases l1 P q i (ha i) with
    | inl h_root_in_q =>
      contradiction
    | inr h_kernel =>
      exact h_kernel

lemma l21 {K : Type*} [Field K] [Module K M] [Module K M] [Module K N]
    (P : RootSystem ι K M N) : span K (range P.coroot') = ⊤ := by
  --simp
  have h0 := P.span_root_eq_top
  have h1 := P.span_coroot_eq_top
  unfold RootPairing.coroot'
  let Q := P.flip
  have h2 := Q.span_root_eq_top
  have h3 := Q.span_coroot_eq_top
  --simp_all only [RootSystem.span_root_eq_top, RootSystem.span_coroot_eq_top, Q]
  have (i : ι) : P.toPerfectPairing.flip (P.coroot i) = Q.toDualLeft (Q.root i) := by
    simp_all only [RootSystem.span_root_eq_top, RootSystem.span_coroot_eq_top,
        PerfectPairing.toDualLeft_apply, Q]
    rfl
  have h2 := Q.span_root_eq_top
  have rrrr : span K (range fun i ↦ P.toPerfectPairing.flip (P.coroot i)) =
      span K (range fun i ↦ Q.toDualLeft (Q.root i)) := by
    simp_all only [RootSystem.span_root_eq_top, RootSystem.span_coroot_eq_top,
      PerfectPairing.toDualLeft_apply, Q]
  rw [rrrr]
  let s := (range fun i ↦ (Q.root i))
  let g := Q.toDualLeft '' s
  let r := Q.toDualLeft
  have needed : span K s = ⊤ := by
    simp_all only [RootSystem.span_root_eq_top, RootSystem.span_coroot_eq_top,
      PerfectPairing.toDualLeft_apply, Q, s]
  have needed2 : (range fun i ↦ Q.toDualLeft (Q.root i)) = Q.toDualLeft '' s := by
    simp_all only [RootSystem.span_root_eq_top, RootSystem.span_coroot_eq_top, PerfectPairing.toDualLeft_apply, Q, s]
    ext x : 1
    simp_all only [mem_range, mem_image, exists_exists_eq_and, Q, s]

  have key (d : Module.Dual K M) : d ∈ span K (range fun i ↦ Q.toDualLeft (Q.root i)) := by
    have rrrr5 := Submodule.apply_mem_span_image_iff_mem_span (s := s) (x := (Q.toDualLeft.invFun d)) Q.toDualLeft.injective
    --simp at rrrr5
    --simp at rrrr5
    have mmm : Q.toDualLeft.symm d ∈ span K s := by
      rw [needed]
      simp_all only [RootSystem.span_root_eq_top, RootSystem.span_coroot_eq_top, PerfectPairing.toDualLeft_apply,
        Submodule.mem_top, iff_true, Q, s]
    have := rrrr5.2 mmm
    --simp [s] at this
    have helpme11 : Q.toDualLeft (Q.toDualLeft.invFun d) = d := by
      simp_all only [RootSystem.span_root_eq_top, RootSystem.span_coroot_eq_top, PerfectPairing.toDualLeft_apply,
        LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply, Submodule.mem_top, iff_true, Q, s]
    rw [helpme11] at this
    rw [needed2]
    exact this
  simp_all only [RootSystem.span_root_eq_top, RootSystem.span_coroot_eq_top,
    PerfectPairing.toDualLeft_apply, Q]
  ext x : 1
  simp_all only [Submodule.mem_top, Q]


lemma l25 {K : Type*} [Field K] [Module K M] [Module K M] [Module K N]
    (P : RootSystem ι K M N) (v : M) (hx : ∀ (i : ι), v ∈ ker (P.coroot' i))
      (hy : span K (range P.coroot') = ⊤) (d : Module.Dual K M) : d v = 0 := by
  have : d ∈ span K (range P.coroot') := by
    simp_all only [LinearMap.mem_ker, PerfectPairing.flip_apply_apply, Submodule.mem_top]
  refine Submodule.span_induction ?_ ?_ ?_ ?_ this
  · intro x h
    simp_all only [LinearMap.mem_ker, PerfectPairing.flip_apply_apply, Submodule.mem_top, mem_range]
    obtain ⟨w, h⟩ := h
    subst h
    simp_all only [PerfectPairing.flip_apply_apply]
  · simp_all only [LinearMap.mem_ker, PerfectPairing.flip_apply_apply, Submodule.mem_top, LinearMap.zero_apply]
  · intro x y hx_1 hy_1 a a_1
    simp_all only [LinearMap.mem_ker, PerfectPairing.flip_apply_apply, Submodule.mem_top, LinearMap.add_apply, add_zero]
  · intro a x hx_1 a_1
    simp_all only [LinearMap.mem_ker, PerfectPairing.flip_apply_apply, Submodule.mem_top, LinearMap.smul_apply,
      smul_eq_mul, mul_zero]



lemma l3 {K : Type*} [Field K] [Module K M] [Module K N]
    (P : RootSystem ι K M N) (q : Submodule K M) (ha : ∀ i, q ∈ invtSubmodule (P.reflection i))
      (h_bot: q ≠ ⊥) (h_top: q ≠ ⊤):
        ∃ (Φ : Set ι), (∀ i ∈ Φ, P.root i ∈ q) ∧ (∀ i ∉ Φ, q ≤ LinearMap.ker (P.coroot' i)) ∧
          Φ ≠ univ ∧ Φ ≠ ∅ := by
  obtain ⟨Φ, b, c⟩ := l2 P.toRootPairing q ha
  use Φ
  constructor
  · exact b
  constructor
  · exact c
  constructor
  by_contra hu
  have lll (i : ι) : P.root i ∈ q := by
    subst hu
    simp_all only [ne_eq, mem_univ, forall_const, not_true_eq_false, IsEmpty.forall_iff,
      implies_true]
  have : span K (P.root '' univ) ≤ q := by
    subst hu
    simp_all only [ne_eq, mem_univ, implies_true, forall_const, not_true_eq_false, IsEmpty.forall_iff, image_univ]
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
  --have : ∃ d : Module.Dual K M, d v1 ≠ 0 := by
    --search_proof
  have xxx (i : ι) : v1 ∈ ker (P.coroot' i) := by
    subst hn
    simp_all only [ne_eq, mem_empty_iff_false, not_false_eq_true, implies_true, IsEmpty.forall_iff, forall_const,
      LinearMap.mem_ker, PerfectPairing.flip_apply_apply]
    apply c
    simp_all only
  have yyy : span K (range  P.coroot') = ⊤ := by
    exact l21 P
    --search_proof
  have help (d : Module.Dual K M) : d v1 = 0 := by
    exact l25 P v1 xxx yyy d
  have : q.dualAnnihilator ≠ ⊤ := by
    subst hn
    simp_all only [ne_eq, mem_empty_iff_false, not_false_eq_true, implies_true, LinearMap.mem_ker, image_univ,
      RootSystem.span_coroot_eq_top, IsEmpty.forall_iff, forall_const, Submodule.dualAnnihilator_eq_top_iff]
  have := (Module.forall_dual_apply_eq_zero_iff K v1).1 help
  contradiction





end RootPairing
