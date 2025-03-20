/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
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
open Submodule (span)
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

lemma span_orbit_eq_top [NeZero (2 : R)] [P.IsIrreducible] (i : ι) :
    span R (MulAction.orbit P.weylGroup (P.root i)) = ⊤ := by
  refine IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P) _ (fun j ↦ ?_) ?_
  · let g : P.weylGroup := ⟨Equiv.reflection P j, P.reflection_mem_weylGroup j⟩
    exact Module.End.span_orbit_mem_invtSubmodule R (P.root i) g
  · simpa using ⟨P.root i, MulAction.mem_orbit_self _, P.ne_zero i⟩

end RootPairing
