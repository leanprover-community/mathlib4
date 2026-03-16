/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Irreducible

/-!
# Lie ideals and invariant root submodules

We construct the forward map `lieIdealToInvtRootSubmodule` from Lie ideals of a Killing Lie
algebra to invariant root submodules of the associated root system.

## Main definitions
* `LieAlgebra.IsKilling.lieIdealRootSet`: the set of roots whose root space is contained in a
  given Lie ideal.
* `LieAlgebra.IsKilling.lieIdealRootSpan`: the submodule of `Dual K H` spanned by
  `lieIdealRootSet`.
* `LieAlgebra.IsKilling.lieIdealToInvtRootSubmodule`: the forward map from Lie ideals to
  invariant root submodules.

## Main results
* `LieAlgebra.IsKilling.lieIdealRootSpan_mem_invtRootSubmodule`: `lieIdealRootSpan` is an
  invariant submodule.

-/

@[expose] public section

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

lemma corootSubmodule_le_lieIdeal (I : LieIdeal K L) {α : Weight K H L}
    (hα : rootSpace H α ≤ I.restr H) :
    corootSubmodule α ≤ I.restr H := by
  intro x hx
  obtain ⟨h, hh, rfl⟩ := (LieSubmodule.mem_map _).mp hx
  have : (⟨h.val, h.property⟩ : H) ∈ corootSpace α := hh
  rw [mem_corootSpace] at this
  refine (Submodule.span_le.mpr ?_) this
  rintro _ ⟨y, hy, _, -, rfl⟩
  exact lie_mem_left K L I y _ (hα hy)

/-- The set of roots whose root space is contained in a given Lie ideal. -/
def lieIdealRootSet (I : LieIdeal K L) : Set H.root :=
  { α | rootSpace H α.1 ≤ I.restr H }

@[simp]
lemma mem_lieIdealRootSet {I : LieIdeal K L} {α : H.root} :
    α ∈ lieIdealRootSet (H := H) I ↔ rootSpace H α.1 ≤ I.restr H := Iff.rfl

variable [IsKilling K L] [IsTriangularizable K H L] [CharZero K]

/-- The submodule of `Dual K H` spanned by the roots associated to a Lie ideal. -/
noncomputable def lieIdealRootSpan (I : LieIdeal K L) : Submodule K (Dual K H) :=
  Submodule.span K ((rootSystem H).root '' lieIdealRootSet (H := H) I)

lemma rootSpace_le_ideal_of_apply_coroot_ne_zero (I : LieIdeal K L)
    {α : Weight K H L} (hI : rootSpace H α ≤ I.restr H)
    {γ : H → K} (hγ_ne : γ (coroot α) ≠ 0) :
    rootSpace H γ ≤ I.restr H := by
  intro y hy
  have : γ (coroot α) • y ∈ I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy (coroot α)]
    exact lie_mem_left K L I _ y (corootSubmodule_le_lieIdeal I hI (coroot_mem_corootSubmodule α))
  exact I.toSubmodule.smul_mem_iff hγ_ne |>.mp this

lemma lieIdealRootSet_reflectionPerm_invariant (I : LieIdeal K L) (i : H.root)
    {α : H.root} (hα : α ∈ lieIdealRootSet (H := H) I) :
    (rootSystem H).reflectionPerm i α ∈ lieIdealRootSet (H := H) I := by
  simp only [mem_lieIdealRootSet] at hα ⊢
  by_cases hp : (rootSystem H).pairing α i = 0
  · rwa [(rootSystem H).reflectionPerm_eq_of_pairing_eq_zero hp]
  · have hi := rootSpace_le_ideal_of_apply_coroot_ne_zero I hα
      (mt (rootSystem H).pairing_eq_zero_iff.mpr hp)
    have h_neg : (rootSystem H).pairing ((rootSystem H).reflectionPerm i α) i ≠ 0 := by
      rwa [← (rootSystem H).pairing_reflectionPerm i α i,
        (rootSystem H).pairing_reflectionPerm_self_right, neg_ne_zero]
    exact rootSpace_le_ideal_of_apply_coroot_ne_zero I hi h_neg

/-- The submodule spanned by roots of a Lie ideal is invariant under all root reflections. -/
lemma lieIdealRootSpan_mem_invtRootSubmodule (I : LieIdeal K L) :
    lieIdealRootSpan (H := H) I ∈ (rootSystem H).invtRootSubmodule := by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro i; rw [Module.End.mem_invtSubmodule]
  apply Submodule.span_le.mpr
  rintro _ ⟨α, hα, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  change (rootSystem H).reflection i ((rootSystem H).root α) ∈ _
  rw [← (rootSystem H).root_reflectionPerm i α]
  exact Submodule.subset_span ⟨_, lieIdealRootSet_reflectionPerm_invariant I i hα, rfl⟩

/-- Maps a Lie ideal to its corresponding invariant root submodule. -/
noncomputable def lieIdealToInvtRootSubmodule (I : LieIdeal K L) :
    (rootSystem H).invtRootSubmodule :=
  ⟨lieIdealRootSpan (H := H) I, lieIdealRootSpan_mem_invtRootSubmodule I⟩

lemma lieIdealToInvtRootSubmodule_mono {I J : LieIdeal K L} (h : I ≤ J) :
    lieIdealToInvtRootSubmodule (H := H) I ≤ lieIdealToInvtRootSubmodule J :=
  Submodule.span_mono (Set.image_mono
    fun α (hα : rootSpace H α.1 ≤ I.restr H) ↦ hα.trans (show I.restr H ≤ J.restr H from h))

end LieAlgebra.IsKilling
