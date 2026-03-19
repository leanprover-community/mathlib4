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
* `LieIdeal.rootSet`: the set of roots whose root space is contained in a
  given Lie ideal.
* `LieAlgebra.IsKilling.lieIdealRootSpan`: the submodule of `Dual K H` spanned by
  `LieIdeal.rootSet`.
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
  obtain ⟨a, ha, rfl⟩ := (LieSubmodule.mem_map _).mp hx
  have : (⟨a.val, a.property⟩ : H) ∈ corootSpace α := ha
  rw [mem_corootSpace] at this
  refine (Submodule.span_le.mpr ?_) this
  rintro _ ⟨y, hy, _, -, rfl⟩
  exact lie_mem_left K L I y _ (hα hy)

/-- The set of roots whose root space is contained in a given Lie ideal. -/
def _root_.LieIdeal.rootSet (I : LieIdeal K L) : Set H.root :=
  { α | rootSpace H α.1 ≤ I.restr H }

@[simp]
lemma _root_.LieIdeal.mem_rootSet {I : LieIdeal K L} {α : H.root} :
    α ∈ I.rootSet ↔ rootSpace H α.1 ≤ I.restr H := Iff.rfl

variable [IsKilling K L] [IsTriangularizable K H L] [CharZero K]

/-- The submodule of `Dual K H` spanned by the roots associated to a Lie ideal. -/
noncomputable def lieIdealRootSpan (I : LieIdeal K L) : Submodule K (Dual K H) :=
  Submodule.span K ((rootSystem H).root '' I.rootSet)

lemma rootSpace_le_ideal_of_apply_coroot_ne_zero (I : LieIdeal K L)
    {α : Weight K H L} (hα : rootSpace H α ≤ I.restr H)
    {γ : H → K} (hγ_ne : γ (coroot α) ≠ 0) :
    rootSpace H γ ≤ I.restr H := by
  intro y hy
  have : γ (coroot α) • y ∈ I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy (coroot α)]
    exact lie_mem_left K L I _ y
      (corootSubmodule_le_lieIdeal I hα (coe_coroot_mem_corootSubmodule α))
  exact I.toSubmodule.smul_mem_iff hγ_ne |>.mp this

lemma reflectionPerm_mem_lieIdeal_rootSet_iff (I : LieIdeal K L) (α β : H.root) :
    (rootSystem H).reflectionPerm β α ∈ I.rootSet ↔ α ∈ I.rootSet := by
  let S := rootSystem H
  suffices h : ∀ γ δ : H.root, δ ∈ I.rootSet → S.reflectionPerm γ δ ∈ I.rootSet by
    exact ⟨fun hα => S.reflectionPerm_self β α ▸ h β _ hα, h β α⟩
  intro γ δ hδ
  simp only [LieIdeal.mem_rootSet] at hδ ⊢
  by_cases hp : S.pairing δ γ = 0
  · rwa [S.reflectionPerm_eq_of_pairing_eq_zero hp]
  · have hγ := rootSpace_le_ideal_of_apply_coroot_ne_zero I hδ
      (mt S.pairing_eq_zero_iff.mpr hp)
    have h_neg : S.pairing (S.reflectionPerm γ δ) γ ≠ 0 := by
      rwa [← S.pairing_reflectionPerm γ δ γ, S.pairing_reflectionPerm_self_right, neg_ne_zero]
    exact rootSpace_le_ideal_of_apply_coroot_ne_zero I hγ h_neg

/-- The submodule spanned by roots of a Lie ideal is invariant under all root reflections. -/
lemma lieIdealRootSpan_mem_invtRootSubmodule (I : LieIdeal K L) :
    lieIdealRootSpan I ∈ (rootSystem H).invtRootSubmodule := by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro β
  rw [Module.End.mem_invtSubmodule, lieIdealRootSpan, Submodule.span_le]
  rintro - ⟨α, hα, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, ← RootPairing.root_reflectionPerm]
  exact Submodule.subset_span ⟨_, (reflectionPerm_mem_lieIdeal_rootSet_iff I α β).mpr hα, rfl⟩

/-- The invariant root submodule corresponding to a Lie ideal. -/
noncomputable def lieIdealToInvtRootSubmodule (I : LieIdeal K L) :
    (rootSystem H).invtRootSubmodule :=
  ⟨lieIdealRootSpan I, lieIdealRootSpan_mem_invtRootSubmodule I⟩

@[gcongr]
lemma lieIdealToInvtRootSubmodule_mono {I J : LieIdeal K L} (h : I ≤ J) :
    lieIdealToInvtRootSubmodule (H := H) I ≤ lieIdealToInvtRootSubmodule J :=
  Submodule.span_mono (Set.image_mono
    fun α (hα : rootSpace H α.1 ≤ I.restr H) ↦ hα.trans (show I.restr H ≤ J.restr H from h))

end LieAlgebra.IsKilling
