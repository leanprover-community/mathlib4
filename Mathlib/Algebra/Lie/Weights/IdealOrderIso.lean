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

/-- If the root space of `α` is contained in a Lie ideal `I`, then the coroot submodule of `α`
is also contained in `I`. -/
lemma corootSubmodule_le_lieIdeal (I : LieIdeal K L) {α : Weight K H L}
    (hα : (rootSpace H α).toSubmodule ≤ I.toSubmodule) :
    (corootSubmodule α).toSubmodule ≤ I.toSubmodule := by
  intro x hx
  obtain ⟨h, hh, rfl⟩ := (LieSubmodule.mem_map _).mp hx
  have key : (⟨h.val, h.property⟩ : H) ∈ corootSpace α := hh
  rw [mem_corootSpace] at key
  refine (Submodule.span_le.mpr ?_) key
  rintro _ ⟨y, hy, _, -, rfl⟩
  exact lie_mem_left K L I y _ (hα hy)

variable [IsKilling K L] [IsTriangularizable K H L] [CharZero K]

/-- The set of roots whose root space is contained in a given Lie ideal. -/
noncomputable def lieIdealRootSet (I : LieIdeal K L) : Set H.root :=
  { α | (rootSpace H α.1).toSubmodule ≤ I.toSubmodule }

/-- The submodule of `Dual K H` spanned by the roots associated to a Lie ideal. -/
noncomputable def lieIdealRootSpan (I : LieIdeal K L) : Submodule K (Dual K H) :=
  Submodule.span K ((↑) '' lieIdealRootSet (H := H) I)

lemma rootSpace_le_ideal_of_apply_coroot_ne_zero (I : LieIdeal K L)
    {α : Weight K H L} (hI : (rootSpace H α).toSubmodule ≤ I.toSubmodule)
    {γ : H → K} (hγ_ne : γ (coroot α) ≠ 0) :
    (rootSpace H γ).toSubmodule ≤ I.toSubmodule := by
  have h_coroot_I : (coroot α : L) ∈ I.toSubmodule :=
    corootSubmodule_le_lieIdeal I hI (coroot_mem_corootSubmodule α)
  intro y hy
  have h_lie : ⁅(coroot α : L), y⁆ ∈ I.toSubmodule :=
    lie_mem_left K L I (coroot α : L) y h_coroot_I
  have h_eq : ⁅(coroot α : L), y⁆ = γ ⟨coroot α, (coroot α).property⟩ • y :=
    lie_eq_smul_of_mem_rootSpace hy ⟨coroot α, (coroot α).property⟩
  rwa [h_eq, I.toSubmodule.smul_mem_iff (by exact_mod_cast hγ_ne)] at h_lie

lemma lieIdealRootSet_reflectionPerm_invariant (I : LieIdeal K L) (i : H.root)
    {α : H.root} (hα : α ∈ lieIdealRootSet (H := H) I) :
    (rootSystem H).reflectionPerm i α ∈ lieIdealRootSet (H := H) I := by
  simp only [lieIdealRootSet, Set.mem_setOf_eq] at hα ⊢
  by_cases hp : (rootSystem H).pairing α i = 0
  · rwa [(rootSystem H).reflectionPerm_eq_of_pairing_eq_zero hp]
  · have hi := rootSpace_le_ideal_of_apply_coroot_ne_zero I hα
      (mt (rootSystem H).pairing_eq_zero_iff.mpr hp)
    have h_neg : (rootSystem H).pairing ((rootSystem H).reflectionPerm i α) i ≠ 0 := by
      rw [show (rootSystem H).pairing ((rootSystem H).reflectionPerm i α) i =
          -(rootSystem H).pairing α i from
        ((rootSystem H).pairing_reflectionPerm i α i).symm.trans
          ((rootSystem H).pairing_reflectionPerm_self_right α i)]
      exact neg_ne_zero.mpr hp
    exact rootSpace_le_ideal_of_apply_coroot_ne_zero I hi h_neg

/-- The submodule spanned by roots of a Lie ideal is invariant under all root reflections. -/
lemma lieIdealRootSpan_mem_invtRootSubmodule (I : LieIdeal K L) :
    lieIdealRootSpan (H := H) I ∈ (rootSystem H).invtRootSubmodule := by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro i; rw [Module.End.mem_invtSubmodule]
  apply Submodule.span_le.mpr
  rintro _ ⟨α, hα, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  rw [show (↑((rootSystem H).reflection i) : Dual K H →ₗ[K] Dual K H)
      (Weight.toLinear K H L ↑α) = (rootSystem H).reflection i ((rootSystem H).root α) from rfl,
    ← (rootSystem H).root_reflectionPerm i α]
  exact Submodule.subset_span ⟨_, lieIdealRootSet_reflectionPerm_invariant I i hα, rfl⟩

/-- Maps a Lie ideal to its corresponding invariant root submodule. -/
noncomputable def lieIdealToInvtRootSubmodule (I : LieIdeal K L) :
    (rootSystem H).invtRootSubmodule :=
  ⟨lieIdealRootSpan (H := H) I, lieIdealRootSpan_mem_invtRootSubmodule I⟩

lemma lieIdealToInvtRootSubmodule_mono {I J : LieIdeal K L} (h : I ≤ J) :
    lieIdealToInvtRootSubmodule (H := H) I ≤ lieIdealToInvtRootSubmodule J :=
  Submodule.span_mono (Set.image_mono
    fun α (hα : (rootSpace H α.1).toSubmodule ≤ I.toSubmodule) ↦ hα.trans h)

end LieAlgebra.IsKilling
