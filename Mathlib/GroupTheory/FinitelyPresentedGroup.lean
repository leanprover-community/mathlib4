/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Finitely Presented Groups

This file defines finitely presented groups.

## Main definitions
* `Subgroup.IsNormalClosureFG N`: says that the subgroup `N` is the normal closure of a
  finitely generated subgroup.
* `IsFinitelyPresented`: defines when a group is finitely presented.

## Main results
* `Subgroup.IsNormalClosureFG_map`: Being the normal closure of a finite set is preserved under
  surjective homomorphism.
* `IsFinitelyPresented.equiv`: finitely presented groups are closed under isomorphism.

## Tags
finitely presented group, finitely generated normal closure
-/

@[expose] public section

variable {G H α β : Type*} [Group G] [Group H]

/-- `IsNormalClosureFG N` says that the subgroup `N` is the normal closure of a finitely-generated
subgroup. -/
@[to_additive /-- `IsNormalClosureFG N` says that the additive subgroup `N` is the normal closure
of an additive finitely-generated subgroup. -/]
def Subgroup.IsNormalClosureFG (N : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = N

namespace Subgroup.IsNormalClosureFG

/-- Being the normal closure of a finite set is invariant under surjective homomorphism. -/
@[to_additive /-- Being the additive normal closure of a finite set is invariant under
surjective homomorphism. -/]
protected theorem map {N : Subgroup G} (hN : IsNormalClosureFG N)
    {f : G →* H} (hf : Function.Surjective f) : (N.map f).IsNormalClosureFG := by
  obtain ⟨S, hSfinite, hSclosure⟩ := hN
  refine ⟨f '' S, hSfinite.image _, ?_⟩
  rw [← hSclosure, Subgroup.map_normalClosure _ _ hf]

/-- The trivial group is the normal closure of a finite set of relations. -/
@[to_additive /-- The trivial additive group is the normal closure of a finite set of relations. -/]
protected theorem bot : IsNormalClosureFG (⊥ : Subgroup G) :=
  ⟨∅, Finite.of_subsingleton, normalClosure_empty⟩

end Subgroup.IsNormalClosureFG

/-- An additive group is finitely presented if it has a finite generating set such that the kernel
of the induced map from the free additive group on that set is the normal closure
of finitely many relations. -/
class AddGroup.IsFinitelyPresented (G : Type*) [AddGroup G] : Prop where
  out : ∃ (n : ℕ) (φ : FreeAddGroup (Fin n) →+ G), Function.Surjective φ ∧ φ.ker.IsNormalClosureFG

/-- A group is finitely presented if it has a finite generating set such that the kernel
of the induced map from the free group on that set is the normal closure of finitely many
relations. -/
@[mk_iff, to_additive existing]
class Group.IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (φ : FreeGroup (Fin n) →* G), Function.Surjective φ ∧ φ.ker.IsNormalClosureFG

namespace Group.IsFinitelyPresented

/-- Finitely presented groups are closed under isomorphism. -/
@[to_additive /-- Finitely presented additive groups are closed under additive isomorphism. -/
]
theorem equiv (iso : G ≃* H) (h : IsFinitelyPresented G) : IsFinitelyPresented H := by
  obtain ⟨n, φ, hφsurj, hNC⟩ := h
  refine ⟨n, (iso : G →* H).comp φ, iso.surjective.comp hφsurj, ?_⟩
  rwa [MonoidHom.ker_mulEquiv_comp φ iso]

/-- A group is finitely presented if there exists a surjective homomorphism from
a free group on an arbitrary finite type such that the kernel is finitely generated as
a normal subgroup. -/
@[to_additive]
theorem of_hom_surj_finite {α : Type*} [Finite α] (f : FreeGroup α →* G)
    (hf_surj : Function.Surjective f) (hf_ker : (MonoidHom.ker f).IsNormalClosureFG) :
    IsFinitelyPresented G := by
  sorry

/-- A group is finitely presented if there exists a `Set G` such that the canonical inclusion map
is surjective and the kernel is finitely generated as a normal subgroup. -/
theorem iff_hom_surj_set_G :
    IsFinitelyPresented G ↔ ∃ (S : Set G) (_ : S.Finite),
      Function.Surjective (FreeGroup.lift ((↑) : S → G)) ∧
      ((FreeGroup.lift ((↑) : S → G)).ker).IsNormalClosureFG := by
  constructor
  · rintro ⟨n, φ, hsurj, hker⟩
    let S : Set G := Set.range (φ ∘ FreeGroup.of)
    let ψ : FreeGroup (Fin n) →* FreeGroup S :=
      FreeGroup.map fun i ↦ ⟨φ (FreeGroup.of i), ⟨i, rfl⟩⟩
    have ψsurj : Function.Surjective ψ := by
      apply FreeGroup.map_surjective
      rintro ⟨_, ⟨a, rfl⟩⟩; exact ⟨a, rfl⟩
    have comp : (FreeGroup.lift ((↑) : S → G)).comp ψ = φ := by ext a; simp [ψ]
    refine ⟨S, Set.finite_range _, ?_, ?_⟩
    · rw [← comp] at hsurj; exact Function.Surjective.of_comp hsurj
    · have H : φ.ker = (FreeGroup.lift ((↑) : S → G)).ker.comap ψ := by
        rw [← comp, MonoidHom.comap_ker]
      rw [H] at hker
      simpa [Subgroup.map_comap_eq_self_of_surjective ψsurj] using hker.map (hf := ψsurj)
  · rintro ⟨S, hS, hsurj, hker⟩
    haveI : Finite S := hS.to_subtype
    exact of_hom_surj_finite _ hsurj hker

/-- A free group with a finite number of generators is finitely presented. -/
@[to_additive /-- A free additive group with a finite number of generators is finitely presented. -/
]
instance [Finite α] : IsFinitelyPresented (FreeGroup α) := by
  have ⟨n, _, f, hf_surj, hf_inj⟩ := Finite.exists_equiv_fin α
  refine ⟨n, FreeGroup.map f, FreeGroup.map_surjective hf_surj.surjective, ?_⟩
  · rw [(FreeGroup.map f).ker_eq_bot_iff.mpr (FreeGroup.map_injective hf_inj.injective)]
    exact Subgroup.IsNormalClosureFG.bot

/-- `Multiplicative ℤ` is finitely presented. -/
instance : IsFinitelyPresented (Multiplicative ℤ) :=
  equiv (FreeGroup.mulEquivIntOfUnique : FreeGroup Unit ≃* Multiplicative ℤ) inferInstance

/-- ℤ is finitely presented -/
instance : AddGroup.IsFinitelyPresented ℤ :=
  AddGroup.IsFinitelyPresented.equiv
    (FreeAddGroup.addEquivIntOfUnique : FreeAddGroup Unit ≃+ ℤ) inferInstance

end Group.IsFinitelyPresented
