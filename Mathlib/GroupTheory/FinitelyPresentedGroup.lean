/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu, Javier Gómez Zaragoza
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Schreier
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finite.Sum
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finitely Presented Groups

This file defines finitely presented groups.

## Main definitions
* `Subgroup.IsFinitelyNormallyGenerated N`: says that the subgroup `N` is the normal closure of a
  finitely generated subgroup.
* `IsFinitelyPresented`: defines when a group is finitely presented.

## Main results
* `Subgroup.IsFinitelyNormallyGenerated.map`: Being the normal closure of a finite set is preserved
under surjective homomorphism.
* `IsFinitelyPresented.equiv`: finitely presented groups are closed under isomorphism.

## Tags
finitely presented group, finitely generated normal closure
-/

@[expose] public section

variable {G H α β : Type*} [Group G] [Group H]

/-- `N.IsFinitelyNormallyGenerated` says that the subgroup `N` is the normal closure
 of a finitely-generated subgroup. -/
@[to_additive /-- `N.IsFinitelyNormallyGenerated` says that the additive subgroup `N`
is the normal closure of an additive finitely-generated subgroup. -/]
def Subgroup.IsFinitelyNormallyGenerated (N : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = N

@[deprecated (since := "2026-06-25")]
alias Subgroup.IsNormalClosureFG := Subgroup.IsFinitelyNormallyGenerated

namespace Subgroup.IsFinitelyNormallyGenerated

/-- Being the normal closure of a finite set is invariant under surjective homomorphism. -/
@[to_additive /-- Being the additive normal closure of a finite set is invariant under
surjective homomorphism. -/]
protected theorem map {N : Subgroup G} (hN : N.IsFinitelyNormallyGenerated)
    {f : G →* H} (hf : Function.Surjective f) : (N.map f).IsFinitelyNormallyGenerated := by
  obtain ⟨S, hSfinite, hSclosure⟩ := hN
  refine ⟨f '' S, hSfinite.image _, ?_⟩
  rw [← hSclosure, Subgroup.map_normalClosure _ _ hf]

@[to_additive]
theorem of_FG (N : Subgroup G) [N.Normal] [h : Group.FG N] : N.IsFinitelyNormallyGenerated := by
  obtain ⟨S, rfl, hS⟩ := N.fg_iff.mp ((Group.fg_iff_subgroup_fg N).mp h)
  exact ⟨S, hS, le_antisymm (normalClosure_le_normal subset_closure) closure_le_normalClosure⟩

open Function Set Subgroup in
/-- The preimage of a finitely generated normal subgroup by a surjective homomorphism with
a finitely generated kernel is finitely generated. -/
@[to_additive /-- The preimage of a finitely generated normal subgroup by a surjective additive
homomorphism with a finitely generated kernel is finitely generated. -/]
protected theorem comap {N : Subgroup H} (hN : N.IsFinitelyNormallyGenerated)
    {f : G →* H} (hf : Surjective f) (hf' : f.ker.IsFinitelyNormallyGenerated) :
    (N.comap f).IsFinitelyNormallyGenerated := by
  obtain ⟨S, hS_fin, hS⟩ := hN
  obtain ⟨T, hT_fin, hT⟩ := hf'
  have : ∃ S', S'.Finite ∧ f '' S' = S :=
    ⟨surjInv hf '' S, hS_fin.image _, by rw [← image_comp, comp_surjInv, image_id]⟩
  clear hS_fin
  obtain ⟨S, hS_fin, rfl⟩ := this
  refine ⟨S ∪ T, hS_fin.union hT_fin, ?_⟩
  rw [← hS, ← map_normalClosure S f hf, comap_map_eq, ← hT, normalClosure_union]

/-- The trivial group is the normal closure of a finite set of relations. -/
@[to_additive /-- The trivial additive group is the normal closure of a finite set of relations. -/]
protected theorem bot : (⊥ : Subgroup G).IsFinitelyNormallyGenerated := of_FG _

end Subgroup.IsFinitelyNormallyGenerated

/-- An additive group is finitely presented if it has a finite generating set such that the kernel
of the induced map from the free additive group on that set is the normal closure
of finitely many relations. -/
class AddGroup.IsFinitelyPresented (G : Type*) [AddGroup G] : Prop where
  out : ∃ (n : ℕ) (φ : FreeAddGroup (Fin n) →+ G),
  Function.Surjective φ ∧ φ.ker.IsFinitelyNormallyGenerated

/-- A group is finitely presented if it has a finite generating set such that the kernel
of the induced map from the free group on that set is the normal closure of finitely many
relations. -/
@[mk_iff, to_additive existing]
class Group.IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (φ : FreeGroup (Fin n) →* G),
  Function.Surjective φ ∧ φ.ker.IsFinitelyNormallyGenerated

namespace Group.IsFinitelyPresented

/-- Finitely presented groups are closed under isomorphism. -/
@[to_additive /-- Finitely presented additive groups are closed under additive isomorphism. -/
]
theorem equiv (iso : G ≃* H) [h : IsFinitelyPresented G] : IsFinitelyPresented H := by
  obtain ⟨n, φ, hφsurj, hNC⟩ := h
  refine ⟨n, (iso : G →* H).comp φ, iso.surjective.comp hφsurj, ?_⟩
  rwa [φ.ker_mulEquiv_comp iso]

/-- The image of a finitely presented group under a surjective homomorphism whose kernel is
finitely generated as a normal subgroup is finitely presented. -/
@[to_additive /-- The image of a finitely presented additive group under a surjective additive
homomorphism whose kernel is finitely generated as a normal subgroup is finitely presented. -/]
theorem of_surjective [hG : IsFinitelyPresented G] (f : G →* H)
    (hf_surj : Function.Surjective f) (hf_ker : f.ker.IsFinitelyNormallyGenerated) :
    IsFinitelyPresented H := by
  obtain ⟨n, φ, hφ_surj, hφ_ker⟩ := hG.out
  refine ⟨n, f.comp φ, hf_surj.comp hφ_surj, ?_⟩
  rw [← MonoidHom.comap_ker]
  exact hf_ker.comap hφ_surj hφ_ker

/-- The quotient of a finitely presented group by a subgroup
which is finitely generated as a normal subgroup is finitely presented. -/
@[to_additive /-- The quotient of a finitely presented additive group by an additive subgroup
which is finitely generated as a normal subgroup is finitely presented. -/]
theorem quotient [hG : IsFinitelyPresented G] (N : Subgroup G) [N.Normal]
    (hN : N.IsFinitelyNormallyGenerated) : IsFinitelyPresented (G ⧸ N) :=
  of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    ((QuotientGroup.ker_mk' N).symm ▸ hN)

open QuotientGroup in
theorem exists_mulEquiv_presentedGroup [hg : IsFinitelyPresented G] :
    ∃ n : ℕ, ∃ s : Set (FreeGroup (Fin n)), Set.Finite s ∧ Nonempty (G ≃* PresentedGroup s) := by
  obtain ⟨n, φ, hφ, s, hs, hsφ⟩ := hg
  exact ⟨n, s, hs, ⟨(quotientKerEquivOfSurjective φ hφ).symm.trans (quotientMulEquivOfEq hsφ.symm)⟩⟩

/-- A free group with a finite number of generators is finitely presented. -/
@[to_additive /-- A free additive group with a finite number of generators is finitely presented. -/
]
instance [Finite α] : IsFinitelyPresented (FreeGroup α) := by
  have ⟨n, _, f, hf_surj, hf_inj⟩ := Finite.exists_equiv_fin α
  refine ⟨n, FreeGroup.map f, FreeGroup.map_surjective hf_surj.surjective, ?_⟩
  · rw [(FreeGroup.map f).ker_eq_bot (FreeGroup.map_injective hf_inj.injective)]
    exact .bot

instance [Finite α] (s : Set (FreeGroup α)) [Finite s] :
    IsFinitelyPresented (PresentedGroup s) :=
  of_surjective (PresentedGroup.mk s) (PresentedGroup.mk_surjective s)
    ⟨s, ‹_›, (QuotientGroup.ker_mk' (Subgroup.normalClosure s)).symm⟩

/-- `Multiplicative ℤ` is finitely presented. -/
instance : IsFinitelyPresented (Multiplicative ℤ) :=
  equiv (FreeGroup.mulEquivIntOfUnique : FreeGroup Unit ≃* Multiplicative ℤ)

/-- ℤ is finitely presented -/
instance : AddGroup.IsFinitelyPresented ℤ :=
  AddGroup.IsFinitelyPresented.equiv (FreeAddGroup.addEquivIntOfUnique : FreeAddGroup Unit ≃+ ℤ)

/-- The free product of finitely presented groups is finitely presented -/
instance [IsFinitelyPresented G] [IsFinitelyPresented H] :
    IsFinitelyPresented (Monoid.Coprod G H) := by
  obtain ⟨_, sG, ⟨_ : Finite sG, ⟨φG⟩⟩⟩ := exists_mulEquiv_presentedGroup (G := G)
  obtain ⟨_, sH, ⟨_ : Finite sH, ⟨φH⟩⟩⟩ := exists_mulEquiv_presentedGroup (G := H)
  exact equiv ((PresentedGroup.coprodPresentations sG sH).trans (MulEquiv.coprodCongr φG φH).symm)

variable (G)

/-- Any finite group is finitely presented. -/
@[to_additive]
instance [Finite G] : IsFinitelyPresented G :=
  of_surjective FreeGroup.prod FreeGroup.prod_surjective (.of_FG FreeGroup.prod.ker)

end Group.IsFinitelyPresented
