/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finitely Presented Groups

This file defines finitely presented groups.

## Main definitions
* `Subgroup.IsNormalClosureFG N`: says that the subgroup `N` is the normal closure of a
  finitely generated subgroup.
* `IsFinitelyPresented`: defines when a group is finitely presented.

## Main results
* `Subgroup.IsNormalClosureFG.map`: Being the normal closure of a finite set is preserved under
  surjective homomorphism.
* `IsFinitelyPresented.equiv`: finitely presented groups are closed under isomorphism.

## Tags
finitely presented group, finitely generated normal closure
-/

@[expose] public section

variable {G H α β : Type*} [Group G] [Group H]

/-- `N.IsNormalClosureFG` says that the subgroup `N` is the normal closure of a finitely-generated
subgroup. -/
@[to_additive /-- `N.IsNormalClosureFG` says that the additive subgroup `N` is the normal closure
of an additive finitely-generated subgroup. -/]
def Subgroup.IsNormalClosureFG (N : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = N

namespace Subgroup.IsNormalClosureFG

/-- Being the normal closure of a finite set is invariant under surjective homomorphism. -/
@[to_additive /-- Being the additive normal closure of a finite set is invariant under
surjective homomorphism. -/]
protected theorem map {N : Subgroup G} (hN : N.IsNormalClosureFG)
    {f : G →* H} (hf : Function.Surjective f) : (N.map f).IsNormalClosureFG := by
  obtain ⟨S, hSfinite, hSclosure⟩ := hN
  refine ⟨f '' S, hSfinite.image _, ?_⟩
  rw [← hSclosure, Subgroup.map_normalClosure _ _ hf]

/-- The trivial group is the normal closure of a finite set of relations. -/
@[to_additive /-- The trivial additive group is the normal closure of a finite set of relations. -/]
protected theorem bot : (⊥ : Subgroup G).IsNormalClosureFG :=
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
  rwa [φ.ker_mulEquiv_comp iso]

/-- A free group with a finite number of generators is finitely presented. -/
@[to_additive /-- A free additive group with a finite number of generators is finitely presented. -/
]
instance [Finite α] : IsFinitelyPresented (FreeGroup α) := by
  have ⟨n, _, f, hf_surj, hf_inj⟩ := Finite.exists_equiv_fin α
  refine ⟨n, FreeGroup.map f, FreeGroup.map_surjective hf_surj.surjective, ?_⟩
  · rw [(FreeGroup.map f).ker_eq_bot (FreeGroup.map_injective hf_inj.injective)]
    exact .bot

/-- `Multiplicative ℤ` is finitely presented. -/
instance : IsFinitelyPresented (Multiplicative ℤ) :=
  equiv (FreeGroup.mulEquivIntOfUnique : FreeGroup Unit ≃* Multiplicative ℤ) inferInstance

/-- ℤ is finitely presented -/
instance : AddGroup.IsFinitelyPresented ℤ :=
  AddGroup.IsFinitelyPresented.equiv
    (FreeAddGroup.addEquivIntOfUnique : FreeAddGroup Unit ≃+ ℤ) inferInstance

open QuotientGroup in
/-- The free product of finitely presented groups is finitely presented -/
instance [hg : IsFinitelyPresented G] [hh : IsFinitelyPresented H] :
    IsFinitelyPresented (Monoid.Coprod G H) := by
  obtain ⟨ng, φg, hφgsurj, setg, hsetgfin, setgker⟩ := hg
  obtain ⟨nh, φh, hφhsurj, seth, hsethfin, sethker⟩ := hh
  refine equiv (MulEquiv.coprodCongr
    ((quotientKerEquivOfSurjective φg hφgsurj).symm.trans (quotientMulEquivOfEq setgker.symm))
    ((quotientKerEquivOfSurjective φh hφhsurj).symm.trans (quotientMulEquivOfEq sethker.symm))).symm
    <| equiv (PresentedGroup.coprodPresentations setg seth) ?_
  use ng + nh
  let s := (FreeGroup.map Sum.inl '' setg ∪ FreeGroup.map Sum.inr '' seth)
  suffices ∃ ψ : FreeGroup (Fin ng ⊕ Fin nh) →* PresentedGroup s,
    Function.Surjective ψ ∧ ψ.ker.IsNormalClosureFG by
    rcases this with ⟨ψ, hsurj, hfg⟩
    let toDisjoint : FreeGroup (Fin (ng + nh)) ≃* FreeGroup (Fin ng ⊕ Fin nh) :=
      FreeGroup.freeGroupCongr (finSumFinEquiv).symm
    refine ⟨ψ.comp toDisjoint, hsurj.comp toDisjoint.surjective, ?_⟩
    simp only [MonoidHom.ker_comp_mulEquiv]
    exact Subgroup.IsNormalClosureFG.map (hfg) (toDisjoint.symm.surjective)
  exact ⟨PresentedGroup.mk s, PresentedGroup.mk_surjective s, s,
    (hsetgfin.image (FreeGroup.map Sum.inl)).union (hsethfin.image (FreeGroup.map Sum.inr)),
    (QuotientGroup.ker_mk' (Subgroup.normalClosure s)).symm⟩
end Group.IsFinitelyPresented
