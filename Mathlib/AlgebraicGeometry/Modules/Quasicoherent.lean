/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib

/-!
# Quasicoherent Sheaves

A module `M : X.Modules` is quasicoherent if it locally admits a presentation.

-/

@[expose] public section

universe u v₁ u₁

section

open CategoryTheory TopologicalSpace Topology Module

namespace AlgebraicGeometry.Scheme.Modules

theorem IsLocallyFree.local {X : Scheme.{u}} (M : X.Modules) :
    M.IsLocallyFree ↔ ∀ x : X, ∃ (U : Scheme.{u}) (f : U ⟶ X) (h : IsOpenImmersion f),
      x ∈ Set.range f ∧ (letI := h; (M.restrict f).IsLocallyFree) := sorry

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) [FinitePresentation R M]

instance [Module.Free R M] : (tilde M).IsFree := by
  let φ : tilde M ≅ _ := (tilde.functor R).mapIso (Module.Free.chooseBasis R M).repr.toModuleIso
    ≪≫ tildeFinsupp _
  have : (SheafOfModules.free (R := (Spec R).ringCatSheaf) (Free.ChooseBasisIndex R M)).IsFree :=
    inferInstance
  exact SheafOfModules.IsFree.ofIso.{u} φ.symm

variable [Module.Free R M]
#check (Module.Free.chooseBasis R M).repr

def freeLocusOpen : (Spec R).Opens := ⟨freeLocus R M, isOpen_freeLocus⟩

variable (ι : Type u)
#check (Scheme.Modules.fromTildeΓ (R := R) (SheafOfModules.free.{u} ι))

#check (tilde M).restrict (freeLocusOpen M).ι

theorem IsLocallyFree.of_restrict_freeLocusOpen :
    ((tilde M).restrict (freeLocusOpen M).ι).IsLocallyFree := by
  rw [IsLocallyFree.local]
  intro x
  have := x.1
  sorry

end AlgebraicGeometry.Scheme.Modules
