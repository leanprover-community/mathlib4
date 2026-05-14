/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib

/-!
# Locally Free Sheaves

A sheaf of modules is locally free if it is locally isomorphic to a free module.

-/

@[expose] public section

universe w u v₁ v₂ u₁ u₂

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

noncomputable section

namespace SheafOfModules

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

@[simps]
def free.generatingSections (I : Type u) : (free (R := R) I).GeneratingSections where
  I := I
  s (i) := freeSection i
  epi := by
    simp only [Equiv.symm_apply_apply]
    infer_instance

@[simp]
lemma free.generatingSections_π_id (I : Type u) :
    (free.generatingSections (R := R) I).π = 𝟙 (free I) :=
  Equiv.symm_apply_apply (free I).freeHomEquiv _

instance free.generatingSections.π_isIso (I : Type u) :
    IsIso (free.generatingSections (R := R) I).π := by
  simp only [generatingSections_I, generatingSections_π_id]
  infer_instance

end

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

structure LocallyFreeData (M : SheafOfModules.{u} R) where
  /-- the index type of the covering -/
  I : Type w
  /-- a family of objects which cover the terminal object -/
  X : I → C
  coversTop : J.CoversTop X
  /-- the index type for the iso -/
  ι : I → Type u
  /-- an isomorphism from a free module to `M.over (X i)` for any `i : I` -/
  freeIso (i : I) : free (ι i) ≅ M.over (X i)

section

open ZeroObject

@[simps]
def zero_generatingSections : (0 : SheafOfModules.{u} R).GeneratingSections where
  I := ULift Empty
  s (i) := Empty.rec (fun _ => sections 0) i.down
  epi := inferInstance

end

@[simps]
def free.presentation (I : Type u) : (free (R := R) I).Presentation where
  generators := free.generatingSections I
  relations := (GeneratingSections.equivOfIso (kernel.ofMono _)).symm zero_generatingSections

namespace LocallyFreeData

@[simps]
def quasiCoherentData {M : SheafOfModules.{u} R} (q : M.LocallyFreeData) :
    M.QuasicoherentData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  presentation (i) := Presentation.ofIsIso (q.freeIso i).hom (free.presentation (q.ι i))

end LocallyFreeData

def LocalGeneratorsData.locallyFreeData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    (h : ∀ i : q.I, IsIso (q.generators i).π) : M.LocallyFreeData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  ι (i) := (q.generators i).I
  freeIso (i) := asIso (q.generators i).π

example {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    (h : ∀ i : q.I, IsIso (q.generators i).π) :
    (q.locallyFreeData h).quasiCoherentData.localGeneratorsData = q := sorry

class IsLocallyFree (M : SheafOfModules.{u} R) : Prop where
  nonempty_locallyFreeData : Nonempty (LocallyFreeData.{u₁} M) := by infer_instance

end SheafOfModules

end
