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

namespace SheafOfModules

noncomputable section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
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

@[simps]
def free.generatingSections (I : Type u) : (free (R := R) I).GeneratingSections where
  I := I
  s (i) := freeSection i
  epi := by
    simp only [Equiv.symm_apply_apply]
    infer_instance

variable (I : Type u)

instance free.generatingSections.π_isIso : IsIso (free.generatingSections (R := R) I).π := by
  sorry

variable [HasZeroObject (SheafOfModules R)]

set_option backward.isDefEq.respectTransparency false in
def free.relations : (kernel (free.generatingSections (R := R) I).π).GeneratingSections := by
  have := kernel.ofMono (free.generatingSections (R := R) I).π
  sorry

set_option backward.isDefEq.respectTransparency false in
def free.locallyFreeData (I : Type u) : (free (R := R) I).Presentation where
  generators := free.generatingSections I
  relations := {
    I := ULift Empty
    s (i) := PresheafOfModules.sectionsMk (fun _ => 0) (by simp)
    epi := by
      simp

      sorry
  }

namespace LocallyFreeData

def quasiCoherentData {M : SheafOfModules.{u} R} (q : M.LocallyFreeData) :
    M.QuasicoherentData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  presentation (i) := {
    generators := sorry
    relations := sorry
  }

end LocallyFreeData

end

end SheafOfModules
