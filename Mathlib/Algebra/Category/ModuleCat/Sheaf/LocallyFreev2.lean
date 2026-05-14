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

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

noncomputable section

namespace SheafOfModules

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Local generator data `q` is locally free data if all of the natural morphisms
`free (q.generators i).I ⟶ M.over (q.X i)` are isomorphisms -/
class IsLocallyFreeData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) : Prop where
  iso : ∀ i, IsIso (q.generators i).π

attribute [instance] IsLocallyFreeData.iso

end LocalGeneratorsData

/-- A sheaf of modules is locally free if there exists locally free data for it. -/
class IsLocallyFree (M : SheafOfModules.{u} R) : Prop where
  nonempty_locallyFreeData : ∃ q : M.LocalGeneratorsData, q.IsLocallyFreeData

end

section

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Given locally free data, this is the quasiCoherentData where there are no relations. -/
@[simps]
def quasiCoherentData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] :
    M.QuasicoherentData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  presentation (i) := {
    generators := q.generators i
    relations := {
      I := ULift Empty
      s (j) := Empty.rec (fun _ => (kernel (q.generators i).π).sections) j.down
      epi := IsZero.epi (IsZero.of_iso (isZero_zero _) (Limits.kernel.ofMono _)) _
    }
  }

@[simp]
lemma quasiCoherentData_localGeneratorsData {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] :
    q.quasiCoherentData.localGeneratorsData = q := rfl

end LocalGeneratorsData

instance (M : SheafOfModules.{u} R) [h : M.IsLocallyFree] : M.IsQuasicoherent :=
  have := h.nonempty_locallyFreeData.choose_spec
  h.nonempty_locallyFreeData.choose.quasiCoherentData.isQuasicoherent

end

end SheafOfModules
