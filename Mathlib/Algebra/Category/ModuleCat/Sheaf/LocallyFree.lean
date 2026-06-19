/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Locally Free Sheaves

A sheaf of modules is locally free if it is locally isomorphic to a free module.

## Main Definitions

- `SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`: This is defined as a predicate on
  `SheafOfModules.LocalGeneratorData` where `q : M.LocalGeneratorData` is said to be locally
  free data if `(q.generators i).π` is an isomorphism for all `i` in `q.I`.

- `SheafOfModules.IsLocallyFree`: `M : SheafOfModules R` is locally free is there exists locally
  free data for it.

-/

public section

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

noncomputable section

namespace SheafOfModules

section

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Local generator data `q` is locally free data if all of the natural morphisms
`free (q.generators i).I ⟶ M.over (q.X i)` are isomorphisms. -/
class IsLocallyFreeData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) : Prop where
  isIso : ∀ i, IsIso (q.generators i).π := by infer_instance

attribute [instance] IsLocallyFreeData.isIso

instance IsLocallyFreeData.shrink {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] : q.shrink.IsLocallyFreeData where
  isIso i := inferInstanceAs (IsIso (q.generators i.2.choose).π)

end LocalGeneratorsData

/-- A sheaf of modules is locally free if it is locally isomorphic to free sheaves:
There exist local generators satisfying `IsLocallyFreeData`. -/
@[stacks 01C6 "(1)"]
class IsLocallyFree (M : SheafOfModules.{u} R) : Prop where
  exists_isLocallyFreeData : ∃ q : LocalGeneratorsData.{u₁} M, q.IsLocallyFreeData

theorem LocalGeneratorsData.isLocallyFree {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] : M.IsLocallyFree := ⟨q.shrink, inferInstance⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : ObjectProperty.IsClosedUnderIsomorphisms (IsLocallyFree (R := R)) where
  of_iso e := by
    intro ⟨q, hq⟩
    have : (q.ofEpi e.hom).IsLocallyFreeData := {
      isIso i := by
        have : IsIso (Hom.over e.hom (q.X i)) := inferInstance
        simpa
    }
    exact LocalGeneratorsData.isLocallyFree (q.ofEpi e.hom)
end

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- The generating sections of the free sheaf of modules. -/
@[expose, simps]
def free.generatingSections (I : Type u) : (free (R := R) I).GeneratingSections where
  I := I
  s (i) := freeSection i
  epi := by
    simp only [Equiv.symm_apply_apply]
    infer_instance

@[simp]
lemma free.generatingSections_π (I : Type u) :
    (free.generatingSections (R := R) I).π = 𝟙 (free I) :=
  Equiv.symm_apply_apply (free I).freeHomEquiv _

set_option backward.isDefEq.respectTransparency false in
instance (I : Type u) : IsIso (free.generatingSections (R := R) I).π := by
  rw [free.generatingSections_π]
  infer_instance

class IsFree (M : SheafOfModules.{u} R) : Prop where
  isIso : ∃ G : M.GeneratingSections, IsIso (G.π)

set_option backward.isDefEq.respectTransparency false in
instance IsFree.isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (IsFree (R := R)) where
  of_iso e := by
    intro ⟨G, _⟩
    use G.ofEpi e.hom
    have : IsIso e.hom := inferInstance
    simpa

instance free.isFree (I : Type u) : (free (R := R) I).IsFree :=
  ⟨free.generatingSections I, inferInstance⟩

theorem IsFree.iso_free (M : SheafOfModules.{u} R) : M.IsFree ↔
    ∃ I : Type u, Nonempty (M ≅ free I) := by
  constructor
  · rintro ⟨G, _⟩
    use G.I
    exact ⟨(asIso G.π).symm⟩
  rintro ⟨I, ⟨φ⟩⟩
  exact ObjectProperty.prop_of_iso IsFree φ.symm (free.isFree I)

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}] [HasBinaryProducts C]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (I : Type u) :
    (free.generatingSections (R := R) I).localGeneratorsData.IsLocallyFreeData where
  isIso i := by
    dsimp
    infer_instance

instance (I : Type u) : (free (R := R) I).IsLocallyFree where
  exists_isLocallyFreeData := ⟨(free.generatingSections I).localGeneratorsData, inferInstance⟩

instance (priority := 100) IsFree.isLocallyFree (M : SheafOfModules.{u} R) [M.IsFree] :
    M.IsLocallyFree := by
  obtain ⟨I, ⟨φ⟩⟩ := (IsFree.iso_free M).mp inferInstance
  exact ObjectProperty.prop_of_isIso SheafOfModules.IsLocallyFree φ.inv inferInstance

end

section

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Given locally free data, this is the `QuasiCoherentData` where there are no relations. -/
@[expose, simps]
def quasiCoherentData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] :
    M.QuasicoherentData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  presentation i := {
    generators := q.generators i
    relations.I := ULift Empty
    relations.s j := Empty.rec _ j.down
    relations.epi := IsZero.epi (IsZero.of_iso (isZero_zero _) (Limits.kernel.ofMono _)) _ }

@[simp]
lemma quasiCoherentData_localGeneratorsData {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] :
    q.quasiCoherentData.localGeneratorsData = q := rfl

end LocalGeneratorsData

instance (priority := 100) (M : SheafOfModules.{u} R) [h : M.IsLocallyFree] : M.IsQuasicoherent :=
  have := h.exists_isLocallyFreeData.choose_spec
  h.exists_isLocallyFreeData.choose.quasiCoherentData.isQuasicoherent

end

end SheafOfModules
