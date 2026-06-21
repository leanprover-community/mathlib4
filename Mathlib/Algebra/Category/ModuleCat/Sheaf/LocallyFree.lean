/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackRestrict

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

universe u v₁ u₁ v₂ u₂ w

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

/-- Locally free data for `M` when `M` is locally free. -/
def locallyFreeData (M : SheafOfModules.{u} R) [M.IsLocallyFree] : M.LocalGeneratorsData :=
    IsLocallyFree.exists_locallyFreeData.choose

instance (M : SheafOfModules.{u} R) [M.IsLocallyFree] : M.locallyFreeData.IsLocallyFreeData :=
    IsLocallyFree.exists_locallyFreeData.choose_spec

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
  have := h.exists_locallyFreeData.choose_spec
  h.exists_locallyFreeData.choose.quasiCoherentData.isQuasicoherent

end

section

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
/-- Being locally free is local -/
theorem LocalGenertorsData.IsLocallFreeData.of_coversTop (M : SheafOfModules.{u} R) {I : Type w}
    (X : I → C) (hX : J.CoversTop X) (D : Π i, LocalGeneratorsData (M.over (X i)))
    [h : ∀ i, (D i).IsLocallyFreeData] : (LocalGeneratorsData.bind M X hX D).IsLocallyFreeData where
  iso i := by
    rw [LocalGeneratorsData.bind_generators, GeneratingSections.ofEpi_π,
      GeneratingSections.map_π_eq]
    infer_instance

theorem IsLocallyFree.of_coversTop (M : SheafOfModules.{u} R) {I : Type w} (X : I → C)
    (hX : J.CoversTop X) [h : ∀ i, (M.over (X i)).IsLocallyFree] :
    M.IsLocallyFree :=
  have := fun i => (h i).1.choose_spec
  have := LocalGenertorsData.IsLocallFreeData.of_coversTop M X hX (fun i => (h i).1.choose)
  (LocalGeneratorsData.bind M X hX (fun i => (h i).1.choose)).isLocallyFree

end

section Pullback

variable {D : Type u₂} [Category.{v₂} D] [HasBinaryProducts C] [HasBinaryProducts D]
  {K : GrothendieckTopology D} {F : C ⥤ D}
  [Functor.PreservesOneHypercovers F J K] [Limits.PreservesLimitsOfShape (Discrete WalkingPair) F]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (K.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (pushforward.{u} (StructureHomOver φ X)).IsRightAdjoint]
  [F.Final] [(pushforward.{u} φ).IsRightAdjoint]

/-- The pullback of local generator data. -/
@[expose, simps]
protected def LocalGeneratorsData.pullback {M : SheafOfModules.{u} S} (q : M.LocalGeneratorsData) :
    ((pullback φ).obj M).LocalGeneratorsData where
  I := q.I
  X i := F.obj (q.X i)
  coversTop := q.coversTop.map J _ K CoverPreserving.of_preservesOneHypercovers
  generators i := ((q.generators i).map _ (asIso (pullbackObjUnitToUnit _)).symm).ofEpi
    (M.overPullbackIso φ (q.X i)).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
protected instance (priority := 100) LocalGeneratorsData.IsLocallyFreeData.pullback
    {M : SheafOfModules.{u} S} (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] :
    (q.pullback φ).IsLocallyFreeData where
  iso i := by simpa [GeneratingSections.map_π_eq] using (by infer_instance)

protected instance IsLocallyFree.pullback {M : SheafOfModules.{u} S} [M.IsLocallyFree] :
    ((pullback φ).obj M).IsLocallyFree := (M.locallyFreeData.pullback φ).isLocallyFree

end Pullback

end SheafOfModules
