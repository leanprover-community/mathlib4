/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

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
`free (q.generators i).I ⟶ M.over (q.X i)` are isomorphisms -/
class IsLocallyFreeData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) : Prop where
  iso : ∀ i, IsIso (q.generators i).π := by infer_instance

attribute [instance] IsLocallyFreeData.iso

instance IsLocallyFreeData.shrink {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] : q.shrink.IsLocallyFreeData where
  iso i := inferInstanceAs (IsIso (q.generators i.2.choose).π)

end LocalGeneratorsData

/-- A sheaf of modules is locally free if there exists locally free data for it. -/
class IsLocallyFree (M : SheafOfModules.{u} R) : Prop where
  exists_locallyFreeData : ∃ q : LocalGeneratorsData.{u₁} M, q.IsLocallyFreeData

theorem LocalGeneratorsData.isLocallyFree {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] : M.IsLocallyFree := ⟨q.shrink, inferInstance⟩

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
lemma free.generatingSections_π_id (I : Type u) :
    (free.generatingSections (R := R) I).π = 𝟙 (free I) :=
  Equiv.symm_apply_apply (free I).freeHomEquiv _

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}] [HasBinaryProducts C]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat]

set_option backward.isDefEq.respectTransparency false in
instance (I : Type u) :
    (free.generatingSections (R := R) I).localGeneratorsData.IsLocallyFreeData where
  iso i := by
    dsimp
    simp only [GeneratingSections.map_π_eq, free.generatingSections_I, free.generatingSections_π_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    infer_instance

instance (I : Type u) : (free (R := R) I).IsLocallyFree where
  exists_locallyFreeData := ⟨(free.generatingSections I).localGeneratorsData, inferInstance⟩

end

section

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Given locally free data, this is the quasiCoherentData where there are no relations. -/
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

section

/- This section shows that the pullback of a locally free sheaf is locally free. -/

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  {M : SheafOfModules.{u} S}

variable [(pushforward.{u} φ).IsRightAdjoint]

variable [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

def GeneratingSections.pullback [F.Final] (G : M.GeneratingSections) :
    ((pullback φ).obj M).GeneratingSections :=
  G.map (SheafOfModules.pullback φ) (asIso (pullbackObjUnitToUnit φ)).symm

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable [∀ X, (K.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, ((K.over X).over Y).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X Y, HasSheafify ((K.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((K.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable [∀ X, Functor.IsContinuous (Over.post F) (J.over X) (K.over (F.obj X))]
  [∀ X, (Over.post (X := X) F).Final]

def overStarPostIso [HasBinaryProducts C] [HasBinaryProducts D] (X : C)
    [h : ∀ Y, IsIso (prodComparison F X Y)] :
    Over.star X ⋙ Over.post F ≅ F ⋙ Over.star (F.obj X) :=
  NatIso.ofComponents (fun Y =>
    letI := h Y
    let e := asIso (prodComparison F X Y)
    Over.isoMk e (by
      dsimp [e]
      simpa only [prod.lift_fst, Functor.map_comp] using (prodComparison_fst F X Y)))
    (fun f => by
      ext
      dsimp
      rw [prodComparison_natural]
      simp)

def overPullbackHom (X : C) :
    S.over X ⟶ ((Over.post F).sheafPushforwardContinuous RingCat.{u}
      (J.over X) (K.over (F.obj X))).obj (R.over (F.obj X)) :=
  letI : Functor.IsContinuous (Over.forget X ⋙ F) (J.over X) K :=
    (Over.forget X).isContinuous_comp F (J.over X) J K
  letI : Functor.IsContinuous (Over.post F ⋙ Over.forget (F.obj X)) (J.over X) K :=
    (Over.post F).isContinuous_comp (Over.forget (F.obj X)) (J.over X) (K.over (F.obj X)) K
  (J.overPullback RingCat.{u} X).map φ ≫
    ((Over.forget X).sheafPushforwardContinuousComp F RingCat.{u} (J.over X) J K).hom.app R ≫
    (Functor.sheafPushforwardContinuousIso (eqToIso (Over.post_forget_eq_forget_comp F X).symm)
      RingCat.{u} (J.over X) K).hom.app R ≫
    (Functor.sheafPushforwardContinuousComp (Over.post F) (Over.forget (F.obj X))
      RingCat.{u} (J.over X) (K.over (F.obj X)) K).inv.app R

variable [∀ X, (pushforward (overPullbackHom φ X)).IsRightAdjoint]

variable [HasBinaryProducts C] [HasBinaryProducts D]
  [∀ X Y, IsIso (prodComparison F X Y)]
  [∀ X, Functor.IsContinuous (Over.star X ⋙ Over.post F) J (K.over (F.obj X))]
  [∀ X, Functor.IsContinuous (F ⋙ Over.star (F.obj X)) J (K.over (F.obj X))]

def overPullbackHomComp (X : C) :
    S ⟶ ((Over.star X ⋙ Over.post F).sheafPushforwardContinuous RingCat.{u}
      J (K.over (F.obj X))).obj (R.over (F.obj X)) :=
  pushforwardOver (R := S) X ≫
    ((Over.star X).sheafPushforwardContinuous RingCat.{u}
      J (J.over X)).map (overPullbackHom φ X)

def pullbackOverHomComp (X : C) :
    S ⟶ ((F ⋙ Over.star (F.obj X)).sheafPushforwardContinuous RingCat.{u}
      J (K.over (F.obj X))).obj (R.over (F.obj X)) :=
  φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map (pushforwardOver (R := R) (F.obj X))

-- The componentwise reduction in `overPullbackHomComp_eq` unfolds several
-- sheaf-pushforward definitions.
set_option linter.flexible false in
omit [(pushforward φ).IsRightAdjoint] [HasSheafify K AddCommGrpCat]
  [K.WEqualsLocallyBijective AddCommGrpCat]
  [K.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]
  [∀ X Y, ((J.over X).over Y).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat]
  [∀ X, (K.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat]
  [∀ X Y, ((K.over X).over Y).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ X Y, HasSheafify ((K.over X).over Y) AddCommGrpCat]
  [∀ X Y, ((K.over X).over Y).WEqualsLocallyBijective AddCommGrpCat]
  [∀ X, (Over.post (X := X) F).Final]
  [∀ X, (pushforward (overPullbackHom φ X)).IsRightAdjoint] in
lemma overPullbackHomComp_eq (X : C) :
    overPullbackHomComp φ X ≫
      (Functor.sheafPushforwardContinuousNatTrans (overStarPostIso (F := F) X).symm.hom
        RingCat.{u} J (K.over (F.obj X))).app (R.over (F.obj X)) =
    pullbackOverHomComp φ X := by
  ext U : 3
  simp [overPullbackHomComp, pullbackOverHomComp, overPullbackHom, pushforwardOver,
    overStarPostIso]
  have hnat :
      S.obj.map (prod.snd : X ⨯ U.unop ⟶ U.unop).op ≫
          φ.hom.app (Opposite.op (X ⨯ U.unop)) =
        φ.hom.app U ≫ R.obj.map (F.map (prod.snd : X ⨯ U.unop ⟶ U.unop)).op := by
    simpa using φ.hom.naturality (prod.snd : X ⨯ U.unop ⟶ U.unop).op
  haveI : IsIso (prodComparison F X U.unop) := inferInstance
  haveI : IsIso ((prodComparison F X U.unop).op) := inferInstance
  haveI : IsIso (R.obj.map (prodComparison F X U.unop).op) := inferInstance
  change (S.obj.map (prod.snd : X ⨯ U.unop ⟶ U.unop).op ≫
      φ.hom.app (Opposite.op (X ⨯ U.unop))) ≫ _ = _
  rw [hnat]
  have hbc :
      R.obj.map (F.map (prod.snd : X ⨯ U.unop ⟶ U.unop)).op ≫
          inv (R.obj.map (prodComparison F X U.unop).op) =
        R.obj.map prod.snd.op := by
    simp [← Functor.map_comp, ← op_comp]
  simpa [Category.assoc] using congrArg (fun f => φ.hom.app U ≫ f) hbc

def overPullbackRightAdjointIso (X : C) :
    pushforward (overPullbackHom φ X) ⋙ pushforward (pushforwardOver (R := S) X) ≅
      pushforward (pushforwardOver (R := R) (F.obj X)) ⋙ pushforward φ :=
  pushforwardComp (pushforwardOver (R := S) X) (overPullbackHom φ X) ≪≫
    pushforwardNatIso (overPullbackHomComp φ X) (overStarPostIso (F := F) X).symm ≪≫
    pushforwardCongr (overPullbackHomComp_eq φ X) ≪≫
    (pushforwardComp φ (pushforwardOver (R := R) (F.obj X))).symm

def pullbackOverIso (X : C) :
    pushforward (𝟙 (S.over X)) ⋙ pullback (overPullbackHom φ X) ≅
      pullback φ ⋙ pushforward (𝟙 (R.over (F.obj X))) :=
  Adjunction.leftAdjointUniq
    (((overPushforwardOverAdj (R := S) X).comp
      (pullbackPushforwardAdjunction (overPullbackHom φ X))).ofNatIsoRight
        (overPullbackRightAdjointIso φ X))
    ((pullbackPushforwardAdjunction φ).comp
      (overPushforwardOverAdj (R := R) (F.obj X)))

def LocalGeneratorsData.pullback (q : M.LocalGeneratorsData)
    (hX : K.CoversTop (fun i => F.obj (q.X i))) :
    ((pullback φ).obj M).LocalGeneratorsData where
  I := q.I
  X i := F.obj (q.X i)
  coversTop := hX
  generators i :=
    ((q.generators i).pullback (overPullbackHom φ (q.X i))).ofEpi
      ((pullbackOverIso φ (q.X i)).app M).hom

end

end SheafOfModules
