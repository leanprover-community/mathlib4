/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro, Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.Adjunctions
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/


open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

universe v u u' w

noncomputable section

local notation "forget" => forget TopCat

namespace TopCat

section Limits

variable {J : Type v} [Category.{w} J]

/-- A choice of limit cone for a functor `F : J ⥤ TopCat`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `Types.limitCone`).
-/
def limitCone (F : J ⥤ TopCat.{max v u}) : Cone F where
  pt := TopCat.of { u : ∀ j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j => ofHom
        { toFun := fun u => u.val j
          -- Porting note: `continuity` from the original mathlib3 proof failed here.
          continuous_toFun := Continuous.comp (continuous_apply _) (continuous_subtype_val) }
      naturality := fun X Y f => by
        ext a
        exact (a.2 f).symm }

/-- A choice of limit cone for a functor `F : J ⥤ TopCat` whose topology is defined as an
infimum of topologies infimum.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `Types.limitCone`).
-/
def limitConeInfi (F : J ⥤ TopCat.{max v u}) : Cone F where
  pt := @of
    ((Types.limitCone.{v,u} (F ⋙ forget)).pt)
    (⨅ j, (F.obj j).str.induced ((Types.limitCone.{v,u} (F ⋙ forget)).π.app j))
  π :=
    { app := fun j => @ofHom _ _ (_) (_) <| @ContinuousMap.mk _ _ (_) (_)
        ((Types.limitCone.{v,u} (F ⋙ forget)).π.app j)
        (continuous_iff_le_induced.mpr (iInf_le _ _))
      naturality := fun _ _ f =>
        ConcreteCategory.coe_ext ((Types.limitCone.{v,u} (F ⋙ forget)).π.naturality f) }

/-- The chosen cone `TopCat.limitCone F` for a functor `F : J ⥤ TopCat` is a limit cone.
Generally you should just use `limit.isLimit F`, unless you need the actual definition
(which is in terms of `Types.limitConeIsLimit`).
-/
def limitConeIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitCone.{v,u} F) where
  lift S := ofHom
    { toFun := fun x =>
        ⟨fun _ => S.π.app _ x, fun f => by
          dsimp
          rw [← S.w f]
          rfl⟩
      continuous_toFun :=
        Continuous.subtype_mk (continuous_pi fun j => (S.π.app j).hom.2) fun x i j f => by
          dsimp
          rw [← S.w f]
          rfl }
  uniq S m h := by
    ext a
    simp [← h]
    rfl

/-- The chosen cone `TopCat.limitConeInfi F` for a functor `F : J ⥤ TopCat` is a limit cone.
Generally you should just use `limit.isLimit F`, unless you need the actual definition
(which is in terms of `Types.limitConeIsLimit`).
-/
def limitConeInfiIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitConeInfi.{v,u} F) := by
  refine IsLimit.ofFaithful forget (Types.limitConeIsLimit.{v,u} (F ⋙ forget))
    -- Porting note: previously could infer all ?_ except continuity
    (fun s => @ofHom _ _ (_) (_) (@ContinuousMap.mk _ _ (_) (_)
      (fun v => ⟨fun j => (Functor.mapCone forget s).π.app j v, ?_⟩)
      ?_)) fun s => ?_
  · dsimp [Functor.sections]
    intro _ _ _
    rw [← ConcreteCategory.comp_apply, ← s.π.naturality]
    dsimp
  · exact
    continuous_iff_coinduced_le.mpr
      (le_iInf fun j =>
        coinduced_le_iff_le_induced.mp <|
          (continuous_iff_coinduced_le.mp (s.π.app j).hom.continuous :))
  · rfl

instance topCat_hasLimitsOfSize : HasLimitsOfSize.{w, v} TopCat.{max v u} where
  has_limits_of_shape _ :=
    { has_limit := fun F =>
        HasLimit.mk
          { cone := limitCone.{v,u} F
            isLimit := limitConeIsLimit F } }

instance topCat_hasLimits : HasLimits TopCat.{u} :=
  TopCat.topCat_hasLimitsOfSize.{u, u}

instance forget_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget : TopCat.{u} ⥤ _) where

instance forget_preservesLimits : PreservesLimits (forget : TopCat.{u} ⥤ _) where

end Limits

section Colimits

variable {J : Type v} [Category.{w} J] {F : J ⥤ TopCat.{u}}

section

variable (c : Cocone (F ⋙ forget))

/-- Given a functor `F : J ⥤ TopCat` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, this is the type `c.pt`
with the infimum of the topologies that are coinduced by the maps `c.ι.app j`. -/
def coconePtOfCoconeForget : Type _ := c.pt

instance topologicalSpaceCoconePtOfCoconeForget :
    TopologicalSpace (coconePtOfCoconeForget c) :=
  (⨆ j, (F.obj j).str.coinduced (c.ι.app j))

/-- Given a functor `F : J ⥤ TopCat` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, this is a cocone for `F` whose point is
`c.pt` with the infimum of the coinduced topologies by the maps `c.ι.app j`. -/
@[simps pt ι_app]
def coconeOfCoconeForget  : Cocone F where
  pt := of (coconePtOfCoconeForget c)
  ι :=
    { app j := ofHom (ContinuousMap.mk (c.ι.app j) (by
        rw [continuous_iff_coinduced_le]
        exact le_iSup (fun j ↦ (F.obj j).str.coinduced (c.ι.app j)) j))
      naturality j j' φ := by
        ext
        apply congr_fun (c.ι.naturality φ) }

/-- Given a functor `F : J ⥤ TopCat` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, the colimit of `F` is `c.pt` equipped
with the infimum of the coinduced topologies by the maps `c.ι.app j`. -/
def isColimitCoconeOfForget (c : Cocone (F ⋙ forget)) (hc : IsColimit c) :
    IsColimit (coconeOfCoconeForget c) := by
  refine IsColimit.ofFaithful forget (ht := hc)
    (fun s ↦ ofHom (ContinuousMap.mk (hc.desc ((forget).mapCocone s)) ?_)) (fun _ ↦ rfl)
  rw [continuous_iff_le_induced]
  dsimp [topologicalSpaceCoconePtOfCoconeForget]
  rw [iSup_le_iff]
  intro j
  rw [coinduced_le_iff_le_induced, induced_compose]
  convert continuous_iff_le_induced.1 (s.ι.app j).hom.continuous
  exact hc.fac ((forget).mapCocone s) j

end

@[deprecated (since := "2024-12-31")] alias colimitCocone := coconeOfCoconeForget
@[deprecated (since := "2024-12-31")] alias colimitCoconeIsColimit := isColimitCoconeOfForget

section IsColimit

variable (c : Cocone F) (hc : IsColimit c)

include hc

theorem coinduced_of_isColimit :
    c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j) := by
  let c' := coconeOfCoconeForget ((forget).mapCocone c)
  let hc' : IsColimit c' := isColimitCoconeOfForget _ (isColimitOfPreserves forget hc)
  let e := IsColimit.coconePointUniqueUpToIso hc' hc
  have he (j : J) : c'.ι.app j ≫ e.hom = c.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hc' hc j
  apply (homeoOfIso e).coinduced_eq.symm.trans
  dsimp [coconeOfCoconeForget_pt, c', topologicalSpaceCoconePtOfCoconeForget]
  simp only [coinduced_iSup, c']
  conv_rhs => simp only [← he]
  rfl

lemma isOpen_iff_of_isColimit (X : Set c.pt) :
    IsOpen X ↔ ∀ (j : J), IsOpen (c.ι.app j ⁻¹' X) := by
  trans (⨆ (j : J), (F.obj j).str.coinduced (c.ι.app j)).IsOpen X
  · rw [← coinduced_of_isColimit c hc, isOpen_fold]
  · simp only [← isOpen_coinduced]
    apply isOpen_iSup_iff

lemma isClosed_iff_of_isColimit (X : Set c.pt) :
    IsClosed X ↔ ∀ (j : J), IsClosed (c.ι.app j ⁻¹' X) := by
  simp only [← isOpen_compl_iff, isOpen_iff_of_isColimit _ hc,
    Functor.const_obj_obj, Set.preimage_compl]

lemma continuous_iff_of_isColimit {X : Type w} [TopologicalSpace X] (f : c.pt → X) :
    Continuous f ↔ ∀ (j : J), Continuous (f ∘ c.ι.app j) := by
  simp only [continuous_def, isOpen_iff_of_isColimit _ hc]
  tauto

end IsColimit

variable (F)

theorem colimit_topology (F : J ⥤ TopCat.{u}) [HasColimit F]:
    (colimit F).str = ⨆ j, (F.obj j).str.coinduced (colimit.ι F j) :=
  coinduced_of_isColimit _ (colimit.isColimit _)

theorem colimit_isOpen_iff (F : J ⥤ TopCat.{u}) [HasColimit F]
    (U : Set ((colimit F : _) : Type u)) :
    IsOpen U ↔ ∀ j, IsOpen (colimit.ι F j ⁻¹' U) := by
  apply isOpen_iff_of_isColimit _ (colimit.isColimit _)

lemma hasColimit_iff_small_quot :
    HasColimit F ↔ Small.{u} (Types.Quot (F ⋙ forget)) := by
  rw [← Types.hasColimit_iff_small_quot]
  constructor <;> intro
  · infer_instance
  · exact ⟨⟨_, isColimitCoconeOfForget _ (colimit.isColimit _)⟩⟩

instance topCat_hasColimitsOfSize : HasColimitsOfSize.{w, v} TopCat.{max v u} where
  has_colimits_of_shape _ := ⟨fun F ↦ by
    rw [hasColimit_iff_small_quot]
    infer_instance⟩

instance topCat_hasColimits : HasColimits TopCat.{u} :=
  TopCat.topCat_hasColimitsOfSize.{u, u}

instance forget_preservesColimitsOfSize :
    PreservesColimitsOfSize.{w, v} (forget : TopCat.{u} ⥤ _) where

instance forget_preservesColimits : PreservesColimits (forget : TopCat.{u} ⥤ Type u) where

end Colimits

/-- The terminal object of `Top` is `PUnit`. -/
def isTerminalPUnit : IsTerminal (TopCat.of PUnit.{u + 1}) :=
  haveI : ∀ X, Unique (X ⟶ TopCat.of PUnit.{u + 1}) := fun X =>
    ⟨⟨ofHom ⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext⟩
  Limits.IsTerminal.ofUnique _

/-- The terminal object of `Top` is `PUnit`. -/
def terminalIsoPUnit : ⊤_ TopCat.{u} ≅ TopCat.of PUnit :=
  terminalIsTerminal.uniqueUpToIso isTerminalPUnit

/-- The initial object of `Top` is `PEmpty`. -/
def isInitialPEmpty : IsInitial (TopCat.of PEmpty.{u + 1}) :=
  haveI : ∀ X, Unique (TopCat.of PEmpty.{u + 1} ⟶ X) := fun X =>
    ⟨⟨ofHom ⟨fun x => x.elim, by continuity⟩⟩, fun f => by ext ⟨⟩⟩
  Limits.IsInitial.ofUnique _

/-- The initial object of `Top` is `PEmpty`. -/
def initialIsoPEmpty : ⊥_ TopCat.{u} ≅ TopCat.of PEmpty :=
  initialIsInitial.uniqueUpToIso isInitialPEmpty

end TopCat
