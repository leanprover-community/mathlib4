/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import topology.category.Top.limits.basic from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/

-- Porting note: every ML3 decl has an uppercase letter
set_option linter.uppercaseLean3 false

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

universe v u w

noncomputable section

namespace TopCat

variable {J : Type v} [SmallCategory J]

local notation "forget" => forget TopCat

/-- A choice of limit cone for a functor `F : J ⥤ TopCat`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `Types.limitCone`).
-/
def limitCone (F : J ⥤ TopCat.{max v u}) : Cone F where
  pt := TopCat.of { u : ∀ j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j =>
        { toFun := fun u => u.val j
          -- Porting note: `continuity` from the original mathlib3 proof failed here.
          continuous_toFun := Continuous.comp (continuous_apply _) (continuous_subtype_val) }
      naturality := fun X Y f => by
        -- Automation fails in various ways in this proof. Why?!
        dsimp
        rw [Category.id_comp]
        apply ContinuousMap.ext
        intro a
        exact (a.2 f).symm }
#align Top.limit_cone TopCat.limitCone

/-- A choice of limit cone for a functor `F : J ⥤ TopCat` whose topology is defined as an
infimum of topologies infimum.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `Types.limitCone`).
-/
def limitConeInfi (F : J ⥤ TopCat.{max v u}) : Cone F where
  pt :=
    ⟨(Types.limitCone.{v,u} (F ⋙ forget)).pt,
      ⨅ j, (F.obj j).str.induced ((Types.limitCone.{v,u} (F ⋙ forget)).π.app j)⟩
  π :=
    { app := fun j =>
        ⟨(Types.limitCone.{v,u} (F ⋙ forget)).π.app j, continuous_iff_le_induced.mpr (iInf_le _ _)⟩
      naturality := fun _ _ f =>
        ContinuousMap.coe_injective ((Types.limitCone.{v,u} (F ⋙ forget)).π.naturality f) }
#align Top.limit_cone_infi TopCat.limitConeInfi

/-- The chosen cone `TopCat.limitCone F` for a functor `F : J ⥤ TopCat` is a limit cone.
Generally you should just use `limit.isLimit F`, unless you need the actual definition
(which is in terms of `Types.limitConeIsLimit`).
-/
def limitConeIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitCone.{v,u} F) where
  lift S :=
    { toFun := fun x =>
        ⟨fun j => S.π.app _ x, fun f => by
          dsimp
          erw [← S.w f]
          rfl⟩
      continuous_toFun :=
        Continuous.subtype_mk (continuous_pi fun j => (S.π.app j).2) fun x i j f => by
          dsimp
          rw [← S.w f]
          rfl }
  uniq S m h := by
    apply ContinuousMap.ext; intros a; apply Subtype.ext; funext j
    dsimp
    rw [← h]
    rfl
#align Top.limit_cone_is_limit TopCat.limitConeIsLimit

/-- The chosen cone `TopCat.limitConeInfi F` for a functor `F : J ⥤ TopCat` is a limit cone.
Generally you should just use `limit.isLimit F`, unless you need the actual definition
(which is in terms of `Types.limitConeIsLimit`).
-/
def limitConeInfiIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitConeInfi.{v,u} F) := by
  refine IsLimit.ofFaithful forget (Types.limitConeIsLimit.{v,u} (F ⋙ forget))
    -- Porting note: previously could infer all ?_ except continuity
    (fun s => ⟨fun v => ⟨fun j => (Functor.mapCone forget s).π.app j v, ?_⟩, ?_⟩) fun s => ?_
  · dsimp [Functor.sections]
    intro _ _ _
    rw [← comp_apply', forget_map_eq_coe, ← s.π.naturality, forget_map_eq_coe]
    dsimp
    rw [Category.id_comp]
  · exact
    continuous_iff_coinduced_le.mpr
      (le_iInf fun j =>
        coinduced_le_iff_le_induced.mp <|
          (continuous_iff_coinduced_le.mp (s.π.app j).continuous : _))
  · rfl
#align Top.limit_cone_infi_is_limit TopCat.limitConeInfiIsLimit

instance topCat_hasLimitsOfSize : HasLimitsOfSize.{v} TopCat.{max v u} where
  has_limits_of_shape _ :=
    { has_limit := fun F =>
        HasLimit.mk
          { cone := limitCone.{v,u} F
            isLimit := limitConeIsLimit F } }
#align Top.Top_has_limits_of_size TopCat.topCat_hasLimitsOfSize

instance topCat_hasLimits : HasLimits TopCat.{u} :=
  TopCat.topCat_hasLimitsOfSize.{u, u}
#align Top.Top_has_limits TopCat.topCat_hasLimits

instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize forget where
  preservesLimitsOfShape {_} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v,u} F)
          (Types.limitConeIsLimit.{v,u} (F ⋙ forget)) }
#align Top.forget_preserves_limits_of_size TopCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits forget :=
  TopCat.forgetPreservesLimitsOfSize.{u,u}
#align Top.forget_preserves_limits TopCat.forgetPreservesLimits

/-- A choice of colimit cocone for a functor `F : J ⥤ TopCat`.
Generally you should just use `colimit.cocone F`, unless you need the actual definition
(which is in terms of `Types.colimitCocone`).
-/
def colimitCocone (F : J ⥤ TopCat.{max v u}) : Cocone F where
  pt :=
    ⟨(Types.TypeMax.colimitCocone.{v,u} (F ⋙ forget)).pt,
      ⨆ j, (F.obj j).str.coinduced ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j)⟩
  ι :=
    { app := fun j =>
        ⟨(Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j, continuous_iff_coinduced_le.mpr <|
          -- Porting note: didn't need function before
          le_iSup (fun j =>
            coinduced ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j) (F.obj j).str) j⟩
      naturality := fun _ _ f =>
        ContinuousMap.coe_injective ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.naturality f) }
#align Top.colimit_cocone TopCat.colimitCocone

/-- The chosen cocone `TopCat.colimitCocone F` for a functor `F : J ⥤ TopCat` is a colimit cocone.
Generally you should just use `colimit.isColimit F`, unless you need the actual definition
(which is in terms of `Types.colimitCoconeIsColimit`).
-/
def colimitCoconeIsColimit (F : J ⥤ TopCat.{max v u}) : IsColimit (colimitCocone F) := by
  refine
    IsColimit.ofFaithful forget (Types.TypeMax.colimitCoconeIsColimit.{v, u} _) (fun s =>
    -- Porting note: it appears notation for forget breaks dot notation (also above)
    -- Porting note: previously function was inferred
      ⟨Quot.lift (fun p => (Functor.mapCocone forget s).ι.app p.fst p.snd) ?_, ?_⟩) fun s => ?_
  · intro _ _ ⟨_, h⟩
    dsimp
    rw [h, Functor.comp_map, ← comp_apply', s.ι.naturality]
    dsimp
    rw [Category.comp_id]
  · exact
    continuous_iff_le_induced.mpr
      (iSup_le fun j =>
        coinduced_le_iff_le_induced.mp <|
          (continuous_iff_coinduced_le.mp (s.ι.app j).continuous : _))
  · rfl
#align Top.colimit_cocone_is_colimit TopCat.colimitCoconeIsColimit

instance topCat_hasColimitsOfSize : HasColimitsOfSize.{v,v} TopCat.{max v u} where
  has_colimits_of_shape _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitCoconeIsColimit F } }
#align Top.Top_has_colimits_of_size TopCat.topCat_hasColimitsOfSize

instance topCat_hasColimits : HasColimits TopCat.{u} :=
  TopCat.topCat_hasColimitsOfSize.{u, u}
#align Top.Top_has_colimits TopCat.topCat_hasColimits

instance forgetPreservesColimitsOfSize :
    PreservesColimitsOfSize.{v, v} forget where
  preservesColimitsOfShape :=
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit F)
          (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget)) }
#align Top.forget_preserves_colimits_of_size TopCat.forgetPreservesColimitsOfSize

instance forgetPreservesColimits : PreservesColimits (forget : TopCat.{u} ⥤ Type u) :=
  TopCat.forgetPreservesColimitsOfSize.{u, u}
#align Top.forget_preserves_colimits TopCat.forgetPreservesColimits

/-- The terminal object of `Top` is `PUnit`. -/
def isTerminalPUnit : IsTerminal (TopCat.of PUnit.{u + 1}) :=
  haveI : ∀ X, Unique (X ⟶ TopCat.of PUnit.{u + 1}) := fun X =>
    ⟨⟨⟨fun _ => PUnit.unit, by continuity⟩⟩, fun f => by ext; aesop⟩
  Limits.IsTerminal.ofUnique _
#align Top.is_terminal_punit TopCat.isTerminalPUnit

/-- The terminal object of `Top` is `PUnit`. -/
def terminalIsoPUnit : ⊤_ TopCat.{u} ≅ TopCat.of PUnit :=
  terminalIsTerminal.uniqueUpToIso isTerminalPUnit
#align Top.terminal_iso_punit TopCat.terminalIsoPUnit

/-- The initial object of `Top` is `PEmpty`. -/
def isInitialPEmpty : IsInitial (TopCat.of PEmpty.{u + 1}) :=
  haveI : ∀ X, Unique (TopCat.of PEmpty.{u + 1} ⟶ X) := fun X =>
    ⟨⟨⟨fun x => x.elim, by continuity⟩⟩, fun f => by ext ⟨⟩⟩
  Limits.IsInitial.ofUnique _
#align Top.is_initial_pempty TopCat.isInitialPEmpty

/-- The initial object of `Top` is `PEmpty`. -/
def initialIsoPEmpty : ⊥_ TopCat.{u} ≅ TopCat.of PEmpty :=
  initialIsInitial.uniqueUpToIso isInitialPEmpty
#align Top.initial_iso_pempty TopCat.initialIsoPEmpty
