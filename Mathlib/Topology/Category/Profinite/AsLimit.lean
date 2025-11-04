/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Adam Topaz
-/
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.DiscreteQuotient

/-!
# Profinite sets as limits of finite sets.

We show that any profinite set is isomorphic to the limit of its
discrete (hence finite) quotients.

## Definitions

There are a handful of definitions in this file, given `X : Profinite`:
1. `X.fintypeDiagram` is the functor `DiscreteQuotient X ⥤ FintypeCat` whose limit
  is isomorphic to `X` (the limit taking place in `Profinite` via `FintypeCat.toProfinite`, see 2).
2. `X.diagram` is an abbreviation for `X.fintypeDiagram ⋙ FintypeCat.toProfinite`.
3. `X.asLimitCone` is the cone over `X.diagram` whose cone point is `X`.
4. `X.isoAsLimitConeLift` is the isomorphism `X ≅ (Profinite.limitCone X.diagram).X` induced
  by lifting `X.asLimitCone`.
5. `X.asLimitConeIso` is the isomorphism `X.asLimitCone ≅ (Profinite.limitCone X.diagram)`
  induced by `X.isoAsLimitConeLift`.
6. `X.asLimit` is a term of type `IsLimit X.asLimitCone`.
7. `X.lim : CategoryTheory.Limits.LimitCone X.asLimitCone` is a bundled combination of 3 and 6.

-/


noncomputable section

open CategoryTheory

namespace Profinite

universe u

variable (X : Profinite.{u})

/-- The functor `DiscreteQuotient X ⥤ Fintype` whose limit is isomorphic to `X`. -/
def fintypeDiagram : DiscreteQuotient X ⥤ FintypeCat where
  obj S := @FintypeCat.of S (Fintype.ofFinite S)
<<<<<<< HEAD
  map f := FintypeCat.homMk (DiscreteQuotient.ofLE f.le)
  -- Porting note: `map_comp` used to be proved by default by `aesop_cat`.
  -- once `aesop_cat` can prove this again, remove the entire `map_comp` here.
  map_comp _ _ := by ext ⟨x⟩; rfl
=======
  map f := DiscreteQuotient.ofLE f.le
  -- Porting note: `map_comp` used to be proved by default by `cat_disch`.
  -- once `cat_disch` can prove this again, remove the entire `map_comp` here.
  map_comp _ _ := by funext; cat_disch
>>>>>>> origin/master

/-- An abbreviation for `X.fintypeDiagram ⋙ FintypeCat.toProfinite`. -/
abbrev diagram : DiscreteQuotient X ⥤ Profinite :=
  X.fintypeDiagram ⋙ FintypeCat.toProfinite

/-- A cone over `X.diagram` whose cone point is `X`. -/
def asLimitCone : CategoryTheory.Limits.Cone X.diagram :=
  { pt := X
    π := { app := fun S => CompHausLike.ofHom (Y := X.diagram.obj S) _
            ⟨S.proj, IsLocallyConstant.continuous (S.proj_isLocallyConstant)⟩ } }

instance isIso_asLimitCone_lift : IsIso ((limitConeIsLimit.{u, u} X.diagram).lift X.asLimitCone) :=
  CompHausLike.isIso_of_bijective _
    (by
      refine ⟨fun a b h => ?_, fun a => ?_⟩
      · refine DiscreteQuotient.eq_of_forall_proj_eq fun S => ?_
        apply_fun fun f : (limitCone.{u, u} X.diagram).pt => f.val S at h
        exact h
      · obtain ⟨b, hb⟩ :=
          DiscreteQuotient.exists_of_compat (fun S => a.val S) fun _ _ h => a.prop (homOfLE h)
        use b
        -- ext S : 3 -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` does not work, replaced with following
        -- three lines.
        apply Subtype.ext
        apply funext
        rintro S
        -- Porting note: end replacement block
        apply hb
    )

/-- The isomorphism between `X` and the explicit limit of `X.diagram`,
induced by lifting `X.asLimitCone`.
-/
def isoAsLimitConeLift : X ≅ (limitCone.{u, u} X.diagram).pt :=
  asIso <| (limitConeIsLimit.{u, u} _).lift X.asLimitCone

/-- The isomorphism of cones `X.asLimitCone` and `Profinite.limitCone X.diagram`.
The underlying isomorphism is defeq to `X.isoAsLimitConeLift`.
-/
def asLimitConeIso : X.asLimitCone ≅ limitCone.{u, u} _ :=
  Limits.Cones.ext (isoAsLimitConeLift _) fun _ => rfl

/-- `X.asLimitCone` is indeed a limit cone. -/
def asLimit : CategoryTheory.Limits.IsLimit X.asLimitCone :=
  Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) X.asLimitConeIso.symm

/-- A bundled version of `X.asLimitCone` and `X.asLimit`. -/
def lim : Limits.LimitCone X.diagram :=
  ⟨X.asLimitCone, X.asLimit⟩

end Profinite
