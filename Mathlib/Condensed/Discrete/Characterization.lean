/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Discrete.Colimit
import Mathlib.Condensed.Discrete.Module
/-!

# Characterizing discrete condensed sets and `R`-modules.

This file proves a characterization of discrete condensed sets, discrete condensed `R`-modules over
a ring `R`, discrete light condensed sets, and discrete light condensed `R`-modules over a ring `R`.
see `CondensedSet.isDiscrete_tfae`, `CondensedMod.isDiscrete_tfae`, `LightCondSet.isDiscrete_tfae`,
and `LightCondMod.isDiscrete_tfae`.

Informally, we can say: The following conditions characterize a condensed set `X` as discrete
(`CondensedSet.isDiscrete_tfae`):

1. There exists a set `X'` and an isomorphism `X ≅ cst X'`, where `cst X'` denotes the constant
   sheaf on `X'`.
2. The counit induces an isomorphism `cst X(*) ⟶ X`.
3. There exists a set `X'` and an isomorphism `X ≅ LocallyConstant · X'`.
4. The counit induces an isomorphism `LocallyConstant · X(*) ⟶ X`.
5. For every profinite set `S = limᵢSᵢ`, the canonical map `colimᵢX(Sᵢ) ⟶ X(S)` is an isomorphism.

The analogues for light condensed sets, condensed `R`-modules over any ring, and light
condensed `R`-modules are nearly identical (`CondensedMod.isDiscrete_tfae`,
`LightCondSet.isDiscrete_tfae`, and `LightCondMod.isDiscrete_tfae`).
-/

universe u

open CategoryTheory Limits Functor FintypeCat

namespace Condensed

variable {C : Type*} [Category C] [HasWeakSheafify (coherentTopology CompHaus.{u}) C]

/--
A condensed object is *discrete* if it is constant as a sheaf, i.e. isomorphic to a constant sheaf.
-/
abbrev IsDiscrete (X : Condensed.{u} C) := X.IsConstant (coherentTopology CompHaus)

end Condensed

namespace CondensedSet

open CompHausLike.LocallyConstant

lemma mem_locallyConstant_essImage_of_isColimit_mapCocone (X : CondensedSet.{u})
    (h : ∀ S : Profinite.{u}, IsColimit <|
      (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op) :
    CondensedSet.LocallyConstant.functor.essImage X := by
  let e : CondensedSet.{u} ≌ Sheaf (coherentTopology Profinite) _ :=
    (Condensed.ProfiniteCompHaus.equivalence (Type (u + 1))).symm
  let i : (e.functor.obj X).val ≅ (e.functor.obj (LocallyConstant.functor.obj _)).val :=
    Condensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨e.functor.preimageIso ((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

@[deprecated (since := "2024-12-25")]
alias mem_locallyContant_essImage_of_isColimit_mapCocone :=
  mem_locallyConstant_essImage_of_isColimit_mapCocone

/--
`CondensedSet.LocallyConstant.functor` is left adjoint to the forgetful functor from condensed
sets to sets.
-/
noncomputable abbrev LocallyConstant.adjunction :
    CondensedSet.LocallyConstant.functor ⊣ Condensed.underlying (Type (u + 1)) :=
  CompHausLike.LocallyConstant.adjunction _ _

open Condensed

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
open CondensedSet.LocallyConstant List in
theorem isDiscrete_tfae (X : CondensedSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , IsIso ((Condensed.discreteUnderlyingAdj _).counit.app X)
    , (Condensed.discrete _).essImage X
    , CondensedSet.LocallyConstant.functor.essImage X
    , IsIso (CondensedSet.LocallyConstant.adjunction.counit.app X)
    , Sheaf.IsConstant (coherentTopology Profinite)
        ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj X)
    , ∀ S : Profinite.{u}, Nonempty
        (IsColimit <| (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op)
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 → 4 := fun h ↦
    mem_locallyConstant_essImage_of_isColimit_mapCocone X (fun S ↦ (h S).some)
  tfae_have 4 → 7 := fun ⟨Y, ⟨i⟩⟩ S ↦
    ⟨IsColimit.mapCoconeEquiv (isoWhiskerLeft profiniteToCompHaus.op
      ((sheafToPresheaf _ _).mapIso i))
      (Condensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

end CondensedSet

namespace CondensedMod

variable (R : Type (u + 1)) [Ring R]

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
lemma isDiscrete_iff_isDiscrete_forget (M : CondensedMod R) :
    M.IsDiscrete ↔ ((Condensed.forget R).obj M).IsDiscrete  :=
  Sheaf.isConstant_iff_forget (coherentTopology CompHaus)
    (forget (ModuleCat R)) M CompHaus.isTerminalPUnit

instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
  hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _

open CondensedMod.LocallyConstant List in
theorem isDiscrete_tfae (M : CondensedMod.{u} R) :
    TFAE
    [ M.IsDiscrete
    , IsIso ((Condensed.discreteUnderlyingAdj _).counit.app M)
    , (Condensed.discrete _).essImage M
    , (CondensedMod.LocallyConstant.functor R).essImage M
    , IsIso ((CondensedMod.LocallyConstant.adjunction R).counit.app M)
    , Sheaf.IsConstant (coherentTopology Profinite)
        ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj M)
    , ∀ S : Profinite.{u}, Nonempty
        (IsColimit <| (profiniteToCompHaus.op ⋙ M.val).mapCocone S.asLimitCone.op)
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 5 :=
    have : (functor R).Faithful := inferInstance
    have : (functor R).Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 → 1 := by
    intro h
    rw [isDiscrete_iff_isDiscrete_forget, ((CondensedSet.isDiscrete_tfae _).out 0 6:)]
    intro S
    letI : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat R)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ⟨isColimitOfPreserves (forget (ModuleCat R)) (h S).some⟩
  tfae_have 1 → 7 := by
    intro h S
    rw [isDiscrete_iff_isDiscrete_forget, ((CondensedSet.isDiscrete_tfae _).out 0 6:)] at h
    letI : ReflectsFilteredColimitsOfSize.{u, u} (forget (ModuleCat R)) :=
      reflectsFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ⟨isColimitOfReflects (forget (ModuleCat R)) (h S).some⟩
  tfae_finish

end CondensedMod

namespace LightCondensed

variable {C : Type*} [Category C] [HasWeakSheafify (coherentTopology LightProfinite.{u}) C]

/--
A light condensed object is *discrete* if it is constant as a sheaf, i.e. isomorphic to a constant
sheaf.
-/
abbrev IsDiscrete (X : LightCondensed.{u} C) := X.IsConstant (coherentTopology LightProfinite)

end LightCondensed

namespace LightCondSet

lemma mem_locallyConstant_essImage_of_isColimit_mapCocone (X : LightCondSet.{u})
    (h : ∀ S : LightProfinite.{u}, IsColimit <|
      X.val.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    LightCondSet.LocallyConstant.functor.essImage X := by
  let i : X.val ≅ (LightCondSet.LocallyConstant.functor.obj _).val :=
    LightCondensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

@[deprecated (since := "2024-12-25")]
alias mem_locallyContant_essImage_of_isColimit_mapCocone :=
  mem_locallyConstant_essImage_of_isColimit_mapCocone

/--
`LightCondSet.LocallyConstant.functor` is left adjoint to the forgetful functor from light condensed
sets to sets.
-/
noncomputable abbrev LocallyConstant.adjunction :
    LightCondSet.LocallyConstant.functor ⊣ LightCondensed.underlying (Type u) :=
  CompHausLike.LocallyConstant.adjunction _ _

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
open LightCondSet.LocallyConstant List in
theorem isDiscrete_tfae (X : LightCondSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , IsIso ((LightCondensed.discreteUnderlyingAdj _).counit.app X)
    , (LightCondensed.discrete _).essImage X
    , LightCondSet.LocallyConstant.functor.essImage X
    , IsIso (LightCondSet.LocallyConstant.adjunction.counit.app X)
    , ∀ S : LightProfinite.{u}, Nonempty
        (IsColimit <| X.val.mapCocone (coconeRightOpOfCone S.asLimitCone))
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 6 → 4 := fun h ↦
    mem_locallyConstant_essImage_of_isColimit_mapCocone X (fun S ↦ (h S).some)
  tfae_have 4 → 6 := fun ⟨Y, ⟨i⟩⟩ S ↦
    ⟨IsColimit.mapCoconeEquiv ((sheafToPresheaf _ _).mapIso i)
      (LightCondensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R]

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
lemma isDiscrete_iff_isDiscrete_forget (M : LightCondMod R) :
    M.IsDiscrete ↔ ((LightCondensed.forget R).obj M).IsDiscrete  :=
  Sheaf.isConstant_iff_forget (coherentTopology LightProfinite)
    (forget (ModuleCat R)) M LightProfinite.isTerminalPUnit

open LightCondMod.LocallyConstant List in
theorem isDiscrete_tfae (M : LightCondMod.{u} R) :
    TFAE
    [ M.IsDiscrete
    , IsIso ((LightCondensed.discreteUnderlyingAdj _).counit.app M)
    , (LightCondensed.discrete _).essImage M
    , (LightCondMod.LocallyConstant.functor R).essImage M
    , IsIso ((LightCondMod.LocallyConstant.adjunction R).counit.app M)
    , ∀ S : LightProfinite.{u}, Nonempty
        (IsColimit <| M.val.mapCocone (coconeRightOpOfCone S.asLimitCone))
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _
    LightProfinite.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 5 :=
    have : (functor R).Faithful := inferInstance
    have : (functor R).Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit (adjunction R) _
  tfae_have 6 → 1 := by
    intro h
    rw [isDiscrete_iff_isDiscrete_forget, ((LightCondSet.isDiscrete_tfae _).out 0 5:)]
    intro S
    letI : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat R)) :=
      preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} _
    exact ⟨isColimitOfPreserves (forget (ModuleCat R)) (h S).some⟩
  tfae_have 1 → 6 := by
    intro h S
    rw [isDiscrete_iff_isDiscrete_forget, ((LightCondSet.isDiscrete_tfae _).out 0 5:)] at h
    letI : ReflectsFilteredColimitsOfSize.{0, 0} (forget (ModuleCat R)) :=
      reflectsFilteredColimitsOfSize_shrink.{0, u, 0, u} _
    exact ⟨isColimitOfReflects (forget (ModuleCat R)) (h S).some⟩
  tfae_finish

end LightCondMod
