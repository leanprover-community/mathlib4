/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Discrete.Colimit
import Mathlib.Condensed.Discrete.Module
/-!

# Characterizing discrete condensed sets.

This file proves a characterization of discrete condensed sets and discrete light condensed sets,
see `CondensedSet.isDiscrete_tfae` and `LightCondSet.isDiscrete_tfae`.
-/

universe u

open CategoryTheory Limits Functor FintypeCat

attribute [local instance] ConcreteCategory.instFunLike

namespace CondensedSet

/--
This is an auxiliary definition to prove that the constant sheaf functor from `Type (u+1)` 
to sheaves for the coherent topology on `Profinite.{u}` is fully faithful.
-/
noncomputable
def constantSheafProfiniteCompHausIso : constantSheaf (coherentTopology Profinite) (Type (u+1)) ≅
    constantSheaf (coherentTopology CompHaus) (Type (u+1)) ⋙
    (Condensed.ProfiniteCompHaus.equivalence _).inverse :=
  (Sheaf.equivCommuteConstant' (coherentTopology Profinite) (Type (u+1))
    Profinite.isTerminalPUnit
    (coherentTopology CompHaus) profiniteToCompHaus CompHaus.isTerminalPUnit)

instance : (constantSheaf (coherentTopology Profinite) (Type (u+1))).Faithful :=
  Functor.Faithful.of_iso constantSheafProfiniteCompHausIso.symm

instance : (constantSheaf (coherentTopology Profinite) (Type (u+1))).Full :=
  Functor.Full.of_iso constantSheafProfiniteCompHausIso.symm

open CompHausLike.LocallyConstant

lemma mem_locallyContant_essImage_of_isColimit_mapCocone (X : CondensedSet.{u})
    (h : ∀ S : Profinite.{u}, IsColimit <|
      (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op) :
    X ∈ CondensedSet.LocallyConstant.functor.essImage := by
  let e : CondensedSet.{u} ≌ Sheaf (coherentTopology Profinite) _ :=
    (Condensed.ProfiniteCompHaus.equivalence (Type (u + 1))).symm
  let i : (e.functor.obj X).val ≅ (e.functor.obj
      (CondensedSet.LocallyConstant.functor.obj _)).val :=
    Condensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨e.functor.preimageIso ((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

/--
`CondensedSet.LocallyConstant.functor` is left adjoint to the forgetful functor from light condensed
sets to sets.
-/
noncomputable abbrev LocallyConstant.adjunction :
    CondensedSet.LocallyConstant.functor ⊣ Condensed.underlying (Type (u+1)) :=
  CompHausLike.LocallyConstant.adjunction _ _

open List in
theorem isDiscrete_tfae  (X : CondensedSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , X ∈ (Condensed.discrete _).essImage
    , X ∈ CondensedSet.LocallyConstant.functor.essImage
    , IsIso (CondensedSet.LocallyConstant.adjunction.counit.app X)
    , Sheaf.IsDiscrete (coherentTopology Profinite) Profinite.isTerminalPUnit
        ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj X)
    , ∀ S : Profinite.{u}, Nonempty
        (IsColimit <| (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op)
    ] := by
  tfae_have 1 ↔ 2
  · exact Sheaf.isDiscrete_iff_mem_essImage _ _ _
  tfae_have 1 ↔ 3
  · exact Sheaf.isDiscrete_iff_mem_essImage' _ _ CondensedSet.LocallyConstant.adjunction _
  tfae_have 1 ↔ 4
  · exact Sheaf.isDiscrete_iff_isIso_counit_app _ _ CondensedSet.LocallyConstant.adjunction _
  tfae_have 1 ↔ 5
  · exact (Sheaf.isDiscrete_iff_of_equivalence (coherentTopology Profinite)
      Profinite.isTerminalPUnit  (coherentTopology CompHaus) profiniteToCompHaus
      CompHaus.isTerminalPUnit _).symm
  tfae_have 6 → 3
  · intro h
    exact mem_locallyContant_essImage_of_isColimit_mapCocone X (fun S ↦ (h S).some)
  tfae_have 3 → 6
  · intro ⟨Y, ⟨i⟩⟩ S
    exact ⟨IsColimit.mapCoconeEquiv (isoWhiskerLeft profiniteToCompHaus.op
      ((sheafToPresheaf _ _).mapIso i))
      (Condensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

end CondensedSet

namespace LightCondSet

instance : (constantSheaf (coherentTopology LightProfinite) (Type u)).Faithful :=
  inferInstanceAs (LightCondensed.discrete _).Faithful

instance : (constantSheaf (coherentTopology LightProfinite) (Type u)).Full :=
  inferInstanceAs (LightCondensed.discrete _).Full

open CompHausLike.LocallyConstant

lemma mem_locallyContant_essImage_of_isColimit_mapCocone (X : LightCondSet.{u})
    (h : ∀ S : LightProfinite.{u}, IsColimit <|
      X.val.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    X ∈ LightCondSet.LocallyConstant.functor.essImage := by
  let i : X.val ≅ (LightCondSet.LocallyConstant.functor.obj _).val :=
    LightCondensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

/--
`LightCondSet.LocallyConstant.functor` is left adjoint to the forgetful functor from light condensed
sets to sets.
-/
noncomputable abbrev LocallyConstant.adjunction :
    LightCondSet.LocallyConstant.functor ⊣ LightCondensed.underlying (Type u) :=
  CompHausLike.LocallyConstant.adjunction _ _

open List in
theorem isDiscrete_tfae  (X : LightCondSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , X ∈ (LightCondensed.discrete _).essImage
    , X ∈ LightCondSet.LocallyConstant.functor.essImage
    , IsIso (LightCondSet.LocallyConstant.adjunction.counit.app X)
    , ∀ S : LightProfinite.{u}, Nonempty
        (IsColimit <| X.val.mapCocone (coconeRightOpOfCone S.asLimitCone))
    ] := by
  tfae_have 1 ↔ 2
  · exact Sheaf.isDiscrete_iff_mem_essImage _ _ _
  tfae_have 1 ↔ 3
  · exact Sheaf.isDiscrete_iff_mem_essImage' _ _ LightCondSet.LocallyConstant.adjunction X
  tfae_have 1 ↔ 4
  · exact Sheaf.isDiscrete_iff_isIso_counit_app _ _ LightCondSet.LocallyConstant.adjunction X
  tfae_have 5 → 3
  · intro h
    exact mem_locallyContant_essImage_of_isColimit_mapCocone X (fun S ↦ (h S).some)
  tfae_have 3 → 5
  · intro ⟨Y, ⟨i⟩⟩ S
    exact ⟨IsColimit.mapCoconeEquiv ((sheafToPresheaf _ _).mapIso i)
      (LightCondensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

end LightCondSet
