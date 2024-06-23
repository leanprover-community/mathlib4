/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Dev.Colimit
import Mathlib.Condensed.LocallyConstantModule
/-!

# Characterizing discrete condensed sets.
-/

universe u

open CategoryTheory Limits Functor FintypeCat

attribute [local instance] ConcreteCategory.instFunLike

namespace CondensedSet

section Terminal

/--
A one-element space is terminal in `Profinite`

TODO: PR if not already done
-/
def _root_.Profinite.isTerminalPUnit :
    IsTerminal (FintypeCat.toProfinite.obj (FintypeCat.of PUnit.{u + 1})) :=
  haveI : ∀ X, Unique (X ⟶ (FintypeCat.toProfinite.obj (FintypeCat.of PUnit.{u + 1}))) := fun X =>
    ⟨⟨⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext; aesop⟩
  Limits.IsTerminal.ofUnique _

end Terminal

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

open Condensed.LocallyConstant CompHausLike.LocallyConstant

noncomputable def isColimitLocallyConstantPresheaf (X' : Type (u+1)) (S : Profinite.{u}) :
    IsColimit ((profiniteToCompHaus.op ⋙
      (CondensedSet.LocallyConstant.functor.{u}.obj X').val).mapCocone S.asLimitCone.op) := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant S X')
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, u} _ S.asLimit f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (S.asLimitCone.π.app i) = fj.comap (S.asLimitCone.π.app j))
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp only [functor_obj_val, comp_obj, op_obj, toProfinite_obj, CompHausLike.toCompHausLike_obj,
      CompHausLike.coe_of, functorToPresheaves_obj_obj, Functor.comp_map, op_map,
      Quiver.Hom.unop_op, CompHausLike.toCompHausLike_map, functorToPresheaves_obj_map]
    apply DFunLike.ext
    intro x'
    obtain ⟨x, hx⟩ := (k.proj_surjective : Function.Surjective (S.asLimitCone.π.app k)) x'
    rw [← hx]
    change fi ((S.asLimitCone.π.app k ≫ (S.fintypeDiagram ⋙ toProfinite).map ki) x) =
      fj ((S.asLimitCone.π.app k ≫ (S.fintypeDiagram ⋙ toProfinite).map kj) x)
    have h := LocallyConstant.congr_fun h x
    rwa [S.asLimitCone.w, S.asLimitCone.w]

theorem isDiscrete_of_isColimit_mapCone (X : CondensedSet.{u}) (h : ∀ S : Profinite.{u},
    IsColimit <| (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op) :
    X ∈ CondensedSet.LocallyConstant.functor.essImage := by
  let e : CondensedSet.{u} ≌ Sheaf (coherentTopology Profinite) _ :=
    (Condensed.ProfiniteCompHaus.equivalence (Type (u + 1))).symm
  let i : (e.functor.obj X).val ≅ (e.functor.obj
      (CondensedSet.LocallyConstant.functor.obj _)).val :=
    Condensed.isoDiscrete _ h
  exact ⟨_, ⟨e.functor.preimageIso ((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

noncomputable abbrev _root_.CondensedSet.LocallyConstant.adjunction :
    CondensedSet.LocallyConstant.functor ⊣ Condensed.underlying (Type (u+1)) :=
  Condensed.LocallyConstant.adjunction _ _

open List in
theorem isDiscrete_tfae  (X : CondensedSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , IsIso ((Condensed.discreteUnderlyingAdj _).counit.app X)
    , X ∈ (Condensed.discrete _).essImage
    , X ∈ CondensedSet.LocallyConstant.functor.essImage
    , IsIso (CondensedSet.LocallyConstant.adjunction.counit.app X)
    , Sheaf.IsDiscrete (coherentTopology Profinite) Profinite.isTerminalPUnit
        ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj X)
    , ∀ S : Profinite.{u}, Nonempty
        (IsColimit <| (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op)
    ] := by
  tfae_have 1 ↔ 2
  · exact Iff.rfl -- TODO: remove `2` in the list
  tfae_have 1 ↔ 3
  · exact Sheaf.isDiscrete_iff_mem_essImage _ _ _
  tfae_have 1 ↔ 4
  · exact Sheaf.isDiscrete_iff_mem_essImage' _ _ CondensedSet.LocallyConstant.adjunction _
  tfae_have 1 ↔ 5
  · exact Sheaf.isDiscrete_iff_isIso_counit_app _ _ CondensedSet.LocallyConstant.adjunction _
  tfae_have 1 ↔ 6
  · exact (Sheaf.isDiscrete_iff_of_equivalence (coherentTopology Profinite)
      Profinite.isTerminalPUnit  (coherentTopology CompHaus) profiniteToCompHaus
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 → 4
  · intro h
    exact isDiscrete_of_isColimit_mapCone X (fun S ↦ (h S).some)
  tfae_have 4 → 7
  · intro ⟨Y, ⟨i⟩⟩ S
    exact ⟨IsColimit.mapCoconeEquiv (isoWhiskerLeft profiniteToCompHaus.op
      ((sheafToPresheaf _ _).mapIso i))
      (isColimitLocallyConstantPresheaf Y S)⟩
  tfae_finish

end CondensedSet
