/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryConnected


/-!
# Equivalence of Galois categories

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D]
  (F : C ⥤ D) [F.IsEquivalence]

open PreGaloisCategory

namespace PreGaloisCategory

instance (X : C) [PreGaloisCategory.IsConnected X] :
    PreGaloisCategory.IsConnected (F.obj X) where
  notInitial h :=
    IsConnected.notInitial (X := X)
      ((IsInitial.isInitialObj F.inv _ h).ofIso
        (F.asEquivalence.unitIso.symm.app X))
  noTrivialComponent Y i _ hY := by
    obtain ⟨i', hi'⟩ := F.map_surjective ((F.objObjPreimageIso Y).hom ≫ i)
    have : Mono i' := Functor.mono_of_mono_map F (by rw [hi']; infer_instance)
    have := IsConnected.noTrivialComponent _ i' (fun hY' ↦ hY
      ((IsInitial.isInitialObj F _ hY').ofIso (F.objObjPreimageIso Y)))
    rw [← isIso_comp_left_iff (F.objObjPreimageIso Y).hom, ← hi']
    infer_instance

include F in
set_option backward.isDefEq.respectTransparency false in
lemma of_isEquivalence [PreGaloisCategory D] : PreGaloisCategory C where
  hasTerminal := Adjunction.hasLimitsOfShape_of_equivalence F
  hasPullbacks := Adjunction.hasLimitsOfShape_of_equivalence F
  hasFiniteCoproducts :=
    ⟨fun n ↦ Adjunction.hasColimitsOfShape_of_equivalence F⟩
  monoInducesIsoOnDirectSummand i _ := by
    obtain ⟨Z, u, ⟨h⟩⟩ := monoInducesIsoOnDirectSummand (F.map i)
    refine ⟨F.inv.obj Z, F.inv.map u ≫ F.asEquivalence.unitIso.inv.app _,
      ⟨isColimitOfReflects F
        ((isColimitMapCoconeBinaryCofanEquiv ..).2 ?_)⟩⟩
    refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).2 h
    · exact Discrete.natIso (fun ⟨i⟩ ↦ WalkingPair.rec (Iso.refl _)
        (F.asEquivalence.counitIso.app Z) i)
    · refine BinaryCofan.ext (Iso.refl _) ?_ ?_
      · simp [BinaryCofan.inl]
      · simp [BinaryCofan.inr, Functor.asEquivalence]
  hasQuotientsByFiniteGroups _ _ _ :=
    Adjunction.hasColimitsOfShape_of_equivalence F

instance (G : D ⥤ FintypeCat.{w}) [PreGaloisCategory C] [PreGaloisCategory D] [FiberFunctor G] :
    FiberFunctor (F ⋙ G) where
  preservesQuotientsByFiniteGroups G _ _:= by
    obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} G
    exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm _

end PreGaloisCategory

namespace GaloisCategory

variable (D) in
lemma exists_fiber_functor [GaloisCategory D] :
    ∃ (F : D ⥤ FintypeCat.{w}), FiberFunctor F :=
  ⟨getFiberFunctor D ⋙ FintypeCat.uSwitch, inferInstance⟩

variable (D) in
/-- A choice of a fiber functor on a Galois category. The difference with
`getFiberFunctor` is that here, we can choose an arbitrary universe `w`
for the target category `FintypeCat.{w}`. -/
@[no_expose]
noncomputable def getFiberFunctor' [GaloisCategory D] : D ⥤ FintypeCat.{w} :=
  getFiberFunctor D ⋙ FintypeCat.uSwitch
deriving FiberFunctor

include F in
lemma of_isEquivalence [GaloisCategory D] :
    GaloisCategory C := by
  have := PreGaloisCategory.of_isEquivalence F
  exact ⟨F ⋙ getFiberFunctor' D, inferInstance⟩

lemma isConnected_iff_of_isEquivalence
    (F : C ⥤ D) [F.IsEquivalence] (X : C) :
    PreGaloisCategory.IsConnected (F.obj X) ↔ PreGaloisCategory.IsConnected X :=
  ⟨fun _ ↦ PreGaloisCategory.IsConnected.of_iso (X := F.inv.obj (F.obj X))
    (F.asEquivalence.unitIso.symm.app X), fun _ ↦ inferInstance⟩

variable [GaloisCategory C] [GaloisCategory D]

instance (X : C) [PreGaloisCategory.IsGalois X] :
    IsGalois (F.obj X) := by
  let G := getFiberFunctor D
  have : F.IsEquivalence := inferInstance
  have hX := (isGalois_iff_pretransitive (F ⋙ G) X).1 inferInstance
  rw [isGalois_iff_pretransitive G]
  rw [MulAction.isPretransitive_iff] at hX ⊢
  intro x y
  obtain ⟨g, rfl⟩ := hX x y
  exact ⟨F.mapAut X g, rfl⟩

lemma isGalois_iff_of_isEquivalence
    (F : C ⥤ D) [F.IsEquivalence] (X : C) :
    IsGalois (F.obj X) ↔ IsGalois X :=
  ⟨fun _ ↦ .of_iso (X := F.inv.obj (F.obj X))
    (F.asEquivalence.unitIso.symm.app X), fun _ ↦ inferInstance⟩

end GaloisCategory

end CategoryTheory
