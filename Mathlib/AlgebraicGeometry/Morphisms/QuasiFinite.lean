/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.ZariskiMain
import Mathlib.RingTheory.RingHom.QuasiFinite

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open Scheme

@[mk_iff]
class LocallyQuasiFinite : Prop where
  quasiFinite_of_affine_subset :
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      (f.appLE U V e).hom.QuasiFinite

instance : HasRingHomProperty @LocallyQuasiFinite RingHom.QuasiFinite where
  isLocal_ringHomProperty := RingHom.QuasiFinite.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [locallyQuasiFinite_iff, affineLocally_iff_affineOpens_le]

instance (priority := 900) [IsOpenImmersion f] : LocallyQuasiFinite f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.QuasiFinite.holdsForLocalizationAway.containsIdentities

instance : MorphismProperty.IsStableUnderComposition @LocallyQuasiFinite :=
  HasRingHomProperty.stableUnderComposition RingHom.QuasiFinite.stableUnderComposition

instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyQuasiFinite f] [hg : LocallyQuasiFinite g] : LocallyQuasiFinite (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

theorem LocallyQuasiFinite.of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite (f ≫ g)] : LocallyQuasiFinite f :=
  HasRingHomProperty.of_comp (fun _ _ ↦ RingHom.QuasiFinite.of_comp) ‹_›

instance : MorphismProperty.IsMultiplicative @LocallyQuasiFinite where
  id_mem _ := inferInstance

instance : MorphismProperty.IsStableUnderBaseChange @LocallyQuasiFinite :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.QuasiFinite.isStableUnderBaseChange

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyQuasiFinite g] :
    LocallyQuasiFinite (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyQuasiFinite f] :
    LocallyQuasiFinite (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [LocallyQuasiFinite f] : LocallyQuasiFinite (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [LocallyQuasiFinite f] :
    LocallyQuasiFinite (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

def Scheme.Hom.quasiFiniteLocus : Set X := { x : X | (f.stalkMap x).hom.QuasiFinite }

lemma Scheme.Hom.quasiFiniteAt_of_memQuasiFiniteLocus
    (x : X) (hx : x ∈ f.quasiFiniteLocus) (V : X.affineOpens) (U : Y.affineOpens)
    (hVU : V ≤ f ⁻¹ᵁ U.1) (hxV : x ∈ V.1) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    Algebra.QuasiFiniteAt Γ(Y, U) (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal := by
  letI := (f.appLE U V hVU).hom.toAlgebra
  have H : (Y.presheaf.germ U.1 _ (hVU hxV)).hom.QuasiFinite := by
    let := (Y.presheaf.germ U.1 _ (hVU hxV)).hom.toAlgebra
    have := U.2.isLocalization_stalk ⟨f x, (hVU hxV)⟩
    rw [← (Y.presheaf.germ U.1 _ (hVU hxV)).hom.algebraMap_toAlgebra,
      RingHom.quasiFinite_algebraMap]
    exact .of_isLocalization (U.2.primeIdealOf ⟨_, hVU hxV⟩).asIdeal.primeCompl
  let := (X.presheaf.germ V.1 x hxV).hom.toAlgebra
  have := V.2.isLocalization_stalk ⟨x, hxV⟩
  let e := IsLocalization.algEquiv (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk (⟨x, hxV⟩ : V.1)) (Localization.AtPrime (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal)
  rw [Algebra.QuasiFiniteAt, ← RingHom.quasiFinite_algebraMap]
  convert (RingHom.QuasiFinite.of_finite e.finite).comp (hx.comp H)
  rw [← CommRingCat.hom_comp, f.germ_stalkMap, ← X.presheaf.germ_res (homOfLE hVU) _ hxV,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc, CommRingCat.hom_comp, ← RingHom.comp_assoc,
    IsScalarTower.algebraMap_eq Γ(Y, U) Γ(X, V)]
  congr 1
  exact e.toAlgHom.comp_algebraMap.symm

lemma Scheme.Hom.quasiFiniteLocus_eq_univ [LocallyQuasiFinite f] :
    f.quasiFiniteLocus = .univ := by
  refine Set.eq_univ_iff_forall.mpr (HasRingHomProperty.stalkMap ?_ ‹_›)
  introv hf
  algebraize [f]
  refine .of_comp (g := algebraMap R _) ?_
  convert RingHom.quasiFinite_algebraMap.mpr (inferInstanceAs
    (Algebra.QuasiFinite R (Localization.AtPrime J)))
  ext; simp; rfl

instance [IsFinite f] : LocallyQuasiFinite f := by
  rw [HasAffineProperty.eq_targetAffineLocally @IsFinite] at ‹IsFinite f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  refine ((targetAffineLocally_affineAnd_eq_affineLocally
    RingHom.QuasiFinite.propertyIsLocal).le f ?_).2
  exact targetAffineLocally_affineAnd_le (fun hf ↦ .of_finite hf) f ‹_›


end AlgebraicGeometry
