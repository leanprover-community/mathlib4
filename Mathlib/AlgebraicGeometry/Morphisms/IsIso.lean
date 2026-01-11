/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!

# Being an isomorphism is local at the target

-/

universe u

@[expose] public section

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

lemma isIso_iff_isOpenImmersion_and_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Surjective f := by
  rw [surjective_iff, ← TopCat.epi_iff_surjective, isIso_iff_isOpenImmersion_and_epi_base]

lemma isomorphisms_eq_isOpenImmersion_inf_surjective :
    isomorphisms Scheme = (@IsOpenImmersion ⊓ @Surjective : MorphismProperty Scheme) := by
  ext
  rw [isomorphisms.iff, isIso_iff_isOpenImmersion_and_surjective]
  rfl

lemma isomorphisms_eq_stalkwise :
    isomorphisms Scheme = (isomorphisms TopCat).inverseImage Scheme.forgetToTop ⊓
      stalkwise (fun f ↦ Function.Bijective f) := by
  rw [isomorphisms_eq_isOpenImmersion_inf_surjective, isOpenImmersion_eq_inf,
    surjective_eq_topologically, inf_right_comm]
  congr 1
  ext X Y f
  exact ⟨fun H ↦ inferInstanceAs (IsIso (TopCat.isoOfHomeo
    (H.1.1.toHomeomorphOfSurjective H.2)).hom), fun (_ : IsIso f.base) ↦
    let e := (TopCat.homeoOfIso <| asIso f.base); ⟨e.isOpenEmbedding, e.surjective⟩⟩

example : IsZariskiLocalAtTarget (isomorphisms Scheme) := inferInstance

instance : HasAffineProperty (isomorphisms Scheme) fun X _ f _ ↦ IsAffine X ∧ IsIso (f.appTop) := by
  convert HasAffineProperty.of_isZariskiLocalAtTarget (isomorphisms Scheme) with X Y f hY
  exact ⟨fun ⟨_, _⟩ ↦ (arrow_mk_iso_iff (isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.appTop)))),
    fun (_ : IsIso f) ↦ ⟨.of_isIso f, inferInstance⟩⟩

instance : IsZariskiLocalAtTarget (monomorphisms Scheme) :=
  diagonal_isomorphisms (C := Scheme).symm ▸ inferInstance

lemma isIso_SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    IsIso (Spec.map f) ↔ Function.Bijective f.hom := by
  rw [← ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  rw [← isomorphisms.iff, (isomorphisms _).arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f),
    isomorphisms.iff]
  infer_instance

end AlgebraicGeometry
