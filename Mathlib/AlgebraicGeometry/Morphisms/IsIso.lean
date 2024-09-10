/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.Topology.IsLocalHomeomorph

/-!

# Being an isomorphism is local at the target

-/

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

lemma isomorphisms_eq_isOpenImmersion_inf_surjective :
    isomorphisms Scheme = (@IsOpenImmersion ⊓ @Surjective : MorphismProperty Scheme) := by
  ext
  exact (isIso_iff_isOpenImmersion _).trans
    (and_congr Iff.rfl ((TopCat.epi_iff_surjective _).trans (surjective_iff _).symm))

lemma isomorphisms_eq_stalkwise :
    isomorphisms Scheme = (isomorphisms TopCat).inverseImage Scheme.forgetToTop ⊓
      stalkwise (fun f ↦ Function.Bijective f) := by
  rw [isomorphisms_eq_isOpenImmersion_inf_surjective, isOpenImmersion_eq_inf,
    surjective_eq_topologically, inf_right_comm]
  congr 1
  ext X Y f
  exact ⟨fun H ↦ inferInstanceAs (IsIso (TopCat.isoOfHomeo
    (H.1.1.toHomeomeomorph_of_surjective H.2)).hom), fun (_ : IsIso f.1.base) ↦
    let e := (TopCat.homeoOfIso <| asIso f.1.base); ⟨e.openEmbedding, e.surjective⟩⟩

instance : IsLocalAtTarget (isomorphisms Scheme) :=
  isomorphisms_eq_isOpenImmersion_inf_surjective ▸ inferInstance

instance : HasAffineProperty (isomorphisms Scheme) fun X Y f _ ↦ IsAffine X ∧ IsIso (f.app ⊤) := by
  convert HasAffineProperty.of_isLocalAtTarget (isomorphisms Scheme) with X Y f hY
  exact ⟨fun ⟨_, _⟩ ↦ (arrow_mk_iso_iff (isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.app ⊤)))),
    fun (_ : IsIso f) ↦ ⟨isAffine_of_isIso f, inferInstance⟩⟩

end AlgebraicGeometry
