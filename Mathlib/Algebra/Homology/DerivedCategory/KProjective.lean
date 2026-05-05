/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Morphisms from K-projective complexes in the derived category

In this file, we show that if `K : CochainComplex C ℤ` is K-projective,
then for any `L : HomotopyCategory C (.up ℤ)`, the functor `DerivedCategory.Qh`
induces a bijection from the type of morphisms `(HomotopyCategory.quotient _ _).obj K) ⟶ L`
(i.e. homotopy classes of morphisms of cochain complexes) to the type of
morphisms in the derived category.
We obtain that a morphism between `K`-projective cochain complexes is a quasi-isomorphism
iff it is a homotopy equivalence. In particular, a morphism between chain complexes
indexed by `ℕ` which consist of projective objects is a quasi-isomorphism iff
it is a homotopy equivalence.

-/

@[expose] public section

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open CategoryTheory Localization DerivedCategory

namespace CochainComplex

namespace IsKProjective

open HomologicalComplex

lemma Qh_map_bijective [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (L : HomotopyCategory C (.up ℤ))
    [K.IsKProjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ _).obj K ⟶ L) → _) :=
  (CochainComplex.IsKProjective.leftOrthogonal K).map_bijective_of_isTriangulated _ _

attribute [local instance] HasDerivedCategory.standard in
lemma quasiIso_iff {K L : CochainComplex C ℤ} [K.IsKProjective] [L.IsKProjective] (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (.up ℤ) f := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ homotopyEquivalences_le_quasiIso _ _ _ hf⟩
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
  obtain ⟨g, hg⟩ := (Qh_map_bijective _ _).surjective
    ((quotientCompQhIso C).hom.app L ≫ inv (Q.map f) ≫ (quotientCompQhIso C).inv.app K)
  refine ⟨g, (Qh_map_bijective _ _).injective ?_, (Qh_map_bijective _ _).injective ?_⟩
  · simp [hg]
  · simp [hg, ← quotientCompQhIso_inv_naturality]

end IsKProjective

namespace HomComplex.CohomologyClass

variable (K L : CochainComplex C ℤ) (n : ℤ)
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

set_option backward.isDefEq.respectTransparency false in
lemma bijective_toSmallShiftedHom_of_isKProjective [K.IsKProjective] :
    Function.Bijective (toSmallShiftedHom.{w} (K := K) (L := L) (n := n)) := by
  letI := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective,
    ← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.app (L⟦n⟧))).bijective]
  convert (CochainComplex.IsKProjective.Qh_map_bijective _ _).comp (toHom_bijective K L n)
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp [toHom_mk, ShiftedHom.map]

variable {K L n} in
/-- When `K` is a K-projective cochain complex, cohomology classes
in `CohomologyClass K L n` identify to elements in a type `SmallShiftedHom` relatively
to quasi-isomorphisms. -/
@[simps! -isSimp]
noncomputable def equivOfIsKProjective [K.IsKProjective] :
    CohomologyClass K L n ≃
      SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) K L n :=
  Equiv.ofBijective _ (bijective_toSmallShiftedHom_of_isKProjective _ _ _)

end HomComplex.CohomologyClass

end CochainComplex

namespace ChainComplex

open HomologicalComplex

lemma quasiIso_iff_of_projective {K L : ChainComplex C ℕ}
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (.down ℕ) f := by
  rw [← quasiIso_extendMap_iff _ ComplexShape.embeddingDownNat,
    CochainComplex.IsKProjective.quasiIso_iff,
    homotopyEquivalences_extendMap_iff]

end ChainComplex
