/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Morphisms to K-injective complexes in the derived category

In this file, we show that if `L : CochainComplex C ℤ` is K-injective,
then for any `K : HomotopyCategory C (.up ℤ)`, the functor `DerivedCategory.Qh`
induces a bijection from the type of morphisms `K ⟶ (HomotopyCategory.quotient _ _).obj L)`
(i.e. homotopy classes of morphisms of cochain complexes) to the type of
morphisms in the derived category.

-/

@[expose] public section

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open CategoryTheory Localization DerivedCategory

namespace CochainComplex

lemma IsKInjective.Qh_map_bijective [HasDerivedCategory C]
    (K : HomotopyCategory C (ComplexShape.up ℤ))
    (L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      (K ⟶ (HomotopyCategory.quotient _ _).obj L) → _) :=
  (CochainComplex.IsKInjective.rightOrthogonal L).map_bijective_of_isTriangulated _ _

namespace HomComplex.CohomologyClass

variable (K L : CochainComplex C ℤ) (n : ℤ)
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

set_option backward.isDefEq.respectTransparency false in
lemma bijective_toSmallShiftedHom_of_isKInjective [L.IsKInjective] :
    Function.Bijective (toSmallShiftedHom.{w} (K := K) (L := L) (n := n)) := by
  letI := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective,
    ← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.app (L⟦n⟧))).bijective]
  convert (CochainComplex.IsKInjective.Qh_map_bijective _ _).comp (toHom_bijective K L n)
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp [toHom_mk, ShiftedHom.map]

variable {K L n} in
/-- When `L` is a K-injective cochain complex, cohomology classes
in `CohomologyClass K L n` identify to elements in a type `SmallShiftedHom` relatively
to quasi-isomorphisms. -/
@[simps! -isSimp]
noncomputable def equivOfIsKInjective [L.IsKInjective] :
    CohomologyClass K L n ≃
      SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) K L n :=
  Equiv.ofBijective _ (bijective_toSmallShiftedHom_of_isKInjective _ _ _)

end HomComplex.CohomologyClass

attribute [local instance] HasDerivedCategory.standard in
lemma IsKInjective.isIso_quotient_map_iff_quasiIso
    {K L : CochainComplex C ℤ} [K.IsKInjective] [L.IsKInjective]
    (f : K ⟶ L) :
    IsIso ((HomotopyCategory.quotient _ _).map f) ↔ QuasiIso f := by
  trans IsIso (Qh.map ((HomotopyCategory.quotient _ _).map f))
  · refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
    let φ := Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)
    obtain ⟨ψ, hψ⟩ := (IsKInjective.Qh_map_bijective _ _).2 (inv φ)
    refine ⟨ψ, ?_, ?_⟩
    all_goals exact (IsKInjective.Qh_map_bijective _ _).1 (by cat_disch)
  · rw [← isIso_Q_map_iff_quasiIso]
    apply (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    exact Arrow.isoMk ((quotientCompQhIso C).app _) ((quotientCompQhIso C).app _)

open HomologicalComplex in
lemma quasiIso_iff_homotopyEquivalences_of_isKInjective {K L : CochainComplex C ℤ}
    (f : K ⟶ L) [K.IsKInjective] [L.IsKInjective] :
    QuasiIso f ↔ homotopyEquivalences _ _ f := by
  rw [← isIso_quotient_map_iff_homotopyEquivalences,
    IsKInjective.isIso_quotient_map_iff_quasiIso]

end CochainComplex
