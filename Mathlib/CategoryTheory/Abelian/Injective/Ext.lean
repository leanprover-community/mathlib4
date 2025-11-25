/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# Computing `Ext` using an injective resolution

-/

@[expose] public section

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

-- to be moved...
namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℤ} {n : ℤ}
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

namespace CohomologyClass

/-- Given `x : CohomologyClass K L n`, this is the element in the type
`SmallShiftedHom` relatively to quasi-isomorphisms that is associated
to the `x`. -/
noncomputable def toSmallShiftedHom (x : CohomologyClass K L n) :
    SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) K L n :=
  Quotient.lift (fun y ↦ SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm y)) (by
    letI := HasDerivedCategory.standard C
    intro y₁ y₂ h
    refine (SmallShiftedHom.equiv _ DerivedCategory.Q).injective ?_
    simp only [SmallShiftedHom.equiv_mk, ShiftedHom.map]
    rw [cancel_mono, DerivedCategory.Q_map_eq_of_homotopy]
    apply HomotopyCategory.homotopyOfEq
    rw [← toHom_mk, ← toHom_mk]
    congr 1
    exact Quotient.sound h) x

lemma toSmallShiftedHom_mk (x : Cocycle K L n) :
    (mk x).toSmallShiftedHom =
      SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm x) := rfl

@[simp]
lemma equiv_toSmallShiftedHom_mk [HasDerivedCategory C] (x : Cocycle K L n) :
    SmallShiftedHom.equiv _ DerivedCategory.Q (mk x).toSmallShiftedHom =
      ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q := by
  simp [toSmallShiftedHom_mk]

open DerivedCategory in
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

/-- When `L` is a K-injective cochain complex, cohomology classes
in `CohomologyClass K L n` identify to elements in a type `SmallShiftedHom` relatively
to quasi-isomorphisms. -/
@[simps! -isSimp]
noncomputable def equivOfIsKInjective [L.IsKInjective] :
    CohomologyClass K L n ≃
      SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) K L n :=
  Equiv.ofBijective _ bijective_toSmallShiftedHom_of_isKInjective

end CohomologyClass

end CochainComplex.HomComplex

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace InjectiveResolution

variable {X Y : C} (R : InjectiveResolution Y) {n : ℕ}

instance : R.cochainComplex.IsKInjective := isKInjective_of_injective _ 0

/-- If `R` is an injective resolution of `Y`, then `Ext X Y n` identify
to the type of cohomology classes of degree `n` from `(singleFunctor C 0).obj X`
to `R.cochainComplex`. -/
noncomputable def extEquivCohomologyClass :
    Ext X Y n ≃ CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n :=
  (SmallShiftedHom.postcompEquiv.{w} R.ι'
      (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)).trans
    CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.{w}.symm

/-- Given an injective resolution `R` of an object `Y` of an abelian category,
this is a constructor for elements in `Ext X Y n` which takes as an input
a "cocycle" `f : X ⟶ R.cocomplex.X n`. -/
noncomputable def extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    Ext X Y n :=
  R.extEquivCohomologyClass.symm
    (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
      m (by cutsat) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])))

end InjectiveResolution

end CategoryTheory
