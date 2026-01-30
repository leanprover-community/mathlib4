/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# Injective resolutions as cochain complexes indexed by the integers

Given an injective resolution `R` of an object `X` in an abelian category `C`,
we define `R.cochainComplex : CochainComplex C ℤ`, which is the extension
of `R.cocomplex : CochainComplex C ℕ`, and the quasi-isomorphism
`R.ι' : (CochainComplex.singleFunctor C 0).obj X ⟶ R.cochainComplex`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace InjectiveResolution

section

variable [HasZeroObject C] [Preadditive C] {X : C}
  (R : InjectiveResolution X)

/-- If `R : InjectiveResolution X`, this is the cochain complex indexed by `ℤ`
obtained by extending by zero the cochain complex `R.cocomplex` indexed by `ℕ`. -/
noncomputable def cochainComplex : CochainComplex C ℤ :=
  R.cocomplex.extend ComplexShape.embeddingUpNat

instance : R.cochainComplex.IsStrictlyGE 0 := by
  dsimp [cochainComplex]
  infer_instance

/-- If `R : InjectiveResolution X`, then `R.cochainComplex.X n` (with `n : ℕ`)
is isomorphic to `R.cocomplex.X k` (with `k : ℕ`) when `k = n`. -/
noncomputable def cochainComplexXIso (n : ℤ) (k : ℕ) (h : k = n) :
    R.cochainComplex.X n ≅ R.cocomplex.X k :=
  HomologicalComplex.extendXIso _ _ h

@[reassoc]
lemma cochainComplex_d (n₁ n₂ : ℤ) (k₁ k₂ : ℕ) (h₁ : k₁ = n₁) (h₂ : k₂ = n₂) :
    R.cochainComplex.d n₁ n₂ = (cochainComplexXIso _ _ _ h₁).hom ≫
      R.cocomplex.d k₁ k₂ ≫ (cochainComplexXIso _ _ _ h₂).inv :=
  HomologicalComplex.extend_d_eq _ _ h₁ h₂

instance : R.cochainComplex.IsStrictlyGE 0 := by
  dsimp [cochainComplex]
  infer_instance

instance (n : ℤ) : Injective (R.cochainComplex.X n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact Injective.of_iso (R.cochainComplexXIso _ _ rfl).symm inferInstance
  · exact IsZero.injective (CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by lia))

/-- The quasi-isomorphism `(CochainComplex.singleFunctor C 0).obj X ⟶ R.cochainComplex`
in `CochainComplex C ℤ` when `R` is an injective resolution of `X`. -/
noncomputable def ι' : (CochainComplex.singleFunctor C 0).obj X ⟶ R.cochainComplex :=
  (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).inv ≫
    (ComplexShape.embeddingUpNat.extendFunctor C).map R.ι

@[reassoc]
lemma ι'_f_zero :
    R.ι'.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫ R.ι.f 0 ≫
      (R.cochainComplexXIso _ _ (by simp)).inv := by
  dsimp [ι']
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp),
    HomologicalComplex.extendSingleIso_inv_f]
  cat_disch

end

variable [Abelian C] {X : C} (R : InjectiveResolution X)

instance : QuasiIso R.ι' := by dsimp [ι']; infer_instance

instance : R.cochainComplex.IsLE 0 := by
  simp only [← HomologicalComplex.isSupported_iff_of_quasiIso R.ι']
  infer_instance

namespace Hom

variable {R} {X' : C} {R' : InjectiveResolution X'} {f : X ⟶ X'}
  (φ : Hom R R' f)

/-- The morphism on cochain complexes indexed by `ℤ` that is induced by
an (heterogeneous) morphism of injective resolutions. -/
noncomputable def hom' : R.cochainComplex ⟶ R'.cochainComplex :=
  HomologicalComplex.extendMap φ.hom _

@[reassoc]
lemma hom'_f (n : ℤ) (m : ℕ) (h : m = n) :
    φ.hom'.f n =
    (R.cochainComplexXIso n m h).hom ≫ φ.hom.f m ≫ (R'.cochainComplexXIso n m h).inv := by
  simp [hom',
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := m) (i' := n) (by simpa),
    cochainComplexXIso]

@[reassoc (attr := simp)]
lemma ι'_comp_hom' :
    R.ι' ≫ φ.hom' = (CochainComplex.singleFunctor C 0).map f ≫ R'.ι' :=
  HomologicalComplex.from_single_hom_ext (by
    simp [hom'_f _ 0 0 rfl, ι'_f_zero, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors,
      HomologicalComplex.single, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq])

end Hom

end InjectiveResolution

end CategoryTheory
