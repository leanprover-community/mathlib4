/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# Projective resolutions as cochain complexes indexed by the integers

Given a projective resolution `R` of an object `X` in an abelian category `C`,
we define `R.cochainComplex : CochainComplex C ℤ`, which is the extension
of `R.complex : ChainComplex C ℕ`, and the quasi-isomorphism
`R.π' : R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ProjectiveResolution

section

variable [HasZeroObject C] [Preadditive C] {X : C}
  (R : ProjectiveResolution X)

/-- If `R : ProjectiveResolution X`, this is the cochain complex indexed by `ℤ`
obtained by extending by zero the chain complex `R.complex` indexed by `ℕ`. -/
noncomputable def cochainComplex : CochainComplex C ℤ :=
  R.complex.extend ComplexShape.embeddingDownNat

/-- If `R : ProjectiveResolution X`, then `R.chainComplex.X n` (with `n : ℕ`)
is isomorphic to `R.complex.X k` (with `k : ℕ`) when `k = n`. -/
noncomputable def cochainComplexXIso (n : ℤ) (k : ℕ) (h : -k = n := by lia) :
    R.cochainComplex.X n ≅ R.complex.X k :=
  HomologicalComplex.extendXIso _ _ h

@[reassoc]
lemma cochainComplex_d (n₁ n₂ : ℤ) (k₁ k₂ : ℕ) (h₁ : -k₁ = n₁ := by lia) (h₂ : -k₂ = n₂ := by lia) :
    R.cochainComplex.d n₁ n₂ = (cochainComplexXIso _ _ _).hom ≫
      R.complex.d k₁ k₂ ≫ (cochainComplexXIso _ _ _).inv :=
  HomologicalComplex.extend_d_eq _ _ h₁ h₂

instance : R.cochainComplex.IsStrictlyLE 0 := by
  dsimp [cochainComplex]
  infer_instance

instance (n : ℤ) : Projective (R.cochainComplex.X n) := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
    exact Projective.of_iso (R.cochainComplexXIso (-k) k).symm inferInstance
  · exact IsZero.projective (CochainComplex.isZero_of_isStrictlyLE _ 0 _)

/-- The quasi-isomorphism `R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X`
in `CochainComplex C ℤ` when `R` is a projective resolution of `X`. -/
noncomputable def π' : R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X :=
    (ComplexShape.embeddingDownNat.extendFunctor C).map R.π ≫
      (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).hom

@[reassoc]
lemma π'_f_zero :
    R.π'.f 0 = (R.cochainComplexXIso _ _).hom ≫ R.π.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv := by
  dsimp [π']
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp),
    HomologicalComplex.extendSingleIso_hom_f]
  cat_disch

end

variable [Abelian C] {X : C} (R : ProjectiveResolution X)

instance : QuasiIso R.π' := by dsimp [π']; infer_instance

end ProjectiveResolution

end CategoryTheory
