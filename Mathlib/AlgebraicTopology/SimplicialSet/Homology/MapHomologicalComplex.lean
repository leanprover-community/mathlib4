/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Extension of scalars

If `X` is a simplicial set, `R₁ →+* R₂` is a morphism of commutative rings,
and `M₁` is a `R₁`-module, then the chain complex of `R₂`-modules of `X` with
coefficients in `R₂ ⊗[R₁] M₁` identifies to the extensions of scalars of the
chain complex of `R₁`-modules of `X` with coefficients in `M₁`. In this file,
we obtain a formulation of this result where the extension of scalars
functor `ModuleCat R₁ ⥤ ModuleCat R₂` is replaced by an arbitrary functor
`F : C ⥤ D` which commutes with coproducts.

-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits AlgebraicTopology Simplicial

namespace SSet

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasCoproducts.{w} C] [HasCoproducts.{w} D]
  (X : SSet.{w}) (F : C ⥤ D) [F.Additive]
  [∀ (T : Type w), PreservesColimitsOfShape (Discrete T) F] (R : C)

open SimplicialObject Functor in
/-- The chain complex functor commutes with the "extension of scalars".
More precisely, if `F : C ⥤ D` is a functor which commutes with coproducts,
`R : C` and `X : SSet`, then the chain complex of `X` with coefficients
in `F.obj R` is obtained by applying `F` to the chain complex of `X`
with coefficients in `R`. -/
noncomputable def chainComplexFunctorObjCompMapIso :
    (chainComplexFunctor C).obj R ⋙ F.mapHomologicalComplex (.down ℕ) ≅
    (chainComplexFunctor D).obj (F.obj R) :=
  calc
    ((whiskering _ _).obj (sigmaConst.obj R) ⋙
      alternatingFaceMapComplex C) ⋙ F.mapHomologicalComplex _ ≅
    (whiskering _ _).obj (sigmaConst.obj R) ⋙
      alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex _ := associator _ _ _
    _ ≅ (whiskering _ _).obj (sigmaConst.obj R) ⋙
      (whiskering _ _).obj F ⋙ alternatingFaceMapComplex D :=
      isoWhiskerLeft _ (alternatingFaceMapComplexCompMapHomologicalComplexIso _)
    _ ≅ ((whiskering _ _).obj (sigmaConst.obj R) ⋙
      (whiskering _ _).obj F) ⋙ alternatingFaceMapComplex D := (associator _ _ _).symm
    _ ≅ (whiskering _ _).obj (sigmaConst.obj R ⋙ F) ⋙ alternatingFaceMapComplex D :=
      isoWhiskerRight (Functor.whiskeringRightObjCompIso _ _) _
    _ ≅ (whiskering _ _).obj (sigmaConst.obj (F.obj R)) ⋙ alternatingFaceMapComplex D :=
      isoWhiskerRight ((whiskering _ _).mapIso (sigmaConstObjCompIso F R)) _

variable {R} in
@[reassoc (attr := simp)]
lemma map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f
    {n : ℕ} (x : X _⦋n⦌) :
   dsimp% F.map (X.ιChainComplex x) ≫
      ((chainComplexFunctorObjCompMapIso F R).hom.app X).f n =
    X.ιChainComplex x := by
  simpa [chainComplexFunctorObjCompMapIso] using map_ι_sigmaConstObjCompIso_hom_app F R x

end SSet
