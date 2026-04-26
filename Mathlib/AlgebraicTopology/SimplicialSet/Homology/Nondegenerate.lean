/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
public import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Computing homology using nondegenerate simplices

In this file, we introduce the normalized chain complex `X.normalizedChainComplex R`
of a simplicial set `X` with coefficients in `R` (where `R` is an object of a
preadditive category `C` with coproducts). The `n`-chains of this complex
identifies to the coproduct of copies of `R` indexed by the nondegenerate
`n`-simplices of `X`. In particular, we deduce that the homology is zero in degree `≥ d`
when `X` has dimension `< d`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomologicalComplex

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (X : SSet.{w}) (R : C)

noncomputable def normalizedChainComplex : ChainComplex C ℕ :=
  (X.splitting.map (sigmaConst.obj R)).nondegComplex

noncomputable def toNormalizedChainComplex : X.chainComplex R ⟶ X.normalizedChainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).toNondegComplex

noncomputable def fromNormalizedChainComplex : X.normalizedChainComplex R ⟶ X.chainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).fromNondegComplex

@[reassoc (attr := simp)]
lemma fromNormalizedChainComplex_toNormalizedChainComplex :
    X.fromNormalizedChainComplex R ≫ X.toNormalizedChainComplex R = 𝟙 _ :=
  SimplicialObject.Splitting.fromNondegComplex_toNondegComplex _

noncomputable def homotopyEquivNormalizedChainComplex :
    HomotopyEquiv (X.chainComplex R) (X.normalizedChainComplex R) :=
  SimplicialObject.Splitting.homotopyEquivNondegComplex _

@[simp]
lemma homotopyEquivNormalizedChainComplex_hom :
    (X.homotopyEquivNormalizedChainComplex R).hom = X.toNormalizedChainComplex R := rfl

@[simp]
lemma homotopyEquivNormalizedChainComplex_inv :
    (X.homotopyEquivNormalizedChainComplex R).inv = X.fromNormalizedChainComplex R := rfl

lemma isZero_normalizedChainComplex_X_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    IsZero ((X.normalizedChainComplex R).X n) := by
  rw [IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ (fun x ↦ (h.not_gt (X.dim_lt_of_nonDegenerate x d)).elim)

section

variable [CategoryWithHomology C]

instance : QuasiIso (X.toNormalizedChainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).quasiIso_hom

instance : QuasiIso (X.fromNormalizedChainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).quasiIso_inv

lemma exactAt_chainComplex_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    (X.chainComplex R).ExactAt n := by
  rw [exactAt_iff_of_quasiIsoAt (X.toNormalizedChainComplex R)]
  exact .of_isZero (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d)

lemma isZero_homology_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    IsZero (X.homology R n) := by
  rw [← exactAt_iff_isZero_homology]
  exact X.exactAt_chainComplex_of_hasDimensionLT R n d

end

end SSet
