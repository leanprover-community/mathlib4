/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Simplicial homology

In this file, we define the homology of simplicial sets.
For any preadditive category `C` with coproducts of size `w` and any
object `R : C`, the simplicial chain complex of a simplicial
set `X` is denoted `X.chainComplex R`, and its homology
in degree `n : ℕ` is `X.homology R n`.

-/

@[expose] public section

open Simplicial CategoryTheory Limits

universe w v u

namespace SSet

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/--
The chain complex associated to a simplicial set, with coefficients in `R : C`.
It computes the simplicial homology of a simplicial sets with coefficients
in `R`. One can recover the ordinary simplicial chain complex when `C := Ab`
and `X := ℤ`.
-/
noncomputable def chainComplexFunctor : C ⥤ SSet.{w} ⥤ ChainComplex C ℕ :=
  (Functor.postcompose₂.obj (AlgebraicTopology.alternatingFaceMapComplex _)).obj
    (sigmaConst ⋙ SimplicialObject.whiskering _ _)

instance : (chainComplexFunctor C).Additive := by
  dsimp [chainComplexFunctor, SimplicialObject.whiskering]
  infer_instance

@[deprecated (since := "2026-04-05")]
alias _root_.AlgebraicTopology.SSet.singularChainComplexFunctor :=
  chainComplexFunctor

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] SSet.chainComplexFunctor in
attribute [local simp←] _root_.SSet.yonedaEquiv_symm_comp in
/-- The adjunction `Hom(Cⁿ(-, X), F) ≃ Hom(X, F(Δ[n]))` for `R : C` and `F : SSet ⥤ C`. -/
noncomputable def chainComplexFunctorAdjunction (n : ℕ) :
    (Functor.postcompose₂.obj (HomologicalComplex.eval _ _ n)).obj
      (SSet.chainComplexFunctor C) ⊣ (evaluation _ _).obj Δ[n] where
  unit.app R := Sigma.ι (fun _ : Δ[n] _⦋n⦌ ↦ R) (SSet.stdSimplex.objEquiv (n := ⦋n⦌).symm (𝟙 ⦋n⦌))
  counit.app F := { app S := Sigma.desc fun α ↦ F.map (SSet.yonedaEquiv.symm α) }
  right_triangle_components F := by dsimp; simp

@[deprecated (since := "2026-04-05")]
alias _root_.SSet.singularChainComplexFunctorAdjunction :=
  SSet.chainComplexFunctorAdjunction

variable {C} (X Y Z : SSet.{w}) (f : X ⟶ Y) (g : Y ⟶ Z) (R : C)

/-- The (simplicial) chain complex of a simplicial set `X` with
coefficients in `R : C`. Its homology is the simplicial homology
of `X`. -/
noncomputable abbrev chainComplex : ChainComplex C ℕ :=
  ((SSet.chainComplexFunctor C).obj R).obj X

variable {X Y} in
/-- The morphism of simplicial chain complexes induces by a morphism
of simplicial sets. -/
noncomputable abbrev chainComplexMap : X.chainComplex R ⟶ Y.chainComplex R :=
  ((SSet.chainComplexFunctor C).obj R).map f

variable {R} in
/-- The inclusion `R ⟶ (X.chainComplex R).X n` of the summand
corresponding to a `n`-simplex `x : X _⦋n⦌`. -/
noncomputable def ιChainComplex {n : ℕ} (x : X _⦋n⦌) : R ⟶ (X.chainComplex R).X n :=
  Sigma.ι (fun (_ : X _⦋n⦌) ↦ R) x

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ιChainComplex_d {n : ℕ} (x : X _⦋n + 1⦌) :
    X.ιChainComplex x ≫ (X.chainComplex R).d (n + 1) n =
      ∑ (i : Fin (n + 2)), (-1) ^ i.val • X.ιChainComplex (X.δ i x) := by
  simp [ιChainComplex, chainComplex, chainComplexFunctor, Preadditive.comp_sum]

@[reassoc (attr := simp)]
lemma ι_chainComplexMap_f {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (chainComplexMap f R).f n =
      Y.ιChainComplex (f.app _ x) := by
  dsimp [chainComplexMap, chainComplexFunctor, ιChainComplex, Sigma.map',
    chainComplex, chainComplexFunctor]
  simp [Sigma.ι_desc]

/-- The colimit cofan which defines the simplicial `n`-chains
`(X.chainComplex R).X n`. -/
noncomputable def chainComplexXCofan (n : ℕ) : Cofan (fun (_ : X _⦋n⦌) ↦ R) :=
  Cofan.mk _ X.ιChainComplex

/-- Simplicial `n`-chains `(X.chainComplex R).X n` of a simplicial set `X`
with coefficients in `R` identify to a coproduct of copies of `R`
indexed by `X _⦋n⦌`. -/
noncomputable def isColimitChainComplexXCofan (n : ℕ) : IsColimit (X.chainComplexXCofan R n) :=
  coproductIsCoproduct _

variable {X R} in
@[ext]
lemma chainComplex_hom_ext {n : ℕ} {T : C} {f g : (X.chainComplex R).X n ⟶ T}
    (h : ∀ (x : X _⦋n⦌), X.ιChainComplex x ≫ f = X.ιChainComplex x ≫ g) :
    f = g :=
  (X.isColimitChainComplexXCofan R n).hom_ext (fun _ ↦ h _)

variable [CategoryWithHomology C]

/-- The simplicial homology with coefficients in `R : C` in degree `n`
of a simplicial set `X`. -/
protected noncomputable abbrev homology (n : ℕ) : C := (X.chainComplex R).homology n

variable {X Y} in
/-- The morphism in simplicial homology that is induced by a morphism
of simplicial sets. -/
protected noncomputable abbrev homologyMap (n : ℕ) : X.homology R n ⟶ Y.homology R n :=
  HomologicalComplex.homologyMap (chainComplexMap f R) n

@[simp]
lemma homologyMap_id (n : ℕ) : SSet.homologyMap (𝟙 X) R n = 𝟙 _ := by
  simp [SSet.homologyMap]

@[reassoc]
lemma homologyMap_comp (n : ℕ) :
    SSet.homologyMap (f ≫ g) R n = SSet.homologyMap f R n ≫ SSet.homologyMap g R n := by
  simp [SSet.homologyMap, HomologicalComplex.homologyMap_comp]

attribute [local simp] homologyMap_comp in
/-- The simplicial homology functor in degree `n` with coefficients in `R : C`. -/
@[simps]
noncomputable def homologyFunctor (n : ℕ) : SSet.{w} ⥤ C where
  obj X := X.homology R n
  map f := SSet.homologyMap f R n

end SSet
