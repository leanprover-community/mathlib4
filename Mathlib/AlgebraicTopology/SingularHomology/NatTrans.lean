/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Constructor for natural transformations from singular chains

Let `F : TopCat ⥤ C` be a functor to a preadditive category `C` with coproducts,
`R : C` and `n : ℕ`, we show that there is a bijection between natural transformations
`(singularChainComplexFunctor C).obj R ⋙ HomologicalComplex.eval _ _ n ⟶ F`
(from the functors of singular `n`-chains) and morhisms
`f : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌)` (the target object is the
image by `F` of the `n`-dimensional topological simplex).
See `singularChainComplexFunctor.natTransMk`and `singularChainComplexFunctor.natTransEquiv`.

-/

public section

universe w v u

open CategoryTheory Limits Simplicial

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

namespace singularChainComplexFunctor

variable {R : C} {n : ℕ} {F : TopCat.{w} ⥤ C}

/-- Constructor for natural transformations from the functor of `n`-singular chains. -/
noncomputable def natTransMk (f : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌)) :
    (singularChainComplexFunctor C).obj R ⋙ HomologicalComplex.eval _ _ n ⟶ F where
  app X := Sigma.desc (fun s ↦ f ≫ F.map s.down)
  naturality _ _ _ :=
    Sigma.hom_ext _ _ (fun s ↦ by
      simp [singularChainComplexFunctor, SSet.chainComplexFunctor, ← Functor.map_comp]
      rfl)

@[reassoc (attr := simp)]
lemma ι_natTransMk (f : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌))
    (X : TopCat.{w}) (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    dsimp% X.ιSingularChainComplex s ≫ (natTransMk f).app X =
      f ≫ F.map s.down :=
  Sigma.ι_comp_desc ..

lemma natTrans_ext
    {f g : (singularChainComplexFunctor C).obj R ⋙ HomologicalComplex.eval _ _ n ⟶ F}
    (h : TopCat.ιSingularChainComplex _ (TopCat.toSSet.univObj n) ≫ f.app _ =
      TopCat.ιSingularChainComplex _ (TopCat.toSSet.univObj n) ≫ g.app _) :
    f = g := by
  ext X
  refine Sigma.hom_ext _ _ (fun s ↦ ?_)
  simpa [← NatTrans.naturality] using! h =≫ F.map s.down

@[simp]
lemma natTransMk_zero :
    natTransMk (0 : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌)) = 0 :=
  natTrans_ext (by simp)

/-- Natural transformations from the singular `n`-chains functor to a
functor `F : TopCat ⥤ C` identify to morphisms `R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌)`. -/
@[expose, simps]
noncomputable def natTransEquiv :
    ((singularChainComplexFunctor C).obj R ⋙ HomologicalComplex.eval _ _ n ⟶ F) ≃
      (R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌)) where
  toFun f := TopCat.ιSingularChainComplex _ (TopCat.toSSet.univObj n) ≫ f.app _
  invFun := natTransMk
  left_inv f := natTrans_ext (by simp)
  right_inv f := by simp

end singularChainComplexFunctor

end AlgebraicTopology
