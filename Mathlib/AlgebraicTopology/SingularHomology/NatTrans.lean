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
`R : C` and `n : ℕ`. We show that there is a bijection between natural transformations
`(singularChainComplexFunctor C).obj R ⋙ HomologicalComplex.eval _ _ n ⟶ F`
(from the functors of singular `n`-chains to `F`) and morphisms
`f : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌)`, see
`singularChainComplexFunctor.natTransMk` and `singularChainComplexFunctor.natTransEquiv`.

-/

public section

universe w v u

open CategoryTheory Limits Simplicial

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

namespace singularChainComplexFunctor

variable {R : C} {n : ℕ} {F : TopCat.{w} ⥤ C}

/-- Let `F : TopCat ⥤ C` be a functor. A natural transformation from the singular
`n`-chains functor (with coefficients in an object `R : C`, e.g. the abelian group `ℤ`) to `F`
can be constructed from the sole data of a morphism `R ⟶ F.obj (SimplexCategory.toTop ^⦋n⦌)`
in `C` (which in the case `R` is the abelian group `ℤ` could be reduced to the
information of an element in the image by the functor `F` of the standard
topological `n`-simplex). See also `natTransEquiv` for the bijection that is
induced by `natTransMk`. -/
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

/-- Let `F : TopCat ⥤ C` be a functor. This bijection shows that natural transformations
from the singular `n`-chains functor (with coefficients in an object `R : C`, e.g. the
abelian group `ℤ`) to `F` are uniquely determined by the data of a morphism
`R ⟶ F.obj (SimplexCategory.toTop ^⦋n⦌)` in `C` that is obtained by considering the action
of the natural transformation on the identity of the standard topological `n`-simplex. -/
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
