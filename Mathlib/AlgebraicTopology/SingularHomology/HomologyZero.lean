/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# Singular homology in degree 0

The main definition in this file is `TopCat.singularHomology₀Iso` which is an
isomorphism `((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ (fun (_ : ZerothHomotopy X) ↦ R)`
for any `X : TopCat`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits AlgebraicTopology Simplicial

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C]

namespace TopCat

variable (X : TopCat.{w}) (R : C)

/-- The singular homology of a topological space `X` with coefficients in `R`
identifies with the coproduct of copies of `R` indexed by `ZerothHomotopy X`. -/
noncomputable def singularHomology₀Iso :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ (fun (_ : ZerothHomotopy X) ↦ R) :=
  SSet.homology₀Iso _ _ ≪≫
    (sigmaConst.obj R).mapIso zerothHomotopyEquiv.toIso.symm

/-- The augmentation map `((singularHomologyFunctor C 0).obj R).obj X ⟶ R`. -/
noncomputable def singularHomology₀ε :
    ((singularHomologyFunctor C 0).obj R).obj X ⟶ R :=
  SSet.homology₀ε _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma singularHomology₀Iso_sigma_desc_id :
    (singularHomology₀Iso X R).hom ≫ Sigma.desc (fun _ ↦ 𝟙 R) = singularHomology₀ε X R := by
  dsimp only [singularHomology₀Iso, singularHomology₀ε, SSet.homology₀ε]
  cat_disch

instance [PathConnectedSpace X] : IsIso (X.singularHomology₀ε R) :=
  inferInstanceAs (IsIso ((toSSet.obj X).homology₀ε R))

end TopCat
