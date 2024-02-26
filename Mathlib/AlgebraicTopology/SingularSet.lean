/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The singular simplicial set of a topological space and geometric realization of a simplicial set

The *singular simplicial set* `TopCat.to_SSet.obj X` of a topological space `X`
has as `n`-simplices the continuous maps `[n].toTop → X`.
Here, `[n].toTop` is the standard topological `n`-simplex,
defined as `{ f : Fin (n+1) → ℝ≥0 // ∑ i, f i = 1 }` with its subspace topology.

The *geometric realization* functor `SSet.toTop.obj` is left adjoint to `TopCat.toSSet`.
It is the left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding.

# Main definitions

* `TopCat.toSSet : TopCat ⥤ SSet` is the functor
  assigning the singular simplicial set to a topological space.
* `SSet.toTop : SSet ⥤ TopCat` is the functor
  assigning the geometric realization to a simplicial set.
* `sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet` is the adjunction between these two functors.

## TODO

- Generalize to an adjunction between `SSet.{u}` and `TopCat.{u}` for any universe `u`
- Show that the singular simplicial set is a Kan complex.
- Show the adjunction `sSetTopAdj` is a Quillen adjunction.

-/

open CategoryTheory

/-- The functor associating the *singular simplicial set* to a topological space.

Let `X` be a topological space.
Then the singular simplicial set of `X`
has as `n`-simplices the continuous maps `[n].toTop → X`.
Here, `[n].toTop` is the standard topological `n`-simplex,
defined as `{ f : Fin (n+1) → ℝ≥0 // ∑ i, f i = 1 }` with its subspace topology. -/
noncomputable def TopCat.toSSet : TopCat ⥤ SSet :=
  ColimitAdj.restrictedYoneda SimplexCategory.toTop
set_option linter.uppercaseLean3 false in
#align Top.to_sSet TopCat.toSSet

/-- The *geometric realization functor* is
the left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding.

It is left adjoint to `TopCat.toSSet`, as witnessed by `sSetTopAdj`. -/
noncomputable def SSet.toTop : SSet ⥤ TopCat :=
  ColimitAdj.extendAlongYoneda SimplexCategory.toTop
set_option linter.uppercaseLean3 false in
#align sSet.to_Top SSet.toTop

/-- Geometric realization is left adjoint to the singular simplicial set construction. -/
noncomputable def sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet :=
  ColimitAdj.yonedaAdjunction _
set_option linter.uppercaseLean3 false in
#align sSet_Top_adj sSetTopAdj

/-- The geometric realization of the representable simplicial sets agree
  with the usual topological simplices. -/
noncomputable def SSet.toTopSimplex :
    (yoneda : SimplexCategory ⥤ _) ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  ColimitAdj.isExtensionAlongYoneda _
set_option linter.uppercaseLean3 false in
#align sSet.to_Top_simplex SSet.toTopSimplex
