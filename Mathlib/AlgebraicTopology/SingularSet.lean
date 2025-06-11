/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The singular simplicial set of a topological space and geometric realization of a simplicial set

The *singular simplicial set* `TopCat.toSSet.obj X` of a topological space `X`
has as `n`-simplices the continuous maps `⦋n⦌.toTop → X`.
Here, `⦋n⦌.toTop` is the standard topological `n`-simplex,
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
has as `n`-simplices the continuous maps `⦋n⦌.toTop → X`.
Here, `⦋n⦌.toTop` is the standard topological `n`-simplex,
defined as `{ f : Fin (n+1) → ℝ≥0 // ∑ i, f i = 1 }` with its subspace topology. -/
noncomputable def TopCat.toSSet : TopCat ⥤ SSet :=
  Presheaf.restrictedYoneda SimplexCategory.toTop

/-- The *geometric realization functor* is
the left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding.

It is left adjoint to `TopCat.toSSet`, as witnessed by `sSetTopAdj`. -/
noncomputable def SSet.toTop : SSet ⥤ TopCat :=
  yoneda.leftKanExtension SimplexCategory.toTop

/-- Geometric realization is left adjoint to the singular simplicial set construction. -/
noncomputable def sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet :=
  Presheaf.yonedaAdjunction (yoneda.leftKanExtension SimplexCategory.toTop)
    (yoneda.leftKanExtensionUnit SimplexCategory.toTop)

/-- The geometric realization of the representable simplicial sets agree
  with the usual topological simplices. -/
noncomputable def SSet.toTopSimplex :
    (yoneda : SimplexCategory ⥤ _) ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  Presheaf.isExtensionAlongYoneda _

/-- The singular simplicial set of a totally disconnected space is the constant simplicial set. -/
noncomputable
def TopCat.toSSetIsoConst (X : TopCat) [TotallyDisconnectedSpace X] :
    TopCat.toSSet.obj X ≅ (Functor.const _).obj X :=
  .symm <|
  NatIso.ofComponents (fun i ↦
    { inv v := v.1 ⟨Pi.single 0 1, show ∑ _, _ = _ by simp⟩
      hom x := TopCat.ofHom ⟨fun _ ↦ x, continuous_const⟩
      inv_hom_id := types_ext _ _ fun f ↦ TopCat.hom_ext (ContinuousMap.ext
        fun j ↦ TotallyDisconnectedSpace.eq_of_continuous (α := i.unop.toTopObj) _ f.1.2 _ _)
      hom_inv_id := rfl }) (by intros; ext; rfl)
