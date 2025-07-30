/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.ULift

/-!
# The singular simplicial set of a topological space and geometric realization of a simplicial set

The *singular simplicial set* `TopCat.toSSet.obj X` of a topological space `X`
has as `n`-simplices which identify to ththe continuous maps `⦋n⦌.toTop → X`.
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

- Show that the singular simplicial set is a Kan complex.
- Show the adjunction `sSetTopAdj` is a Quillen equivalence.

-/

universe u

open CategoryTheory

/-- The functor associating the *singular simplicial set* to a topological space.

Let `X : TopCat.{u}` be a topological space.
Then the singular simplicial set of `X`
has as `n`-simplices the continuous maps `ULift.{u} ⦋n⦌.toTop → X`.
Here, `⦋n⦌.toTop` is the standard topological `n`-simplex,
defined as `{ f : Fin (n+1) → ℝ≥0 // ∑ i, f i = 1 }` with its subspace topology. -/
noncomputable def TopCat.toSSet : TopCat.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.toTop.{u}

-- to be moved...
/-- The bijection `C(X₁, Y₁) ≃ C(X₂, Y₂)` induced by homeomorphisms
`e : X₁ ≃ₜ X₂` and `e' : Y₁ ≃ₜ Y₂`. -/
@[simps]
def Homeomorph.continuousMapCongr {X₁ X₂ Y₁ Y₂ : Type*}
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    (e : X₁ ≃ₜ X₂) (e' : Y₁ ≃ₜ Y₂) :
    C(X₁, Y₁) ≃ C(X₂, Y₂) where
  toFun f := ContinuousMap.comp ⟨_, e'.continuous⟩ (f.comp ⟨_, e.symm.continuous⟩)
  invFun g := ContinuousMap.comp ⟨_, e'.symm.continuous⟩ (g.comp ⟨_, e.continuous⟩)
  left_inv _ := by aesop
  right_inv _ := by aesop

/-- If `X : TopCat.{u}` and `n : SimplexCategoryᵒᵖ`,
then `(toSSet.obj X).obj n` identifies to the type of continuous
maps from the standard simplex `n.unop.toTopObj` to `X`. -/
def TopCat.toSSetObjEquiv (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (toSSet.obj X).obj n ≃ C(n.unop.toTopObj, X) :=
  Equiv.ulift.{0}.trans (ConcreteCategory.homEquiv.trans
    (Homeomorph.ulift.continuousMapCongr (.refl _)))

/-- The *geometric realization functor* is
the left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding.

It is left adjoint to `TopCat.toSSet`, as witnessed by `sSetTopAdj`. -/
noncomputable def SSet.toTop : SSet.{u} ⥤ TopCat.{u} :=
  stdSimplex.{u}.leftKanExtension SimplexCategory.toTop

/-- Geometric realization is left adjoint to the singular simplicial set construction. -/
noncomputable def sSetTopAdj : SSet.toTop.{u} ⊣ TopCat.toSSet.{u} :=
  Presheaf.uliftYonedaAdjunction
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.toTop)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop)

/-- The geometric realization of the representable simplicial sets agree
  with the usual topological simplices. -/
noncomputable def SSet.toTopSimplex :
    SSet.stdSimplex.{u} ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  Presheaf.isExtensionAlongULiftYoneda _

instance : SSet.toTop.{u}.IsLeftKanExtension SSet.toTopSimplex.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop.{u}))

-- to be moved...
noncomputable def TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace
    (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] [TotallyDisconnectedSpace Y] [ConnectedSpace X] :
    C(X, Y) ≃ Y where
  toFun f := f (Classical.arbitrary _)
  invFun y := ⟨fun _ ↦ y, by continuity⟩
  left_inv f := ContinuousMap.ext (TotallyDisconnectedSpace.eq_of_continuous _ f.2 _)
  right_inv _ := rfl

/-- The singular simplicial set of a totally disconnected space is the constant simplicial set. -/
noncomputable def TopCat.toSSetIsoConst (X : TopCat.{u}) [TotallyDisconnectedSpace X] :
    TopCat.toSSet.obj X ≅ (Functor.const _).obj X :=
  (NatIso.ofComponents (fun n ↦ Equiv.toIso
    ((TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace _ X).symm.trans
      (X.toSSetObjEquiv n).symm))).symm
