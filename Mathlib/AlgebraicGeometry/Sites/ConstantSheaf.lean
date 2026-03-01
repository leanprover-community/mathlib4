/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# Constant sheaf associated to topological space

In this file we define a constant sheaf associated to a topological space. For a topological space
`T`, this is the sheaf on `Scheme` given by `U ↦ C(U, T)`. This is a sheaf
for the fpqc topology (TODO, see below).

## Main declarations

- `AlgebraicGeometry.topConstantSheaf`: The sheaf `U ↦ C(U, T)` for a topological space `T`.
- `AlgebraicGeometry.topConstantSheafAb`: For a topological abelian group `A`, this is
  `topConstantSheaf A` viewed as a sheaf of abelian groups.

## TODOs

- Show that the constant sheaf is a sheaf for the fpqc topology (@chrisflav).
-/

@[expose] public section

open CategoryTheory Limits

universe w' w v₂ u₂ v u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (T : Type v) [TopologicalSpace T]

/--
The constant sheaf associated to a topological space: The yoneda embedding of `TopCat` precomposed
with the forgetful functor from `Scheme`. This is the presheaf `U ↦ C(U, T)`.
For universe reasons, we implement it by hand.
-/
@[simps]
def topConstantSheaf (T : Type v) [TopologicalSpace T] : Scheme.{u}ᵒᵖ ⥤ Type (max v u) where
  obj U := C(U.unop, T)
  map {U V} f g := g.comp f.unop.base.hom

/-- The constant sheaf is, modulo universes, isomorphic to the composition of the forgetful
functor to `TopCat` and the yoneda embedding. -/
def topConstantSheafIsoUlift :
    topConstantSheaf T ≅
      Scheme.forgetToTop.op ⋙ TopCat.uliftFunctor.op ⋙ yoneda.obj (.of <| ULift T) :=
  NatIso.ofComponents fun U ↦ equivEquivIso <|
    (ContinuousMap.uliftEquiv U.1 T).symm.trans
    (TopCat.Hom.equivContinuousMap
      (TopCat.uliftFunctor.obj <| Scheme.forgetToTop.obj U.1)
      (TopCat.uliftFunctor.obj (TopCat.of T))).symm

lemma isSheaf_zariskiTopology_topConstantSheaf :
    Presheaf.IsSheaf Scheme.zariskiTopology (topConstantSheaf T) := by
  rw [Presheaf.isSheaf_of_iso_iff (topConstantSheafIsoUlift T)]
  apply Scheme.forgetToTop.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  apply TopCat.uliftFunctor.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The constant sheaf associated to `T` is `U ↦ C(ConnectedComponents U, T)` if `T` is totally
disconnected. -/
def topConstantSheafEquivOfTotallyDisconnectedSpace [TotallyDisconnectedSpace T] (U : Scheme.{u}) :
    (topConstantSheaf T).obj (.op U) ≃ C(ConnectedComponents U, T) where
  toFun f := ⟨f.continuous.connectedComponentsLift, f.continuous.connectedComponentsLift_continuous⟩
  invFun f := .comp f ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  right_inv f := by
    apply ContinuousMap.coe_injective
    dsimp
    exact (Continuous.connectedComponentsLift_unique _ _ (by simp)).symm

/-- The constant sheaf associated to a topological abelian group. -/
def topConstantSheafAb (A : Type v) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] :
    Scheme.{u}ᵒᵖ ⥤ Ab.{max v u} where
  obj U := AddCommGrpCat.of C(U.unop, A)
  map {U V} f := AddCommGrpCat.ofHom (ContinuousMap.compAddMonoidHom' f.unop.base.hom)

variable (A : Type v) [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A]

/-- The constant sheaf associated to a topological abelian group viewed as a type valued sheaf
is isomorphic to the constant sheaf associated to the underlying topological space. -/
def topConstantSheafAbForgetIso :
    topConstantSheafAb A ⋙ CategoryTheory.forget Ab ≅ topConstantSheaf A :=
  Iso.refl _

end AlgebraicGeometry
