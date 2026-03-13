/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# Sheaf of continuous maps associated to topological space

Given a topological space `T`, we consider the presheaf on `Scheme` given by `U ↦ C(U, T)`
and show that it is a Zariski sheaf (TODO: show that it is a fpqc sheaf).
When `T` is discrete, this is the constant sheaf associated to `T` (TODO).

## Main declarations

- `AlgebraicGeometry.continuousMapPresheaf`: The sheaf `U ↦ C(U, T)` for a topological space `T`.
- `AlgebraicGeometry.continuousMapPresheafAb`: For a topological abelian group `A`, this is
  `continuousMapPresheaf A` viewed as a sheaf of abelian groups.

## TODOs

- Show that `continuousMapPresheaf` is a sheaf for the fpqc topology (@chrisflav).
-/

@[expose] public section

open CategoryTheory Limits

universe w' w v₂ u₂ v u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (T : Type v) [TopologicalSpace T]

/--
The yoneda embedding of `TopCat` precomposed with the forgetful functor from `Scheme`. This is the
presheaf `U ↦ C(U, T)`. For universe reasons, we implement it by hand.
-/
@[simps]
def continuousMapPresheaf (T : Type v) [TopologicalSpace T] : Scheme.{u}ᵒᵖ ⥤ Type (max v u) where
  obj U := C(U.unop, T)
  map {U V} f g := g.comp f.unop.base.hom

/-- `continuousMapPresheaf` is isomorphic to the composition of the forgetful
functor to `TopCat` and the yoneda embedding. -/
def continuousMapPresheafIsoUlift :
    continuousMapPresheaf T ≅
      Scheme.forgetToTop.op ⋙ TopCat.uliftFunctor.op ⋙ yoneda.obj (.of <| ULift T) :=
  NatIso.ofComponents fun U ↦ equivEquivIso <|
    (ContinuousMap.uliftEquiv U.1 T).symm.trans
    (TopCat.Hom.equivContinuousMap
      (TopCat.uliftFunctor.obj <| Scheme.forgetToTop.obj U.1)
      (TopCat.uliftFunctor.obj (TopCat.of T))).symm

lemma isSheaf_zariskiTopology_continuousMapPresheaf :
    Presheaf.IsSheaf Scheme.zariskiTopology (continuousMapPresheaf T) := by
  rw [Presheaf.isSheaf_of_iso_iff (continuousMapPresheafIsoUlift T)]
  apply Scheme.forgetToTop.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  apply TopCat.uliftFunctor.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- `continuousMapPresheaf` is `U ↦ C(ConnectedComponents U, T)` if `T` is totally
disconnected. -/
def continuousMapPresheafEquivOfTotallyDisconnectedSpace [TotallyDisconnectedSpace T]
    (U : Scheme.{u}) :
    (continuousMapPresheaf T).obj (.op U) ≃ C(ConnectedComponents U, T) where
  toFun f := ⟨f.continuous.connectedComponentsLift, f.continuous.connectedComponentsLift_continuous⟩
  invFun f := .comp f ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  right_inv f := by
    apply ContinuousMap.coe_injective
    dsimp
    exact (Continuous.connectedComponentsLift_unique _ _ (by simp)).symm

/-- `continuousMapPresheaf` as a presheaf of abelian groups associated to a topological abelian
group. -/
def continuousMapPresheafAb (A : Type v) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] :
    Scheme.{u}ᵒᵖ ⥤ Ab.{max v u} where
  obj U := AddCommGrpCat.of C(U.unop, A)
  map {U V} f := AddCommGrpCat.ofHom (ContinuousMap.compAddMonoidHom' f.unop.base.hom)

variable (A : Type v) [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A]

/-- `continuousMapPresheafAb` viewed as a type valued sheaf is isomorphic to
`continuousMapPresheaf. -/
def continuousMapPresheafAbForgetIso :
    continuousMapPresheafAb A ⋙ CategoryTheory.forget Ab ≅ continuousMapPresheaf A :=
  Iso.refl _

end AlgebraicGeometry
