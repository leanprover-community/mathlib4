/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Sheaves.Init

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
  map {U V} f := TypeCat.ofHom fun g ↦ ContinuousMap.comp g f.unop.base.hom

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

set_option backward.isDefEq.respectTransparency false in
lemma isSheaf_fpqcTopology_continuousMapPresheaf :
    Presheaf.IsSheaf Scheme.fpqcTopology (continuousMapPresheaf T) := by
  rw [isSheaf_iff_isSheaf_of_type, Scheme.fpqcTopology_eq_propQCTopology,
    isSheaf_type_propQCTopology_iff]
  refine ⟨?_, fun {R S} f hf₁ hf₂ ↦ ?_⟩
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact isSheaf_zariskiTopology_continuousMapPresheaf _
  · rw [Presieve.isSheafFor_singleton]
    have : Topology.IsQuotientMap (Spec.map f) := Flat.isQuotientMap_of_surjective _
    intro (x : C(Spec S, T)) h
    refine ⟨?_, ?_, ?_⟩
    · refine Topology.IsQuotientMap.lift this x fun a b hfab ↦ ?_
      obtain ⟨c, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback a b hfab
      exact congr($(h (pullback.fst (Spec.map f) (Spec.map f))
        (pullback.snd _ _) pullback.condition).1 c)
    · apply Topology.IsQuotientMap.lift_comp
    · intro y hy
      rwa [← ContinuousMap.cancel_right (Spec.map f).surjective, Topology.IsQuotientMap.lift_comp]

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
`continuousMapPresheaf`. -/
def continuousMapPresheafAbForgetIso :
    continuousMapPresheafAb A ⋙ CategoryTheory.forget Ab ≅ continuousMapPresheaf A :=
  Iso.refl _

lemma isSheaf_fpqcTopology_continuousMapPresheafAb :
    Presheaf.IsSheaf Scheme.fpqcTopology (continuousMapPresheafAb A) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget Ab)
  exact isSheaf_fpqcTopology_continuousMapPresheaf _

end AlgebraicGeometry
