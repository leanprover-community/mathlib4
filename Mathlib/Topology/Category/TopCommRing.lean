/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module topology.category.TopCommRing
! leanprover-community/mathlib commit 9a59dcb7a2d06bf55da57b9030169219980660cd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.Topology.Category.Top.Basic
import Mathbin.Topology.Algebra.Ring.Basic

/-!
# Category of topological commutative rings

We introduce the category `TopCommRing` of topological commutative rings together with the relevant
forgetful functors to topological spaces and commutative rings.
-/


universe u

open CategoryTheory

/-- A bundled topological commutative ring. -/
structure TopCommRing where
  α : Type u
  [isCommRing : CommRing α]
  [isTopologicalSpace : TopologicalSpace α]
  [is_topologicalRing : TopologicalRing α]
#align TopCommRing TopCommRing

namespace TopCommRing

instance : Inhabited TopCommRing :=
  ⟨⟨PUnit⟩⟩

instance : CoeSort TopCommRing (Type u) :=
  ⟨TopCommRing.α⟩

attribute [instance] is_comm_ring is_topological_space is_topological_ring

instance : Category TopCommRing.{u}
    where
  Hom R S := { f : R →+* S // Continuous f }
  id R := ⟨RingHom.id R, by obviously⟩
  -- TODO remove obviously?
  comp R S T f g :=
    ⟨g.val.comp f.val,
      by
      -- TODO automate
      cases f;
      cases g
      dsimp; apply Continuous.comp <;> assumption⟩

instance : ConcreteCategory TopCommRing.{u}
    where
  forget :=
    { obj := fun R => R
      map := fun R S f => f.val }
  forget_faithful := { }

/-- Construct a bundled `TopCommRing` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [CommRing X] [TopologicalSpace X] [TopologicalRing X] : TopCommRing :=
  ⟨X⟩
#align TopCommRing.of TopCommRing.of

@[simp]
theorem coe_of (X : Type u) [CommRing X] [TopologicalSpace X] [TopologicalRing X] :
    (of X : Type u) = X :=
  rfl
#align TopCommRing.coe_of TopCommRing.coe_of

instance forgetTopologicalSpace (R : TopCommRing) : TopologicalSpace ((forget TopCommRing).obj R) :=
  R.isTopologicalSpace
#align TopCommRing.forget_topological_space TopCommRing.forgetTopologicalSpace

instance forgetCommRing (R : TopCommRing) : CommRing ((forget TopCommRing).obj R) :=
  R.isCommRing
#align TopCommRing.forget_comm_ring TopCommRing.forgetCommRing

instance forget_topologicalRing (R : TopCommRing) : TopologicalRing ((forget TopCommRing).obj R) :=
  R.is_topologicalRing
#align TopCommRing.forget_topological_ring TopCommRing.forget_topologicalRing

instance hasForgetToCommRing : HasForget₂ TopCommRing CommRingCat :=
  HasForget₂.mk' (fun R => CommRingCat.of R) (fun x => rfl) (fun R S f => f.val) fun R S f =>
    HEq.rfl
#align TopCommRing.has_forget_to_CommRing TopCommRing.hasForgetToCommRing

instance forgetToCommRingTopologicalSpace (R : TopCommRing) :
    TopologicalSpace ((forget₂ TopCommRing CommRingCat).obj R) :=
  R.isTopologicalSpace
#align TopCommRing.forget_to_CommRing_topological_space TopCommRing.forgetToCommRingTopologicalSpace

/-- The forgetful functor to Top. -/
instance hasForgetToTop : HasForget₂ TopCommRing TopCat :=
  HasForget₂.mk' (fun R => TopCat.of R) (fun x => rfl) (fun R S f => ⟨⇑f.1, f.2⟩) fun R S f =>
    HEq.rfl
#align TopCommRing.has_forget_to_Top TopCommRing.hasForgetToTop

instance forgetToTopCommRing (R : TopCommRing) : CommRing ((forget₂ TopCommRing TopCat).obj R) :=
  R.isCommRing
#align TopCommRing.forget_to_Top_comm_ring TopCommRing.forgetToTopCommRing

instance forget_to_topCat_topologicalRing (R : TopCommRing) :
    TopologicalRing ((forget₂ TopCommRing TopCat).obj R) :=
  R.is_topologicalRing
#align TopCommRing.forget_to_Top_topological_ring TopCommRing.forget_to_topCat_topologicalRing

/-- The forgetful functors to `Type` do not reflect isomorphisms,
but the forgetful functor from `TopCommRing` to `Top` does.
-/
instance : ReflectsIsomorphisms (forget₂ TopCommRing.{u} TopCat.{u})
    where reflects X Y f _ := by
    skip
    -- We have an isomorphism in `Top`,
    let i_Top := as_iso ((forget₂ TopCommRing TopCat).map f)
    -- and a `ring_equiv`.
    let e_Ring : X ≃+* Y := { f.1, ((forget TopCat).mapIso i_Top).toEquiv with }
    -- Putting these together we obtain the isomorphism we're after:
    exact
      ⟨⟨⟨e_Ring.symm, i_Top.inv.2⟩,
          ⟨by
            ext x
            exact e_Ring.left_inv x, by
            ext x
            exact e_Ring.right_inv x⟩⟩⟩

end TopCommRing

