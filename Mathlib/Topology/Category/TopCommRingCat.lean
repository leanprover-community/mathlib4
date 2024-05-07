/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Algebra.Ring.Basic

#align_import topology.category.TopCommRing from "leanprover-community/mathlib"@"9a59dcb7a2d06bf55da57b9030169219980660cd"

/-!
# Category of topological commutative rings

We introduce the category `TopCommRingCat` of topological commutative rings together with the
relevant forgetful functors to topological spaces and commutative rings.
-/


universe u

open CategoryTheory

set_option linter.uppercaseLean3 false -- `TopCommRingCat`

/-- A bundled topological commutative ring. -/
structure TopCommRingCat where
  /-- carrier of a topological commutative ring. -/
  α : Type u
  [isCommRing : CommRing α]
  [isTopologicalSpace : TopologicalSpace α]
  [isTopologicalRing : TopologicalRing α]
#align TopCommRing TopCommRingCat

namespace TopCommRingCat

instance : Inhabited TopCommRingCat :=
  ⟨⟨PUnit⟩⟩

instance : CoeSort TopCommRingCat (Type u) :=
  ⟨TopCommRingCat.α⟩

attribute [instance] isCommRing isTopologicalSpace isTopologicalRing

instance : Category TopCommRingCat.{u} where
  Hom R S := { f : R →+* S // Continuous f }
  id R := ⟨RingHom.id R, by rw [RingHom.id]; continuity⟩
  comp f g :=
    ⟨g.val.comp f.val, by
      -- TODO automate
      cases f
      cases g
      dsimp; apply Continuous.comp <;> assumption⟩

instance : ConcreteCategory TopCommRingCat.{u} where
  forget :=
    { obj := fun R => R
      map := fun f => f.val }
  -- Porting note: Old proof was `forget_faithful := { }`
  forget_faithful :=
    { map_injective := fun {_ _ a b} h => Subtype.ext <| RingHom.coe_inj h }

/-- Construct a bundled `TopCommRingCat` from the underlying type and the appropriate typeclasses.
-/
def of (X : Type u) [CommRing X] [TopologicalSpace X] [TopologicalRing X] : TopCommRingCat :=
  ⟨X⟩
#align TopCommRing.of TopCommRingCat.of

@[simp]
theorem coe_of (X : Type u) [CommRing X] [TopologicalSpace X] [TopologicalRing X] :
    (of X : Type u) = X := rfl
#align TopCommRing.coe_of TopCommRingCat.coe_of

instance forgetTopologicalSpace (R : TopCommRingCat) :
    TopologicalSpace ((forget TopCommRingCat).obj R) :=
  R.isTopologicalSpace
#align TopCommRing.forget_topological_space TopCommRingCat.forgetTopologicalSpace

instance forgetCommRing (R : TopCommRingCat) : CommRing ((forget TopCommRingCat).obj R) :=
  R.isCommRing
#align TopCommRing.forget_comm_ring TopCommRingCat.forgetCommRing

instance forgetTopologicalRing (R : TopCommRingCat) :
    TopologicalRing ((forget TopCommRingCat).obj R) :=
  R.isTopologicalRing
#align TopCommRing.forget_topological_ring TopCommRingCat.forgetTopologicalRing

instance hasForgetToCommRingCat : HasForget₂ TopCommRingCat CommRingCat :=
  HasForget₂.mk' (fun R => CommRingCat.of R) (fun _ => rfl) (fun f => f.val) HEq.rfl
#align TopCommRing.has_forget_to_CommRing TopCommRingCat.hasForgetToCommRingCat

instance forgetToCommRingCatTopologicalSpace (R : TopCommRingCat) :
    TopologicalSpace ((forget₂ TopCommRingCat CommRingCat).obj R) :=
  R.isTopologicalSpace
#align TopCommRing.forget_to_CommRing_topological_space TopCommRingCat.forgetToCommRingCatTopologicalSpace

/-- The forgetful functor to `TopCat`. -/
instance hasForgetToTopCat : HasForget₂ TopCommRingCat TopCat :=
  HasForget₂.mk' (fun R => TopCat.of R) (fun _ => rfl) (fun f => ⟨⇑f.1, f.2⟩) HEq.rfl
#align TopCommRing.has_forget_to_Top TopCommRingCat.hasForgetToTopCat

instance forgetToTopCatCommRing (R : TopCommRingCat) :
    CommRing ((forget₂ TopCommRingCat TopCat).obj R) :=
  R.isCommRing
#align TopCommRing.forget_to_Top_comm_ring TopCommRingCat.forgetToTopCatCommRing

instance forgetToTopCatTopologicalRing (R : TopCommRingCat) :
    TopologicalRing ((forget₂ TopCommRingCat TopCat).obj R) :=
  R.isTopologicalRing
#align TopCommRing.forget_to_Top_topological_ring TopCommRingCat.forgetToTopCatTopologicalRing

/-- The forgetful functors to `Type` do not reflect isomorphisms,
but the forgetful functor from `TopCommRingCat` to `TopCat` does.
-/
instance : (forget₂ TopCommRingCat.{u} TopCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    -- We have an isomorphism in `TopCat`,
    let i_Top := asIso ((forget₂ TopCommRingCat TopCat).map f)
    -- and a `RingEquiv`.
    let e_Ring : X ≃+* Y := { f.1, ((forget TopCat).mapIso i_Top).toEquiv with }
    -- Putting these together we obtain the isomorphism we're after:
    exact
      ⟨⟨⟨e_Ring.symm, i_Top.inv.2⟩,
          ⟨by
            ext x
            exact e_Ring.left_inv x, by
            ext x
            exact e_Ring.right_inv x⟩⟩⟩

end TopCommRingCat
