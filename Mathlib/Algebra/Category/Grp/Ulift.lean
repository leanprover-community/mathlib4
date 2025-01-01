/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Properties of the universe lift functor for groups

This file shows that the functors `Grp.uliftFunctor` and `CommGrp.uliftFunctor`
(as well as the additive versions) are fully faithful, preserves all limits and
create small limits.

It also shows that `AddCommGrp.uliftFunctor` is an additive functor.

-/

universe v w w' u

open CategoryTheory Limits

namespace Grp

/-- The universe lift functor for groups is fully faithful.
-/
@[to_additive
  "The universe lift functor for additive groups is fully faithful."]
def uliftFunctorFullyFaithful : uliftFunctor.{u, v}.FullyFaithful where
  preimage f := Grp.ofHom (MulEquiv.ulift.toMonoidHom.comp
    (f.comp MulEquiv.ulift.symm.toMonoidHom))
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- The universe lift functor for groups is faithful.
-/
@[to_additive
  "The universe lift functor for additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful := uliftFunctorFullyFaithful.faithful


/-- The universe lift functor for groups is full.
-/
@[to_additive
  "The universe lift functor for additive groups is full."]
instance : uliftFunctor.{u, v}.Full := uliftFunctorFullyFaithful.full

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ Grp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
  preserves lc := ⟨isLimitOfReflects (forget Grp.{max u v})
    (isLimitOfPreserves CategoryTheory.uliftFunctor (isLimitOfPreserves (forget Grp) lc))⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where

/--
The universe lift for groups preserves limits of arbitrary size.
-/
@[to_additive
  "The universe lift functor for additive groups preserves limits of arbitrary size."]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where

/--
The universe lift functor on `Grp.{u}` creates `u`-small limits.
-/
@[to_additive
  "The universe lift functor on `AddGrp.{u}` creates `u`-small limits."]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end Grp

namespace CommGrp

/-- The universe lift functor for commutative groups is fully faithful.
-/
@[to_additive
  "The universe lift functor for commutative additive groups is fully faithful."]
def uliftFunctorFullyFaithful : uliftFunctor.{u, v}.FullyFaithful where
  preimage f := Grp.ofHom (MulEquiv.ulift.toMonoidHom.comp
    (f.comp MulEquiv.ulift.symm.toMonoidHom))
  map_preimage _ := rfl
  preimage_map _ := rfl

-- The universe lift functor for commutative groups is faithful. -/
@[to_additive
  "The universe lift functor for commutative additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful := uliftFunctorFullyFaithful.faithful

-- The universe lift functor for commutative groups is full. -/
@[to_additive
  "The universe lift functor for commutative additive groups is full."]
instance : uliftFunctor.{u, v}.Full := uliftFunctorFullyFaithful.full

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ CommGrp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
  preserves lc := ⟨isLimitOfReflects (forget CommGrp.{max u v})
    (isLimitOfPreserves CategoryTheory.uliftFunctor (isLimitOfPreserves (forget CommGrp) lc))⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where

/--
The universe lift for commutative groups preserves limits of arbitrary size.
-/
@[to_additive
  "The universe lift functor for commutative additive groups preserves limits of arbitrary size."]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where

/--
The universe lift functor on `CommGrp.{u}` creates `u`-small limits.
-/
@[to_additive
  "The universe lift functor on `AddCommGrp.{u}` creates `u`-small limits."]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end CommGrp

namespace AddCommGroup

/-- The universe lift for commutative additive groups is additive.
-/
instance uliftFunctor_additive :
    AddCommGrp.uliftFunctor.{u,v}.Additive where

end AddCommGroup
