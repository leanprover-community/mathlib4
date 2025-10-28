/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.LargeColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Properties of the universe lift functor for groups

This file shows that the functors `GrpCat.uliftFunctor` and `CommGrpCat.uliftFunctor`
(as well as the additive versions) are fully faithful, preserve all limits and
create small limits.

Full faithfulness is pretty obvious. To prove that the functors preserve limits,
we use the fact that the forgetful functor from `GrpCat` or `CommGrpCat` into `Type`
creates all limits (because of the way limits are constructed in `GrpCat` and `CommGrpCat`),
and that the universe lift functor on `Type` preserves all limits. Once we know
that `GrpCat.uliftFunctor` preserves all limits and is fully faithful, it will
automatically create all limits that exist, i.e. all small ones.

We then switch to `AddCommGrpCat` and show that `AddCommGrpCat.uliftFunctor` preserves zero
morphisms and is an additive functor, which again is pretty obvious.

The last result is a proof that `AddCommGrpCat.uliftFunctor` preserves all colimits
(and hence creates small colimits). This is the only non-formal part of this file,
as we follow the same strategy as for the categories `Type`.

Suppose that we have a functor `K : J ⥤ AddCommGrpCat.{u}` (with `J` any category), a
colimit cocone `c` of `K` and a cocone `lc` of `K ⋙ uliftFunctor.{u v}`. We want to
construct a morphism of cocones `uliftFunctor.mapCocone c → lc` witnessing the fact
that `uliftFunctor.mapCocone c` is also a colimit cocone, but we have no direct way
to do this. The idea is to use that `AddCommGrpCat.{max v u}` has a small cogenerator,
which is just the additive (rational) circle `ℚ / ℤ`, so any abelian group of
any size can be recovered from its morphisms into `ℚ / ℤ`. More precisely, the functor
sending an abelian group `A` to its dual `A →+ ℚ / ℤ` is fully faithful, *if* we consider
the dual as a (right) module over the endomorphism ring of `ℚ / ℤ`. So an abelian
group `C` is totally determined by the restriction of the coyoneda
functor `A ↦ (C →+ A)` to the category of abelian groups at a smaller universe level.
We do not develop this totally here but do a direct construction. Every time we have
a morphism from `lc.pt` into `ℚ / ℤ`, or more generally into any small abelian group
`A`, we can construct a cocone of `K ⋙ uliftFunctor` by sticking `ULift A` at the
cocone point (this is `CategoryTheory.Limits.Cocone.extensions`), and this cocone is
actually made up of `u`-small abelian groups, hence gives a cocone of `K`. Using
the universal property of `c`, we get a morphism `c.pt →+ A`. So we have constructed
a map `(lc.pt →+ A) → (c.pt →+ A)`, and it is easy to prove that it is compatible with
postcomposition of morphisms of small abelian groups. To actually get the
morphism `c.pt →+ lc.pt`, we apply this to the canonical embedding of `lc.pt` into
`Π (_ : lc.pt →+ ℚ / ℤ), ℚ / ℤ` (this group is not small but is a product of small
groups, so our construction extends). To show that the image of `c.pt` in this product
is contained in that of `lc.pt`, we use the compatibility with postcomposition and the
fact that we can detect elements of the image just by applying morphisms from
`Π (_ : lc.pt →+ ℚ / ℤ), ℚ / ℤ` to `ℚ / ℤ`.

Note that this does *not* work for noncommutative groups, because the existence of
simple groups of arbitrary size implies that a general object `G` of `GrpCat` is not
determined by the restriction of `coyoneda.obj G` to the category of groups at
a smaller universe level. Indeed, the functor `GrpCat.uliftFunctor` does not commute
with arbitrary colimits: if we take an increasing family `K` of simple groups in
`GrpCat.{u}` of unbounded cardinality indexed by a linearly ordered type
(for example finitary alternating groups on a family of types in `u` of unbounded cardinality),
then the colimit of `K` in `GrpCat.{u}` exists and is the trivial group; meanwhile, the colimit
of `K ⋙ GrpCat.uliftFunctor.{u + 1}` is nontrivial (it is the "union" of all the `K j`, which is
too big to be in `GrpCat.{u}`).
-/

universe v w w' u

open CategoryTheory Limits

namespace GrpCat

/-- The universe lift functor for groups is fully faithful.
-/
@[to_additive
  /-- The universe lift functor for additive groups is fully faithful. -/]
def uliftFunctorFullyFaithful : uliftFunctor.{u, v}.FullyFaithful where
  preimage f := GrpCat.ofHom (MulEquiv.ulift.toMonoidHom.comp
    (f.hom.comp MulEquiv.ulift.symm.toMonoidHom))
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- The universe lift functor for groups is faithful.
-/
@[to_additive
  /-- The universe lift functor for additive groups is faithful. -/]
instance : uliftFunctor.{u, v}.Faithful := uliftFunctorFullyFaithful.faithful


/-- The universe lift functor for groups is full.
-/
@[to_additive
  /-- The universe lift functor for additive groups is full. -/]
instance : uliftFunctor.{u, v}.Full := uliftFunctorFullyFaithful.full

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ GrpCat.{u}) : PreservesLimit K uliftFunctor.{v, u} where
  preserves lc := ⟨isLimitOfReflects (forget GrpCat.{max u v})
    (isLimitOfPreserves CategoryTheory.uliftFunctor (isLimitOfPreserves (forget GrpCat) lc))⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where

/--
The universe lift for groups preserves limits of arbitrary size.
-/
@[to_additive
  /-- The universe lift functor for additive groups preserves limits of arbitrary size. -/]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where

/--
The universe lift functor on `GrpCat.{u}` creates `u`-small limits.
-/
@[to_additive
  /-- The universe lift functor on `AddGrpCat.{u}` creates `u`-small limits. -/]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end GrpCat

namespace CommGrpCat

/-- The universe lift functor for commutative groups is fully faithful.
-/
@[to_additive
  /-- The universe lift functor for commutative additive groups is fully faithful. -/]
def uliftFunctorFullyFaithful : uliftFunctor.{u, v}.FullyFaithful where
  preimage f := CommGrpCat.ofHom (MulEquiv.ulift.toMonoidHom.comp
    (f.hom.comp MulEquiv.ulift.symm.toMonoidHom))
  map_preimage _ := rfl
  preimage_map _ := rfl

-- The universe lift functor for commutative groups is faithful. -/
@[to_additive
  /-- The universe lift functor for commutative additive groups is faithful. -/]
instance : uliftFunctor.{u, v}.Faithful := uliftFunctorFullyFaithful.faithful

-- The universe lift functor for commutative groups is full. -/
@[to_additive
  /-- The universe lift functor for commutative additive groups is full. -/]
instance : uliftFunctor.{u, v}.Full := uliftFunctorFullyFaithful.full

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ CommGrpCat.{u}) : PreservesLimit K uliftFunctor.{v, u} where
  preserves lc := ⟨isLimitOfReflects (forget CommGrpCat.{max u v})
    (isLimitOfPreserves CategoryTheory.uliftFunctor (isLimitOfPreserves (forget CommGrpCat) lc))⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where

/--
The universe lift for commutative groups preserves limits of arbitrary size.
-/
@[to_additive /-- The universe lift functor for commutative additive groups preserves limits of
  arbitrary size. -/]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where

/--
The universe lift functor on `CommGrpCat.{u}` creates `u`-small limits.
-/
@[to_additive
  /-- The universe lift functor on `AddCommGrpCat.{u}` creates `u`-small limits. -/]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end CommGrpCat

namespace AddCommGrpCat

/-- The universe lift for commutative additive groups is additive.
-/
instance uliftFunctor_additive :
    AddCommGrpCat.uliftFunctor.{u,v}.Additive where

open Colimits in
/--
The functor `uliftFunctor : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{max u v}` preserves colimits
of arbitrary size.
-/
noncomputable instance : PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u} where
  preservesColimitsOfShape {J _} :=
  { preservesColimit := fun {F} ↦
    { preserves := fun {c} hc ↦ by
        classical
        rw [isColimit_iff_bijective_desc, ← Function.Bijective.of_comp_iff _
          (quotQuotUliftAddEquiv F).bijective, ← AddEquiv.coe_toAddMonoidHom,
          ← AddMonoidHom.coe_comp, Quot.desc_quotQuotUliftAddEquiv]
        exact ULift.up_bijective.comp ((isColimit_iff_bijective_desc c).mp (Nonempty.intro hc)) } }

/--
The functor `uliftFunctor : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{max u v}` creates `u`-small colimits.
-/
noncomputable instance : CreatesColimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesColimitsOfShape :=
    { CreatesColimit := fun {_} ↦ createsColimitOfReflectsIsomorphismsOfPreserves }

end AddCommGrpCat
