/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
This file shows that the functors `Grp.uliftFunctor` and `CommGrp.uliftFunctor`
(as well as the additive versions) are fully faithful, preserves all limits and
create small limits.

It also shows that `AddCommGrp.uliftFunctor` preserves zero morphisms and is an additive functor.

-/

universe v w w' u

open CategoryTheory Limits

namespace Grp

/-- The universe lift functor for groups is faithful.
-/
@[to_additive
  "The universe lift functor for additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful where
  map_injective := by
    intro X Y f g
    intro heq
    ext a
    apply_fun (fun h ↦ h {down := a}) at heq
    change Equiv.ulift.symm (f a) = Equiv.ulift.symm (g a) at heq
    exact (EmbeddingLike.apply_eq_iff_eq _).mp heq

/-- The universe lift functor for groups is full.
-/
@[to_additive
  "The universe lift functor for additive groups is full."]
instance : uliftFunctor.{u, v}.Full where
  map_surjective {X Y} f :=
    ⟨ofHom (MonoidHom.mk (OneHom.mk (fun x => (f (ULift.up x)).down)
          (by change (f 1).down = ?_; rw [f.map_one]; rfl))
          (fun _ _ ↦ by simp only [uliftFunctor_obj, coe_of];
                        change (f (_ * _)).down = _; rw [f.map_mul]; rfl)), rfl⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ Grp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
      preserves {c} lc := by
        apply ReflectsLimit.reflects (F := forget Grp.{max u v})
        set e : CategoryTheory.uliftFunctor.{v,u}.mapCone ((forget Grp).mapCone c) ≅
            (forget Grp).mapCone (uliftFunctor.mapCone c) := Cones.ext (Iso.refl _) (fun _ ↦ rfl)
        exact IsLimit.ofIsoLimit (Classical.choice (PreservesLimit.preserves
          (F := CategoryTheory.uliftFunctor) (Classical.choice (PreservesLimit.preserves
          (F := forget Grp) lc)))) e

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where
      preservesLimit := inferInstance

/--
The universe lift for groups preserves limits of arbitrary size.
-/
@[to_additive
  "The universe lift functor for additive groups preserves limits of arbitrary size."]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where
      preservesLimitsOfShape := inferInstance

@[to_additive]
noncomputable instance uliftFunctor_preservesLimits :
    PreservesLimits uliftFunctor.{v, u} := uliftFunctor_preservesLimitsOfSize

/--
The universe lift functor on `Grp.{u}` creates `u`-small limits.
-/
@[to_additive
  "The universe lift functor on `AddGrp.{u}` creates `u`-small limits."
]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end Grp

namespace CommGrp

-- The universe lift functor for commutative groups is faithful. -/
@[to_additive
  "The universe lift functor for commutative additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful where
  map_injective := by
    intro X Y f g
    intro heq
    ext a
    apply_fun (fun h ↦ h {down := a}) at heq
    change Equiv.ulift.symm (f a) = Equiv.ulift.symm (g a) at heq
    exact (EmbeddingLike.apply_eq_iff_eq _).mp heq

-- The universe lift functor for commutative groups is full. -/
@[to_additive
  "The universe lift functor for commutative additive groups is full."]
instance : uliftFunctor.{u, v}.Full where
  map_surjective {X Y} f :=
    ⟨ofHom (MonoidHom.mk (OneHom.mk (fun x => (f (ULift.up x)).down)
          (by change (f 1).down = ?_; rw [f.map_one]; rfl))
          (fun _ _ ↦ by simp only [uliftFunctor_obj, coe_of];
                        change (f (_ * _)).down = _; rw [f.map_mul]; rfl)), rfl⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ CommGrp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
      preserves {c} lc := by
        apply ReflectsLimit.reflects (F := forget CommGrp.{max u v})
        set e : CategoryTheory.uliftFunctor.{v,u}.mapCone ((forget CommGrp).mapCone c) ≅
            (forget CommGrp).mapCone (uliftFunctor.mapCone c) :=
          Cones.ext (Iso.refl _) (fun _ ↦ rfl)
        exact IsLimit.ofIsoLimit (Classical.choice (PreservesLimit.preserves
          (F := CategoryTheory.uliftFunctor) (Classical.choice (PreservesLimit.preserves
          (F := forget CommGrp) lc)))) e

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where
      preservesLimit := inferInstance

/--
The universe lift for commutative groups preserves limits of arbitrary size.
-/
@[to_additive
  "The universe lift functor for commutative additive groups preserves limits of arbitrary size."]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where
      preservesLimitsOfShape := inferInstance

@[to_additive]
noncomputable instance uliftFunctor_preservesLimits :
    PreservesLimits uliftFunctor.{v, u} := uliftFunctor_preservesLimitsOfSize

/--
The universe lift functor on `CommGrp.{u}` creates `u`-small limits.
-/
@[to_additive
  "The universe lift functor on `AddCommGrp.{u}` creates `u`-small limits."
]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end CommGrp

namespace AddCommGroup

/-- The universe lift for commutative additive groups preserves zero morphisms.
-/
instance uliftFunctor_preservesZeroMorphisms :
    AddCommGrp.uliftFunctor.{u,v}.PreservesZeroMorphisms := {map_zero := fun X Y ↦ by rfl}

instance uliftFunctor_additive :
    AddCommGrp.uliftFunctor.{u,v}.Additive where map_add := rfl

end AddCommGroup
