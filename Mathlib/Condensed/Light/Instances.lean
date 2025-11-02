/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# `HasSheafify` instances

In this file, we obtain a `HasSheafify (coherentTopology LightProfinite.{u}) (Type u)`
instance (and similarly for other concrete categories). These instances
are not obtained automatically because `LightProfinite.{u}` is a large category,
but as it is essentially small, the instances can be obtained using the results
in the file `CategoryTheory.Sites.Equivalence`.

-/

universe u u' v

open CategoryTheory Limits

namespace LightProfinite

variable (A : Type u') [Category.{u} A] [HasLimits A] [HasColimits A]
  {FA : A → A → Type v} {CA : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [PreservesFilteredColimits (forget A)]
  [PreservesLimits (forget A)] [(forget A).ReflectsIsomorphisms]

instance hasSheafify :
    HasSheafify (coherentTopology LightProfinite.{u}) A :=
  hasSheafifyEssentiallySmallSite _ _

instance hasSheafify_type :
    HasSheafify (coherentTopology LightProfinite.{u}) (Type u) :=
  hasSheafifyEssentiallySmallSite _ _

instance : (coherentTopology LightProfinite.{u}).WEqualsLocallyBijective A :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end LightProfinite
