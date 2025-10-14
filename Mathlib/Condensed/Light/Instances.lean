/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Condensed.Light.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.Instances

/-!
# Instances

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

instance hasSheafifyType :
    HasSheafify (coherentTopology LightProfinite.{u}) (Type u) :=
  hasSheafifyEssentiallySmallSite _ _

example : (coherentTopology LightProfinite.{u}).HasSheafCompose (forget A) := by
  infer_instance

end LightProfinite
