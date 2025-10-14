/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!
# Instances...

-/

universe t u u' w

namespace CategoryTheory

open Limits

section

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{u} A] [HasLimits A] [HasColimits A]
  {FA : A → A → Type w} {CA : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [PreservesFilteredColimits (forget A)]
  [PreservesLimits (forget A)] [(forget A).ReflectsIsomorphisms]

instance hasSheafifyOfConcrete : HasSheafify J A := by
  infer_instance

instance hasSheafComposeForget : J.HasSheafCompose (forget A) :=
  hasSheafCompose_of_preservesMulticospan _ _

end

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    HasSheafify J (Type u) := by
  infer_instance

end CategoryTheory
