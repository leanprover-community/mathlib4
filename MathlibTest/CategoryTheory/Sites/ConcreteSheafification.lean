import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Equivalence

universe u

open CategoryTheory

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Small

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

example : HasSheafify J (Type u) := inferInstance

example (R : Type u) [Ring R] : HasSheafify J (ModuleCat.{u} R) := inferInstance

end Small

section Large

variable {C : Type (u + 1)} [LargeCategory C] (J : GrothendieckTopology C)

example : HasSheafify J (Type (u+1)) := inferInstance

example (R : Type (u + 1)) [Ring R] : HasSheafify J (ModuleCat.{u+1} R) := inferInstance

variable [EssentiallySmall.{u} C]

example : HasSheafify J (Type u) := inferInstance

example (R : Type u) [Ring R] : HasSheafify J (ModuleCat.{u} R) := inferInstance

end Large
