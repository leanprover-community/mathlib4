import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Equivalence

universe u

open CategoryTheory GrothendieckTopology

section Small

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Type u) [Ring R]

example : HasSheafCompose J (forget (ModuleCat.{u} R)) := inferInstance

end Small

section Large

variable {C : Type (u + 1)} [LargeCategory C] (J : GrothendieckTopology C)

example (R : Type (u + 1)) [Ring R] : HasSheafCompose J (forget (ModuleCat.{u+1} R)) := inferInstance

variable [EssentiallySmall.{u} C]

example (R : Type u) [Ring R] : HasSheafCompose J (forget (ModuleCat.{u} R)) := inferInstance

end Large
