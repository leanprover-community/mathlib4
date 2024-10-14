import Mathlib.Algebra.Category.ModuleCat.Differentials.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf

universe u

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

noncomputable def differentials : X.Modules :=
  SheafOfModules.relativeDifferentials (φ := SheafedSpace.sheafMap f.val)

end Modules

end Scheme

end AlgebraicGeometry
