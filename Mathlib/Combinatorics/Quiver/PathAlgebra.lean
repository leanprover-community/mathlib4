import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.CategoryTheory.Linear.CategoryAlgebra
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Cast
universe w v u

namespace Quiver

open CategoryTheory.Linear

/- TODO: does not work, why? -/
--  def PathAlgebra (R : Type w) [CommRing R] {V : Type u} [Quiver.{v} V] :=
--    CategoryAlgebra R (CategoryTheory.Free R (CategoryTheory.Paths V))


def PathAlgebra (R : Type w) [CommRing R] {V : Type u} [Quiver.{v} V] :=
  @CategoryAlgebra R inferInstance (CategoryTheory.Free R (CategoryTheory.Paths V))



end Quiver
