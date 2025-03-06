import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Combinatorics.Quiver.Cast
import Mathlib.CategoryTheory.PathCategory.Basic
universe v u

namespace Quiver

namespace Path

def hnil {V : Type u} [Quiver.{v} V] {a b : V} (h : a = b) : Path a b :

end Path

namespace PathAlgebra

inductive TotalPath (V : Type u) [Quiver.{v} V] : Type max (u + 1) v
  | mk : ∀ (a b : V), Path a b → TotalPath V


instance {V : Type u} [Quiver.{v} V] [DecidableEq V] : Mul (WithZero (TotalPath V)) where
  mul := fun p q ↦ match p, q with
  | 0, _ => 0
  | _, 0 => 0
  | some (.mk a b p), some (.mk c d q) =>
    if h : (b = c) then some (TotalPath.mk a d (p.comp (h ▸ q))) else 0

instance {V : Type u} [Quiver.{v} V] [DecidableEq V] : SemigroupWithZero (WithZero (TotalPath V)) where
  zero_mul := fun p => by cases p <;> rfl
  mul_zero := fun p => by cases p <;> rfl
  mul_assoc := fun p q r => by
    cases p <;> cases q <;> cases r <;> try rfl
    next p q => cases ((p : WithZero (TotalPath V)) * q) <;> rfl
    next p q => cases ((p : WithZero (TotalPath V)) * q) <;> rfl
    next p q r =>
      cases p
      cases q
      cases r


end PathAlgebra

end Quiver
