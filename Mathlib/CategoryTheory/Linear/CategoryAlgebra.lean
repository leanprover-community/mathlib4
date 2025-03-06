import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Linear.Basic

universe w v u

namespace CategoryTheory.Linear

open DirectSum
open CategoryTheory.Preadditive

def CategoryAlgebra (R : Type w) [CommSemiring R] (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear R C] := ⨁ (p : C × C), p.1 ⟶ p.2

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [DecidableEq C]


instance CategoryAlgebra.inhabited : Inhabited (CategoryAlgebra R C) :=
  inferInstanceAs (Inhabited (⨁ (p : C × C), p.1 ⟶ p.2))

instance CategoryAlgebra.addCommMonoid : AddCommMonoid (CategoryAlgebra R C) :=
  inferInstanceAs (AddCommMonoid (⨁ (p : C × C), p.1 ⟶ p.2))

instance CategoryAlgebra.instIsCancelAdd [IsCancelAdd R] : IsCancelAdd (CategoryAlgebra R C) :=
  inferInstanceAs (IsCancelAdd (⨁ (p : C × C), p.1 ⟶ p.2))

instance CategoryAlgebra.instModule : Module R (CategoryAlgebra R C) :=
  inferInstanceAs (Module R (⨁ (p : C × C), p.1 ⟶ p.2))

def CategoryAlgebra.of (a b : C) : (a ⟶ b) →+ CategoryAlgebra R C :=
  DirectSum.of (fun (p : C × C) ↦ p.1 ⟶ p.2) (a,b)

@[simps]
def comp' (X Y Z W : C) (h : Y = Z) : (X ⟶ Y) →+ (Z ⟶ W) →+ (CategoryAlgebra R C) where
  toFun f := AddMonoidHom.comp (CategoryAlgebra.of X W) (compHom (f ≫ eqToHom h))
  map_add' := by
    intros
    ext
    simp
  map_zero' := by
    ext
    simp

def comp'' (X Y Z W : C) : (X ⟶ Y) →+ (Z ⟶ W) →+ (CategoryAlgebra R C) :=
  if h : Y = Z then comp' X Y Z W h else 0

@[irreducible] def mul' (f g : CategoryAlgebra R C) : CategoryAlgebra R C :=
  DFinsupp.sumAddHom (fun p ↦ DFinsupp.sumAddHom (fun q ↦ comp'' q.1 q.2 p.1 p.2) g) f

instance instMul : Mul (CategoryAlgebra R C) := ⟨mul'⟩

theorem mul_def (f g : CategoryAlgebra R C) :
  f * g = DFinsupp.sumAddHom (fun p ↦ DFinsupp.sumAddHom (fun q ↦ comp'' q.1 q.2 p.1 p.2) g) f := by
  with_unfolding_all rfl

instance : NonUnitalSemiring (CategoryAlgebra R C) where
  mul := mul'
  left_distrib := fun a b c => by simp [mul_def]
  right_distrib := fun a b c => by simp [mul_def]
  zero_mul := fun a => by simp [mul_def]
  mul_zero := fun a => by simp [mul_def]
  mul_assoc := fun a b c => by sorry


end CategoryTheory.Linear
