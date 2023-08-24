import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Quotient.Linear

universe w' w v u

open CategoryTheory

variable {R : Type w} [Ring R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {ι : Type w'} {c : ComplexShape ι}

namespace HomologicalComplex

variable {X Y : HomologicalComplex C c}

instance : SMul R (X ⟶ Y) where
  smul r f :=
    { f := fun n => r • f.f n }

@[simp]
lemma smul_f (r : R) (f : X ⟶ Y) (n : ι) : (r • f).f n = r • f.f n := rfl

instance (X Y : HomologicalComplex C c) : Module R (X ⟶ Y) where
  one_smul a := by aesop_cat
  smul_zero := by aesop_cat
  smul_add := by aesop_cat
  zero_smul := by aesop_cat
  add_smul := by
    intros
    ext
    apply add_smul
  mul_smul := by
    intros
    ext
    apply mul_smul

instance : Linear R (HomologicalComplex C c) where

end HomologicalComplex

namespace HomotopyCategory

-- the next two instances should be moved to `Algebra.Homology.HomotopyCategory`
instance : Preadditive (CategoryTheory.Quotient (homotopic C c)) :=
  (inferInstance : Preadditive (HomotopyCategory C c))

instance : Functor.Additive (Quotient.functor (homotopic C c)) :=
  (inferInstance : (HomotopyCategory.quotient C c).Additive)

instance : Linear R (HomotopyCategory C c) :=
  Quotient.linear R (homotopic C c) (by
    rintro a X Y f g ⟨h⟩
    -- this should be a definition `Homotopy.smul` in `Algebra.Homology.Homotopy`
    exact
    ⟨{  hom := fun i j => a • h.hom i j
        zero := fun i j hij => by
          dsimp
          rw [h.zero i j hij, smul_zero]
        comm := fun i => by
          dsimp
          rw [h.comm]
          dsimp [fromNext, toPrev]
          simp only [smul_add, Linear.comp_smul, Linear.smul_comp] }⟩)

instance : Functor.Linear R (HomotopyCategory.quotient C c) :=
  Quotient.linear_functor _ _ _

end HomotopyCategory
