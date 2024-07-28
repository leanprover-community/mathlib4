import Mathlib.CategoryTheory.ChosenFiniteProducts

namespace CategoryTheory.Cat

open Limits

/-- The chosen terminal object in `Cat` is terminal. -/
def isTerminalPUnit : IsTerminal (Cat.of <| Discrete PUnit) where
  lift s := Functor.star s.pt
  fac s (j : Discrete PEmpty.{1}) := by dsimp; exact PEmpty.elim j.as
  uniq s m _ :=  Functor.punit_ext' m (Functor.star s.pt)

/-- The product cone in `Cat`. -/
def prodCone (C D : Cat) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _) (Prod.snd _ _)

def isLimitProdCone (X Y : Cat) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => Functor.prod' S.fst S.snd)-- def prod' (F : A ⥤ B) (G : A ⥤ C) : A ⥤ B × C
  (fun S => rfl)
  (fun S => rfl)
  (fun S m (h1 : m ≫ Prod.fst X Y = S.fst) (h2 : m ≫ Prod.snd X Y = S.snd) => by
    fapply Functor.hext
    · intro X
      apply Prod.ext <;> simp [← h1, ← h2]
    · intro X Y f
      dsimp
      rw [← h1, ← h2]
      rfl)


instance : ChosenFiniteProducts Cat where
  product (X Y : Cat) :  LimitCone (pair X Y) := { isLimit := isLimitProdCone X Y }
  terminal : LimitCone (Functor.empty Cat) := {isLimit := isTerminalPUnit }

end CategoryTheory.Cat
