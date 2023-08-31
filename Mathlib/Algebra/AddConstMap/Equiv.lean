import Mathlib.Algebra.AddConstMap.Basic

structure AddConstEquiv (G H : Type _) [Add G] [Add H] (a : G) (b : H) extends G ≃ H, G →+c[a, b] H

class AddConstEquivClass (F : Type _) (G H : outParam (Type _)) [Add G] [Add H]
    (a : outParam G) (b : outParam H) extends EquivLike F G H where
  map_add_const (f : F) (x : G) : f (x + a) = f x + b
