import Mathlib.Algebra.AddConstMap.Basic

/-- An equivalence between `G` and `H` conjugating `(· + a)` to `(· + b)`. -/
structure AddConstEquiv (G H : Type*) [Add G] [Add H] (a : G) (b : H)
  extends G ≃ H, G →+c[a, b] H

@[inherit_doc]
notation:25 G " ≃+c[" a ", " b "] " H => AddConstEquiv G H a b

class AddConstEquivClass (F : Type*) (G H : outParam (Type*)) [Add G] [Add H]
    (a : outParam G) (b : outParam H) extends EquivLike F G H where
  map_add_const (f : F) (x : G) : f (x + a) = f x + b

instance (priority := 100) {F : Type*} {G H : outParam Type*} [Add G] [Add H]
    {a : outParam G} {b : outParam H} [h : AddConstEquivClass F G H a b] :
    AddConstMapClass F G H a b where
  toFunLike := inferInstance
  __ := h

instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    AddConstEquivClass (G ≃+c[a, b] H) G H a b where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' | ⟨_, _⟩, ⟨_, _⟩, h, _ => by congr; exact FunLike.ext' h
  map_add_const f x := f.map_add_const' x

namespace AddConstEquiv

end AddConstEquiv
