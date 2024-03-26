/-

@[simps]
def MyHom.inverse (f:MyHom a b) (g : b → a) (h₁ : Function.LeftInverse g f) : MyHom b a :=
  { toFun := g,
    map_one' := by rw [← f.map_one, h₁]}

structure MyEquiv (A B : Type*) ⋯ extends A ≃ B, MyHom A B

-/
