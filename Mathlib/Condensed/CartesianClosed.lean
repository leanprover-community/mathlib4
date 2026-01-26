/-!

# Condensed sets form a Cartesian closed category
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

instance : CartesianMonoidalCategory (CondensedSet.{u}) :=
  inferInstanceAs (CartesianMonoidalCategory (Sheaf _ _))

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : MonoidalClosed (CondensedSet.{u}) := inferInstanceAs (MonoidalClosed (Sheaf _ _))
