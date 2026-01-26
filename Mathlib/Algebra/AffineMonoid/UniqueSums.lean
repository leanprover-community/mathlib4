
/-!
# Affine monoids have unique sums

In this file we show that finitely generated cancellative torsion-free commutative monoids have
unique sums. This is a direct corollary of them embedding into `ℤⁿ` for some `n`.
-/

public section

variable {M : Type*}

instance (priority := low) AffineAddMonoid.to_twoUniqueSums [AddCancelCommMonoid M] [AddMonoid.FG M]
    [IsAddTorsionFree M] : TwoUniqueSums M :=
  .of_injective_addHom (embedding M).toAddHom embedding_injective inferInstance

@[to_additive existing AffineAddMonoid.to_twoUniqueSums]
instance (priority := low) AffineMonoid.to_twoUniqueProds [CancelCommMonoid M] [Monoid.FG M]
    [IsMulTorsionFree M] : TwoUniqueProds M :=
  Multiplicative.instTwoUniqueProdsOfTwoUniqueSums (M := Additive M)
