
/-!
# Pulling back rings along injective maps, and pushing them forward along surjective maps
-/

public section

open Function

variable {α β : Type*}

/-- Pullback `IsDomain` instance along an injective function. -/
protected theorem Function.Injective.isDomain [Semiring α] [IsDomain α] [Semiring β] {F}
    [FunLike F β α] [MonoidWithZeroHomClass F β α] (f : F) (hf : Injective f) : IsDomain β where
  __ := domain_nontrivial f (map_zero _) (map_one _)
  __ := hf.isCancelMulZero f (map_zero _) (map_mul _)
