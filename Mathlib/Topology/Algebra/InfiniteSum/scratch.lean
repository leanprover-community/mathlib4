import Mathlib

lemma bot_eq_zero''' {R : Type*} [AddCommMonoid R] [CompleteLattice R] [IsOrderedAddMonoid R]
  [CanonicallyOrderedAdd R] : (⊥ : R) = 0 :=
  -- `exact?`, `simp` and all versions of `bot_eq_zero` fail here
  bot_le.antisymm <| zero_le _

@[simp]
lemma bot_eq_zero'''' {R : Type*} [AddCommMonoid R] [CompleteLinearOrder R] [IsOrderedAddMonoid R]
  [CanonicallyOrderedAdd R] : (⊥ : R) = 0 :=
  -- `exact?`, `simp` and all versions of `bot_eq_zero` fail here
  bot_eq_zero'''
