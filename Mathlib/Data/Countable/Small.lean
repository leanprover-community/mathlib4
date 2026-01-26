import Mathlib.Logic.Small.Defs

/-!
# All countable types are small.

That is, any countable type is equivalent to a type in any universe.
-/

@[expose] public section

universe w v

instance (priority := 100) Countable.toSmall (α : Type v) [Countable α] : Small.{w} α :=
  let ⟨_, hf⟩ := exists_injective_nat α
  small_of_injective hf

theorem Uncountable.of_not_small {α : Type v} (h : ¬ Small.{w} α) : Uncountable α := by
  rw [uncountable_iff_not_countable]
  exact mt (@Countable.toSmall α) h
