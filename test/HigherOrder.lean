import Mathlib.Tactic.HigherOrder

namespace HigherOrderTest

@[higher_order map_comp_pure]
lemma map_pure' {f : Type u → Type v} [Applicative f] [LawfulApplicative f]
  {α β : Type u} (g : α → β) (x : α) : g <$> (pure x : f α) = pure (g x) := map_pure g x

example {f : Type u → Type v} [Applicative f] [LawfulApplicative f]
    {α β : Type u} (g : α → β) : Functor.map g ∘ (pure : α → f α) = pure ∘ g := by
  apply map_comp_pure

end HigherOrderTest
