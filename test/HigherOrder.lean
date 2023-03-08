import Mathlib.Tactic.HigherOrder

@[higher_order map_comp_pure]
lemma map_pure' {f : Type u → Type v} [Applicative f] [LawfulApplicative f]
  {α β : Type u} (g : α → β) (x : α) : g <$> (pure x : f α) = pure (g x) := map_pure g x

#check map_comp_pure
