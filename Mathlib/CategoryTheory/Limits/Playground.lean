import Mathlib

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

instance IsFilteredOrEmpty.IsPreconnected [IsFilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun j j' => .trans (.single <| .inl <| .intro <| IsFiltered.leftToMax j j')
    (.single <| .inr <| .intro <| IsFiltered.rightToMax j j')

attribute [local instance] IsFiltered.nonempty

instance IsFiltered.IsConnected [IsFiltered C] : IsConnected C :=
  { IsFilteredOrEmpty.IsPreconnected C with }

end CategoryTheory
