/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.IsConnected

/-!
# Filtered categories are connected
-/

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

instance (priority := 100) IsFilteredOrEmpty.isPreconnected [IsFilteredOrEmpty C] :
    IsPreconnected C :=
  zigzag_isPreconnected fun j j' => .trans
    (.single <| .inl <| .intro <| IsFiltered.leftToMax j j')
    (.single <| .inr <| .intro <| IsFiltered.rightToMax j j')

instance (priority := 100) IsCofilteredOrEmpty.isPreconnected [IsCofilteredOrEmpty C] :
    IsPreconnected C :=
  zigzag_isPreconnected fun j j' => .trans
    (.single <| .inr <| .intro <| IsCofiltered.minToLeft j j')
    (.single <| .inl <| .intro <| IsCofiltered.minToRight j j')

instance (priority := 100) IsFiltered.isConnected [IsFiltered C] : IsConnected C :=
  { IsFilteredOrEmpty.isPreconnected C with }

instance (priority := 100) IsCofiltered.isConnected [IsCofiltered C] : IsConnected C :=
  { IsCofilteredOrEmpty.isPreconnected C with }

end CategoryTheory
