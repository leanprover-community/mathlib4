/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.WithTerminal.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Further lemmas on `WithTerminal`

These lemmas and instances need more imports.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

namespace WithTerminal

open IsCofiltered in
instance [IsCofilteredOrEmpty C] : IsCofiltered (WithTerminal C) where
  cone_objs x y :=
    match x, y with
    | star, y => ⟨y, default, 𝟙 y, trivial⟩
    | x, star => ⟨x, 𝟙 x, default, trivial⟩
    | of x, of y => ⟨.of <| min x y, minToLeft _ _, minToRight _ _, trivial⟩
  cone_maps x y f g :=
    match x, y with
    | star, _ => ⟨star, 𝟙 _, (IsIso.eq_comp_inv f).mp rfl⟩
    | x, star => ⟨x, 𝟙 _, Subsingleton.elim _ _⟩
    | of _, of _ => ⟨.of <| eq f g, eqHom _ _, eq_condition _ _⟩

end WithTerminal

namespace WithInitial

instance [IsFilteredOrEmpty C] : IsFiltered (WithInitial C) :=
  have := IsCofiltered.of_equivalence (opEquiv C).symm
  isFiltered_of_isCofiltered_op _

end WithInitial

end CategoryTheory
