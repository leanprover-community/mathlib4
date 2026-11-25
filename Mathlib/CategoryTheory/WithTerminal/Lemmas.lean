/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.WithTerminal.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Further lemmas on `WithTerminal`

These lemmas and instances need more imports.
-/

public section

namespace CategoryTheory.WithTerminal

variable {C : Type*} [Category* C]

open IsCofiltered in
@[to_dual]
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

end CategoryTheory.WithTerminal
