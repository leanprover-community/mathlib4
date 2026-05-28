/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Mapping quiver paths under prefunctors
-/

@[expose] public section

namespace Prefunctor

open Quiver

variable {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W)

@[simp]
lemma end_map {a b : V} (p : Path a b) : F.obj p.end = (F.mapPath p).end := by
  induction p with
  | nil => rfl
  | cons p' e ih => simp [ih]

end Prefunctor
