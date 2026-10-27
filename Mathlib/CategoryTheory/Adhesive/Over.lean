/-
Copyright (c) 2026 Dénes Pápai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dénes Pápai
-/
module

public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Adhesive structure on slice categories

The slice category `Over B` inherits the property of being adhesive from the
base category, and dually so does the coslice category `Under B`.
-/

public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

/-- Slices of adhesive categories are adhesive. See [adhesive2004], Proposition 8 (ii). -/
instance adhesive_over [Adhesive C] [HasPullbacks C] [HasPushouts C] (B : C) :
    Adhesive (Over B) :=
  adhesive_of_preserves_and_reflects_isomorphism (Over.forget B)

/-- Coslices of adhesive categories are adhesive. See [adhesive2004], Proposition 8 (ii). -/
instance adhesive_under [Adhesive C] [HasPullbacks C] [HasPushouts C] (B : C) :
    Adhesive (Under B) :=
  adhesive_of_preserves_and_reflects_isomorphism (Under.forget B)

end CategoryTheory
