/-
Copyright (c) 2026 GDIES. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GDIES
-/
module

public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!

# Adhesive structure on slice categories

We show that the slice (over) category `Over B` inherits the adhesive structure from the
base category.

## Main Results
- `CategoryTheory.adhesive_over`: `Over B` is adhesive when the base
  category is adhesive with pullbacks and pushouts.

## TODO
- The dual result for `Under B` (coslice).

## References
- [Stephen Lack and Paweł Sobociński, *Adhesive Categories*][adhesive2004], Proposition 3.5(ii)

-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- Slices of adhesive categories are adhesive. The forgetful functor `Over.forget B : Over B ⥤ C`
creates all colimits and creates connected limits (in particular pullbacks), so
`adhesive_of_preserves_and_reflects_isomorphism` transfers the adhesive structure.

See [adhesive2004], Proposition 3.5(ii). -/
instance adhesive_over [Adhesive C] [HasPullbacks C] [HasPushouts C] (B : C) :
    Adhesive (Over B) :=
  adhesive_of_preserves_and_reflects_isomorphism (Over.forget B)

end CategoryTheory
