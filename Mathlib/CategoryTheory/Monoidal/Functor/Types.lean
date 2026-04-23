/-
Copyright (c) 2025 Vilim Lendvaj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vilim Lendvaj
-/
module

public import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Control.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Convert from `Applicative` to `CategoryTheory.Functor.LaxMonoidal`

This allows us to use Lean's `Type`-based applicative functors in category theory.

-/

@[expose] public section

namespace CategoryTheory

section

variable (F : Type* → Type*) [Applicative F] [LawfulApplicative F]

attribute [local simp] map_seq seq_map_assoc types_tensorObj_def types_tensorUnit_def
  LawfulApplicative.pure_seq LawfulApplicative.seq_assoc in
/-- A lawful `Applicative` gives a category theory `LaxMonoidal` functor
between categories of types. -/
@[simps]
instance : (ofTypeFunctor F).LaxMonoidal where
  ε := TypeCat.ofHom (fun _ ↦ (pure PUnit.unit : F _))
  μ _ _ := TypeCat.ofHom (fun p ↦ (Prod.mk <$> p.1 <*> p.2 : F _))

end

end CategoryTheory
