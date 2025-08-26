/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
import Lean.Meta.Basic

/-!
To avoid an initialization order issue, we move the `IO.Ref` declarations into an earlier file.
-/

open Lean Meta

namespace CategoryTheory

/--
IO ref for reassociation handlers `reassoc` attribute, so that it can be extended
with additional handlers. Handlers take a proof of the equation.

The default handler is `reassocExprHom` for morphism reassociation.
This will be extended in `Tactic.CategoryTheory.IsoReassoc` for isomorphism reassociation.
-/
initialize reassocImplRef : IO.Ref (Array (Expr → MetaM Expr)) ← IO.mkRef #[]
