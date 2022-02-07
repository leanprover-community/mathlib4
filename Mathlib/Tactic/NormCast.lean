/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis, Mario Carneiro
-/

import Lean
import Mathlib.Tactic.RunCmd

/-!
# Stub for implementation of the `@[norm_cast]` attribute.

This file is currently just a stub that creates a no-operation `@[norm_cast]` attribute.
Without this, all declarations in the mathport output for mathlib3 that use `@[norm_cast]` fail.
With the no-operation attribute, the declarations can succeed,
but of course the `norm_cast` tactic itself will not work.

Later we will need to port the implementation from mathlib3.

-/


open Lean Meta

namespace Lean.Parser.Attr

syntax (name := normCast) "norm_cast" (ppSpace (&"elim" <|> &"move" <|> &"squash"))? : attr

end Lean.Parser.Attr

namespace Tactic.NormCast

initialize pushCastExt : SimpExtension ←
  registerSimpAttr `push_cast (extName := `Tactic.NormCast.pushCastExt) $
    "The `push_cast` simp attribute uses `norm_cast` lemmas " ++
    "to move casts toward the leaf nodes of the expression."

/--  The `norm_cast` attribute stores three simp sets. -/
structure NormCastExtension where
  up : SimpExtension
  down : SimpExtension
  squash : SimpExtension
  deriving Inhabited

initialize normCastExt : NormCastExtension ← pure {
  up := ← mkSimpExt `Tactic.NormCast.normCastExt.up
  down := ← mkSimpExt `Tactic.NormCast.normCastExt.down
  squash := ← mkSimpExt `Tactic.NormCast.normCastExt.squash
}

/-- `addElim decl` adds `decl` as an `elim` lemma to the cache. -/
def addElim (decl : Name)
  (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit :=
  addSimpTheorem normCastExt.up decl false (inv := false) kind prio

/-- `addMove decl` adds `decl` as a `move` lemma to the cache. -/
def addMove (decl : Name)
  (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  addSimpTheorem pushCastExt decl false (inv := false) kind prio
  addSimpTheorem normCastExt.up decl false (inv := true) kind prio
  addSimpTheorem normCastExt.down decl false (inv := false) kind prio

/-- `addSquash decl` adds `decl` as a `squash` lemma to the cache. -/
def addSquash (decl : Name)
  (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  addSimpTheorem pushCastExt decl false (inv := false) kind prio
  addSimpTheorem normCastExt.squash decl false (inv := false) kind prio
  addSimpTheorem normCastExt.down decl false (inv := false) kind prio

/-- `addInfer decl` infers the label of `decl` and adds it to the cache.

* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes
-/
def addInfer (decl : Name)
  (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  let ty := (← getConstInfo decl).type
  -- TODO: not just elim
  addElim decl kind prio

-- FIXME: put this in a different file, because we can't access attributes in
-- the file they're defined in.
-- run_cmd Elab.Command.liftCoreM $ MetaM.run' do
--   addElim ``ne_eq

initialize registerBuiltinAttribute {
  name := `normCast
  descr := "attribute for norm_cast"
  add := fun decl stx kind => MetaM.run' <|
    match stx with
    | `(attr| norm_cast elim) => addElim decl kind
    | `(attr| norm_cast move) => addMove decl kind
    | `(attr| norm_cast squash) => addSquash decl kind
    | `(attr| norm_cast) => addInfer decl kind
    | _ => unreachable!
}
