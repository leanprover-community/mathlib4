/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Util.Syntax

/-! # Notation for "functions" based on syntax transformations

In the `notation3` command there are syntaxes such as `scoped(a => iSup a)`.
This file is to support `a => iSup a` and evaluations and transformations
of such functions.

Defines `syntaxFun₁` and `syntaxFun₂` syntaxes along with functions
to expand them into `SyntaxFun₁` and `SyntaxFun₂` terms.
Provides `Lean.Quote` instances for these.
-/

namespace Mathlib.SyntaxFun
open Lean

/-- A "function" of one argument. -/
structure SyntaxFun₁ where
  /-- The parameter. -/
  param : Ident
  /-- The function body. -/
  body : Term

/-- Replace all instances of `f.param` with `v`. -/
def SyntaxFun₁.eval (f : SyntaxFun₁) (v : Term) : Term :=
  Id.run <| f.body.replaceM fun t =>
    if t == f.param then return v
    else return none

/-- Run a transformation on the body of the function,
skipping the parameter. -/
def SyntaxFun₁.updateBody {m : Type → Type} [Monad m]
    (f : SyntaxFun₁) (r : Syntax → m (Option Syntax)) :
    m SyntaxFun₁ := do
  return {f with body := ← f.body.replaceM fun t =>
                  if t == f.param then return none
                  else r t}

/-- A "function" of two arguments. -/
structure SyntaxFun₂ where
  /-- The first parameter. -/
  param₁ : Ident
  /-- The second parameter. -/
  param₂ : Ident
  /-- The function body. -/
  body : Term

/-- Replace all instances of `f.param₁` and `f.param₂` with `v₁` and `v₂`, respectively. -/
def SyntaxFun₂.eval (f : SyntaxFun₂) (v₁ v₂ : Term) : Term :=
  Id.run <| f.body.replaceM fun t =>
    if t == f.param₁ then return v₁
    else if t == f.param₂ then return v₂
    else return none

/-- Run a transformation on the body of the function,
skipping the parameters. -/
def SyntaxFun₂.updateBody {m : Type → Type} [Monad m]
    (f : SyntaxFun₂) (r : Syntax → m (Option Syntax)) :
    m SyntaxFun₂ := do
  return {f with body := ← f.body.replaceM fun t =>
                  if t == f.param₁ || t == f.param₂ then return none
                  else r t}

/-- Syntax for a `SyntaxFun₁`. -/
syntax syntaxFun₁ := ident " => " term

/-- Syntax for a `SyntaxFun₂`. -/
syntax syntaxFun₂ := ident ppSpace ident " => " term

/-- Recognize a `SyntaxFun₁`. -/
def expandSyntaxFun₁ : TSyntax ``syntaxFun₁ → Option SyntaxFun₁
  | `(syntaxFun₁| $p => $body) => some ⟨p, body⟩
  | _ => none

/-- Recognize a `SyntaxFun₂`. -/
def expandSyntaxFun₂ : TSyntax ``syntaxFun₂ → Option SyntaxFun₂
  | `(syntaxFun₂| $p₁ $p₂ => $body) => some ⟨p₁, p₂, body⟩
  | _ => none

instance : Quote SyntaxFun₁ ``syntaxFun₁ where
  quote f := Unhygienic.run `(syntaxFun₁| $f.param => $f.body)

instance : Quote SyntaxFun₂ ``syntaxFun₂ where
  quote f := Unhygienic.run `(syntaxFun₂| $f.param₁ $f.param₂ => $f.body)
