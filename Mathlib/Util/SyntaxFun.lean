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

Defines `syntaxFun` syntax along with functions
to expand them into `SyntaxFun` terms.
Provides `Lean.Quote` instances for these.
-/

namespace Mathlib.SyntaxFun
open Lean

/-- A "function" of some number of arguments.
Works purely syntactically and is completely ignorant of shadowing. -/
structure SyntaxFun (arity : Nat) where
  /-- The parameters. -/
  params : Array Ident
  /-- The function body. -/
  body : Term
  /-- That there are the correct number of parameters. -/
  params_size : params.size = arity := by rfl

/-- Replace all instances of `f.param` with the respective arguments. -/
def SyntaxFun.eval {arity} (f : SyntaxFun arity) (args : Array Term)
    (args_size : args.size = arity := by rfl) : Term :=
  Id.run <| f.body.replaceM fun t => do
    for h : i in [0:arity] do
      have : i < f.params.size := by rw [f.params_size]; exact h.2
      have : i < args.size := by rw [args_size]; exact h.2
      if t == f.params[i] then return args[i]
    return none

/-- Replace all instances of the parameters with the respective values. -/
def SyntaxFun.eval₁ (f : SyntaxFun 1) (v : Term) : Term :=
  Id.run <| f.body.replaceM fun t =>
    if t == f.params[0]! then return v
    else return none

/-- Replace all instances of the parameters with the respective values. -/
def SyntaxFun.eval₂ (f : SyntaxFun 2) (v₁ v₂ : Term) : Term :=
  Id.run <| f.body.replaceM fun t =>
    if t == f.params[0]! then return v₁
    else if t == f.params[1]! then return v₂
    else return none

/-- Replace all instances of the parameters with the respective values. -/
def SyntaxFun₃.eval₃ (f : SyntaxFun 3) (v₁ v₂ v₃ : Term) : Term :=
  Id.run <| f.body.replaceM fun t =>
    if t == f.params[0]! then return v₁
    else if t == f.params[1]! then return v₂
    else if t == f.params[2]! then return v₃
    else return none

/-- Run a transformation on the body of the function,
skipping the parameter. -/
def SyntaxFun.updateBody {m : Type → Type} [Monad m] {arity}
    (f : SyntaxFun arity) (r : Syntax → m (Option Syntax)) :
    m (SyntaxFun arity) := do
  return {f with body := ← f.body.replaceM fun t =>
                  if f.params.any (· == t) then return none
                  else r t}

/-- Syntax for a `SyntaxFun`. -/
syntax syntaxFun := (ident ppSpace)+ "=> " term

/-- Syntax for specifically a `SyntaxFun 1`. -/
syntax syntaxFun₁ := ident "=> " term

/-- Syntax for specifically a `SyntaxFun 2`. -/
syntax syntaxFun₂ := ident ppSpace ident "=> " term

/-- Recognize a `SyntaxFun`. -/
def expandSyntaxFun : TSyntax ``syntaxFun → Option ((arity : Nat) × SyntaxFun arity)
  | `(syntaxFun| $ps* => $body) => some ⟨ps.size, .mk ps body⟩
  | _ => none

/-- Recognize a `SyntaxFun` with a given arity. -/
def expandSyntaxFunWithArity (arity : Nat) (s : TSyntax ``syntaxFun) : Option (SyntaxFun arity) :=
  match expandSyntaxFun s with
  | some ⟨arity', params, body, pf⟩ =>
    if h : arity' = arity then
      some ⟨params, body, by rw [pf, h]⟩
    else
      none
  | _ => none

/-- Recognize a `SyntaxFun 1`. -/
def expandSyntaxFun₁ : TSyntax ``syntaxFun₁ → Option (SyntaxFun 1)
  | `(syntaxFun₁| $p₁ => $body) => some <| .mk #[p₁] body
  | _ => none

/-- Recognize a `SyntaxFun`. -/
def expandSyntaxFun₂ : TSyntax ``syntaxFun₂ → Option (SyntaxFun 2)
  | `(syntaxFun₂| $p₁ $p₂ => $body) => some <| .mk #[p₁, p₂] body
  | _ => none

instance (arity : Nat) : Quote (SyntaxFun arity) ``syntaxFun where
  quote f := Unhygienic.run `(syntaxFun| $f.params* => $f.body)

instance : Quote (SyntaxFun 1) ``syntaxFun₁ where
  quote f := Unhygienic.run `(syntaxFun₁| $(f.params[0]!) => $f.body)

instance : Quote (SyntaxFun 2) ``syntaxFun₂ where
  quote f := Unhygienic.run `(syntaxFun₂| $(f.params[0]!) $(f.params[1]!) => $f.body)
