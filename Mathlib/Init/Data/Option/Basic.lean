/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Logic
import Std.Data.Option.Basic

/-!
# Basic definitions on `Option`.

Ported from Lean 3's `init.data.option.basic`.
-/

open Decidable

universe u v

namespace Option

def getOrElse {α : Type u} : Option α → α → α
  | some x, _ => x
  | none, e => e

def rhoare {α : Type u} : Bool → α → Option α
  | .true,  _ => none
  | .false, a => some a

def lhoare {α : Type u} : α → Option α → α
  | a, none => a
  | _, some b => b

instance : Monad Option where
  pure := @some
  bind := @Option.bind
  map := @Option.map

protected def orelse {α : Type u} : Option α → Option α → Option α
  | some a, _ => some a
  | none, some a => some a
  | none, none => none

instance : Alternative Option where
  failure := @none
  orElse := @Option.orElse

end Option

instance (α : Type u) : Inhabited (Option α) :=
  ⟨none⟩

instance {α : Type u} [d : DecidableEq α] : DecidableEq (Option α)
  | none, none => isTrue rfl
  | none, some _ => isFalse fun h => Option.noConfusion h
  | some _, none => isFalse fun h => Option.noConfusion h
  | some v₁, some v₂ =>
    match d v₁ v₂ with
    | isTrue e => isTrue (congrArg (@some α) e)
    | isFalse n => isFalse fun h => Option.noConfusion h fun e => absurd e n
