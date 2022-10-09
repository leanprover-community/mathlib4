/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.RBMap

/-!
# `RBSet α` is implemented as `RBMap α Unit`

This is a minimal-effort implementation until it is done properly in `Std`.
-/

namespace Std

/--
An `RBMap`, implemented as `RBMap α := RBMap α Unit`.
-/
def RBSet (α : Type _) (cmp : α → α → Ordering) := RBMap α Unit cmp

namespace RBSet

variable {α : Type _} {cmp : α → α → Ordering}

def empty : RBSet α cmp := RBMap.empty

def foldl (self : RBSet α cmp) (f : β → α → β) (b : β) : β :=
  RBMap.foldl (fun b a _ => f b a) b self

/-- Construct a `RBSet` from a `List`, ignoring duplicates. -/
def ofList (L : List α) : RBSet α cmp :=
  RBMap.ofList (L.map (⟨·, ()⟩)) cmp

def insert (self : RBSet α cmp) (a : α) : RBSet α cmp := RBMap.insert self a ()

def toList (self : RBSet α comp) : List α := RBMap.toList self |>.map (·.1)

/-- Combine the elements of two `RBSet`s. -/
def union (f g : RBSet α cmp) : RBSet α cmp :=
  f.foldl (·.insert ·) g
