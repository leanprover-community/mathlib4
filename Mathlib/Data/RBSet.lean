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
An red-black tree backed set, implemented as `RBSet α := RBMap α Unit`.
It is parameterised by the ordering function for elements.
-/
def RBSet (α : Type _) (cmp : α → α → Ordering) := RBMap α Unit cmp

namespace RBSet

variable {α : Type _} {cmp : α → α → Ordering}

/-- Construct an empty red-black set. -/
def empty : RBSet α cmp := RBMap.empty

/-- Fold a function over a red-black set. -/
def foldl (self : RBSet α cmp) (f : β → α → β) (b : β) : β :=
  RBMap.foldl (fun b a _ => f b a) b self

/-- Construct a `RBSet` from a `List`, ignoring duplicates. -/
def ofList (L : List α) : RBSet α cmp :=
  RBMap.ofList (L.map (⟨·, ()⟩)) cmp

/-- Insert an element into a red-black set. -/
def insert (self : RBSet α cmp) (a : α) : RBSet α cmp := RBMap.insert self a ()

/-- Convert a red-black set to a list, with the elements appearing in order parameterising
the red-black set. -/
def toList (self : RBSet α comp) : List α := RBMap.toList self |>.map (·.1)

/-- Combine the elements of two `RBSet`s. -/
def union (f g : RBSet α cmp) : RBSet α cmp :=
  f.foldl (·.insert ·) g
