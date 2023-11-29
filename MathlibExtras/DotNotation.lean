/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller
-/
import Mathlib.Algebra.BigOperators.Multiset.Basic

@[app_unexpander List.take]
def List.take.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `take) $f)
  | _ => throw ()

@[app_unexpander List.drop]
def List.drop.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `drop) $f)
  | _ => throw ()

@[app_unexpander List.takeWhile]
def List.takeWhile.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `takeWhile) $f)
  | _ => throw ()

@[app_unexpander List.dropWhile]
def List.dropWhile.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `dropWhile) $f)
  | _ => throw ()

@[app_unexpander List.map]
def List.map.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `map) $f)
  | _ => throw ()

@[app_unexpander Multiset.map]
def Multiset.map.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `map) $f)
  | _ => throw ()

attribute [pp_dot] List.get List.sum Multiset.sum Sigma.fst Sigma.snd
