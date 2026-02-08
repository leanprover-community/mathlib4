/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GSimp.Types

/-!
# HA
-/

public meta section

namespace Mathlib.Tactic.GSimp

def rewritePre (rflOnly := false) : GSimproc := fun e => do
  for thms in (← getContext).simpTheorems do
    if let some r ← rewrite? e thms.pre thms.erased (tag := "pre") (rflOnly := rflOnly) then
      return .visit r
  return .continue

def rewritePost (rflOnly := false) : GSimproc := fun e => do
  for thms in (← getContext).simpTheorems do
    if let some r ← rewrite? e thms.post thms.erased (tag := "post") (rflOnly := rflOnly) then
      return .visit r
  return .continue
