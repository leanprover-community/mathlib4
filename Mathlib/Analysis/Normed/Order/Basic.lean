/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Ordered normed spaces

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/

@[expose] public section


open Filter Set

open Topology

variable {α : Type*}
