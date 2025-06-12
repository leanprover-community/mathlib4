/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth, Jovan Gerbscheid
-/
import Mathlib.Tactic.GRewrite.Elab
import Mathlib.Tactic.GCongr

/-!

# The generalized rewriting tactic

The `grw`/`grewrite` tactic is a generalization of the `rewrite` tactic that works with relations
other than equality.

This file also imports the `positivity` tactic so that it can be used in `grewrite`.

-/
