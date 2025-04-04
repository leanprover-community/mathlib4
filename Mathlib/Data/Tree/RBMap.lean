/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki
-/
import Batteries.Data.RBMap.Basic
import Mathlib.Data.Tree.Basic

/-!
# Binary tree and RBMaps

In this file we define `Tree.ofRBNode`.
This definition was moved from the main file to avoid a dependency on `RBMap`.

## TODO

Implement a `Traversable` instance for `Tree`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/

namespace Tree

universe u

variable {α : Type u}

open Batteries (RBNode)

/-- Makes a `Tree α` out of a red-black tree. -/
@[deprecated "Deprecated without replacement." (since := "2025-04-02")]
def ofRBNode : RBNode α → Tree α
  | RBNode.nil => nil
  | RBNode.node _color l key r => node key (ofRBNode l) (ofRBNode r)

end Tree
