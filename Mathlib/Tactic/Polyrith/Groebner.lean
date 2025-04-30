/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Tactic.TypeStar

namespace Tactic.Polyrith.Groebner

structure Polynomial (𝕜 m: Type*) (cmp : m → m → Ordering) where
  ofList ::
    toList : List (𝕜 × m)

end Tactic.Polyrith.Groebner
