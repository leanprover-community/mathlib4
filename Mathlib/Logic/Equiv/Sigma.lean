/-
Copyright (c) 2026 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
module

public import Mathlib.Data.Set.Sigma

/-!
# Equivalences and sigma types
-/

@[expose] public section

namespace Equiv

namespace Set

/-- The indexed sum of sets is equivalent to the sigma-type of their coercions to types. -/
protected def sigma {α} {β : α → Type*} (s : Set α) (t : (i : α) → Set (β i)) :
    ↥(s.sigma t) ≃ Σ i : s, t i :=
  subtypeSigmaEquivSigma

end Set

end Equiv
