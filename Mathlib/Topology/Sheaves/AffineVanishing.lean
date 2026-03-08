/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib
public import Mathlib.Topology.Sheaves.Restrict

@[expose] public section

universe u

open CategoryTheory

namespace TopCat.Sheaf

#check restrict

end TopCat.Sheaf


namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]

def p : ℕ → Prop := fun n => ∀ {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent], Subsingleton (H F.sheaf (n + 1))

instance (n : ℕ) : Subsingleton (H F.sheaf (n + 1)) := by
  revert F X
  refine Nat.case_strong_induction_on (p := p) n ?_ ?_
  · intro X F _
    sorry
  intro n hn X F _

  sorry

end AlgebraicGeometry.Scheme.Modules
