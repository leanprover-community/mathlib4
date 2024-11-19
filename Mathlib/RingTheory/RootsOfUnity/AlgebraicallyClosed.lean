/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Instances for HasEnoughRootsOfUnity

We provide an instance for `HasEnoughRootsOfUnity F n` when `F` is an algebraically closed field
and `n` is not divisible by the characteristic. In particular, when `F` has characterstic zero,
this hold for all `n ≠ 0`.

### TODO

Add an instance `HasEnoughRootsOfUnity Circle n` for all `n ≠ 0`.
This is probably easiest via setting up an isomorphism
`rootsOfUnity n Circle ≃* rootsOfUnity n ℂ`.
-/

namespace IsAlgClosed

/-- An algebraically closed field `F` satisfies `HasEnoughRootsOfUnity F n` for all `n`
that are not divisible by the characteristic of `F`. -/
instance hasEnoughRootsOfUnity (F : Type*) [Field F] [IsAlgClosed F] (n : ℕ) [i : NeZero (n : F)] :
    HasEnoughRootsOfUnity F n where
  prim := by
    have : NeZero n := .of_neZero_natCast F
    have := isCyclotomicExtension {⟨n, NeZero.pos n⟩} F fun _ h ↦ Set.mem_singleton_iff.mp h ▸ i
    exact IsCyclotomicExtension.exists_prim_root (S := {(⟨n, NeZero.pos n⟩ : ℕ+)}) F rfl
  cyc :=
    have : NeZero n := .of_neZero_natCast F
    rootsOfUnity.isCyclic F n

end IsAlgClosed
