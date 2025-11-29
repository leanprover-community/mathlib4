/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# `Module.End R M` is a central algebra
-/

open Module Free

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Free R M]

/-- The center of endomorphisms on a free module is trivial,
in other words, it is a central algebra. -/
public instance Algebra.IsCentral.end : IsCentral R (End R M) where
  out T hT := by
    nontriviality M
    let b := chooseBasis R M
    let i := b.index_nonempty.some
    refine ⟨b.coord i (T (b i)), LinearMap.ext fun y ↦ ?_⟩
    simpa using congr($(Subalgebra.mem_center_iff.mp hT <| (b.coord i).smulRight y) (b i))
