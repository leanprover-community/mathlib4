/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!

# `Module.End K V` is a central algebra

-/

@[expose] public section

open Module Free

variable {R V : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Free R M]

/-- The center of endomorphisms on a vector space is trivial,
in other words, it is a central algebra. -/
instance Algebra.IsCentral.end : IsCentral R (End R M) where
  out T hT := by
    have h' (f : M →ₗ[R] R) (y v : M) : f (T v) • y = f v • T y := by
      simpa using congr($(Subalgebra.mem_center_iff.mp hT <| f.smulRight y) v)
    nontriviality M
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    let b := chooseBasis R M
    have ⟨i, hi⟩ := not_forall.mp fun h ↦ b.repr.map_ne_zero_iff.mpr hx <| Finsupp.ext h
    exact ⟨b.coord i (T (b i)), LinearMap.ext fun y ↦ by simpa using h' (b.coord i) y (b i)⟩
