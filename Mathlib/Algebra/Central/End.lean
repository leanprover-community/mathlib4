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

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V] [Free K V]

/-- The center of endomorphisms on a vector space is trivial,
in other words, it is a central algebra. -/
instance Algebra.IsCentral.end : IsCentral K (End K V) where
  out T hT := by
    have h' (f : Dual K V) (y v : V) : f (T v) • y = f v • T y := by
      simpa using congr($(Subalgebra.mem_center_iff.mp hT <| f.smulRight y) v)
    nontriviality V
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    let b := chooseBasis K V
    have ⟨i, hi⟩ := not_forall.mp fun h ↦ b.repr.map_ne_zero_iff.mpr hx <| Finsupp.ext h
    exact ⟨b.coord i (T (b i)), LinearMap.ext fun y ↦ by simpa using h' (b.coord i) y (b i)⟩
