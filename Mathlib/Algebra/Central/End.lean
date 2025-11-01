/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Central.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!

# `Module.End K V` is a central algebra

-/

open Module

variable {K V : Type*} [Semifield K] [AddCommMonoid V] [Module K V] [Free K V]

/-- The center of endomorphisms on a vector space is trivial,
in other words, it is a central algebra. -/
instance Algebra.IsCentral.end : IsCentral K (End K V) where
  out T hT := by
    have h' (f : V →ₗ[K] K) (y v : V) : f (T v) • y = f v • T y := by
      simpa using congr($(Subalgebra.mem_center_iff.mp hT <| f.smulRight y) v)
    nontriviality V
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨f, hf⟩ := Free.exists_linearMap_apply_eq_one_of_ne_zero K hx
    exact ⟨f (T x), LinearMap.ext fun _ => by simp [h', hf]⟩
