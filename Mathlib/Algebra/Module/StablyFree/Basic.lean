/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Stably free modules

## Main definitions
* `IsStablyFree`: A module `M` over a commutative ring `R` is called stably free if there exists a
  finite free module `N` over `R` such that `M ⊕ N` is free.
-/

@[expose] public section

universe u v

/-- A module `M` over a commutative ring `R` is called stably free if there exists a
  finite free module `N` over `R` such that `M ⊕ N` is free. -/
def IsStablyFree (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N)
    (_ : Module.Finite R N) (_ : Module.Free R N), Module.Free R (M × N)

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem IsStablyFree.projective (h : IsStablyFree R M) : Module.Projective R M := by
  obtain ⟨N, _, _, _, _, _⟩ := h
  exact Module.Projective.of_split (LinearMap.inl R M N) (LinearMap.fst R M N)
    (LinearMap.ext fun _ ↦ rfl)
