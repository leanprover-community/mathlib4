/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Stably free modules

## Main definition
* `IsStablyFree`: A module `M` over a commutative ring `R` is called stably free if there exists a
  finite free module `N` over `R` such that `M ⊕ N` is free.
-/

@[expose] public section

universe u

/-- A module `M` over a commutative ring `R` is called stably free if there exists a
  finite free module `N` over `R` such that `M ⊕ N` is free. -/
@[stacks 0BC3 "(2)"]
def IsStablyFree (R : Type u) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N)
    (_ : Module.Finite R N) (_ : Module.Free R N), Module.Free R (M × N)

variable {R : Type u} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem IsStablyFree.equiv (e : M ≃ₗ[R] N) (h : IsStablyFree R M) : IsStablyFree R N := by
  obtain ⟨P, hPc, hPm, hPfin, hPfree, _⟩ := h
  exact ⟨P, hPc, hPm, hPfin, hPfree, Module.Free.of_equiv ((e.prodCongr (LinearEquiv.refl R P)))⟩

theorem IsStablyFree.equiv_iff (e : M ≃ₗ[R] N) : IsStablyFree R M ↔ IsStablyFree R N :=
  ⟨fun h ↦ h.equiv e, fun h ↦ h.equiv e.symm⟩

variable (R M N) in
theorem IsStablyFree.of_free_prod [Module.Finite R N] [Module.Free R N] [Module.Free R (M × N)] :
    IsStablyFree R M := by
  have : Small.{u} N := Module.Finite.small.{u} R N
  have eN : N ≃ₗ[R] Shrink.{u} N := (Shrink.linearEquiv R N).symm
  exact ⟨Shrink.{u} N, inferInstance, inferInstance, Module.Finite.equiv eN,
    Module.Free.of_equiv eN, Module.Free.of_equiv ((LinearEquiv.refl R M).prodCongr eN)⟩

theorem IsStablyFree.projective (h : IsStablyFree R M) : Module.Projective R M := by
  obtain ⟨N, _, _, _, _, _⟩ := h
  exact Module.Projective.of_split (LinearMap.inl R M N) (LinearMap.fst R M N)
    (LinearMap.ext fun _ ↦ rfl)
