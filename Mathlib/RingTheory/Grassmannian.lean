/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Grassmannians

## Main definitions

- `Grassmannian`: `G(M; R, k)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined to be
  the set of submodules of `M` whose quotient is locally free of rank `k`. Note that this indexing
  is the opposite of some indexing in literature, where this rank would be `n - k` instead, where
  `M = R ^ n`.

## TODO
- Define the functor `Grassmannian.functor R M k` that sends an `R`-algebra `A` to the set
  `G(A ⊗[R] M; A, k)`.
- Define `chart x` indexed by `x : Fin k → M` as a subtype consisting of those
  `N ∈ G(A ⊗[R] M; A, k)` such that the composition `R^k → M → M⧸N` is an isomorphism.
- Define `chartFunctor x` to turn `chart x` into a subfunctor of `Grassmannian.functor`. This will
  correspond to an affine open chart in the Grassmannian.
- Grassmannians for schemes and quasi-coherent sheaf of modules.
- Representability of `Grassmannian.functor R M k`.
-/

universe u v w

open Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)

/-- `G(M; R, k)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined to be the set of
submodules of `M` whose quotient is locally free of rank `k`. Note that this indexing is the
opposite of some indexing in literature, where this rank would be `n-k` instead, where `M=R^n`. -/
def Grassmannian : Type v :=
  { N : Submodule R M // Module.Finite R (M ⧸ N) ∧ Projective R (M ⧸ N) ∧
    ∀ p, rankAtStalk (R := R) (M ⧸ N) p = k }

namespace Grassmannian

@[inherit_doc] scoped notation "G("M"; "R", "k")" => Grassmannian R M k

variable {R M k}

/-- The underlying submodule of an element of `G(M; R, k)`. This cannot be a coercion because `k`
cannot be inferred. -/
def val (N : G(M; R, k)) : Submodule R M :=
  Subtype.val N

@[simp] lemma val_mk (N : Submodule R M) {h} : val (k := k) ⟨N, h⟩ = N := rfl

@[ext] lemma ext {N₁ N₂ : G(M; R, k)} (h : N₁.val = N₂.val) : N₁ = N₂ := Subtype.ext h

variable (N : G(M; R, k))

instance : Module.Finite R (M ⧸ N.val) := (Subtype.prop N).1

instance : Module.Projective R (M ⧸ N.val) := (Subtype.prop N).2.1

lemma rankAtStalk_eq (p : PrimeSpectrum R) : rankAtStalk (M ⧸ N.val) p = k := (Subtype.prop N).2.2 p

end Grassmannian
