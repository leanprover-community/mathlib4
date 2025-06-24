/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Grassmannians

## Main definitions

- `Grassmannian`: `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined to be
  the set of submodules of `M` whose quotient is locally free of rank `k`. Note that this indexing
  is the opposite of some indexing in literature, where this rank would be `n - k` instead, where
  `M = R ^ n`.

## Implementation notes

Convention for a finite dimensional vector space `V` over a field `F`, is that `G(k, V; F)` should
parametrise `k`-dimensional subspaces of `V`, but this only works for finite dimensional spaces, and
over fields. This is why Grothendieck in EGA V.11 (unpublished) and
[Grothendieck, EGA I.9.7.3][grothendieck-1971] (Springer edition only)
defines the Grassmannians to parametrise locally free rank-`k` quotients instead.

Then the conventional `k`-dimensional subspaces of `V` with dimension `n`, can be recovered by
`G(n-k, V; F)`.

## TODO
- Define the functor `Grassmannian.functor R M k` that sends an `R`-algebra `A` to the set
  `G(k, A ⊗[R] M; A)`.
- Define `chart x` indexed by `x : Fin k → M` as a subtype consisting of those
  `N ∈ G(k, A ⊗[R] M; A)` such that the composition `R^k → M → M⧸N` is an isomorphism.
- Define `chartFunctor x` to turn `chart x` into a subfunctor of `Grassmannian.functor`. This will
  correspond to an affine open chart in the Grassmannian.
- Grassmannians for schemes and quasi-coherent sheaf of modules.
- Representability of `Grassmannian.functor R M k`.
-/

universe u v w

open Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)

/-- `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined to be the set of
submodules of `M` whose quotient is locally free of rank `k`. Note that this indexing is the
opposite of some indexing in literature, where this rank would be `n - k` instead, where
`M = R ^ n`. -/
@[stacks 089R] structure Grassmannian extends Submodule R M where
  finite_quotient : Module.Finite R (M ⧸ toSubmodule)
  projective_quotient : Projective R (M ⧸ toSubmodule)
  rankAtStalk_eq : ∀ p, rankAtStalk (R := R) (M ⧸ toSubmodule) p = k

attribute [instance] Grassmannian.finite_quotient Grassmannian.projective_quotient

namespace Grassmannian

@[inherit_doc] scoped notation "G("k", "M"; "R")" => Grassmannian R M k

variable {R M k}

instance : CoeOut G(k, M; R) (Submodule R M) :=
  ⟨toSubmodule⟩

@[ext] lemma ext {N₁ N₂ : G(k, M; R)} (h : (N₁ : Submodule R M) = N₂) : N₁ = N₂ := by
  cases N₁; cases N₂; congr 1

end Grassmannian
