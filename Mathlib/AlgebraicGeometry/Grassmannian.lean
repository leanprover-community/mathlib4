/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Grassmannians

## Main definitions

- `AlgebraicGeometry.Grassmannian.Module`: `𝔾(M; R, k)` is the `k`ᵗʰ Grassmannian of the `R`-module
  `M`. It is defined to be the set of submodules of `M` whose quotient is locally free of rank `k`.
  Note that this indexing is the opposite of some indexing in literature, where this rank would be
  `n-k` instead, where `M=R^n`.
-/

/-
TODO:
- Grassmannians for schemes and quasi-coherent sheaf of modules.
- Representability.
-/

universe u v

namespace AlgebraicGeometry

open Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)

/-- `𝔾(M; R, k)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined to be the set of
submodules of `M` whose quotient is locally free of rank `k`. Note that this indexing is the
opposite of some indexing in literature, where this rank would be `n-k` instead, where `M=R^n`. -/
def Grassmannian : Type v :=
{ N : Submodule R M // Module.Finite R (_ ⧸ N) ∧ Projective R (_ ⧸ N) ∧
  ∀ p, rankAtStalk (R:=R) (_ ⧸ N) p = k }

namespace Grassmannian

@[inherit_doc] scoped notation "𝔾("M"; "R", "k")" => Grassmannian R M k

variable {R M k}

/-- The underlying submodule of an element of `𝔾(M; R, k)`. This cannot be a coercion because `k`
cannot be inferred. -/
def val (N : 𝔾(M; R, k)) : Submodule R M :=
  Subtype.val N

variable (N : 𝔾(M; R, k))

instance : Module.Finite R (_ ⧸ N.val) :=
  (Subtype.prop N).1

instance : Module.Projective R (_ ⧸ N.val) :=
  (Subtype.prop N).2.1

lemma rankAtStalk_eq (p : PrimeSpectrum R) : rankAtStalk (_ ⧸ N.val) p = k :=
  (Subtype.prop N).2.2 p

/-- Given a surjection `M ↠ R^k`, return an element of `𝔾(M; R, k)`. -/
def ofSurjection [Nontrivial R] (f : M →ₗ[R] (Fin k → R)) (hf : Function.Surjective f) :
    𝔾(M; R, k) :=
  ⟨LinearMap.ker f, Module.Finite.equiv (f.quotKerEquivOfSurjective hf).symm,
    Projective.of_equiv (f.quotKerEquivOfSurjective hf).symm,
    fun p ↦ by rw [rankAtStalk_eq_of_equiv (f.quotKerEquivOfSurjective hf),
      rankAtStalk_eq_finrank_of_free, finrank_fin_fun]; rfl⟩

end Grassmannian

end AlgebraicGeometry
