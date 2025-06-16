/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
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

open CategoryTheory Limits TensorProduct

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

@[simp] lemma val_mk (N : Submodule R M) {h} : val (k:=k) ⟨N, h⟩ = N := rfl

@[ext] lemma ext {N₁ N₂ : 𝔾(M; R, k)} (h : N₁.val = N₂.val) : N₁ = N₂ :=
  Subtype.ext h

variable (N : 𝔾(M; R, k))

instance : Module.Finite R (_ ⧸ N.val) :=
  (Subtype.prop N).1

instance : Module.Projective R (_ ⧸ N.val) :=
  (Subtype.prop N).2.1

lemma rankAtStalk_eq (p : PrimeSpectrum R) : rankAtStalk (_ ⧸ N.val) p = k :=
  (Subtype.prop N).2.2 p

/-- Given a surjection `M ↠ R^k`, return an element of `𝔾(M; R, k)`. -/
def ofSurjection (f : M →ₗ[R] (Fin k → R)) (hf : Function.Surjective f) : 𝔾(M; R, k) :=
  ⟨LinearMap.ker f, Module.Finite.equiv (f.quotKerEquivOfSurjective hf).symm,
    Projective.of_equiv (f.quotKerEquivOfSurjective hf).symm,
    fun p ↦ haveI := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨p⟩
      by rw [rankAtStalk_eq_of_equiv (f.quotKerEquivOfSurjective hf),
        rankAtStalk_eq_finrank_of_free, finrank_fin_fun]; rfl⟩

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- If `M₁` and `M₂` are isomorphic, then `𝔾(M₁; R, k) ≃ 𝔾(M₂; R, k)`. -/
def ofLinearEquiv (e : M₁ ≃ₗ[R] M₂) : 𝔾(M₁; R, k) ≃ 𝔾(M₂; R, k) where
  toFun N := ⟨N.val.map e, Module.Finite.equiv (Submodule.Quotient.equiv N.val _ _ rfl),
    Projective.of_equiv (Submodule.Quotient.equiv N.val _ _ rfl),
    fun p ↦ by rw [← rankAtStalk_eq_of_equiv (Submodule.Quotient.equiv N.val _ _ rfl),
      rankAtStalk_eq]⟩
  invFun N := ⟨N.val.map e.symm, Module.Finite.equiv (Submodule.Quotient.equiv N.val _ _ rfl),
    Projective.of_equiv (Submodule.Quotient.equiv N.val _ _ rfl),
    fun p ↦ by rw [← rankAtStalk_eq_of_equiv (Submodule.Quotient.equiv N.val _ _ rfl),
      rankAtStalk_eq]⟩
  left_inv N := ext <| (Submodule.map_symm_eq_iff e).2 rfl
  right_inv N := ext <| (Submodule.map_symm_eq_iff e).1 rfl

/-- The affine chart corresponding to a chosen `f : R^k → M`, or equivalent, `k` elements in `M`.
It is the quotients `q : M ↠ V` such that the composition `f ∘ q : R^k → V` is an isomorphism. -/
def chart (f : (Fin k → R) →ₗ[R] M) : Set 𝔾(M; R, k) :=
  { N | Function.Bijective (N.val.mkQ ∘ f) }
-- TODO: `chart f` is affine
-- Proof sketch: we have equalizer diagram `chart f → Hom[R-Mod](M,R^k) ⇒ Hom[R-Mod](R^k,R^k)`

variable (A B : Type*) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B]

/-- Functoriality of Grassmannian with respect to the ring `R`. Note that given an `R`-algebra `A`,
we replace `M` with `A ⊗[R] M`. This is the resulting submodule, as an auxiliary definition.
Given submodule `N ≤ A ⊗[R] M`, the resulting `B`-submodule is morally
`B ⊗[R] N ≤ B ⊗[R] (A ⊗[R] M) ≃ B ⊗[R] M`. -/
noncomputable def mapSubmodule (p : 𝔾(A ⊗[R] M; A, k)) : Submodule B (B ⊗[R] M) :=
  LinearMap.range ((AlgebraTensorModule.cancelBaseChange R A B B M).toLinearMap ∘ₗ
    (p.val.subtype.baseChange B))

/-- The quotient by `mapSubmodule` is the tensor of the original quotient. -/
def equiv (p : 𝔾(A ⊗[R] M; A, k)) : _ ⧸ mapSubmodule A B p ≃ₗ[B] B ⊗[R] (_ ⧸ p.val) :=
  _

/-- Functoriality of Grassmannian with respect to the ring `R`. Note that given an `R`-algebra `A`,
we replace `M` with `A ⊗[R] M`. -/
def map (p : 𝔾(A ⊗[R] M; A, k)) : 𝔾(B ⊗[R] M; B, k) :=
  ⟨mapSubmodule A B p, _, _, _⟩
  -- ⟨.span B (p.val.map (LinearMap.rTensor M (IsScalarTower.toAlgHom R A B))), _, _, _⟩

#check LinearMap.range

def functor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (k : ℕ) : Under R ⥤ Type (max u v) where
  obj A := 𝔾(A ⊗[R] M; A, k)
  map f := _

end Grassmannian

namespace ProjectiveSpace

end ProjectiveSpace

end AlgebraicGeometry
