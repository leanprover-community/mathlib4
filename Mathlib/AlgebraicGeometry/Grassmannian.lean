/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Grassmannians

## Main definitions

- `AlgebraicGeometry.Grassmannian.Module`: `G(M; R, k)` is the `k`ᵗʰ Grassmannian of the `R`-module
  `M`. It is defined to be the set of submodules of `M` whose quotient is locally free of rank `k`.
  Note that this indexing is the opposite of some indexing in literature, where this rank would be
  `n-k` instead, where `M=R^n`.
-/

/-
TODO:
- Grassmannians for schemes and quasi-coherent sheaf of modules.
- Representability.
-/

universe u v w

section MOVE_THIS!!

open TensorProduct

-- Pending discussion: https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Refactor.20Submodule.2EbaseChange.20and.20LinearMap.2EbaseChange/with/524353687
noncomputable def Submodule.quotient_baseChange {R : Type u} {M : Type v} (A : Type w) [CommRing R]
    [Ring A] [Algebra R A] [AddCommGroup M] [Module R M] (S : Submodule R M) :
    -- (A ⊗[R] M ⧸ S.baseChange A) ≃ₗ[A] A ⊗[R] (M ⧸ S) :=
    (A ⊗[R] M ⧸ LinearMap.range (S.subtype.baseChange A)) ≃ₗ[A] A ⊗[R] (M ⧸ S) :=
  Function.Exact.linearEquivOfSurjective
    (g := S.mkQ.baseChange A)
    (by convert lTensor_exact A (LinearMap.exact_subtype_mkQ S) S.mkQ_surjective)
    (S.mkQ.lTensor_surjective A S.mkQ_surjective)

end MOVE_THIS!!

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

open Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)

/-- `G(M; R, k)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined to be the set of
submodules of `M` whose quotient is locally free of rank `k`. Note that this indexing is the
opposite of some indexing in literature, where this rank would be `n-k` instead, where `M=R^n`. -/
def Grassmannian : Type v :=
{ N : Submodule R M // Module.Finite R (_ ⧸ N) ∧ Projective R (_ ⧸ N) ∧
  ∀ p, rankAtStalk (R:=R) (_ ⧸ N) p = k }

namespace Grassmannian

@[inherit_doc] scoped notation "G("M"; "R", "k")" => Grassmannian R M k

variable {R M k}

/-- The underlying submodule of an element of `G(M; R, k)`. This cannot be a coercion because `k`
cannot be inferred. -/
def val (N : G(M; R, k)) : Submodule R M :=
  Subtype.val N

@[simp] lemma val_mk (N : Submodule R M) {h} : val (k:=k) ⟨N, h⟩ = N := rfl

@[ext] lemma ext {N₁ N₂ : G(M; R, k)} (h : N₁.val = N₂.val) : N₁ = N₂ :=
  Subtype.ext h

variable (N : G(M; R, k))

instance : Module.Finite R (_ ⧸ N.val) :=
  (Subtype.prop N).1

instance : Module.Projective R (_ ⧸ N.val) :=
  (Subtype.prop N).2.1

lemma rankAtStalk_eq (p : PrimeSpectrum R) : rankAtStalk (_ ⧸ N.val) p = k :=
  (Subtype.prop N).2.2 p

/-- Given a surjection `M ↠ R^k`, return an element of `G(M; R, k)`. -/
def ofSurjection (f : M →ₗ[R] (Fin k → R)) (hf : Function.Surjective f) : G(M; R, k) :=
  ⟨LinearMap.ker f, Module.Finite.equiv (f.quotKerEquivOfSurjective hf).symm,
    Projective.of_equiv (f.quotKerEquivOfSurjective hf).symm,
    fun p ↦ haveI := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨p⟩
      by rw [rankAtStalk_eq_of_equiv (f.quotKerEquivOfSurjective hf),
        rankAtStalk_eq_finrank_of_free, finrank_fin_fun]; rfl⟩

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]

/-- If `M₁` surjects to `M₂`, then there is an induced map `G(M₂; R, k) → G(M₁; R, k)` by
"pulling back" a submodule. -/
def ofLinearMap (f : M₁ →ₗ[R] M₂) (he : Function.Surjective f) (N : G(M₂; R, k)) : G(M₁; R, k) :=
  ⟨N.val.comap f, _, _, _⟩
-- TODO

/-- If `M₁` and `M₂` are isomorphic, then `G(M₁; R, k) ≃ G(M₂; R, k)`. -/
def ofLinearEquiv (e : M₁ ≃ₗ[R] M₂) : G(M₁; R, k) ≃ G(M₂; R, k) where
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

lemma ofLinearEquiv_val (e : M₁ ≃ₗ[R] M₂) (N : G(M₁; R, k)) :
    (ofLinearEquiv e N).val = N.val.map e :=
  rfl

/-- The quotients of `ofLinearEquiv` are isomorphic. -/
def ofLinearEquivEquiv (e : M₁ ≃ₗ[R] M₂) (N : G(M₁; R, k)) :
    (M₂ ⧸ (N.ofLinearEquiv e).val) ≃ₗ[R] M₁ ⧸ N.val :=
  (Submodule.Quotient.equiv _ _ _ rfl).symm

/-- The affine chart corresponding to a chosen `f : R^k → M`, or equivalent, `k` elements in `M`.
It is the quotients `q : M ↠ V` such that the composition `f ∘ q : R^k → V` is an isomorphism. -/
def chart (f : (Fin k → R) →ₗ[R] M) : Set G(M; R, k) :=
  { N | Function.Bijective (N.val.mkQ ∘ f) }
-- TODO: `chart f` is affine
-- Proof sketch: we have equalizer diagram `chart f → Hom[R-Mod](M,R^k) ⇒ Hom[R-Mod](R^k,R^k)`

variable (A : Type*) [CommRing A] [Algebra R A]

/- /-- Base change to an `R`-algebra `A`, where `M` is replaced with `A ⊗[R] M`. This is the
resulting submodule, as an auxiliary definition. -/
noncomputable def baseChangeSubmodule (N : G(M; R, k)) : Submodule A (A ⊗[R] M) :=
  LinearMap.range (N.val.subtype.baseChange A)

noncomputable def baseChangeSubmoduleEquiv (N : G(M; R, k)) :
    (_ ⧸ baseChangeSubmodule A N) ≃ₗ[A] A ⊗[R] (_ ⧸ N.val) :=
  have := (tensorQuotientEquiv A N.val).symm; by convert this
-- TODO -/

/-- Base change to an `R`-algebra `A`, where `M` is replaced with `A ⊗[R] M`. -/
noncomputable def baseChange (N : G(M; R, k)) : G(A ⊗[R] M; A, k) :=
  ⟨LinearMap.range (N.val.subtype.baseChange A),
    Module.Finite.equiv (N.val.quotient_baseChange A).symm,
    Projective.of_equiv (N.val.quotient_baseChange A).symm,
    fun _ ↦ by rw [rankAtStalk_eq_of_equiv (N.val.quotient_baseChange A),
      rankAtStalk_baseChange, rankAtStalk_eq]⟩

lemma baseChange_val (N : G(M; R, k)) :
    (baseChange A N).val = LinearMap.range (N.val.subtype.baseChange A) :=
  rfl

/- /-- Functoriality of Grassmannian with respect to the ring `R`. Note that given an `R`-algebra `A`,
we replace `M` with `A ⊗[R] M`. This is the resulting submodule, as an auxiliary definition.
Given submodule `N ≤ A ⊗[R] M`, the resulting `B`-submodule is morally
`B ⊗[R] N ≤ B ⊗[R] (A ⊗[R] M) ≃ B ⊗[R] M`. -/
noncomputable def mapSubmodule (N : G(A ⊗[R] M; A, k)) : Submodule B (B ⊗[R] M) :=
  LinearMap.range ((AlgebraTensorModule.cancelBaseChange R A B B M).toLinearMap ∘ₗ
    (p.val.subtype.baseChange B))

/-- The quotient by `mapSubmodule` is the tensor of the original quotient. -/
def equiv (N : G(A ⊗[R] M; A, k)) : (_ ⧸ mapSubmodule A B p) ≃ₗ[B] B ⊗[R] (_ ⧸ p.val) :=
  _ -/

/- /-- Functoriality of Grassmannian with respect to the ring `R`. Note that given an `R`-algebra `A`,
we replace `M` with `A ⊗[R] M`. -/
noncomputable def map (N : G(A ⊗[R] M; A, k)) : G(B ⊗[R] M; B, k) :=
  ofLinearEquiv (AlgebraTensorModule.cancelBaseChange R A B B M) (baseChange B p) -/

variable {A} {B : Type*} [CommRing B] [Algebra R B]

/-- Functoriality of Grassmannian in the category of `R`-algebras. Note that given an `R`-algebra
`A`, we replace `M` with `A ⊗[R] M`. The map `f : A →ₐ[R] B` should technically provide an instance
`[Algebra A B]`, but this might cause problems later down the line, so we do not require this
instance in the type signature of the function. Instead, given any instance `[Algebra A B]`, we
later prove that the map is equal to the one induced by `IsScalarTower.toAlgHom R A B : A →ₐ[R] B`.
-/
noncomputable def map (f : A →ₐ[R] B) (N : G(A ⊗[R] M; A, k)) : G(B ⊗[R] M; B, k) :=
  letI := f.toAlgebra;
  ofLinearEquiv (AlgebraTensorModule.cancelBaseChange R A B B M) (baseChange B N)

lemma val_map (f : A →ₐ[R] B) (N : G(A ⊗[R] M; A, k)) :
    (map f N).val = Submodule.span B ((N.val.restrictScalars R).map (f.toLinearMap.rTensor M)) := by
  letI := f.toAlgebra;
  rw [map, ofLinearEquiv_val, baseChange_val]
  refine (LinearMap.range_comp ..).symm.trans (le_antisymm (LinearMap.range_le_iff_comap.2 ?_)
    (Submodule.span_le.2 (show Submodule.map _ _ ≤ Submodule.restrictScalars _ from Submodule.map_le_iff_le_comap.2 ?_)))

#check Submodule.restrictScalars

lemma map_eq [Algebra A B] [IsScalarTower R A B] (N : G(A ⊗[R] M; A, k)) :
    map (IsScalarTower.toAlgHom R A B) p = ofLinearEquiv
      (AlgebraTensorModule.cancelBaseChange R A B B M) (baseChange B p) := by
  have h₁ : (IsScalarTower.toAlgHom R A B).toAlgebra = ‹Algebra A B› :=
    Algebra.algebra_ext _ _ (fun r ↦ rfl)
  unfold map
  conv => enter [1]

def functor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (k : ℕ) : Under R ⥤ Type (max u v) where
  obj A := G(A ⊗[R] M; A, k)
  map {A B} f := --letI := RingHom.toAlgebra (RingHomClass.toRingHom <| CommRingCat.toAlgHom f);
    map A B
#check RingHom.toAlgebra

end Grassmannian

namespace ProjectiveSpace

end ProjectiveSpace

end AlgebraicGeometry
