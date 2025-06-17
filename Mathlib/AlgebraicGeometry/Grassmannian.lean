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

noncomputable def Submodule.quotient_baseChange {R : Type u} {M : Type v} (A : Type w) [CommRing R]
    [Ring A] [Algebra R A] [AddCommGroup M] [Module R M] (S : Submodule R M) :
    (A ⊗[R] M ⧸ S.baseChange A) ≃ₗ[A] A ⊗[R] (M ⧸ S) :=
  Function.Exact.linearEquivOfSurjective
    (g := S.mkQ.baseChange A)
    (by convert lTensor_exact A (LinearMap.exact_subtype_mkQ S) S.mkQ_surjective)
    (S.mkQ.lTensor_surjective A S.mkQ_surjective)

/-- The triangle of `R`-modules `A ⊗[R] M ⟶ B ⊗[A] (A ⊗[R] M) ⟶ B ⊗[R] M` commutes. -/
lemma AlgebraTensorModule.cancelBaseChange_comp_mk_one {R A B M : Type*}
    [CommSemiring R] [CommSemiring A] [Semiring B] [AddCommMonoid M] [Module R M]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] :
    (AlgebraTensorModule.cancelBaseChange R A B B M).toLinearMap.restrictScalars R ∘ₗ
        (TensorProduct.mk A B (A ⊗[R] M) 1).restrictScalars R =
      LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap :=
  ext <| LinearMap.ext₂ fun a m ↦ by simp [Algebra.algebraMap_eq_smul_one]

/-- The triangle of `R`-modules `A ⊗[R] M ⟶ B ⊗[A] (A ⊗[R] M) ⟶ B ⊗[R] M` commutes. -/
lemma AlgebraTensorModule.cancelBaseChange_comp_mk_one' {R A B M : Type*}
    [CommSemiring R] [CommSemiring A] [Semiring B] [AddCommMonoid M] [Module R M]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] :
    ((AlgebraTensorModule.cancelBaseChange R A B B M).toLinearMap.restrictScalars A ∘ₗ
        TensorProduct.mk A B (A ⊗[R] M) 1).restrictScalars R =
      LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap :=
  cancelBaseChange_comp_mk_one

/-- The triangle of `R`-modules `A ⊗[R] M ⟶ B ⊗[A] (A ⊗[R] M) ⟶ B ⊗[R] M` commutes. -/
lemma AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one {R A B M : Type*}
    [CommSemiring R] [CommSemiring A] [Semiring B] [AddCommMonoid M] [Module R M]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] :
    (AlgebraTensorModule.cancelBaseChange R A B B M) ∘ (TensorProduct.mk A B (A ⊗[R] M) 1) =
      LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap :=
  funext <| LinearMap.congr_fun cancelBaseChange_comp_mk_one

lemma LinearMap.restrictScalars_baseChange {R A M N : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (f.baseChange A).restrictScalars R = f.lTensor A :=
  rfl

@[simp] lemma LinearMap.quotKerEquivOfSurjective_apply {R M M₂ : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]
    (f : M →ₗ[R] M₂) (hf : Function.Surjective f) (x : M) :
    f.quotKerEquivOfSurjective hf (Submodule.Quotient.mk x) = f x :=
  rfl

lemma LinearEquiv.piRing_symm_apply_single {R M ι S : Type*} [Semiring R] [Fintype ι]
    [DecidableEq ι] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M] [SMulCommClass R S M]
    (f : ι → M) (i : ι) (r : R) :
    (LinearEquiv.piRing R M ι S).symm f (Pi.single i r) = r • f i := by
  rw [piRing_symm_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by intros; simp [*]),
    Pi.single_apply, if_pos rfl]

lemma LinearEquiv.piRing_symm_apply_single_one {R M ι S : Type*} [Semiring R] [Fintype ι]
    [DecidableEq ι] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M] [SMulCommClass R S M]
    (f : ι → M) (i : ι) :
    (LinearEquiv.piRing R M ι S).symm f (Pi.single i 1) = f i := by
  rw [piRing_symm_apply_single, one_smul]

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

/-- Copy of an element of the Grassmannian, with a new carrier equal to the old one. Useful to fix
definitional equalities. -/
def copy (N : G(M; R, k)) (N' : Set M) (h : N' = N.val) : G(M; R, k) :=
  ⟨N.val.copy N' h, let e := (N.val.quotEquivOfEq _ (SetLike.coe_set_eq.1 h.symm));
    ⟨Module.Finite.equiv e, Projective.of_equiv e, fun p ↦ by
      rw [← rankAtStalk_eq_of_equiv e, rankAtStalk_eq]⟩⟩

/-- Given an isomorphism `M⧸N ↠ R^k`, return an element of `G(M; R, k)`. -/
def ofEquiv (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (Fin k → R)) : G(M; R, k) :=
  ⟨N, Module.Finite.equiv e.symm, Projective.of_equiv e.symm, fun p ↦ by
    haveI := PrimeSpectrum.nontrivial p
    rw [rankAtStalk_eq_of_equiv e, rankAtStalk_eq_finrank_of_free, finrank_fin_fun]; rfl⟩

lemma ofEquiv_val (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (Fin k → R)) : (ofEquiv N e).val = N :=
  rfl

/-- Given a surjection `M ↠ R^k`, return an element of `G(M; R, k)`. -/
def ofSurjective (f : M →ₗ[R] (Fin k → R)) (hf : Function.Surjective f) : G(M; R, k) :=
  ofEquiv _ (f.quotKerEquivOfSurjective hf)

lemma ofSurjective_val (f : M →ₗ[R] (Fin k → R)) (hf : Function.Surjective f) :
    (ofSurjective f hf).val = LinearMap.ker f :=
  rfl

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]

/-- If `M₁` surjects to `M₂`, then there is an induced map `G(M₂; R, k) → G(M₁; R, k)` by
"pulling back" a submodule. -/
def ofLinearMap (f : M₁ →ₗ[R] M₂) (he : Function.Surjective f) (N : G(M₂; R, k)) : G(M₁; R, k) :=
  ⟨N.val.comap f, _, _, _⟩
-- TODO

/-- If `M₁` and `M₂` are isomorphic, then `G(M₁; R, k) ≃ G(M₂; R, k)`. -/
def ofLinearEquiv (e : M₁ ≃ₗ[R] M₂) : G(M₁; R, k) ≃ G(M₂; R, k) where
  toFun N := ⟨N.val.map e, let e' := Submodule.Quotient.equiv N.val _ _ rfl;
    ⟨Module.Finite.equiv e', Projective.of_equiv e', fun p ↦ by
      rw [← rankAtStalk_eq_of_equiv e', rankAtStalk_eq]⟩⟩
  invFun N := ⟨N.val.map e.symm, let e' := Submodule.Quotient.equiv N.val _ _ rfl;
    ⟨Module.Finite.equiv e', Projective.of_equiv e', fun p ↦ by
      rw [← rankAtStalk_eq_of_equiv e', rankAtStalk_eq]⟩⟩
  left_inv N := ext <| (Submodule.map_symm_eq_iff e).2 rfl
  right_inv N := ext <| (Submodule.map_symm_eq_iff e).1 rfl

lemma ofLinearEquiv_val (e : M₁ ≃ₗ[R] M₂) (N : G(M₁; R, k)) :
    (ofLinearEquiv e N).val = N.val.map e :=
  rfl

/-- The quotients of `ofLinearEquiv` are isomorphic. -/
def ofLinearEquivEquiv (e : M₁ ≃ₗ[R] M₂) (N : G(M₁; R, k)) :
    (M₂ ⧸ (N.ofLinearEquiv e).val) ≃ₗ[R] M₁ ⧸ N.val :=
  (Submodule.Quotient.equiv _ _ _ rfl).symm

variable (R) in
/-- The affine chart corresponding to a chosen `f : R^k → M`, or equivalently, `k` elements in `M`.
It is the quotients `q : M ↠ V` such that the composition `f ∘ q : R^k → V` is an isomorphism. -/
def chart (f : Fin k → M) : Set G(M; R, k) :=
  { N | Function.Bijective (N.val.mkQ ∘ (LinearEquiv.piRing R M (Fin k) R).symm f) }
-- TODO: `chart f` is affine
-- Proof sketch: we have equalizer diagram `chart f → Hom[R-Mod](M,R^k) ⇒ Hom[R-Mod](R^k,R^k)`

/-- An element `N ∈ chart R f` produces an isomorphism `M ⧸ N.val ≃ₗ[R] R^k`. -/
noncomputable def equivOfChart {f : Fin k → M} {N : G(M; R, k)} (hn : N ∈ chart R f) :
    (M ⧸ N.val) ≃ₗ[R] (Fin k → R) :=
  (LinearEquiv.ofBijective (N.val.mkQ ∘ₗ _) hn).symm

lemma ofEquiv_mem_chart {N : Submodule R M} (e : (M ⧸ N) ≃ₗ[R] (Fin k → R))
    (f : Fin k → M) (hf : ∀ i, e (Submodule.Quotient.mk (f i)) = Pi.single i 1) :
    ofEquiv N e ∈ chart R f := by
  rw [chart, Set.mem_setOf, ← LinearMap.coe_comp]
  convert e.symm.bijective using 1
  refine DFunLike.coe_fn_eq.2 (LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring <| Eq.symm <|
    e.symm_apply_eq.2 ?_)
  simp [-LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_symm_apply_single_one, hf]

lemma ofSurjective_mem_chart {q : M →ₗ[R] Fin k → R} (hq : Function.Surjective q)
    (f : Fin k → M) (hf : ∀ i, q (f i) = Pi.single i 1) :
    ofSurjective q hq ∈ chart R f :=
  ofEquiv_mem_chart _ _ hf

lemma exists_ofEquiv_mem_chart {N : Submodule R M} (e : (M ⧸ N) ≃ₗ[R] (Fin k → R)) :
    ∃ f, ofEquiv N e ∈ chart R f :=
  ⟨_, ofEquiv_mem_chart _ (fun i ↦ (e.symm (Pi.single i 1)).out) fun i ↦
    by simp [Submodule.Quotient.mk]⟩

lemma exists_ofSurjective_mem_chart {q : M →ₗ[R] Fin k → R} (hq : Function.Surjective q) :
    ∃ f, ofSurjective q hq ∈ chart R f :=
  exists_ofEquiv_mem_chart _

variable (A : Type*) [CommRing A] [Algebra R A]

/-- Base change to an `R`-algebra `A`, where `M` is replaced with `A ⊗[R] M`. -/
noncomputable def baseChange (N : G(M; R, k)) : G(A ⊗[R] M; A, k) :=
  ⟨N.val.baseChange A, let e := (N.val.quotient_baseChange A).symm;
    ⟨Module.Finite.equiv e, Projective.of_equiv e, fun p ↦ by
      rw [← rankAtStalk_eq_of_equiv e, rankAtStalk_baseChange, rankAtStalk_eq]⟩⟩

lemma baseChange_val (N : G(M; R, k)) : (baseChange A N).val = N.val.baseChange A := rfl

variable {A} {B : Type*} [CommRing B] [Algebra R B]

/-- Functoriality of Grassmannian in the category of `R`-algebras. Note that given an `R`-algebra
`A`, we replace `M` with `A ⊗[R] M`. The map `f : A →ₐ[R] B` should technically provide an instance
`[Algebra A B]`, but this might cause problems later down the line, so we do not require this
instance in the type signature of the function. Instead, given any instance `[Algebra A B]`, we
later prove that the map is equal to the one induced by `IsScalarTower.toAlgHom R A B : A →ₐ[R] B`.
See `map_val` and `map_eq`.
-/
noncomputable def map (f : A →ₐ[R] B) (N : G(A ⊗[R] M; A, k)) : G(B ⊗[R] M; B, k) :=
  letI := f.toAlgebra;
  ofLinearEquiv (AlgebraTensorModule.cancelBaseChange R A B B M) (baseChange B N)

lemma map_val (f : A →ₐ[R] B) (N : G(A ⊗[R] M; A, k)) :
    (N.map f).val = Submodule.span B (f.toLinearMap.rTensor M '' N.val) := by
  letI := f.toAlgebra;
  rw [map, ofLinearEquiv_val, baseChange_val, Submodule.baseChange_eq_span, Submodule.map_span,
    Submodule.map_coe, ← Set.image_comp, AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one]
  rfl

lemma map_val' (f : A →ₐ[R] B) (N : G(A ⊗[R] M; A, k)) :
    (N.map f).val = Submodule.span B ((N.val.restrictScalars R).map (f.toLinearMap.rTensor M)) :=
  map_val f N

lemma map_eq [Algebra A B] [IsScalarTower R A B] (N : G(A ⊗[R] M; A, k)) :
    N.map (IsScalarTower.toAlgHom R A B) = ofLinearEquiv
      (AlgebraTensorModule.cancelBaseChange R A B B M) (baseChange B N) := by
  ext; rw [map_val, ofLinearEquiv_val, baseChange_val, Submodule.baseChange_eq_span,
    Submodule.map_span, Submodule.map_coe, ← Set.image_comp,
    AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one]

lemma map_id (N : G(A ⊗[R] M; A, k)) : N.map (AlgHom.id R A) = N :=
  ext (by rw [map_val, AlgHom.toLinearMap_id, LinearMap.rTensor_id, LinearMap.id_coe, Set.image_id,
    Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self])

variable {C : Type*} [CommRing C] [Algebra R C]

lemma map_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (N : G(A ⊗[R] M; A, k)) :
    N.map (g.comp f) = (N.map f).map g := by
  refine letI := f.toAlgebra; letI := g.toAlgebra; ext ?_
  have hg : g = IsScalarTower.toAlgHom R B C := rfl
  rw [map_val, map_val', map_val, hg, ← AlgebraTensorModule.cancelBaseChange_comp_mk_one',
    ← Submodule.restrictScalars_map, Submodule.map_span, Submodule.coe_restrictScalars,
    Submodule.span_span_of_tower, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_toLinearMap, AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one,
    AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.coe_comp, Set.image_comp]

/-- The Grassmannian functor given a ring `R`, an `R`-module `M`, and a natural number `k`.
Given an `R`-algebra `A`, we return the set `G(A ⊗[R] M; A, k)`. -/
@[simps!] noncomputable def functor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (k : ℕ) :
    Under R ⥤ Type (max u v) where
  obj A := G(A ⊗[R] M; A, k)
  map f := map (CommRingCat.toAlgHom f)
  map_id _ := funext map_id
  map_comp f g := funext (map_comp (CommRingCat.toAlgHom f) (CommRingCat.toAlgHom g))

/-- Functoriality of `chart`. -/
lemma baseChange_chart_subset (f : Fin k → M) :
    baseChange A '' (chart R f) ⊆ chart A (TensorProduct.mk R A M 1 ∘ f) := by
  rintro - ⟨N, hn, rfl⟩
  convert ofSurjective_mem_chart (R:=A) (M := A ⊗[R] M) (q:=?_) ?_ ?_ ?_
  -- refine ofSurjective_mem_chart (q:=?_) ?_ ?_ ?_

end Grassmannian

namespace ProjectiveSpace

end ProjectiveSpace

end AlgebraicGeometry
