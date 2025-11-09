/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.GroupTheory.CosetCover

/-!
# Algebraic extensions are determined by their sets of minimal polynomials up to isomorphism

## Main results

`Field.nonempty_algHom_of_exist_roots` says if `E/F` and `K/F` are field extensions
with `E/F` algebraic, and if the minimal polynomial of every element of `E` over `F` has a root
in `K`, then there exists an `F`-embedding of `E` into `K`. If `E/F` and `K/F` have the same
set of minimal polynomials, then `E` and `K` are isomorphic as `F`-algebras. As a corollary:

`IsAlgClosure.of_exist_roots`: if `E/F` is algebraic and every monic irreducible polynomial
in `F[X]` has a root in `E`, then `E` is an algebraic closure of `F`.

## Reference

[Isaacs1980] *Roots of Polynomials in Algebraic Extensions of Fields*,
The American Mathematical Monthly

-/

namespace Field

open Polynomial IntermediateField

variable {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
variable [alg : Algebra.IsAlgebraic F E]

theorem nonempty_algHom_of_exist_roots (h : ∀ x : E, ∃ y : K, aeval y (minpoly F x) = 0) :
    Nonempty (E →ₐ[F] K) := by
  refine Lifts.nonempty_algHom_of_exist_lifts_finset fun S ↦ ⟨⟨adjoin F S, ?_⟩, subset_adjoin _ _⟩
  let p := (S.prod <| minpoly F).map (algebraMap F K)
  let K' := SplittingField p
  have splits s (hs : s ∈ S) : (minpoly F s).Splits (algebraMap F K') := by
    apply splits_of_splits_of_dvd _
      (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ minpoly.ne_zero <| (alg.isIntegral).1 _)
      ((splits_map_iff _ _).mp <| SplittingField.splits p) (Finset.dvd_prod_of_mem _ hs)
  let K₀ := (⊥ : IntermediateField K K').restrictScalars F
  let FS := adjoin F (S : Set E)
  let Ω := FS →ₐ[F] K'
  have := finiteDimensional_adjoin (S := (S : Set E)) fun _ _ ↦ (alg.isIntegral).1 _
  let M (ω : Ω) := Subalgebra.toSubmodule (K₀.comap ω).toSubalgebra
  have : ⋃ ω : Ω, (M ω : Set FS) = Set.univ :=
    Set.eq_univ_of_forall fun ⟨α, hα⟩ ↦ Set.mem_iUnion.mpr <| by
      have ⟨β, hβ⟩ := h α
      let ϕ : F⟮α⟯ →ₐ[F] K' := (IsScalarTower.toAlgHom _ _ _).comp
        ((AdjoinRoot.liftAlgHom _ _ _ hβ).comp
        (adjoinRootEquivAdjoin F <| (alg.isIntegral).1 _).symm.toAlgHom)
      have ⟨ω, hω⟩ := exists_algHom_adjoin_of_splits
        (fun s hs ↦ ⟨(alg.isIntegral).1 _, splits s hs⟩) ϕ (adjoin_simple_le_iff.mpr hα)
      refine ⟨ω, β, ((DFunLike.congr_fun hω <| AdjoinSimple.gen F α).trans ?_).symm⟩
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom,
        adjoinRootEquivAdjoin_symm_apply_gen, AdjoinRoot.liftAlgHom_root]
      rfl
  have ω : ∃ ω : Ω, ⊤ ≤ M ω := by
    cases finite_or_infinite F
    · have ⟨α, hα⟩ := exists_primitive_element_of_finite_bot F FS
      have ⟨ω, hω⟩ := Set.mem_iUnion.mp (this ▸ Set.mem_univ α)
      exact ⟨ω, show ⊤ ≤ K₀.comap ω by rwa [← hα, adjoin_simple_le_iff]⟩
    · simp_rw [top_le_iff, Subspace.exists_eq_top_of_iUnion_eq_univ this]
  exact ((botEquiv K K').toAlgHom.restrictScalars F).comp
    (ω.choose.codRestrict K₀.toSubalgebra fun x ↦ ω.choose_spec trivial)

theorem nonempty_algHom_of_minpoly_eq
    (h : ∀ x : E, ∃ y : K, minpoly F x = minpoly F y) :
    Nonempty (E →ₐ[F] K) :=
  nonempty_algHom_of_exist_roots fun x ↦ have ⟨y, hy⟩ := h x; ⟨y, by rw [hy, minpoly.aeval]⟩

theorem nonempty_algHom_of_range_minpoly_subset
    (h : Set.range (@minpoly F E _ _ _) ⊆ Set.range (@minpoly F K _ _ _)) :
    Nonempty (E →ₐ[F] K) :=
  nonempty_algHom_of_minpoly_eq fun x ↦ have ⟨y, hy⟩ := h ⟨x, rfl⟩; ⟨y, hy.symm⟩

theorem nonempty_algEquiv_of_range_minpoly_eq
    (h : Set.range (@minpoly F E _ _ _) = Set.range (@minpoly F K _ _ _)) :
    Nonempty (E ≃ₐ[F] K) :=
  have ⟨σ⟩ := nonempty_algHom_of_range_minpoly_subset h.le
  have : Algebra.IsAlgebraic F K := ⟨fun y ↦ IsIntegral.isAlgebraic <| by
    by_contra hy
    have ⟨x, hx⟩ := h.ge ⟨y, rfl⟩
    rw [minpoly.eq_zero hy] at hx
    exact minpoly.ne_zero ((alg.isIntegral).1 x) hx⟩
  have ⟨τ⟩ := nonempty_algHom_of_range_minpoly_subset h.ge
  ⟨.ofBijective _ (Algebra.IsAlgebraic.algHom_bijective₂ σ τ).1⟩

theorem nonempty_algHom_of_aeval_eq_zero_subset
    (h : {p : F[X] | ∃ x : E, aeval x p = 0} ⊆ {p | ∃ y : K, aeval y p = 0}) :
    Nonempty (E →ₐ[F] K) :=
  nonempty_algHom_of_minpoly_eq fun x ↦
    have ⟨y, hy⟩ := h ⟨_, minpoly.aeval F x⟩
    ⟨y, (minpoly.eq_iff_aeval_minpoly_eq_zero <| (alg.isIntegral).1 x).mpr hy⟩

theorem nonempty_algEquiv_of_aeval_eq_zero_eq [Algebra.IsAlgebraic F K]
    (h : {p : F[X] | ∃ x : E, aeval x p = 0} = {p | ∃ y : K, aeval y p = 0}) :
    Nonempty (E ≃ₐ[F] K) :=
  have ⟨σ⟩ := nonempty_algHom_of_aeval_eq_zero_subset h.le
  have ⟨τ⟩ := nonempty_algHom_of_aeval_eq_zero_subset h.ge
  ⟨.ofBijective _ (Algebra.IsAlgebraic.algHom_bijective₂ σ τ).1⟩

theorem _root_.IsAlgClosure.of_exist_roots
    (h : ∀ p : F[X], p.Monic → Irreducible p → ∃ x : E, aeval x p = 0) :
    IsAlgClosure F E :=
  .of_splits fun p _ _ ↦
    have ⟨σ⟩ := nonempty_algHom_of_exist_roots fun x : p.SplittingField ↦
      have := Algebra.IsAlgebraic.isIntegral (K := F).1 x
      h _ (minpoly.monic this) (minpoly.irreducible this)
    splits_of_algHom (SplittingField.splits _) σ

end Field
