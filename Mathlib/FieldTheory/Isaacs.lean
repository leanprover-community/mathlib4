/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.GroupTheory.CosetCover

/-!
# Characterize algebraic extensions by minimal polynomials

## Main results

`Field.nonempty_algHom_of_exists_roots` says if `E/F` and `K/F` are field extensions
with `E/F` algebraic, and if the minimal polynomial of every element of `E` over `F` has a root
in `K`, then there exists an `F`-embedding of `E` into `K`.

As a corollary, if `E/F` is algebraic and every irreducible polynomial in `F[X]` has a root
in `E`, then `E` is an algebraic closure of `F`.

As another corollary, if `E/F` and `K/F` are both algebraic and have the same set of minimal
polynomials, then `E` and `K` are isomorphic as `F`-algebras.

## Reference

[Isaacs1980] *Roots of Polynomials in Algebraic Extensions of Fields*,
The American Mathematical Monthly

-/

namespace Field

open Polynomial IntermediateField

variable {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
variable [alg : Algebra.IsAlgebraic F E]

theorem nonempty_algHom_of_exists_roots (h : ∀ x : E, ∃ y : K, aeval y (minpoly F x) = 0) :
    Nonempty (E →ₐ[F] K) := by
  refine nonempty_algHom_of_exists_lifts_finset
    fun S ↦ ⟨⟨adjoin F S, Nonempty.some ?_⟩, subset_adjoin _ _⟩
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
  have : ⋃ ω : Ω, ↑(M ω) = @Set.univ FS := Set.eq_univ_of_forall fun α ↦ Set.mem_iUnion.mpr <| by
    have ⟨β, hβ⟩ := h α.1
    let ϕ : F⟮α.1⟯ →ₐ[F] K' := (IsScalarTower.toAlgHom _ _ _).comp ((AdjoinRoot.liftHom _ _ hβ).comp
      (adjoinRootEquivAdjoin F <| (alg.isIntegral).1 _).symm.toAlgHom)
    have ⟨ω, hω⟩ := exists_algHom_adjoin_of_splits
      (fun s hs ↦ ⟨(alg.isIntegral).1 _, splits s hs⟩) ϕ (adjoin_simple_le_iff.mpr α.2)
    refine ⟨ω, β, .symm ?_⟩
    refine (DFunLike.congr_fun hω <| AdjoinSimple.gen F α.1).trans ?_
    /- rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom,
      adjoinRootEquivAdjoin_symm_apply_gen, AdjoinRoot.liftHom_root] -/
    sorry --rfl
  have ⟨ω, hω⟩ : ∃ ω : Ω, ⊤ ≤ M ω := by
    cases finite_or_infinite F
    · have ⟨α, hα⟩ := exists_primitive_element_of_finite_bot F FS
      have ⟨ω, hω⟩ := Set.mem_iUnion.mp (this ▸ Set.mem_univ α)
      exact ⟨ω, show ⊤ ≤ K₀.comap ω by rwa [← hα, adjoin_simple_le_iff]⟩
    · simp_rw [top_le_iff, Subspace.exists_eq_top_of_iUnion_eq_univ this]
  exact ⟨((botEquiv K K').toAlgHom.restrictScalars F).comp <|
    ω.codRestrict K₀.toSubalgebra fun x ↦ hω trivial⟩

theorem nonempty_algHom_of_minpoly_eq (h : ∀ x : E, ∃ y : K, minpoly F x = minpoly F y) :
    Nonempty (E →ₐ[F] K) := by
  _
