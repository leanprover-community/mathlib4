/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

#align_import linear_algebra.eigenspace.is_alg_closed from "leanprover-community/mathlib"@"6b0169218d01f2837d79ea2784882009a0da1aa1"

/-!
# Triangularizable linear endomorphisms

This file contains basic results relevant to the triangularizability of linear endomorphisms.

* Every linear operator on a vector space over an algebraically closed field has an eigenvalue.
* The generalized eigenvectors span the entire vector space.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/


universe u v w

namespace Module

namespace End

open FiniteDimensional

variable {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]

-- This is Lemma 5.21 of [axler2015], although we are no longer following that proof.
/-- Every linear operator on a vector space over an algebraically closed field has
    an eigenvalue. -/
theorem exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    ∃ c : K, f.HasEigenvalue c := by
  simp_rw [hasEigenvalue_iff_mem_spectrum]
  exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K f
#align module.End.exists_eigenvalue Module.End.exists_eigenvalue

noncomputable instance [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    Inhabited f.Eigenvalues :=
  ⟨⟨f.exists_eigenvalue.choose, f.exists_eigenvalue.choose_spec⟩⟩

/-- The generalized eigenvectors span the entire vector space (Lemma 8.21 of [axler2015]). -/
theorem iSup_generalizedEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ⨆ (μ : K) (k : ℕ), f.generalizedEigenspace μ k = ⊤ := by
  -- We prove the claim by strong induction on the dimension of the vector space.
  induction' h_dim : finrank K V using Nat.strong_induction_on with n ih generalizing V
  cases' n with n
  -- If the vector space is 0-dimensional, the result is trivial.
  · rw [← top_le_iff]
    simp only [finrank_eq_zero.1 (Eq.trans (finrank_top _ _) h_dim), bot_le]
  -- Otherwise the vector space is nontrivial.
  · haveI : Nontrivial V := finrank_pos_iff.1 (by rw [h_dim]; apply Nat.zero_lt_succ)
    -- Hence, `f` has an eigenvalue `μ₀`.
    obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, f.HasEigenvalue μ₀ := exists_eigenvalue f
    -- We define `ES` to be the generalized eigenspace
    let ES := f.generalizedEigenspace μ₀ (finrank K V)
    -- and `ER` to be the generalized eigenrange.
    let ER := f.generalizedEigenrange μ₀ (finrank K V)
    -- `f` maps `ER` into itself.
    have h_f_ER : ∀ x : V, x ∈ ER → f x ∈ ER := fun x hx =>
      map_generalizedEigenrange_le (Submodule.mem_map_of_mem hx)
    -- Therefore, we can define the restriction `f'` of `f` to `ER`.
    let f' : End K ER := f.restrict h_f_ER
    -- The dimension of `ES` is positive
    have h_dim_ES_pos : 0 < finrank K ES := by
      dsimp only
      rw [h_dim]
      apply pos_finrank_generalizedEigenspace_of_hasEigenvalue hμ₀ (Nat.zero_lt_succ n)
    -- and the dimensions of `ES` and `ER` add up to `finrank K V`.
    have h_dim_add : finrank K ER + finrank K ES = finrank K V := by
      apply LinearMap.finrank_range_add_finrank_ker
    -- Therefore the dimension `ER` mus be smaller than `finrank K V`.
    have h_dim_ER : finrank K ER < n.succ := by linarith
    -- This allows us to apply the induction hypothesis on `ER`:
    have ih_ER : ⨆ (μ : K) (k : ℕ), f'.generalizedEigenspace μ k = ⊤ :=
      ih (finrank K ER) h_dim_ER f' rfl
    -- The induction hypothesis gives us a statement about subspaces of `ER`. We can transfer this
    -- to a statement about subspaces of `V` via `submodule.subtype`:
    have ih_ER' : ⨆ (μ : K) (k : ℕ), (f'.generalizedEigenspace μ k).map ER.subtype = ER := by
      simp only [(Submodule.map_iSup _ _).symm, ih_ER, Submodule.map_subtype_top ER]
    -- Moreover, every generalized eigenspace of `f'` is contained in the corresponding generalized
    -- eigenspace of `f`.
    have hff' :
      ∀ μ k, (f'.generalizedEigenspace μ k).map ER.subtype ≤ f.generalizedEigenspace μ k := by
      intros
      rw [generalizedEigenspace_restrict]
      apply Submodule.map_comap_le
    -- It follows that `ER` is contained in the span of all generalized eigenvectors.
    have hER : ER ≤ ⨆ (μ : K) (k : ℕ), f.generalizedEigenspace μ k := by
      rw [← ih_ER']
      exact iSup₂_mono hff'
    -- `ES` is contained in this span by definition.
    have hES : ES ≤ ⨆ (μ : K) (k : ℕ), f.generalizedEigenspace μ k :=
      le_trans (le_iSup (fun k => f.generalizedEigenspace μ₀ k) (finrank K V))
        (le_iSup (fun μ : K => ⨆ k : ℕ, f.generalizedEigenspace μ k) μ₀)
    -- Moreover, we know that `ER` and `ES` are disjoint.
    have h_disjoint : Disjoint ER ES := generalized_eigenvec_disjoint_range_ker f μ₀
    -- Since the dimensions of `ER` and `ES` add up to the dimension of `V`, it follows that the
    -- span of all generalized eigenvectors is all of `V`.
    show ⨆ (μ : K) (k : ℕ), f.generalizedEigenspace μ k = ⊤
    · rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES h_dim_add h_disjoint]
      apply sup_le hER hES
#align module.End.supr_generalized_eigenspace_eq_top Module.End.iSup_generalizedEigenspace_eq_top

end End

end Module
