/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Order.Irreducible
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Lasker ring

## Main declarations

- `IsLasker`: An `R`-module `M` satisfies `IsLasker R M` when any `N : Submodule R M` can be
  decomposed into finitely many primary submodules.
- `IsLasker.exists_isMinimalPrimaryDecomposition`: Any `N : Submodule R N` in an `R`-module `M`
  satisfying `IsLasker R M` can be decomposed into finitely many primary submodules `Nᵢ`, such
  that the decomposition is minimal: each `Nᵢ` is necessary, and the `√Ann(M/Nᵢ)` are distinct.
- `Submodule.isLasker`: Every Noetherian module is Lasker.

## TODO

One needs to prove that the radicals of minimal decompositions are independent of the
  precise decomposition.

-/

@[expose] public section

section IsLasker

open Ideal

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- An `R`-module `M` satisfies `IsLasker R M` when any `N : Submodule R M` can be
  decomposed into finitely many primary submodules. -/
def IsLasker : Prop :=
  ∀ N : Submodule R M, ∃ s : Finset (Submodule R M), s.inf id = N ∧ ∀ ⦃J⦄, J ∈ s → J.IsPrimary

variable {R M}

namespace Submodule

lemma decomposition_erase_inf [DecidableEq (Submodule R M)] {N : Submodule R M}
    {s : Finset (Submodule R M)} (hs : s.inf id = N) :
    ∃ t : Finset (Submodule R M), t ⊆ s ∧ t.inf id = N ∧
      ∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J := by
  induction s using Finset.eraseInduction with
  | H s IH =>
    by_cases! H : ∀ J ∈ s, ¬ (s.erase J).inf id ≤ J
    · exact ⟨s, Finset.Subset.rfl, hs, H⟩
    obtain ⟨J, hJ, hJ'⟩ := H
    refine (IH _ hJ ?_).imp
      fun t ↦ And.imp_left (fun ht ↦ ht.trans (Finset.erase_subset _ _))
    rw [← Finset.insert_erase hJ] at hs
    simp [← hs, hJ']

open scoped Function -- required for scoped `on` notation

lemma isPrimary_decomposition_pairwise_ne_radical {N : Submodule R M}
    {s : Finset (Submodule R M)} (hs : s.inf id = N) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Submodule R M), t.inf id = N ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      (t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical) := by
  classical
  refine ⟨(s.image fun J ↦ {I ∈ s | (I.colon .univ).radical = (J.colon .univ).radical}).image
    fun t ↦ t.inf id, ?_, ?_, ?_⟩
  · ext
    grind [Finset.inf_image, Submodule.mem_finsetInf]
  · simp only [Finset.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
    intro J hJ
    refine isPrimary_finsetInf (i := J) ?_ ?_ (by simp)
    · simp [hJ]
    · simp only [Finset.mem_filter, id_eq, and_imp]
      intro y hy
      simp [hs' hy]
  · intro I hI J hJ hIJ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, exists_exists_and_eq_and] at hI hJ
    obtain ⟨I', hI', hI⟩ := hI
    obtain ⟨J', hJ', hJ⟩ := hJ
    simp only [Function.onFun, ne_eq]
    contrapose! hIJ
    suffices (I'.colon Set.univ).radical = (J'.colon Set.univ).radical by
      rw [← hI, ← hJ, this]
    · rw [← hI, colon_finsetInf,
        radical_finset_inf (i := I') (by simp [hI']) (by simp), id_eq] at hIJ
      rw [hIJ, ← hJ, colon_finsetInf,
        radical_finset_inf (i := J') (by simp [hJ']) (by simp), id_eq]

lemma exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition
    [DecidableEq (Submodule R M)] {N : Submodule R M} {s : Finset (Submodule R M)}
    (hs : s.inf id = N) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Submodule R M), t.inf id = N ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      ((t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical)) ∧
      (∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J) := by
  obtain ⟨t, ht, ht', ht''⟩ := isPrimary_decomposition_pairwise_ne_radical hs hs'
  obtain ⟨u, hut, hu, hu'⟩ := decomposition_erase_inf ht
  exact ⟨u, hu, fun _ hi ↦ ht' (hut hi), ht''.mono hut, hu'⟩

/-- A `Finset` of submodules is a minimal primary decomposition of `N` if the submodules `Nᵢ`
intersect to `N`, are primary, the `√Ann(M/Nᵢ)` are distinct, and each `Nᵢ` is necessary. -/
structure IsMinimalPrimaryDecomposition [DecidableEq (Submodule R M)]
    (N : Submodule R M) (t : Finset (Submodule R M)) where
  inf_eq : t.inf id = N
  primary : ∀ ⦃J⦄, J ∈ t → J.IsPrimary
  distinct : (t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical)
  minimal : ∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J

lemma IsLasker.exists_isMinimalPrimaryDecomposition [DecidableEq (Submodule R M)]
    (h : IsLasker R M) (N : Submodule R M) :
    ∃ t : Finset (Submodule R M), N.IsMinimalPrimaryDecomposition t := by
  obtain ⟨s, hs1, hs2⟩ := h N
  obtain ⟨t, h1, h2, h3, h4⟩ :=
    exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hs1 hs2
  exact ⟨t, h1, h2, h3, h4⟩

end Submodule

@[deprecated (since := "2026-01-19")]
alias Ideal.decomposition_erase_inf := Submodule.decomposition_erase_inf

@[deprecated (since := "2026-01-19")]
alias Ideal.isPrimary_decomposition_pairwise_ne_radical :=
  Submodule.isPrimary_decomposition_pairwise_ne_radical

@[deprecated (since := "2026-01-19")]
alias Ideal.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition :=
  Submodule.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition

@[deprecated (since := "2026-01-19")]
alias Ideal.IsMinimalPrimaryDecomposition := Submodule.IsMinimalPrimaryDecomposition

@[deprecated (since := "2026-01-19")]
alias Ideal.IsLasker.exists_isMinimalPrimaryDecomposition :=
  Submodule.IsLasker.exists_isMinimalPrimaryDecomposition

@[deprecated (since := "2026-01-19")]
alias Ideal.IsLasker.minimal := Submodule.IsLasker.exists_isMinimalPrimaryDecomposition

end IsLasker

namespace Submodule

section Noetherian

open Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherian R M]

lemma _root_.InfIrred.isPrimary {N : Submodule R M} (h : InfIrred N) : N.IsPrimary := by
  rw [Submodule.IsPrimary]
  refine ⟨h.ne_top, fun {a b} hab ↦ ?_⟩
  let f : ℕ → Submodule R M := fun n ↦
  { carrier := {x | a ^ n • x ∈ N}
    add_mem' hx hy := by simp [N.add_mem hx hy]
    zero_mem' := by simp
    smul_mem' x y h := by simp [smul_comm _ x, N.smul_mem x h] }
  have hf : Monotone f := by
    intro n m hnm x hx
    simpa [hnm, smul_smul, ← pow_add] using N.smul_mem (a ^ (m - n)) hx
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹_› ⟨f, hf⟩
  rcases h with ⟨-, h⟩
  specialize @h (f n) (N + a ^ n • ⊤) ?_
  · refine le_antisymm (fun r ⟨h1, h2⟩ ↦ ?_) (le_inf (fun x ↦ N.smul_mem (a ^ n)) (by simp))
    simp only [add_eq_sup, SetLike.mem_coe, mem_sup, mem_smul_pointwise_iff_exists] at h2
    obtain ⟨x, hx, -, ⟨y, -, rfl⟩, rfl⟩ := h2
    have h : (a ^ n • y ∈ N) = (a ^ (n + n) • y ∈ N) := congr_arg (y ∈ ·) (hn (n + n) le_add_self)
    rw [pow_add, mul_smul] at h
    rwa [N.add_mem_iff_right hx, h, ← N.add_mem_iff_right (N.smul_mem (a ^ n) hx), ← smul_add]
  rw [add_eq_sup, sup_eq_left] at h
  refine h.imp (fun h ↦ ?_) (fun h ↦ ⟨n, h⟩)
  replace hn : f n = f (n + 1) := hn (n + 1) n.le_succ
  rw [← h, hn]
  rw [← h] at hab
  simpa [f, pow_succ, mul_smul] using hab

variable (R M) in
/-- The Lasker--Noether theorem: every submodule in a Noetherian module admits a decomposition into
  primary submodules. -/
lemma isLasker : IsLasker R M := fun I ↦
  (exists_infIrred_decomposition I).imp fun _ h ↦ h.imp_right fun h' _ ht ↦ (h' ht).isPrimary

end Noetherian

end Submodule

@[deprecated (since := "2026-01-19")]
alias Ideal.isLasker := Submodule.isLasker
