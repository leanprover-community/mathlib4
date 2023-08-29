/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.RingTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension

#align_import field_theory.finiteness from "leanprover-community/mathlib"@"039a089d2a4b93c761b234f3e5f5aeb752bac60f"

/-!
# A module over a division ring is noetherian if and only if it is finite.

-/


universe u v

open Classical Cardinal

open Cardinal Submodule Module Function

namespace IsNoetherian

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A module over a division ring is noetherian if and only if
its dimension (as a cardinal) is strictly less than the first infinite cardinal `ℵ₀`.
-/
theorem iff_rank_lt_aleph0 : IsNoetherian K V ↔ Module.rank K V < ℵ₀ := by
  let b := Basis.ofVectorSpace K V
  -- ⊢ IsNoetherian K V ↔ Module.rank K V < ℵ₀
  rw [← b.mk_eq_rank'', lt_aleph0_iff_set_finite]
  -- ⊢ IsNoetherian K V ↔ Set.Finite (Basis.ofVectorSpaceIndex K V)
  constructor
  -- ⊢ IsNoetherian K V → Set.Finite (Basis.ofVectorSpaceIndex K V)
  · intro
    -- ⊢ Set.Finite (Basis.ofVectorSpaceIndex K V)
    exact finite_of_linearIndependent (Basis.ofVectorSpaceIndex.linearIndependent K V)
    -- 🎉 no goals
  · intro hbfinite
    -- ⊢ IsNoetherian K V
    refine'
      @isNoetherian_of_linearEquiv K (⊤ : Submodule K V) V _ _ _ _ _ (LinearEquiv.ofTop _ rfl)
        (id _)
    refine' isNoetherian_of_fg_of_noetherian _ ⟨Set.Finite.toFinset hbfinite, _⟩
    -- ⊢ span K ↑(Set.Finite.toFinset hbfinite) = ⊤
    rw [Set.Finite.coe_toFinset, ← b.span_eq, Basis.coe_ofVectorSpace, Subtype.range_coe]
    -- 🎉 no goals
#align is_noetherian.iff_rank_lt_aleph_0 IsNoetherian.iff_rank_lt_aleph0

variable (K V)

/-- The dimension of a noetherian module over a division ring, as a cardinal,
is strictly less than the first infinite cardinal `ℵ₀`. -/
theorem rank_lt_aleph0 : ∀ [IsNoetherian K V], Module.rank K V < ℵ₀ :=
  @IsNoetherian.iff_rank_lt_aleph0.1
#align is_noetherian.rank_lt_aleph_0 IsNoetherian.rank_lt_aleph0

variable {K V}

/-- In a noetherian module over a division ring, all bases are indexed by a finite type. -/
noncomputable def fintypeBasisIndex {ι : Type*} [IsNoetherian K V] (b : Basis ι K V) : Fintype ι :=
  b.fintypeIndexOfRankLtAleph0 (rank_lt_aleph0 K V)
#align is_noetherian.fintype_basis_index IsNoetherian.fintypeBasisIndex

/-- In a noetherian module over a division ring,
`Basis.ofVectorSpace` is indexed by a finite type. -/
noncomputable instance [IsNoetherian K V] : Fintype (Basis.ofVectorSpaceIndex K V) :=
  fintypeBasisIndex (Basis.ofVectorSpace K V)

/-- In a noetherian module over a division ring,
if a basis is indexed by a set, that set is finite. -/
theorem finite_basis_index {ι : Type*} {s : Set ι} [IsNoetherian K V] (b : Basis s K V) :
    s.Finite :=
  b.finite_index_of_rank_lt_aleph0 (rank_lt_aleph0 K V)
#align is_noetherian.finite_basis_index IsNoetherian.finite_basis_index

variable (K V)

/-- In a noetherian module over a division ring,
there exists a finite basis. This is the indexing `Finset`. -/
noncomputable def finsetBasisIndex [IsNoetherian K V] : Finset V :=
  (finite_basis_index (Basis.ofVectorSpace K V)).toFinset
#align is_noetherian.finset_basis_index IsNoetherian.finsetBasisIndex

@[simp]
theorem coe_finsetBasisIndex [IsNoetherian K V] :
    (↑(finsetBasisIndex K V) : Set V) = Basis.ofVectorSpaceIndex K V :=
  Set.Finite.coe_toFinset _
#align is_noetherian.coe_finset_basis_index IsNoetherian.coe_finsetBasisIndex

@[simp]
theorem coeSort_finsetBasisIndex [IsNoetherian K V] :
    (finsetBasisIndex K V : Type _) = Basis.ofVectorSpaceIndex K V :=
  Set.Finite.coeSort_toFinset _
#align is_noetherian.coe_sort_finset_basis_index IsNoetherian.coeSort_finsetBasisIndex

/-- In a noetherian module over a division ring, there exists a finite basis.
This is indexed by the `Finset` `FiniteDimensional.finsetBasisIndex`.
This is in contrast to the result `finite_basis_index (Basis.ofVectorSpace K V)`,
which provides a set and a `Set.finite`.
-/
noncomputable def finsetBasis [IsNoetherian K V] : Basis (finsetBasisIndex K V) K V :=
  (Basis.ofVectorSpace K V).reindex (by rw [coeSort_finsetBasisIndex])
                                        -- 🎉 no goals
#align is_noetherian.finset_basis IsNoetherian.finsetBasis

@[simp]
theorem range_finsetBasis [IsNoetherian K V] :
    Set.range (finsetBasis K V) = Basis.ofVectorSpaceIndex K V := by
  rw [finsetBasis, Basis.range_reindex, Basis.range_ofVectorSpace]
  -- 🎉 no goals
#align is_noetherian.range_finset_basis IsNoetherian.range_finsetBasis

variable {K V}

/-- A module over a division ring is noetherian if and only if it is finitely generated. -/
theorem iff_fg : IsNoetherian K V ↔ Module.Finite K V := by
  constructor
  -- ⊢ IsNoetherian K V → Module.Finite K V
  · intro h
    -- ⊢ Module.Finite K V
    exact
      ⟨⟨finsetBasisIndex K V, by
          convert (finsetBasis K V).span_eq
          simp⟩⟩
  · rintro ⟨s, hs⟩
    -- ⊢ IsNoetherian K V
    rw [IsNoetherian.iff_rank_lt_aleph0, ← rank_top, ← hs]
    -- ⊢ Module.rank K { x // x ∈ span K ↑s } < ℵ₀
    exact lt_of_le_of_lt (rank_span_le _) s.finite_toSet.lt_aleph0
    -- 🎉 no goals
#align is_noetherian.iff_fg IsNoetherian.iff_fg

end IsNoetherian
