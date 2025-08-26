/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# A module over a division ring is Noetherian if and only if it is finite.

-/


universe u v

open Cardinal Submodule Module Function

namespace IsNoetherian

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A module over a division ring is Noetherian if and only if
its dimension (as a cardinal) is strictly less than the first infinite cardinal `ℵ₀`.
-/
theorem iff_rank_lt_aleph0 : IsNoetherian K V ↔ Module.rank K V < ℵ₀ := by
  let b := Basis.ofVectorSpace K V
  rw [← b.mk_eq_rank'', lt_aleph0_iff_set_finite]
  constructor
  · intro
    exact (Basis.ofVectorSpaceIndex.linearIndependent K V).set_finite_of_isNoetherian
  · intro hbfinite
    refine
      @isNoetherian_of_linearEquiv K (⊤ : Submodule K V) V _ _ _ _ _ (LinearEquiv.ofTop _ rfl)
        (id ?_)
    refine isNoetherian_of_fg_of_noetherian _ ⟨Set.Finite.toFinset hbfinite, ?_⟩
    rw [Set.Finite.coe_toFinset, ← b.span_eq, Basis.coe_ofVectorSpace, Subtype.range_coe]

/-- In a Noetherian module over a division ring, all bases are indexed by a finite type. -/
noncomputable def fintypeBasisIndex {ι : Type*} [IsNoetherian K V] (b : Basis ι K V) : Fintype ι :=
  b.fintypeIndexOfRankLtAleph0 (rank_lt_aleph0 K V)

/-- In a Noetherian module over a division ring,
`Basis.ofVectorSpace` is indexed by a finite type. -/
noncomputable instance [IsNoetherian K V] : Fintype (Basis.ofVectorSpaceIndex K V) :=
  fintypeBasisIndex (Basis.ofVectorSpace K V)

/-- In a Noetherian module over a division ring,
if a basis is indexed by a set, that set is finite. -/
theorem finite_basis_index {ι : Type*} {s : Set ι} [IsNoetherian K V] (b : Basis s K V) :
    s.Finite :=
  b.finite_index_of_rank_lt_aleph0 (rank_lt_aleph0 K V)

variable (K V)

/-- In a Noetherian module over a division ring,
there exists a finite basis. This is the indexing `Finset`. -/
noncomputable def finsetBasisIndex [IsNoetherian K V] : Finset V :=
  (finite_basis_index (Basis.ofVectorSpace K V)).toFinset

@[simp]
theorem coe_finsetBasisIndex [IsNoetherian K V] :
    (↑(finsetBasisIndex K V) : Set V) = Basis.ofVectorSpaceIndex K V :=
  Set.Finite.coe_toFinset _

@[simp]
theorem coeSort_finsetBasisIndex [IsNoetherian K V] :
    (finsetBasisIndex K V : Type _) = Basis.ofVectorSpaceIndex K V :=
  Set.Finite.coeSort_toFinset _

/-- In a Noetherian module over a division ring, there exists a finite basis.
This is indexed by the `Finset` `IsNoetherian.finsetBasisIndex`.
This is in contrast to the result `finite_basis_index (Basis.ofVectorSpace K V)`,
which provides a set and a `Set.Finite`.
-/
noncomputable def finsetBasis [IsNoetherian K V] : Basis (finsetBasisIndex K V) K V :=
  (Basis.ofVectorSpace K V).reindex (by rw [coeSort_finsetBasisIndex])

@[simp]
theorem range_finsetBasis [IsNoetherian K V] :
    Set.range (finsetBasis K V) = Basis.ofVectorSpaceIndex K V := by
  rw [finsetBasis, Basis.range_reindex, Basis.range_ofVectorSpace]

variable {K V}

theorem _root_.Module.card_eq_pow_finrank [Fintype K] [Fintype V] :
    Fintype.card V = Fintype.card K ^ Module.finrank K V := by
  let b := IsNoetherian.finsetBasis K V
  rw [Module.card_fintype b, ← Module.finrank_eq_card_basis b]

@[deprecated (since := "2025-03-14")] alias _root_.card_eq_pow_finrank := Module.card_eq_pow_finrank

theorem _root_.Module.natCard_eq_pow_finrank [Module.Finite K V] :
    Nat.card V = Nat.card K ^ finrank K V := by
  let b := IsNoetherian.finsetBasis K V
  rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, finrank_eq_nat_card_basis b]

/-- A module over a division ring is Noetherian if and only if it is finitely generated. -/
theorem iff_fg : IsNoetherian K V ↔ Module.Finite K V := by
  constructor
  · intro h
    exact
      ⟨⟨finsetBasisIndex K V, by
          convert (finsetBasis K V).span_eq
          simp⟩⟩
  · rintro ⟨s, hs⟩
    rw [IsNoetherian.iff_rank_lt_aleph0, ← rank_top, ← hs]
    exact lt_of_le_of_lt (rank_span_le _) s.finite_toSet.lt_aleph0

end IsNoetherian
