/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Anne Baanen
-/
import Mathlib.LinearAlgebra.Dimension

#align_import linear_algebra.finrank from "leanprover-community/mathlib"@"347636a7a80595d55bedf6e6fbd996a3c39da69a"

/-!
# Finite dimension of vector spaces

Definition of the rank of a module, or dimension of a vector space, as a natural number.

## Main definitions

Defined is `FiniteDimensional.finrank`, the dimension of a finite dimensional space, returning a
`Nat`, as opposed to `Module.rank`, which returns a `Cardinal`. When the space has infinite
dimension, its `finrank` is by convention set to `0`.

The definition of `finrank` does not assume a `FiniteDimensional` instance, but lemmas might.
Import `LinearAlgebra.FiniteDimensional` to get access to these additional lemmas.

Formulas for the dimension are given for linear equivs, in `LinearEquiv.finrank_eq`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `Dimension.lean`. Not all results have been ported yet.

You should not assume that there has been any effort to state lemmas as generally as possible.
-/


universe u v v' w

open Cardinal

open Cardinal Submodule Module Function

variable {K : Type u} {V : Type v}

namespace FiniteDimensional

open IsNoetherian

section Ring

variable [Ring K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

/-- The rank of a module as a natural number.

Defined by convention to be `0` if the space has infinite rank.

For a vector space `V` over a field `K`, this is the same as the finite dimension
of `V` over `K`.
-/
noncomputable def finrank (R V : Type*) [Semiring R] [AddCommGroup V] [Module R V] : ℕ :=
  Cardinal.toNat (Module.rank R V)
#align finite_dimensional.finrank FiniteDimensional.finrank

theorem finrank_eq_of_rank_eq {n : ℕ} (h : Module.rank K V = ↑n) : finrank K V = n := by
  apply_fun toNat at h
  -- ⊢ finrank K V = n
  rw [toNat_cast] at h
  -- ⊢ finrank K V = n
  exact_mod_cast h
  -- 🎉 no goals
#align finite_dimensional.finrank_eq_of_rank_eq FiniteDimensional.finrank_eq_of_rank_eq

lemma rank_eq_one_iff_finrank_eq_one : Module.rank K V = 1 ↔ finrank K V = 1 :=
  Cardinal.toNat_eq_one.symm

/-- This is like `rank_eq_one_iff_finrank_eq_one` but works for `2`, `3`, `4`, ... -/
lemma rank_eq_ofNat_iff_finrank_eq_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
    Module.rank K V = OfNat.ofNat n ↔ finrank K V = OfNat.ofNat n :=
  Cardinal.toNat_eq_ofNat.symm

theorem finrank_le_of_rank_le {n : ℕ} (h : Module.rank K V ≤ ↑n) : finrank K V ≤ n := by
  rwa [← Cardinal.toNat_le_iff_le_of_lt_aleph0, toNat_cast] at h
  -- ⊢ Module.rank K V < ℵ₀
  · exact h.trans_lt (nat_lt_aleph0 n)
    -- 🎉 no goals
  · exact nat_lt_aleph0 n
    -- 🎉 no goals
#align finite_dimensional.finrank_le_of_rank_le FiniteDimensional.finrank_le_of_rank_le

theorem finrank_lt_of_rank_lt {n : ℕ} (h : Module.rank K V < ↑n) : finrank K V < n := by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_cast] at h
  -- ⊢ Module.rank K V < ℵ₀
  · exact h.trans (nat_lt_aleph0 n)
    -- 🎉 no goals
  · exact nat_lt_aleph0 n
    -- 🎉 no goals
#align finite_dimensional.finrank_lt_of_rank_lt FiniteDimensional.finrank_lt_of_rank_lt

theorem lt_rank_of_lt_finrank {n : ℕ} (h : n < finrank K V) : ↑n < Module.rank K V := by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_cast]
  -- ⊢ ↑n < ℵ₀
  · exact nat_lt_aleph0 n
    -- 🎉 no goals
  · contrapose! h
    -- ⊢ finrank K V ≤ n
    rw [finrank, Cardinal.toNat_apply_of_aleph0_le h]
    -- ⊢ 0 ≤ n
    exact n.zero_le
    -- 🎉 no goals
#align finite_dimensional.rank_lt_of_finrank_lt FiniteDimensional.lt_rank_of_lt_finrank

theorem one_lt_rank_of_one_lt_finrank (h : 1 < finrank K V) : 1 < Module.rank K V := by
  simpa using lt_rank_of_lt_finrank h
  -- 🎉 no goals

theorem finrank_le_finrank_of_rank_le_rank
    (h : lift.{v'} (Module.rank K V) ≤ Cardinal.lift.{v} (Module.rank K V₂))
    (h' : Module.rank K V₂ < ℵ₀) : finrank K V ≤ finrank K V₂ := by
  simpa only [toNat_lift] using toNat_le_of_le_of_lt_aleph0 (lift_lt_aleph0.mpr h') h
  -- 🎉 no goals
#align finite_dimensional.finrank_le_finrank_of_rank_le_rank FiniteDimensional.finrank_le_finrank_of_rank_le_rank

section

variable [Nontrivial K] [NoZeroSMulDivisors K V]

/-- A finite dimensional space is nontrivial if it has positive `finrank`. -/
theorem nontrivial_of_finrank_pos (h : 0 < finrank K V) : Nontrivial V :=
  rank_pos_iff_nontrivial.mp (lt_rank_of_lt_finrank h)
#align finite_dimensional.nontrivial_of_finrank_pos FiniteDimensional.nontrivial_of_finrank_pos

/-- A finite dimensional space is nontrivial if it has `finrank` equal to the successor of a
natural number. -/
theorem nontrivial_of_finrank_eq_succ {n : ℕ} (hn : finrank K V = n.succ) : Nontrivial V :=
  nontrivial_of_finrank_pos (by rw [hn]; exact n.succ_pos)
                                -- ⊢ 0 < Nat.succ n
                                         -- 🎉 no goals
#align finite_dimensional.nontrivial_of_finrank_eq_succ FiniteDimensional.nontrivial_of_finrank_eq_succ

/-- A (finite dimensional) space that is a subsingleton has zero `finrank`. -/
theorem finrank_zero_of_subsingleton [h : Subsingleton V] : finrank K V = 0 := by
  by_contra h0
  -- ⊢ False
  obtain ⟨x, y, hxy⟩ := nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h0)
  -- ⊢ False
  exact hxy (Subsingleton.elim _ _)
  -- 🎉 no goals
#align finite_dimensional.finrank_zero_of_subsingleton FiniteDimensional.finrank_zero_of_subsingleton

end

section

variable [StrongRankCondition K]

/-- If a vector space (or module) has a finite basis, then its dimension (or rank) is equal to the
cardinality of the basis. -/
theorem finrank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι K V) :
    finrank K V = Fintype.card ι :=
  finrank_eq_of_rank_eq (rank_eq_card_basis h)
#align finite_dimensional.finrank_eq_card_basis FiniteDimensional.finrank_eq_card_basis

/-- If a vector space (or module) has a finite basis, then its dimension (or rank) is equal to the
cardinality of the basis. This lemma uses a `Finset` instead of indexed types. -/
theorem finrank_eq_card_finset_basis {ι : Type w} {b : Finset ι} (h : Basis b K V) :
    finrank K V = Finset.card b := by rw [finrank_eq_card_basis h, Fintype.card_coe]
                                      -- 🎉 no goals
#align finite_dimensional.finrank_eq_card_finset_basis FiniteDimensional.finrank_eq_card_finset_basis

variable (K)

/-- A ring satisfying `StrongRankCondition` (such as a `DivisionRing`) is one-dimensional as a
module over itself. -/
@[simp]
theorem finrank_self : finrank K K = 1 :=
  finrank_eq_of_rank_eq (by simp)
                            -- 🎉 no goals
#align finite_dimensional.finrank_self FiniteDimensional.finrank_self

/-- The vector space of functions on a `Fintype ι` has finrank equal to the cardinality of `ι`. -/
@[simp]
theorem finrank_fintype_fun_eq_card {ι : Type v} [Fintype ι] : finrank K (ι → K) = Fintype.card ι :=
  finrank_eq_of_rank_eq rank_fun'
#align finite_dimensional.finrank_fintype_fun_eq_card FiniteDimensional.finrank_fintype_fun_eq_card

/-- The vector space of functions on `Fin n` has finrank equal to `n`. -/
-- @[simp] -- Porting note: simp already proves this
theorem finrank_fin_fun {n : ℕ} : finrank K (Fin n → K) = n := by simp
                                                                  -- 🎉 no goals
#align finite_dimensional.finrank_fin_fun FiniteDimensional.finrank_fin_fun

end

end Ring

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem Basis.subset_extend {s : Set V} (hs : LinearIndependent K ((↑) : s → V)) :
    s ⊆ hs.extend (Set.subset_univ _) :=
  hs.subset_extend _
#align finite_dimensional.basis.subset_extend FiniteDimensional.Basis.subset_extend

end DivisionRing

end FiniteDimensional

section ZeroRank

variable [Ring K] [StrongRankCondition K] [AddCommGroup V] [Module K V] [Module.Free K V]

open FiniteDimensional

theorem finrank_eq_zero_of_basis_imp_not_finite
    (h : ∀ s : Set V, Basis.{v} (s : Set V) K V → ¬s.Finite) : finrank K V = 0 := by
  obtain ⟨_, ⟨b⟩⟩ := (Module.free_iff_set K V).mp ‹_›
  -- ⊢ finrank K V = 0
  exact dif_neg fun rank_lt => h _ b (b.finite_index_of_rank_lt_aleph0 rank_lt)
  -- 🎉 no goals
#align finrank_eq_zero_of_basis_imp_not_finite finrank_eq_zero_of_basis_imp_not_finite

theorem finrank_eq_zero_of_basis_imp_false (h : ∀ s : Finset V, Basis.{v} (s : Set V) K V → False) :
    finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs =>
    h hs.toFinset
      (by
        convert b
        -- ⊢ ↑(Set.Finite.toFinset hs) = s
        simp)
        -- 🎉 no goals
#align finrank_eq_zero_of_basis_imp_false finrank_eq_zero_of_basis_imp_false

theorem finrank_eq_zero_of_not_exists_basis
    (h : ¬∃ s : Finset V, Nonempty (Basis (s : Set V) K V)) : finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩
#align finrank_eq_zero_of_not_exists_basis finrank_eq_zero_of_not_exists_basis

theorem finrank_eq_zero_of_not_exists_basis_finite
    (h : ¬∃ (s : Set V) (_ : Basis.{v} (s : Set V) K V), s.Finite) : finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs => h ⟨s, b, hs⟩
#align finrank_eq_zero_of_not_exists_basis_finite finrank_eq_zero_of_not_exists_basis_finite

theorem finrank_eq_zero_of_not_exists_basis_finset (h : ¬∃ s : Finset V, Nonempty (Basis s K V)) :
    finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩
#align finrank_eq_zero_of_not_exists_basis_finset finrank_eq_zero_of_not_exists_basis_finset

end ZeroRank

namespace LinearEquiv

open FiniteDimensional

variable [Ring K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

variable {R M M₂ : Type*} [Ring R] [AddCommGroup M] [AddCommGroup M₂]

variable [Module R M] [Module R M₂]

/-- The dimension of a finite dimensional space is preserved under linear equivalence. -/
theorem finrank_eq (f : M ≃ₗ[R] M₂) : finrank R M = finrank R M₂ := by
  unfold finrank
  -- ⊢ ↑toNat (Module.rank R M) = ↑toNat (Module.rank R M₂)
  rw [← Cardinal.toNat_lift, f.lift_rank_eq, Cardinal.toNat_lift]
  -- 🎉 no goals
#align linear_equiv.finrank_eq LinearEquiv.finrank_eq

/-- Pushforwards of finite-dimensional submodules along a `LinearEquiv` have the same finrank. -/
theorem finrank_map_eq (f : M ≃ₗ[R] M₂) (p : Submodule R M) :
    finrank R (p.map (f : M →ₗ[R] M₂)) = finrank R p :=
  (f.submoduleMap p).finrank_eq.symm
#align linear_equiv.finrank_map_eq LinearEquiv.finrank_map_eq

end LinearEquiv

namespace LinearMap

open FiniteDimensional

section Ring

variable [Ring K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

/-- The dimensions of the domain and range of an injective linear map are equal. -/
theorem finrank_range_of_inj {f : V →ₗ[K] V₂} (hf : Function.Injective f) :
    finrank K (LinearMap.range f) = finrank K V := by rw [(LinearEquiv.ofInjective f hf).finrank_eq]
                                                      -- 🎉 no goals
#align linear_map.finrank_range_of_inj LinearMap.finrank_range_of_inj

end Ring

end LinearMap

open Module FiniteDimensional

section

variable [Ring K] [AddCommGroup V] [Module K V]

variable (K V)

@[simp]
theorem finrank_bot [Nontrivial K] : finrank K (⊥ : Submodule K V) = 0 :=
  finrank_eq_of_rank_eq (rank_bot _ _)
#align finrank_bot finrank_bot

@[simp]
theorem finrank_top : finrank K (⊤ : Submodule K V) = finrank K V := by
  unfold finrank
  -- ⊢ ↑toNat (Module.rank K { x // x ∈ ⊤ }) = ↑toNat (Module.rank K V)
  simp [rank_top]
  -- 🎉 no goals
#align finrank_top finrank_top

end

namespace Submodule

section Ring

variable [Ring K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

theorem lt_of_le_of_finrank_lt_finrank {s t : Submodule K V} (le : s ≤ t)
    (lt : finrank K s < finrank K t) : s < t :=
  lt_of_le_of_ne le fun h => ne_of_lt lt (by rw [h])
                                             -- 🎉 no goals
#align submodule.lt_of_le_of_finrank_lt_finrank Submodule.lt_of_le_of_finrank_lt_finrank

theorem lt_top_of_finrank_lt_finrank {s : Submodule K V} (lt : finrank K s < finrank K V) :
    s < ⊤ := by
  rw [← finrank_top K V] at lt
  -- ⊢ s < ⊤
  exact lt_of_le_of_finrank_lt_finrank le_top lt
  -- 🎉 no goals
#align submodule.lt_top_of_finrank_lt_finrank Submodule.lt_top_of_finrank_lt_finrank

end Ring

end Submodule

section Span

open Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

variable (K)

/-- The rank of a set of vectors as a natural number. -/
protected noncomputable def Set.finrank (s : Set V) : ℕ :=
  finrank K (span K s)
#align set.finrank Set.finrank

variable {K}

theorem finrank_span_le_card (s : Set V) [Fintype s] : finrank K (span K s) ≤ s.toFinset.card :=
  finrank_le_of_rank_le (by simpa using rank_span_le (K := K) s)
                            -- 🎉 no goals
#align finrank_span_le_card finrank_span_le_card

theorem finrank_span_finset_le_card (s : Finset V) : (s : Set V).finrank K ≤ s.card :=
  calc
    (s : Set V).finrank K ≤ (s : Set V).toFinset.card := finrank_span_le_card (V := V) s
    _ = s.card := by simp
                     -- 🎉 no goals
#align finrank_span_finset_le_card finrank_span_finset_le_card

theorem finrank_range_le_card {ι : Type*} [Fintype ι] {b : ι → V} :
    (Set.range b).finrank K ≤ Fintype.card ι := by
  classical
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_range]
  exact Finset.card_image_le
#align finrank_range_le_card finrank_range_le_card

theorem finrank_span_eq_card {ι : Type*} [Fintype ι] {b : ι → V} (hb : LinearIndependent K b) :
    finrank K (span K (Set.range b)) = Fintype.card ι :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank K (span K (Set.range b)) = #(Set.range b) := rank_span hb
      -- ⊢ Module.rank K { x // x ∈ span K (Set.range b) } = ↑(Fintype.card ι)
      rwa [← lift_inj, mk_range_eq_of_injective hb.injective, Cardinal.mk_fintype, lift_natCast,
        lift_eq_nat_iff] at this)
#align finrank_span_eq_card finrank_span_eq_card

theorem finrank_span_set_eq_card (s : Set V) [Fintype s] (hs : LinearIndependent K ((↑) : s → V)) :
    finrank K (span K s) = s.toFinset.card :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank K (span K s) = #s := rank_span_set hs
      -- ⊢ Module.rank K { x // x ∈ span K s } = ↑(Finset.card (Set.toFinset s))
      rwa [Cardinal.mk_fintype, ← Set.toFinset_card] at this)
      -- 🎉 no goals
#align finrank_span_set_eq_card finrank_span_set_eq_card

theorem finrank_span_finset_eq_card (s : Finset V) (hs : LinearIndependent K ((↑) : s → V)) :
    finrank K (span K (s : Set V)) = s.card := by
  convert finrank_span_set_eq_card (s : Set V) hs
  -- ⊢ s = Set.toFinset ↑s
  ext
  -- ⊢ a✝ ∈ s ↔ a✝ ∈ Set.toFinset ↑s
  simp
  -- 🎉 no goals
#align finrank_span_finset_eq_card finrank_span_finset_eq_card

theorem span_lt_of_subset_of_card_lt_finrank {s : Set V} [Fintype s] {t : Submodule K V}
    (subset : s ⊆ t) (card_lt : s.toFinset.card < finrank K t) : span K s < t :=
  lt_of_le_of_finrank_lt_finrank (span_le.mpr subset)
    (lt_of_le_of_lt (finrank_span_le_card _) card_lt)
#align span_lt_of_subset_of_card_lt_finrank span_lt_of_subset_of_card_lt_finrank

theorem span_lt_top_of_card_lt_finrank {s : Set V} [Fintype s]
    (card_lt : s.toFinset.card < finrank K V) : span K s < ⊤ :=
  lt_top_of_finrank_lt_finrank (lt_of_le_of_lt (finrank_span_le_card _) card_lt)
#align span_lt_top_of_card_lt_finrank span_lt_top_of_card_lt_finrank

/-- Given a family of `n` linearly independent vectors in a finite-dimensional space of
dimension `> n`, one may extend the family by another vector while retaining linear independence. -/
theorem exists_linear_independent_snoc_of_lt_finrank {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (h : n < finrank K V) :
    ∃ (x : V), LinearIndependent K (Fin.snoc v x) :=
  exists_linear_independent_snoc_of_lt_rank hv (lt_rank_of_lt_finrank h)

/-- Given a family of `n` linearly independent vectors in a finite-dimensional space of
dimension `> n`, one may extend the family by another vector while retaining linear independence. -/
theorem exists_linear_independent_cons_of_lt_finrank {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (h : n < finrank K V) :
    ∃ (x : V), LinearIndependent K (Fin.cons x v) :=
  exists_linear_independent_cons_of_lt_rank hv (lt_rank_of_lt_finrank h)

/-- Given a nonzero vector in a finite-dimensional space of dimension `> 1`, one may find another
vector linearly independent of the first one. -/
theorem exists_linear_independent_pair_of_one_lt_finrank
    (h : 1 < finrank K V) {x : V} (hx : x ≠ 0) :
    ∃ y, LinearIndependent K ![x, y] :=
  exists_linear_independent_pair_of_one_lt_rank (one_lt_rank_of_one_lt_finrank h) hx

end DivisionRing

end Span

section Basis

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem linearIndependent_of_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι] {b : ι → V}
    (spans : ⊤ ≤ span K (Set.range b)) (card_eq : Fintype.card ι = finrank K V) :
    LinearIndependent K b :=
  linearIndependent_iff'.mpr fun s g dependent i i_mem_s => by
    classical
    by_contra gx_ne_zero
    -- We'll derive a contradiction by showing `b '' (univ \ {i})` of cardinality `n - 1`
    -- spans a vector space of dimension `n`.
    refine' not_le_of_gt (span_lt_top_of_card_lt_finrank
      (show (b '' (Set.univ \ {i})).toFinset.card < finrank K V from _)) _
    · calc
        (b '' (Set.univ \ {i})).toFinset.card = ((Set.univ \ {i}).toFinset.image b).card := by
          rw [Set.toFinset_card, Fintype.card_ofFinset]
        _ ≤ (Set.univ \ {i}).toFinset.card := Finset.card_image_le
        _ = (Finset.univ.erase i).card := (congr_arg Finset.card (Finset.ext (by simp [and_comm])))
        _ < Finset.univ.card := (Finset.card_erase_lt_of_mem (Finset.mem_univ i))
        _ = finrank K V := card_eq
    -- We already have that `b '' univ` spans the whole space,
    -- so we only need to show that the span of `b '' (univ \ {i})` contains each `b j`.
    refine' spans.trans (span_le.mpr _)
    rintro _ ⟨j, rfl, rfl⟩
    -- The case that `j ≠ i` is easy because `b j ∈ b '' (univ \ {i})`.
    by_cases j_eq : j = i
    swap
    · refine' subset_span ⟨j, (Set.mem_diff _).mpr ⟨Set.mem_univ _, _⟩, rfl⟩
      exact mt Set.mem_singleton_iff.mp j_eq
    -- To show `b i ∈ span (b '' (univ \ {i}))`, we use that it's a weighted sum
    -- of the other `b j`s.
    rw [j_eq, SetLike.mem_coe, show b i = -((g i)⁻¹ • (s.erase i).sum fun j => g j • b j) from _]
    · refine' neg_mem (smul_mem _ _ (sum_mem fun k hk => _))
      obtain ⟨k_ne_i, _⟩ := Finset.mem_erase.mp hk
      refine' smul_mem _ _ (subset_span ⟨k, _, rfl⟩)
      simp_all only [Set.mem_univ, Set.mem_diff, Set.mem_singleton_iff]
    -- To show `b i` is a weighted sum of the other `b j`s, we'll rewrite this sum
    -- to have the form of the assumption `dependent`.
    apply eq_neg_of_add_eq_zero_left
    calc
      (b i + (g i)⁻¹ • (s.erase i).sum fun j => g j • b j) =
          (g i)⁻¹ • (g i • b i + (s.erase i).sum fun j => g j • b j) :=
        by rw [smul_add, ← mul_smul, inv_mul_cancel gx_ne_zero, one_smul]
      _ = (g i)⁻¹ • (0 : V) := (congr_arg _ ?_)
      _ = 0 := smul_zero _
    -- And then it's just a bit of manipulation with finite sums.
    rwa [← Finset.insert_erase i_mem_s, Finset.sum_insert (Finset.not_mem_erase _ _)] at dependent
#align linear_independent_of_top_le_span_of_card_eq_finrank linearIndependent_of_top_le_span_of_card_eq_finrank

/-- A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span. -/
theorem linearIndependent_iff_card_eq_finrank_span {ι : Type*} [Fintype ι] {b : ι → V} :
    LinearIndependent K b ↔ Fintype.card ι = (Set.range b).finrank K := by
  constructor
  -- ⊢ LinearIndependent K b → Fintype.card ι = Set.finrank K (Set.range b)
  · intro h
    -- ⊢ Fintype.card ι = Set.finrank K (Set.range b)
    exact (finrank_span_eq_card h).symm
    -- 🎉 no goals
  · intro hc
    -- ⊢ LinearIndependent K b
    let f := Submodule.subtype (span K (Set.range b))
    -- ⊢ LinearIndependent K b
    let b' : ι → span K (Set.range b) := fun i =>
      ⟨b i, mem_span.2 fun p hp => hp (Set.mem_range_self _)⟩
    have hs : ⊤ ≤ span K (Set.range b') := by
      intro x
      have h : span K (f '' Set.range b') = map f (span K (Set.range b')) := span_image f
      have hf : f '' Set.range b' = Set.range b := by
        ext x
        simp [Set.mem_image, Set.mem_range]
      rw [hf] at h
      have hx : (x : V) ∈ span K (Set.range b) := x.property
      conv at hx =>
        arg 2
        rw [h]
      simpa [mem_map] using hx
    have hi : LinearMap.ker f = ⊥ := ker_subtype _
    -- ⊢ LinearIndependent K b
    convert (linearIndependent_of_top_le_span_of_card_eq_finrank hs hc).map' _ hi
    -- 🎉 no goals
#align linear_independent_iff_card_eq_finrank_span linearIndependent_iff_card_eq_finrank_span

theorem linearIndependent_iff_card_le_finrank_span {ι : Type*} [Fintype ι] {b : ι → V} :
    LinearIndependent K b ↔ Fintype.card ι ≤ (Set.range b).finrank K := by
  rw [linearIndependent_iff_card_eq_finrank_span, finrank_range_le_card.le_iff_eq]
  -- 🎉 no goals
#align linear_independent_iff_card_le_finrank_span linearIndependent_iff_card_le_finrank_span

/-- A family of `finrank K V` vectors forms a basis if they span the whole space. -/
noncomputable def basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → V)
    (le_span : ⊤ ≤ span K (Set.range b)) (card_eq : Fintype.card ι = finrank K V) : Basis ι K V :=
  Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span
#align basis_of_top_le_span_of_card_eq_finrank basisOfTopLeSpanOfCardEqFinrank

@[simp]
theorem coe_basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → V)
    (le_span : ⊤ ≤ span K (Set.range b)) (card_eq : Fintype.card ι = finrank K V) :
    ⇑(basisOfTopLeSpanOfCardEqFinrank b le_span card_eq) = b :=
  Basis.coe_mk _ _
#align coe_basis_of_top_le_span_of_card_eq_finrank coe_basisOfTopLeSpanOfCardEqFinrank

/-- A finset of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps! repr_apply]
noncomputable def finsetBasisOfTopLeSpanOfCardEqFinrank {s : Finset V}
    (le_span : ⊤ ≤ span K (s : Set V)) (card_eq : s.card = finrank K V) : Basis (s : Set V) K V :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : ↥(s : Set V) → V)
    ((@Subtype.range_coe_subtype _ fun x => x ∈ s).symm ▸ le_span)
    (_root_.trans (Fintype.card_coe _) card_eq)
#align finset_basis_of_top_le_span_of_card_eq_finrank finsetBasisOfTopLeSpanOfCardEqFinrank

/-- A set of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps! repr_apply]
noncomputable def setBasisOfTopLeSpanOfCardEqFinrank {s : Set V} [Fintype s]
    (le_span : ⊤ ≤ span K s) (card_eq : s.toFinset.card = finrank K V) : Basis s K V :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : s → V) ((@Subtype.range_coe_subtype _ s).symm ▸ le_span)
    (_root_.trans s.toFinset_card.symm card_eq)
#align set_basis_of_top_le_span_of_card_eq_finrank setBasisOfTopLeSpanOfCardEqFinrank

end DivisionRing

end Basis

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/


section finrank_eq_one

variable [Ring K] [AddCommGroup V] [Module K V]

variable [NoZeroSMulDivisors K V] [StrongRankCondition K]

/-- If there is a nonzero vector and every other vector is a multiple of it,
then the module has dimension one. -/
theorem finrank_eq_one (v : V) (n : v ≠ 0) (h : ∀ w : V, ∃ c : K, c • v = w) : finrank K V = 1 := by
  haveI := nontrivial_of_invariantBasisNumber K
  -- ⊢ finrank K V = 1
  obtain ⟨b⟩ := (Basis.basis_singleton_iff.{u} PUnit).mpr ⟨v, n, h⟩
  -- ⊢ finrank K V = 1
  rw [finrank_eq_card_basis b, Fintype.card_punit]
  -- 🎉 no goals
#align finrank_eq_one finrank_eq_one

/-- If every vector is a multiple of some `v : V`, then `V` has dimension at most one.
-/
theorem finrank_le_one (v : V) (h : ∀ w : V, ∃ c : K, c • v = w) : finrank K V ≤ 1 := by
  haveI := nontrivial_of_invariantBasisNumber K
  -- ⊢ finrank K V ≤ 1
  rcases eq_or_ne v 0 with (rfl | hn)
  -- ⊢ finrank K V ≤ 1
  · haveI :=
      subsingleton_of_forall_eq (0 : V) fun w => by
        obtain ⟨c, rfl⟩ := h w
        simp
    rw [finrank_zero_of_subsingleton]
    -- ⊢ 0 ≤ 1
    exact zero_le_one
    -- 🎉 no goals
  · exact (finrank_eq_one v hn h).le
    -- 🎉 no goals
#align finrank_le_one finrank_le_one

end finrank_eq_one

section SubalgebraRank

open Module

variable {F E : Type*} [CommRing F] [Ring E] [Algebra F E]

@[simp]
theorem Subalgebra.rank_toSubmodule (S : Subalgebra F E) :
    Module.rank F (Subalgebra.toSubmodule S) = Module.rank F S :=
  rfl
#align subalgebra.rank_to_submodule Subalgebra.rank_toSubmodule

@[simp]
theorem Subalgebra.finrank_toSubmodule (S : Subalgebra F E) :
    finrank F (Subalgebra.toSubmodule S) = finrank F S :=
  rfl
#align subalgebra.finrank_to_submodule Subalgebra.finrank_toSubmodule

theorem subalgebra_top_rank_eq_submodule_top_rank :
    Module.rank F (⊤ : Subalgebra F E) = Module.rank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_toSubmodule]
  -- ⊢ Module.rank F { x // x ∈ ⊤ } = Module.rank F { x // x ∈ ↑Subalgebra.toSubmod …
  rfl
  -- 🎉 no goals
#align subalgebra_top_rank_eq_submodule_top_rank subalgebra_top_rank_eq_submodule_top_rank

theorem subalgebra_top_finrank_eq_submodule_top_finrank :
    finrank F (⊤ : Subalgebra F E) = finrank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_toSubmodule]
  -- ⊢ finrank F { x // x ∈ ⊤ } = finrank F { x // x ∈ ↑Subalgebra.toSubmodule ⊤ }
  rfl
  -- 🎉 no goals
#align subalgebra_top_finrank_eq_submodule_top_finrank subalgebra_top_finrank_eq_submodule_top_finrank

theorem Subalgebra.rank_top : Module.rank F (⊤ : Subalgebra F E) = Module.rank F E := by
  rw [subalgebra_top_rank_eq_submodule_top_rank]
  -- ⊢ Module.rank F { x // x ∈ ⊤ } = Module.rank F E
  exact _root_.rank_top F E
  -- 🎉 no goals
#align subalgebra.rank_top Subalgebra.rank_top

section

variable [StrongRankCondition F] [NoZeroSMulDivisors F E] [Nontrivial E]

@[simp]
theorem Subalgebra.rank_bot : Module.rank F (⊥ : Subalgebra F E) = 1 :=
  ((Subalgebra.toSubmoduleEquiv (⊥ : Subalgebra F E)).symm.trans <|
          LinearEquiv.ofEq _ _ Algebra.toSubmodule_bot).rank_eq.trans <| by
    letI := Module.nontrivial F E
    -- ⊢ Module.rank F { x // x ∈ span F {1} } = 1
    rw [rank_span_set]
    -- ⊢ #↑{1} = 1
    exacts [mk_singleton _, linearIndependent_singleton one_ne_zero]
    -- 🎉 no goals
#align subalgebra.rank_bot Subalgebra.rank_bot

@[simp]
theorem Subalgebra.finrank_bot : finrank F (⊥ : Subalgebra F E) = 1 :=
  finrank_eq_of_rank_eq (by simp)
                            -- 🎉 no goals
#align subalgebra.finrank_bot Subalgebra.finrank_bot

end

end SubalgebraRank
