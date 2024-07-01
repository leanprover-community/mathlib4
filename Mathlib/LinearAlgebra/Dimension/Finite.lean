/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Scott Morrison
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition


#align_import linear_algebra.dimension from "leanprover-community/mathlib"@"47a5f8186becdbc826190ced4312f8199f9db6a5"

/-!
# Conditions for rank to be finite

Also contains characterization for when rank equals zero or rank equals one.

-/


noncomputable section

universe u v v' w

variable {R : Type u} {M M₁ : Type v} {M' : Type v'} {ι : Type w}
variable [Ring R] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M₁]
variable [Module R M] [Module R M'] [Module R M₁]

attribute [local instance] nontrivial_of_invariantBasisNumber

open Cardinal Basis Submodule Function Set FiniteDimensional

theorem rank_le {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    Module.rank R M ≤ n := by
  rw [Module.rank_def]
  apply ciSup_le'
  rintro ⟨s, li⟩
  exact linearIndependent_bounded_of_finset_linearIndependent_bounded H _ li
#align rank_le rank_le

section RankZero

/-- See `rank_zero_iff` for a stronger version with `NoZeroSMulDivisor R M`. -/
lemma rank_eq_zero_iff :
    Module.rank R M = 0 ↔ ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x = 0 := by
  nontriviality R
  constructor
  · contrapose!
    rintro ⟨x, hx⟩
    rw [← Cardinal.one_le_iff_ne_zero]
    have : LinearIndependent R (fun _ : Unit ↦ x) :=
      linearIndependent_iff.mpr (fun l hl ↦ Finsupp.unique_ext <| not_not.mp fun H ↦
        hx _ H ((Finsupp.total_unique _ _ _).symm.trans hl))
    simpa using this.cardinal_lift_le_rank
  · intro h
    rw [← le_zero_iff, Module.rank_def]
    apply ciSup_le'
    intro ⟨s, hs⟩
    rw [nonpos_iff_eq_zero, Cardinal.mk_eq_zero_iff, ← not_nonempty_iff]
    rintro ⟨i : s⟩
    obtain ⟨a, ha, ha'⟩ := h i
    apply ha
    simpa using DFunLike.congr_fun (linearIndependent_iff.mp hs (Finsupp.single i a) (by simpa)) i

variable [Nontrivial R]
variable [NoZeroSMulDivisors R M]

theorem rank_zero_iff_forall_zero :
    Module.rank R M = 0 ↔ ∀ x : M, x = 0 := by
  simp_rw [rank_eq_zero_iff, smul_eq_zero, and_or_left, not_and_self_iff, false_or,
    exists_and_right, and_iff_right (exists_ne (0 : R))]
#align rank_zero_iff_forall_zero rank_zero_iff_forall_zero

/-- See `rank_subsingleton` for the reason that `Nontrivial R` is needed.
Also see `rank_eq_zero_iff` for the version without `NoZeroSMulDivisor R M`. -/
theorem rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M :=
  rank_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm
#align rank_zero_iff rank_zero_iff

theorem rank_pos_iff_exists_ne_zero : 0 < Module.rank R M ↔ ∃ x : M, x ≠ 0 := by
  rw [← not_iff_not]
  simpa using rank_zero_iff_forall_zero
#align rank_pos_iff_exists_ne_zero rank_pos_iff_exists_ne_zero

theorem rank_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M :=
  rank_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm
#align rank_pos_iff_nontrivial rank_pos_iff_nontrivial

lemma rank_eq_zero_iff_isTorsion {R M} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] :
    Module.rank R M = 0 ↔ Module.IsTorsion R M := by
  rw [Module.IsTorsion, rank_eq_zero_iff]
  simp [mem_nonZeroDivisors_iff_ne_zero]

theorem rank_pos [Nontrivial M] : 0 < Module.rank R M :=
  rank_pos_iff_nontrivial.mpr ‹_›
#align rank_pos rank_pos

variable (R M)

/-- See `rank_subsingleton` that assumes `Subsingleton R` instead. -/
theorem rank_subsingleton' [Subsingleton M] : Module.rank R M = 0 :=
  rank_eq_zero_iff.mpr fun _ ↦ ⟨1, one_ne_zero, Subsingleton.elim _ _⟩

@[simp]
theorem rank_punit : Module.rank R PUnit = 0 := rank_subsingleton' _ _
#align rank_punit rank_punit

@[simp]
theorem rank_bot : Module.rank R (⊥ : Submodule R M) = 0 := rank_subsingleton' _ _
#align rank_bot rank_bot

variable {R M}

theorem exists_mem_ne_zero_of_rank_pos {s : Submodule R M} (h : 0 < Module.rank R s) :
    ∃ b : M, b ∈ s ∧ b ≠ 0 :=
  exists_mem_ne_zero_of_ne_bot fun eq => by rw [eq, rank_bot] at h; exact lt_irrefl _ h
#align exists_mem_ne_zero_of_rank_pos exists_mem_ne_zero_of_rank_pos

end RankZero

section Finite

theorem Module.finite_of_rank_eq_nat [Module.Free R M] {n : ℕ} (h : Module.rank R M = n) :
    Module.Finite R M := by
  nontriviality R
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  have := mk_lt_aleph0_iff.mp <|
    b.linearIndependent.cardinal_le_rank |>.trans_eq h |>.trans_lt <| nat_lt_aleph0 n
  exact Module.Finite.of_basis b

theorem Module.finite_of_rank_eq_zero [NoZeroSMulDivisors R M]
    (h : Module.rank R M = 0) :
    Module.Finite R M := by
  nontriviality R
  rw [rank_zero_iff] at h
  infer_instance

theorem Module.finite_of_rank_eq_one [Module.Free R M] (h : Module.rank R M = 1) :
    Module.Finite R M :=
  Module.finite_of_rank_eq_nat <| h.trans Nat.cast_one.symm

variable [StrongRankCondition R]

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
theorem Basis.nonempty_fintype_index_of_rank_lt_aleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Nonempty (Fintype ι) := by
  rwa [← Cardinal.lift_lt, ← b.mk_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0,
    Cardinal.lt_aleph0_iff_fintype] at h
#align basis.nonempty_fintype_index_of_rank_lt_aleph_0 Basis.nonempty_fintype_index_of_rank_lt_aleph0

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
noncomputable def Basis.fintypeIndexOfRankLtAleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Fintype ι :=
  Classical.choice (b.nonempty_fintype_index_of_rank_lt_aleph0 h)
#align basis.fintype_index_of_rank_lt_aleph_0 Basis.fintypeIndexOfRankLtAleph0

/-- If a module has a finite dimension, all bases are indexed by a finite set. -/
theorem Basis.finite_index_of_rank_lt_aleph0 {ι : Type*} {s : Set ι} (b : Basis s R M)
    (h : Module.rank R M < ℵ₀) : s.Finite :=
  finite_def.2 (b.nonempty_fintype_index_of_rank_lt_aleph0 h)
#align basis.finite_index_of_rank_lt_aleph_0 Basis.finite_index_of_rank_lt_aleph0

namespace LinearIndependent

theorem cardinal_mk_le_finrank [Module.Finite R M]
    {ι : Type w} {b : ι → M} (h : LinearIndependent R b) : #ι ≤ finrank R M := by
  rw [← lift_le.{max v w}]
  simpa only [← finrank_eq_rank, lift_natCast, lift_le_nat_iff] using h.cardinal_lift_le_rank
#align finite_dimensional.cardinal_mk_le_finrank_of_linear_independent LinearIndependent.cardinal_mk_le_finrank

theorem fintype_card_le_finrank [Module.Finite R M]
    {ι : Type*} [Fintype ι] {b : ι → M} (h : LinearIndependent R b) :
    Fintype.card ι ≤ finrank R M := by
  simpa using h.cardinal_mk_le_finrank
#align finite_dimensional.fintype_card_le_finrank_of_linear_independent LinearIndependent.fintype_card_le_finrank

theorem finset_card_le_finrank [Module.Finite R M]
    {b : Finset M} (h : LinearIndependent R (fun x => x : b → M)) :
    b.card ≤ finrank R M := by
  rw [← Fintype.card_coe]
  exact h.fintype_card_le_finrank
#align finite_dimensional.finset_card_le_finrank_of_linear_independent LinearIndependent.finset_card_le_finrank

theorem lt_aleph0_of_finite {ι : Type w}
    [Module.Finite R M] {v : ι → M} (h : LinearIndependent R v) : #ι < ℵ₀ := by
  apply Cardinal.lift_lt.1
  apply lt_of_le_of_lt
  · apply h.cardinal_lift_le_rank
  · rw [← finrank_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_natCast]
    apply Cardinal.nat_lt_aleph0

theorem finite [Module.Finite R M] {ι : Type*} {f : ι → M}
    (h : LinearIndependent R f) : Finite ι :=
  Cardinal.lt_aleph0_iff_finite.1 <| h.lt_aleph0_of_finite

theorem setFinite [Module.Finite R M] {b : Set M}
    (h : LinearIndependent R fun x : b => (x : M)) : b.Finite :=
  Cardinal.lt_aleph0_iff_set_finite.mp h.lt_aleph0_of_finite
#align linear_independent.finite LinearIndependent.setFinite

end LinearIndependent

@[deprecated (since := "2023-12-27")]
alias cardinal_mk_le_finrank_of_linearIndependent := LinearIndependent.cardinal_mk_le_finrank
@[deprecated (since := "2023-12-27")]
alias fintype_card_le_finrank_of_linearIndependent := LinearIndependent.fintype_card_le_finrank
@[deprecated (since := "2023-12-27")]
alias finset_card_le_finrank_of_linearIndependent := LinearIndependent.finset_card_le_finrank
@[deprecated (since := "2023-12-27")]
alias Module.Finite.lt_aleph0_of_linearIndependent := LinearIndependent.lt_aleph0_of_finite

lemma exists_set_linearIndependent_of_lt_rank {n : Cardinal} (hn : n < Module.rank R M) :
    ∃ s : Set M, #s = n ∧ LinearIndependent R ((↑) : s → M) := by
  obtain ⟨⟨s, hs⟩, hs'⟩ := exists_lt_of_lt_ciSup' (hn.trans_eq (Module.rank_def R M))
  obtain ⟨t, ht, ht'⟩ := le_mk_iff_exists_subset.mp hs'.le
  exact ⟨t, ht', .mono ht hs⟩

lemma exists_finset_linearIndependent_of_le_rank {n : ℕ} (hn : n ≤ Module.rank R M) :
    ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) := by
  have := nonempty_linearIndependent_set
  cases' hn.eq_or_lt with h h
  · obtain ⟨⟨s, hs⟩, hs'⟩ := Cardinal.exists_eq_natCast_of_iSup_eq _
      (Cardinal.bddAbove_range.{v, v} _) _ (h.trans (Module.rank_def R M)).symm
    have : Finite s := lt_aleph0_iff_finite.mp (hs' ▸ nat_lt_aleph0 n)
    cases nonempty_fintype s
    exact ⟨s.toFinset, by simpa using hs', by convert hs <;> exact Set.mem_toFinset⟩
  · obtain ⟨s, hs, hs'⟩ := exists_set_linearIndependent_of_lt_rank h
    have : Finite s := lt_aleph0_iff_finite.mp (hs ▸ nat_lt_aleph0 n)
    cases nonempty_fintype s
    exact ⟨s.toFinset, by simpa using hs, by convert hs' <;> exact Set.mem_toFinset⟩

lemma exists_linearIndependent_of_le_rank {n : ℕ} (hn : n ≤ Module.rank R M) :
    ∃ f : Fin n → M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_rank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

lemma natCast_le_rank_iff {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ f : Fin n → M, LinearIndependent R f :=
  ⟨exists_linearIndependent_of_le_rank,
    fun H ↦ by simpa using H.choose_spec.cardinal_lift_le_rank⟩

lemma natCast_le_rank_iff_finset {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) :=
  ⟨exists_finset_linearIndependent_of_le_rank,
    fun ⟨s, h₁, h₂⟩ ↦ by simpa [h₁] using h₂.cardinal_le_rank⟩

lemma exists_finset_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) := by
  by_cases h : finrank R M = 0
  · rw [le_zero_iff.mp (hn.trans_eq h)]
    exact ⟨∅, rfl, by convert linearIndependent_empty R M using 2 <;> aesop⟩
  exact exists_finset_linearIndependent_of_le_rank
    ((natCast_le.mpr hn).trans_eq (cast_toNat_of_lt_aleph0 (toNat_ne_zero.mp h).2))

lemma exists_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ f : Fin n → M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_finrank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

variable [Module.Finite R M]

theorem Module.Finite.not_linearIndependent_of_infinite {ι : Type*} [Infinite ι]
    (v : ι → M) : ¬LinearIndependent R v := mt LinearIndependent.finite <| @not_finite _ _
#align finite_dimensional.not_linear_independent_of_infinite Module.Finite.not_linearIndependent_of_infinite

variable [NoZeroSMulDivisors R M]

theorem CompleteLattice.Independent.subtype_ne_bot_le_rank [Nontrivial R]
    {V : ι → Submodule R M} (hV : CompleteLattice.Independent V) :
    Cardinal.lift.{v} #{ i : ι // V i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank R M) := by
  set I := { i : ι // V i ≠ ⊥ }
  have hI : ∀ i : I, ∃ v ∈ V i, v ≠ (0 : M) := by
    intro i
    rw [← Submodule.ne_bot_iff]
    exact i.prop
  choose v hvV hv using hI
  have : LinearIndependent R v := (hV.comp Subtype.coe_injective).linearIndependent _ hvV hv
  exact this.cardinal_lift_le_rank
#align complete_lattice.independent.subtype_ne_bot_le_rank CompleteLattice.Independent.subtype_ne_bot_le_rank

theorem CompleteLattice.Independent.subtype_ne_bot_le_finrank_aux
    {p : ι → Submodule R M} (hp : CompleteLattice.Independent p) :
    #{ i // p i ≠ ⊥ } ≤ (finrank R M : Cardinal.{w}) := by
  suffices Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{v} (finrank R M : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc
    Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank R M) :=
      hp.subtype_ne_bot_le_rank
    _ = Cardinal.lift.{w} (finrank R M : Cardinal.{v}) := by rw [finrank_eq_rank]
    _ = Cardinal.lift.{v} (finrank R M : Cardinal.{w}) := by simp
#align complete_lattice.independent.subtype_ne_bot_le_finrank_aux CompleteLattice.Independent.subtype_ne_bot_le_finrank_aux

/-- If `p` is an independent family of submodules of a `R`-finite module `M`, then the
number of nontrivial subspaces in the family `p` is finite. -/
noncomputable def CompleteLattice.Independent.fintypeNeBotOfFiniteDimensional
    {p : ι → Submodule R M} (hp : CompleteLattice.Independent p) :
    Fintype { i : ι // p i ≠ ⊥ } := by
  suffices #{ i // p i ≠ ⊥ } < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph0_iff_fintype] at this
    exact this.some
  refine lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux ?_
  simp [Cardinal.nat_lt_aleph0]
#align complete_lattice.independent.fintype_ne_bot_of_finite_dimensional CompleteLattice.Independent.fintypeNeBotOfFiniteDimensional

/-- If `p` is an independent family of submodules of a `R`-finite module `M`, then the
number of nontrivial subspaces in the family `p` is bounded above by the dimension of `M`.

Note that the `Fintype` hypothesis required here can be provided by
`CompleteLattice.Independent.fintypeNeBotOfFiniteDimensional`. -/
theorem CompleteLattice.Independent.subtype_ne_bot_le_finrank
    {p : ι → Submodule R M} (hp : CompleteLattice.Independent p) [Fintype { i // p i ≠ ⊥ }] :
    Fintype.card { i // p i ≠ ⊥ } ≤ finrank R M := by simpa using hp.subtype_ne_bot_le_finrank_aux
#align complete_lattice.independent.subtype_ne_bot_le_finrank CompleteLattice.Independent.subtype_ne_bot_le_finrank

section

open Finset

/-- If a finset has cardinality larger than the rank of a module,
then there is a nontrivial linear relation amongst its elements. -/
theorem Module.exists_nontrivial_relation_of_finrank_lt_card {t : Finset M}
    (h : finrank R M < t.card) : ∃ f : M → R, ∑ e ∈ t, f e • e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  obtain ⟨g, sum, z, nonzero⟩ := Fintype.not_linearIndependent_iff.mp
    (mt LinearIndependent.finset_card_le_finrank h.not_le)
  refine ⟨Subtype.val.extend g 0, ?_, z, z.2, by rwa [Subtype.val_injective.extend_apply]⟩
  rw [← Finset.sum_finset_coe]; convert sum; apply Subtype.val_injective.extend_apply
#align finite_dimensional.exists_nontrivial_relation_of_rank_lt_card Module.exists_nontrivial_relation_of_finrank_lt_card

/-- If a finset has cardinality larger than `finrank + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero. -/
theorem Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card
    {t : Finset M} (h : finrank R M + 1 < t.card) :
    ∃ f : M → R, ∑ e ∈ t, f e • e = 0 ∧ ∑ e ∈ t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  -- Pick an element x₀ ∈ t,
  obtain ⟨x₀, x₀_mem⟩ := card_pos.1 ((Nat.succ_pos _).trans h)
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : M ↪ M := ⟨(· - x₀), sub_left_injective⟩
  classical
  let t' := (t.erase x₀).map shift
  have h' : finrank R M < t'.card := by
    rw [card_map, card_erase_of_mem x₀_mem]
    exact Nat.lt_pred_iff.mpr h
  -- to obtain a function `g`.
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_finrank_lt_card h'
  -- Then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e ∈ t, f e = 0`.
  let f : M → R := fun z ↦ if z = x₀ then -∑ z ∈ t.erase x₀, g (z - x₀) else g (z - x₀)
  refine ⟨f, ?_, ?_, ?_⟩
  -- After this, it's a matter of verifying the properties,
  -- based on the corresponding properties for `g`.
  · rw [sum_map, Embedding.coeFn_mk] at gsum
    simp_rw [f, ← t.sum_erase_add _ x₀_mem, if_pos, neg_smul, sum_smul,
             ← sub_eq_add_neg, ← sum_sub_distrib, ← gsum, smul_sub]
    refine sum_congr rfl fun x x_mem ↦ ?_
    rw [if_neg (mem_erase.mp x_mem).1]
  · simp_rw [f, ← t.sum_erase_add _ x₀_mem, if_pos, add_neg_eq_zero]
    exact sum_congr rfl fun x x_mem ↦ if_neg (mem_erase.mp x_mem).1
  · obtain ⟨x₁, x₁_mem', rfl⟩ := Finset.mem_map.mp x₁_mem
    have := mem_erase.mp x₁_mem'
    exact ⟨x₁, by
      simpa only [f, Embedding.coeFn_mk, sub_add_cancel, this.2, true_and, if_neg this.1]⟩
#align finite_dimensional.exists_nontrivial_relation_sum_zero_of_rank_succ_lt_card Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card

end

end Finite

section FinrankZero

variable [Nontrivial R] [NoZeroSMulDivisors R M]

/-- A finite dimensional space is nontrivial if it has positive `finrank`. -/
theorem FiniteDimensional.nontrivial_of_finrank_pos (h : 0 < finrank R M) : Nontrivial M :=
  rank_pos_iff_nontrivial.mp (lt_rank_of_lt_finrank h)
#align finite_dimensional.nontrivial_of_finrank_pos FiniteDimensional.nontrivial_of_finrank_pos

/-- A finite dimensional space is nontrivial if it has `finrank` equal to the successor of a
natural number. -/
theorem FiniteDimensional.nontrivial_of_finrank_eq_succ {n : ℕ}
    (hn : finrank R M = n.succ) : Nontrivial M :=
  nontrivial_of_finrank_pos (by rw [hn]; exact n.succ_pos)
#align finite_dimensional.nontrivial_of_finrank_eq_succ FiniteDimensional.nontrivial_of_finrank_eq_succ

/-- A (finite dimensional) space that is a subsingleton has zero `finrank`. -/
@[nontriviality]
theorem FiniteDimensional.finrank_zero_of_subsingleton [Subsingleton M] : finrank R M = 0 := by
  rw [finrank, rank_subsingleton', _root_.map_zero]
#align finite_dimensional.finrank_zero_of_subsingleton FiniteDimensional.finrank_zero_of_subsingleton

lemma LinearIndependent.finrank_eq_zero_of_infinite {ι} [Nontrivial R] [Infinite ι] {v : ι → M}
    (hv : LinearIndependent R v) : finrank R M = 0 := toNat_eq_zero.mpr <| .inr hv.aleph0_le_rank

variable (R M)

@[simp]
theorem finrank_bot : finrank R (⊥ : Submodule R M) = 0 :=
  finrank_eq_of_rank_eq (rank_bot _ _)
#align finrank_bot finrank_bot

variable {R M}

section StrongRankCondition

variable [StrongRankCondition R] [Module.Finite R M]

/-- A finite rank torsion-free module has positive `finrank` iff it has a nonzero element. -/
theorem FiniteDimensional.finrank_pos_iff_exists_ne_zero [NoZeroSMulDivisors R M] :
    0 < finrank R M ↔ ∃ x : M, x ≠ 0 := by
  rw [← @rank_pos_iff_exists_ne_zero R M, ← finrank_eq_rank]
  norm_cast
#align finite_dimensional.finrank_pos_iff_exists_ne_zero FiniteDimensional.finrank_pos_iff_exists_ne_zero

/-- An `R`-finite torsion-free module has positive `finrank` iff it is nontrivial. -/
theorem FiniteDimensional.finrank_pos_iff [NoZeroSMulDivisors R M] :
    0 < finrank R M ↔ Nontrivial M := by
  rw [← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank]
  norm_cast
#align finite_dimensional.finrank_pos_iff FiniteDimensional.finrank_pos_iff

/-- A nontrivial finite dimensional space has positive `finrank`. -/
theorem FiniteDimensional.finrank_pos [NoZeroSMulDivisors R M] [h : Nontrivial M] :
    0 < finrank R M :=
  finrank_pos_iff.mpr h
#align finite_dimensional.finrank_pos FiniteDimensional.finrank_pos

/-- See `FiniteDimensional.finrank_zero_iff`
  for the stronger version with `NoZeroSMulDivisors R M`. -/
theorem FiniteDimensional.finrank_eq_zero_iff :
    finrank R M = 0 ↔ ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x = 0 := by
  rw [← rank_eq_zero_iff (R := R), ← finrank_eq_rank]
  norm_cast

/-- The `StrongRankCondition` is automatic. See `commRing_strongRankCondition`. -/
theorem FiniteDimensional.finrank_eq_zero_iff_isTorsion {R} [CommRing R] [StrongRankCondition R]
    [IsDomain R] [Module R M] [Module.Finite R M] :
    finrank R M = 0 ↔ Module.IsTorsion R M := by
  rw [← rank_eq_zero_iff_isTorsion (R := R), ← finrank_eq_rank]
  norm_cast

/-- A finite dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `rank_zero_iff`. -/
theorem FiniteDimensional.finrank_zero_iff [NoZeroSMulDivisors R M] :
    finrank R M = 0 ↔ Subsingleton M := by
  rw [← rank_zero_iff (R := R), ← finrank_eq_rank]
  norm_cast
#align finite_dimensional.finrank_zero_iff FiniteDimensional.finrank_zero_iff

end StrongRankCondition

theorem FiniteDimensional.finrank_eq_zero_of_rank_eq_zero (h : Module.rank R M = 0) :
    finrank R M = 0 := by
  delta finrank
  rw [h, zero_toNat]
#align finrank_eq_zero_of_rank_eq_zero FiniteDimensional.finrank_eq_zero_of_rank_eq_zero

theorem Submodule.bot_eq_top_of_rank_eq_zero [NoZeroSMulDivisors R M] (h : Module.rank R M = 0) :
    (⊥ : Submodule R M) = ⊤ := by
  nontriviality R
  rw [rank_zero_iff] at h
  exact Subsingleton.elim _ _
#align bot_eq_top_of_rank_eq_zero Submodule.bot_eq_top_of_rank_eq_zero

/-- See `rank_subsingleton` for the reason that `Nontrivial R` is needed. -/
@[simp]
theorem Submodule.rank_eq_zero [Nontrivial R] [NoZeroSMulDivisors R M] {S : Submodule R M} :
    Module.rank R S = 0 ↔ S = ⊥ :=
  ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
      congr_arg Subtype.val <|
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| Submodule.bot_eq_top_of_rank_eq_zero h) ⟨x, hx⟩
          Submodule.mem_top,
    fun h => by rw [h, rank_bot]⟩
#align rank_eq_zero Submodule.rank_eq_zero

@[simp]
theorem Submodule.finrank_eq_zero [StrongRankCondition R] [NoZeroSMulDivisors R M]
    {S : Submodule R M} [Module.Finite R S] :
    finrank R S = 0 ↔ S = ⊥ := by
  rw [← Submodule.rank_eq_zero, ← finrank_eq_rank, ← @Nat.cast_zero Cardinal, Cardinal.natCast_inj]
#align finrank_eq_zero Submodule.finrank_eq_zero

@[simp]
lemma Submodule.one_le_finrank_iff [StrongRankCondition R] [NoZeroSMulDivisors R M]
    {S : Submodule R M} [Module.Finite R S] :
    1 ≤ finrank R S ↔ S ≠ ⊥ := by
  simp [← not_iff_not]

variable [Module.Free R M]

theorem finrank_eq_zero_of_basis_imp_not_finite
    (h : ∀ s : Set M, Basis.{v} (s : Set M) R M → ¬s.Finite) : finrank R M = 0 := by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    exact (h ∅ ⟨LinearEquiv.ofSubsingleton _ _⟩ Set.finite_empty).elim
  obtain ⟨_, ⟨b⟩⟩ := (Module.free_iff_set R M).mp ‹_›
  have := Set.Infinite.to_subtype (h _ b)
  exact b.linearIndependent.finrank_eq_zero_of_infinite
#align finrank_eq_zero_of_basis_imp_not_finite finrank_eq_zero_of_basis_imp_not_finite

theorem finrank_eq_zero_of_basis_imp_false (h : ∀ s : Finset M, Basis.{v} (s : Set M) R M → False) :
    finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs =>
    h hs.toFinset
      (by
        convert b
        simp)
#align finrank_eq_zero_of_basis_imp_false finrank_eq_zero_of_basis_imp_false

theorem finrank_eq_zero_of_not_exists_basis
    (h : ¬∃ s : Finset M, Nonempty (Basis (s : Set M) R M)) : finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩
#align finrank_eq_zero_of_not_exists_basis finrank_eq_zero_of_not_exists_basis

theorem finrank_eq_zero_of_not_exists_basis_finite
    (h : ¬∃ (s : Set M) (_ : Basis.{v} (s : Set M) R M), s.Finite) : finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs => h ⟨s, b, hs⟩
#align finrank_eq_zero_of_not_exists_basis_finite finrank_eq_zero_of_not_exists_basis_finite

theorem finrank_eq_zero_of_not_exists_basis_finset (h : ¬∃ s : Finset M, Nonempty (Basis s R M)) :
    finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩
#align finrank_eq_zero_of_not_exists_basis_finset finrank_eq_zero_of_not_exists_basis_finset

end FinrankZero

section RankOne

variable [NoZeroSMulDivisors R M] [StrongRankCondition R]

/-- If there is a nonzero vector and every other vector is a multiple of it,
then the module has dimension one. -/
theorem rank_eq_one (v : M) (n : v ≠ 0) (h : ∀ w : M, ∃ c : R, c • v = w) :
    Module.rank R M = 1 := by
  haveI := nontrivial_of_invariantBasisNumber R
  obtain ⟨b⟩ := (Basis.basis_singleton_iff.{_, _, u} PUnit).mpr ⟨v, n, h⟩
  rw [rank_eq_card_basis b, Fintype.card_punit, Nat.cast_one]

/-- If there is a nonzero vector and every other vector is a multiple of it,
then the module has dimension one. -/
theorem finrank_eq_one (v : M) (n : v ≠ 0) (h : ∀ w : M, ∃ c : R, c • v = w) : finrank R M = 1 :=
  finrank_eq_of_rank_eq (rank_eq_one v n h)
#align finrank_eq_one finrank_eq_one

/-- If every vector is a multiple of some `v : M`, then `M` has dimension at most one.
-/
theorem finrank_le_one (v : M) (h : ∀ w : M, ∃ c : R, c • v = w) : finrank R M ≤ 1 := by
  haveI := nontrivial_of_invariantBasisNumber R
  rcases eq_or_ne v 0 with (rfl | hn)
  · haveI :=
      _root_.subsingleton_of_forall_eq (0 : M) fun w => by
        obtain ⟨c, rfl⟩ := h w
        simp
    rw [finrank_zero_of_subsingleton]
    exact zero_le_one
  · exact (finrank_eq_one v hn h).le
#align finrank_le_one finrank_le_one

end RankOne
