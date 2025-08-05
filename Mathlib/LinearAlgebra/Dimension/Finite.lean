/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Subsingleton
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.SetTheory.Cardinal.Cofinality

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

open Basis Cardinal Function Module Set Submodule

/-- If every finite set of linearly independent vectors has cardinality at most `n`,
then the same is true for arbitrary sets of linearly independent vectors.
-/
theorem linearIndependent_bounded_of_finset_linearIndependent_bounded {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    ∀ s : Set M, LinearIndependent R ((↑) : s → M) → #s ≤ n := by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype s)]
  apply H
  apply linearIndependent_finset_map_embedding_subtype _ li

theorem rank_le {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    Module.rank R M ≤ n := by
  rw [Module.rank_def]
  apply ciSup_le'
  rintro ⟨s, li⟩
  exact linearIndependent_bounded_of_finset_linearIndependent_bounded H _ li

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
        hx _ H ((Finsupp.linearCombination_unique _ _ _).symm.trans hl))
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

theorem rank_pos_of_free [Module.Free R M] [Nontrivial M] :
    0 < Module.rank R M :=
  have := Module.nontrivial R M
  (pos_of_ne_zero <| Cardinal.mk_ne_zero _).trans_le
    (Free.chooseBasis R M).linearIndependent.cardinal_le_rank

variable [Nontrivial R]

section
variable [NoZeroSMulDivisors R M]

theorem rank_zero_iff_forall_zero :
    Module.rank R M = 0 ↔ ∀ x : M, x = 0 := by
  simp_rw [rank_eq_zero_iff, smul_eq_zero, and_or_left, not_and_self_iff, false_or,
    exists_and_right, and_iff_right (exists_ne (0 : R))]

/-- See `rank_subsingleton` for the reason that `Nontrivial R` is needed.
Also see `rank_eq_zero_iff` for the version without `NoZeroSMulDivisor R M`. -/
theorem rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M :=
  rank_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm

theorem rank_pos_iff_exists_ne_zero : 0 < Module.rank R M ↔ ∃ x : M, x ≠ 0 := by
  rw [← not_iff_not]
  simpa using rank_zero_iff_forall_zero

theorem rank_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M :=
  rank_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm

theorem rank_pos [Nontrivial M] : 0 < Module.rank R M :=
  rank_pos_iff_nontrivial.mpr ‹_›

end

theorem exists_mem_ne_zero_of_rank_pos {s : Submodule R M} (h : 0 < Module.rank R s) :
    ∃ b : M, b ∈ s ∧ b ≠ 0 :=
  exists_mem_ne_zero_of_ne_bot fun eq => by rw [eq, rank_bot] at h; exact lt_irrefl _ h

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

section
variable [StrongRankCondition R]

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
theorem Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Nonempty (Fintype ι) := by
  rwa [← Cardinal.lift_lt, ← b.mk_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0,
    Cardinal.lt_aleph0_iff_fintype] at h

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
noncomputable def Module.Basis.fintypeIndexOfRankLtAleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Fintype ι :=
  Classical.choice (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

/-- If a module has a finite dimension, all bases are indexed by a finite set. -/
theorem Module.Basis.finite_index_of_rank_lt_aleph0 {ι : Type*} {s : Set ι} (b : Basis s R M)
    (h : Module.rank R M < ℵ₀) : s.Finite :=
  Set.finite_def.2 (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

end

namespace LinearIndependent
variable [StrongRankCondition R]

theorem cardinalMk_le_finrank [Module.Finite R M]
    {ι : Type w} {b : ι → M} (h : LinearIndependent R b) : #ι ≤ finrank R M := by
  rw [← lift_le.{max v w}]
  simpa only [← finrank_eq_rank, lift_natCast, lift_le_nat_iff] using h.cardinal_lift_le_rank

@[deprecated (since := "2024-11-10")] alias cardinal_mk_le_finrank := cardinalMk_le_finrank

theorem fintype_card_le_finrank [Module.Finite R M]
    {ι : Type*} [Fintype ι] {b : ι → M} (h : LinearIndependent R b) :
    Fintype.card ι ≤ finrank R M := by
  simpa using h.cardinalMk_le_finrank

theorem finset_card_le_finrank [Module.Finite R M]
    {b : Finset M} (h : LinearIndependent R (fun x => x : b → M)) :
    b.card ≤ finrank R M := by
  rw [← Fintype.card_coe]
  exact h.fintype_card_le_finrank

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

end LinearIndependent

lemma exists_set_linearIndependent_of_lt_rank {n : Cardinal} (hn : n < Module.rank R M) :
    ∃ s : Set M, #s = n ∧ LinearIndepOn R id s := by
  obtain ⟨⟨s, hs⟩, hs'⟩ := exists_lt_of_lt_ciSup' (hn.trans_eq (Module.rank_def R M))
  obtain ⟨t, ht, ht'⟩ := le_mk_iff_exists_subset.mp hs'.le
  exact ⟨t, ht', hs.mono ht⟩

lemma exists_finset_linearIndependent_of_le_rank {n : ℕ} (hn : n ≤ Module.rank R M) :
    ∃ s : Finset M, s.card = n ∧ LinearIndepOn R id (s : Set M) := by
  rcases hn.eq_or_lt with h | h
  · obtain ⟨⟨s, hs⟩, hs'⟩ := Cardinal.exists_eq_natCast_of_iSup_eq _
      (Cardinal.bddAbove_range _) _ (h.trans (Module.rank_def R M)).symm
    have : Finite s := lt_aleph0_iff_finite.mp (hs' ▸ nat_lt_aleph0 n)
    cases nonempty_fintype s
    refine ⟨s.toFinset, by simpa using hs', by simpa⟩
  · obtain ⟨s, hs, hs'⟩ := exists_set_linearIndependent_of_lt_rank h
    have : Finite s := lt_aleph0_iff_finite.mp (hs ▸ nat_lt_aleph0 n)
    cases nonempty_fintype s
    exact ⟨s.toFinset, by simpa using hs, by simpa⟩

lemma exists_linearIndependent_of_le_rank {n : ℕ} (hn : n ≤ Module.rank R M) :
    ∃ f : Fin n → M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_rank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

lemma natCast_le_rank_iff [Nontrivial R] {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ f : Fin n → M, LinearIndependent R f :=
  ⟨exists_linearIndependent_of_le_rank,
    fun H ↦ by simpa using H.choose_spec.cardinal_lift_le_rank⟩

lemma natCast_le_rank_iff_finset [Nontrivial R] {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) :=
  ⟨exists_finset_linearIndependent_of_le_rank,
    fun ⟨s, h₁, h₂⟩ ↦ by simpa [h₁] using h₂.cardinal_le_rank⟩

lemma exists_finset_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) := by
  by_cases h : finrank R M = 0
  · rw [le_zero_iff.mp (hn.trans_eq h)]
    exact ⟨∅, rfl, by convert linearIndependent_empty R M using 2 <;> aesop⟩
  exact exists_finset_linearIndependent_of_le_rank
    ((Nat.cast_le.mpr hn).trans_eq (cast_toNat_of_lt_aleph0 (toNat_ne_zero.mp h).2))

lemma exists_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ f : Fin n → M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_finrank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

variable [Module.Finite R M] [StrongRankCondition R] in
theorem Module.Finite.not_linearIndependent_of_infinite {ι : Type*} [Infinite ι]
    (v : ι → M) : ¬LinearIndependent R v := mt LinearIndependent.finite <| @not_finite _ _

section
variable [NoZeroSMulDivisors R M]

theorem iSupIndep.subtype_ne_bot_le_rank [Nontrivial R]
    {V : ι → Submodule R M} (hV : iSupIndep V) :
    Cardinal.lift.{v} #{ i : ι // V i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank R M) := by
  set I := { i : ι // V i ≠ ⊥ }
  have hI : ∀ i : I, ∃ v ∈ V i, v ≠ (0 : M) := by
    intro i
    rw [← Submodule.ne_bot_iff]
    exact i.prop
  choose v hvV hv using hI
  have : LinearIndependent R v := (hV.comp Subtype.coe_injective).linearIndependent _ hvV hv
  exact this.cardinal_lift_le_rank

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.Independent.subtype_ne_bot_le_rank := iSupIndep.subtype_ne_bot_le_rank

variable [Module.Finite R M] [StrongRankCondition R]

theorem iSupIndep.subtype_ne_bot_le_finrank_aux
    {p : ι → Submodule R M} (hp : iSupIndep p) :
    #{ i // p i ≠ ⊥ } ≤ (finrank R M : Cardinal.{w}) := by
  suffices Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{v} (finrank R M : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc
    Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank R M) :=
      hp.subtype_ne_bot_le_rank
    _ = Cardinal.lift.{w} (finrank R M : Cardinal.{v}) := by rw [finrank_eq_rank]
    _ = Cardinal.lift.{v} (finrank R M : Cardinal.{w}) := by simp

/-- If `p` is an independent family of submodules of a `R`-finite module `M`, then the
number of nontrivial subspaces in the family `p` is finite. -/
noncomputable def iSupIndep.fintypeNeBotOfFiniteDimensional
    {p : ι → Submodule R M} (hp : iSupIndep p) :
    Fintype { i : ι // p i ≠ ⊥ } := by
  suffices #{ i // p i ≠ ⊥ } < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph0_iff_fintype] at this
    exact this.some
  refine lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux ?_
  simp [Cardinal.nat_lt_aleph0]

/-- If `p` is an independent family of submodules of a `R`-finite module `M`, then the
number of nontrivial subspaces in the family `p` is bounded above by the dimension of `M`.

Note that the `Fintype` hypothesis required here can be provided by
`iSupIndep.fintypeNeBotOfFiniteDimensional`. -/
theorem iSupIndep.subtype_ne_bot_le_finrank
    {p : ι → Submodule R M} (hp : iSupIndep p) [Fintype { i // p i ≠ ⊥ }] :
    Fintype.card { i // p i ≠ ⊥ } ≤ finrank R M := by simpa using hp.subtype_ne_bot_le_finrank_aux

end

variable [Module.Finite R M] [StrongRankCondition R]

section

open Finset

/-- If a finset has cardinality larger than the rank of a module,
then there is a nontrivial linear relation amongst its elements. -/
theorem Module.exists_nontrivial_relation_of_finrank_lt_card {t : Finset M}
    (h : finrank R M < t.card) : ∃ f : M → R, ∑ e ∈ t, f e • e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  obtain ⟨g, sum, z, nonzero⟩ := Fintype.not_linearIndependent_iff.mp
    (mt LinearIndependent.finset_card_le_finrank h.not_ge)
  refine ⟨Subtype.val.extend g 0, ?_, z, z.2, by rwa [Subtype.val_injective.extend_apply]⟩
  rw [← Finset.sum_finset_coe]; convert sum; apply Subtype.val_injective.extend_apply

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

end

end Finite

section FinrankZero

section
variable [Nontrivial R]

/-- A (finite dimensional) space that is a subsingleton has zero `finrank`. -/
@[nontriviality]
theorem Module.finrank_zero_of_subsingleton [Subsingleton M] :
    finrank R M = 0 := by
  rw [finrank, rank_subsingleton', map_zero]

lemma LinearIndependent.finrank_eq_zero_of_infinite {ι} [Infinite ι] {v : ι → M}
    (hv : LinearIndependent R v) : finrank R M = 0 := toNat_eq_zero.mpr <| .inr hv.aleph0_le_rank

section
variable [NoZeroSMulDivisors R M]

/-- A finite dimensional space is nontrivial if it has positive `finrank`. -/
theorem Module.nontrivial_of_finrank_pos (h : 0 < finrank R M) : Nontrivial M :=
  rank_pos_iff_nontrivial.mp (lt_rank_of_lt_finrank h)

/-- A finite dimensional space is nontrivial if it has `finrank` equal to the successor of a
natural number. -/
theorem Module.nontrivial_of_finrank_eq_succ {n : ℕ}
    (hn : finrank R M = n.succ) : Nontrivial M :=
  nontrivial_of_finrank_pos (R := R) (by rw [hn]; exact n.succ_pos)

end

variable (R M)

@[simp]
theorem finrank_bot : finrank R (⊥ : Submodule R M) = 0 :=
  finrank_eq_of_rank_eq (rank_bot _ _)

end

section StrongRankCondition

variable [StrongRankCondition R] [Module.Finite R M]

/-- A finite rank torsion-free module has positive `finrank` iff it has a nonzero element. -/
theorem Module.finrank_pos_iff_exists_ne_zero [NoZeroSMulDivisors R M] :
    0 < finrank R M ↔ ∃ x : M, x ≠ 0 := by
  rw [← @rank_pos_iff_exists_ne_zero R M, ← finrank_eq_rank]
  norm_cast

/-- An `R`-finite torsion-free module has positive `finrank` iff it is nontrivial. -/
theorem Module.finrank_pos_iff [NoZeroSMulDivisors R M] :
    0 < finrank R M ↔ Nontrivial M := by
  rw [← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank]
  norm_cast

/-- A nontrivial finite dimensional space has positive `finrank`. -/
theorem Module.finrank_pos [NoZeroSMulDivisors R M] [h : Nontrivial M] :
    0 < finrank R M :=
  finrank_pos_iff.mpr h

/-- See `Module.finrank_zero_iff`
  for the stronger version with `NoZeroSMulDivisors R M`. -/
theorem Module.finrank_eq_zero_iff :
    finrank R M = 0 ↔ ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x = 0 := by
  rw [← rank_eq_zero_iff (R := R), ← finrank_eq_rank]
  norm_cast

/-- A finite dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `rank_zero_iff`. -/
theorem Module.finrank_zero_iff [NoZeroSMulDivisors R M] :
    finrank R M = 0 ↔ Subsingleton M := by
  rw [← rank_zero_iff (R := R), ← finrank_eq_rank]
  norm_cast

/-- Similar to `rank_quotient_add_rank_le` but for `finrank` and a finite `M`. -/
lemma Module.finrank_quotient_add_finrank_le (N : Submodule R M) :
    finrank R (M ⧸ N) + finrank R N ≤ finrank R M := by
  haveI := nontrivial_of_invariantBasisNumber R
  have := rank_quotient_add_rank_le N
  rw [← finrank_eq_rank R M, ← finrank_eq_rank R, ← N.finrank_eq_rank] at this
  exact mod_cast this

end StrongRankCondition

theorem Module.finrank_eq_zero_of_rank_eq_zero (h : Module.rank R M = 0) :
    finrank R M = 0 := by
  delta finrank
  rw [h, zero_toNat]

theorem Submodule.bot_eq_top_of_rank_eq_zero [NoZeroSMulDivisors R M] (h : Module.rank R M = 0) :
    (⊥ : Submodule R M) = ⊤ := by
  nontriviality R
  rw [rank_zero_iff] at h
  subsingleton

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

@[simp]
theorem Submodule.finrank_eq_zero [StrongRankCondition R] [NoZeroSMulDivisors R M]
    {S : Submodule R M} [Module.Finite R S] :
    finrank R S = 0 ↔ S = ⊥ := by
  rw [← Submodule.rank_eq_zero, ← finrank_eq_rank, ← @Nat.cast_zero Cardinal, Nat.cast_inj]

@[simp]
lemma Submodule.one_le_finrank_iff [StrongRankCondition R] [NoZeroSMulDivisors R M]
    {S : Submodule R M} [Module.Finite R S] :
    1 ≤ finrank R S ↔ S ≠ ⊥ := by
  simp [← not_iff_not]

@[simp]
theorem Set.finrank_empty [Nontrivial R] :
    Set.finrank R (∅ : Set M) = 0 := by
  rw [Set.finrank, span_empty, finrank_bot]

variable [Module.Free R M]

theorem finrank_eq_zero_of_basis_imp_not_finite
    (h : ∀ s : Set M, Basis.{v} (s : Set M) R M → ¬s.Finite) : finrank R M = 0 := by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    exact (h ∅ ⟨LinearEquiv.ofSubsingleton _ _⟩ Set.finite_empty).elim
  obtain ⟨_, ⟨b⟩⟩ := (Module.free_iff_set R M).mp ‹_›
  have := Set.Infinite.to_subtype (h _ b)
  exact b.linearIndependent.finrank_eq_zero_of_infinite

theorem finrank_eq_zero_of_basis_imp_false (h : ∀ s : Finset M, Basis.{v} (s : Set M) R M → False) :
    finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs =>
    h hs.toFinset
      (by
        convert b
        simp)

theorem finrank_eq_zero_of_not_exists_basis
    (h : ¬∃ s : Finset M, Nonempty (Basis (s : Set M) R M)) : finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

theorem finrank_eq_zero_of_not_exists_basis_finite
    (h : ¬∃ (s : Set M) (_ : Basis.{v} (s : Set M) R M), s.Finite) : finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs => h ⟨s, b, hs⟩

theorem finrank_eq_zero_of_not_exists_basis_finset (h : ¬∃ s : Finset M, Nonempty (Basis s R M)) :
    finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

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

end RankOne

namespace Module
variable {ι : Type*}

@[simp] lemma finite_finsupp_iff :
    Module.Finite R (ι →₀ M) ↔ IsEmpty ι ∨ Subsingleton M ∨ Module.Finite R M ∧ Finite ι where
  mp := by
    simp only [or_iff_not_imp_left, not_subsingleton_iff_nontrivial, not_isEmpty_iff]
    rintro h ⟨i⟩ _
    obtain ⟨s, hs⟩ := id h
    exact ⟨.of_surjective (Finsupp.lapply (R := R) (M := M) i) (Finsupp.apply_surjective i),
       finite_of_span_finite_eq_top_finsupp s.finite_toSet hs⟩
  mpr
  | .inl _ => inferInstance
  | .inr <| .inl h => inferInstance
  | .inr <| .inr h => by cases h; infer_instance

@[simp high]
lemma finite_finsupp_self_iff : Module.Finite R (ι →₀ R) ↔ Subsingleton R ∨ Finite ι := by
  simp only [finite_finsupp_iff, Finite.self, true_and, or_iff_right_iff_imp]
  exact fun _ ↦ .inr inferInstance

end Module
