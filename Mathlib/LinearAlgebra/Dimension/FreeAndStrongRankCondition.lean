/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!

# Some results on free modules over rings satisfying strong rank condition

This file contains some results on free modules over rings satisfying strong rank condition.
Most of them are generalized from the same result assuming the base ring being division ring,
and are moved from the files `Mathlib/LinearAlgebra/Dimension/DivisionRing.lean`
and `Mathlib/LinearAlgebra/FiniteDimensional.lean`.

-/

open Cardinal Submodule Set FiniteDimensional

universe u v

section Module

variable {K : Type u} {V : Type v} [Ring K] [StrongRankCondition K] [AddCommGroup V] [Module K V]

/-- The `ι` indexed basis on `V`, where `ι` is an empty type and `V` is zero-dimensional.

See also `FiniteDimensional.finBasis`.
-/
noncomputable def Basis.ofRankEqZero [Module.Free K V] {ι : Type*} [IsEmpty ι]
    (hV : Module.rank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := by
    obtain ⟨_, b⟩ := Module.Free.exists_basis (R := K) (M := V)
    haveI := mk_eq_zero_iff.1 (hV ▸ b.mk_eq_rank'')
    exact b.repr.toEquiv.subsingleton
  Basis.empty _
#align basis.of_rank_eq_zero Basis.ofRankEqZero

@[simp]
theorem Basis.ofRankEqZero_apply [Module.Free K V] {ι : Type*} [IsEmpty ι]
    (hV : Module.rank K V = 0) (i : ι) : Basis.ofRankEqZero hV i = 0 := rfl
#align basis.of_rank_eq_zero_apply Basis.ofRankEqZero_apply

theorem le_rank_iff_exists_linearIndependent [Module.Free K V] {c : Cardinal} :
    c ≤ Module.rank K V ↔ ∃ s : Set V, #s = c ∧ LinearIndependent K ((↑) : s → V) := by
  haveI := nontrivial_of_invariantBasisNumber K
  constructor
  · intro h
    obtain ⟨κ, t'⟩ := Module.Free.exists_basis (R := K) (M := V)
    let t := t'.reindexRange
    have : LinearIndependent K ((↑) : Set.range t' → V) := by
      convert t.linearIndependent
      ext; exact (Basis.reindexRange_apply _ _).symm
    rw [← t.mk_eq_rank'', le_mk_iff_exists_subset] at h
    rcases h with ⟨s, hst, hsc⟩
    exact ⟨s, hsc, this.mono hst⟩
  · rintro ⟨s, rfl, si⟩
    exact si.cardinal_le_rank
#align le_rank_iff_exists_linear_independent le_rank_iff_exists_linearIndependent

theorem le_rank_iff_exists_linearIndependent_finset
    [Module.Free K V] {n : ℕ} : ↑n ≤ Module.rank K V ↔
    ∃ s : Finset V, s.card = n ∧ LinearIndependent K ((↑) : ↥(s : Set V) → V) := by
  simp only [le_rank_iff_exists_linearIndependent, mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩
#align le_rank_iff_exists_linear_independent_finset le_rank_iff_exists_linearIndependent_finset

/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
theorem rank_le_one_iff [Module.Free K V] :
    Module.rank K V ≤ 1 ↔ ∃ v₀ : V, ∀ v, ∃ r : K, r • v₀ = v := by
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := V)
  constructor
  · intro hd
    rw [← b.mk_eq_rank'', le_one_iff_subsingleton] at hd
    rcases isEmpty_or_nonempty κ with hb | ⟨⟨i⟩⟩
    · use 0
      have h' : ∀ v : V, v = 0 := by
        simpa [range_eq_empty, Submodule.eq_bot_iff] using b.span_eq.symm
      intro v
      simp [h' v]
    · use b i
      have h' : (K ∙ b i) = ⊤ :=
        (subsingleton_range b).eq_singleton_of_mem (mem_range_self i) ▸ b.span_eq
      intro v
      have hv : v ∈ (⊤ : Submodule K V) := mem_top
      rwa [← h', mem_span_singleton] at hv
  · rintro ⟨v₀, hv₀⟩
    have h : (K ∙ v₀) = ⊤ := by
      ext
      simp [mem_span_singleton, hv₀]
    rw [← rank_top, ← h]
    refine (rank_span_le _).trans_eq ?_
    simp
#align rank_le_one_iff rank_le_one_iff

/-- A vector space has dimension `1` if and only if there is a
single non-zero vector of which all vectors are multiples. -/
theorem rank_eq_one_iff [Module.Free K V] :
    Module.rank K V = 1 ↔ ∃ v₀ : V, v₀ ≠ 0 ∧ ∀ v, ∃ r : K, r • v₀ = v := by
  haveI := nontrivial_of_invariantBasisNumber K
  refine ⟨fun h ↦ ?_, fun ⟨v₀, h, hv⟩ ↦ (rank_le_one_iff.2 ⟨v₀, hv⟩).antisymm ?_⟩
  · obtain ⟨v₀, hv⟩ := rank_le_one_iff.1 h.le
    refine ⟨v₀, fun hzero ↦ ?_, hv⟩
    simp_rw [hzero, smul_zero, exists_const] at hv
    haveI : Subsingleton V := .intro fun _ _ ↦ by simp_rw [← hv]
    exact one_ne_zero (h ▸ rank_subsingleton' K V)
  · by_contra H
    rw [not_le, lt_one_iff_zero] at H
    obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := V)
    haveI := mk_eq_zero_iff.1 (H ▸ b.mk_eq_rank'')
    haveI := b.repr.toEquiv.subsingleton
    exact h (Subsingleton.elim _ _)

/-- A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span. -/
theorem rank_submodule_le_one_iff (s : Submodule K V) [Module.Free K s] :
    Module.rank K s ≤ 1 ↔ ∃ v₀ ∈ s, s ≤ K ∙ v₀ := by
  simp_rw [rank_le_one_iff, le_span_singleton_iff]
  constructor
  · rintro ⟨⟨v₀, hv₀⟩, h⟩
    use v₀, hv₀
    intro v hv
    obtain ⟨r, hr⟩ := h ⟨v, hv⟩
    use r
    rwa [Subtype.ext_iff, coe_smul] at hr
  · rintro ⟨v₀, hv₀, h⟩
    use ⟨v₀, hv₀⟩
    rintro ⟨v, hv⟩
    obtain ⟨r, hr⟩ := h v hv
    use r
    rwa [Subtype.ext_iff, coe_smul]
#align rank_submodule_le_one_iff rank_submodule_le_one_iff

/-- A submodule has dimension `1` if and only if there is a
single non-zero vector in the submodule such that the submodule is contained in
its span. -/
theorem rank_submodule_eq_one_iff (s : Submodule K V) [Module.Free K s] :
    Module.rank K s = 1 ↔ ∃ v₀ ∈ s, v₀ ≠ 0 ∧ s ≤ K ∙ v₀ := by
  simp_rw [rank_eq_one_iff, le_span_singleton_iff]
  refine ⟨fun ⟨⟨v₀, hv₀⟩, H, h⟩ ↦ ⟨v₀, hv₀, fun h' ↦ by simp [h'] at H, fun v hv ↦ ?_⟩,
    fun ⟨v₀, hv₀, H, h⟩ ↦ ⟨⟨v₀, hv₀⟩, fun h' ↦ H (by simpa using h'), fun ⟨v, hv⟩ ↦ ?_⟩⟩
  · obtain ⟨r, hr⟩ := h ⟨v, hv⟩
    exact ⟨r, by rwa [Subtype.ext_iff, coe_smul] at hr⟩
  · obtain ⟨r, hr⟩ := h v hv
    exact ⟨r, by rwa [Subtype.ext_iff, coe_smul]⟩

/-- A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span. -/
theorem rank_submodule_le_one_iff' (s : Submodule K V) [Module.Free K s] :
    Module.rank K s ≤ 1 ↔ ∃ v₀, s ≤ K ∙ v₀ := by
  haveI := nontrivial_of_invariantBasisNumber K
  constructor
  · rw [rank_submodule_le_one_iff]
    rintro ⟨v₀, _, h⟩
    exact ⟨v₀, h⟩
  · rintro ⟨v₀, h⟩
    obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := s)
    simpa [b.mk_eq_rank''] using b.linearIndependent.map' _ (ker_inclusion _ _ h)
      |>.cardinal_le_rank.trans (rank_span_le {v₀})
#align rank_submodule_le_one_iff' rank_submodule_le_one_iff'

theorem Submodule.rank_le_one_iff_isPrincipal (W : Submodule K V) [Module.Free K W] :
    Module.rank K W ≤ 1 ↔ W.IsPrincipal := by
  simp only [rank_le_one_iff, Submodule.isPrincipal_iff, le_antisymm_iff, le_span_singleton_iff,
    span_singleton_le_iff_mem]
  constructor
  · rintro ⟨⟨m, hm⟩, hm'⟩
    choose f hf using hm'
    exact ⟨m, ⟨fun v hv => ⟨f ⟨v, hv⟩, congr_arg ((↑) : W → V) (hf ⟨v, hv⟩)⟩, hm⟩⟩
  · rintro ⟨a, ⟨h, ha⟩⟩
    choose f hf using h
    exact ⟨⟨a, ha⟩, fun v => ⟨f v.1 v.2, Subtype.ext (hf v.1 v.2)⟩⟩
#align submodule.rank_le_one_iff_is_principal Submodule.rank_le_one_iff_isPrincipal

theorem Module.rank_le_one_iff_top_isPrincipal [Module.Free K V] :
    Module.rank K V ≤ 1 ↔ (⊤ : Submodule K V).IsPrincipal := by
  haveI := Module.Free.of_equiv (topEquiv (R := K) (M := V)).symm
  rw [← Submodule.rank_le_one_iff_isPrincipal, rank_top]
#align module.rank_le_one_iff_top_is_principal Module.rank_le_one_iff_top_isPrincipal

/-- A module has dimension 1 iff there is some `v : V` so `{v}` is a basis.
-/
theorem finrank_eq_one_iff [Module.Free K V] (ι : Type*) [Unique ι] :
    finrank K V = 1 ↔ Nonempty (Basis ι K V) := by
  constructor
  · intro h
    exact ⟨basisUnique ι h⟩
  · rintro ⟨b⟩
    simpa using finrank_eq_card_basis b
#align finrank_eq_one_iff finrank_eq_one_iff

/-- A module has dimension 1 iff there is some nonzero `v : V` so every vector is a multiple of `v`.
-/
theorem finrank_eq_one_iff' [Module.Free K V] :
    finrank K V = 1 ↔ ∃ v ≠ 0, ∀ w : V, ∃ c : K, c • v = w := by
  rw [← rank_eq_one_iff]
  exact toNat_eq_iff one_ne_zero
#align finrank_eq_one_iff' finrank_eq_one_iff'

-- Not sure why this aren't found automatically.
/-- A finite dimensional module has dimension at most 1 iff
there is some `v : V` so every vector is a multiple of `v`.
-/
theorem finrank_le_one_iff [Module.Free K V] [Module.Finite K V] :
    finrank K V ≤ 1 ↔ ∃ v : V, ∀ w : V, ∃ c : K, c • v = w := by
  rw [← rank_le_one_iff, ← finrank_eq_rank, ← natCast_le, Nat.cast_one]
#align finrank_le_one_iff finrank_le_one_iff

theorem Submodule.finrank_le_one_iff_isPrincipal
    (W : Submodule K V) [Module.Free K W] [Module.Finite K W] :
    finrank K W ≤ 1 ↔ W.IsPrincipal := by
  rw [← W.rank_le_one_iff_isPrincipal, ← finrank_eq_rank, ← natCast_le, Nat.cast_one]
#align submodule.finrank_le_one_iff_is_principal Submodule.finrank_le_one_iff_isPrincipal

theorem Module.finrank_le_one_iff_top_isPrincipal [Module.Free K V] [Module.Finite K V] :
    finrank K V ≤ 1 ↔ (⊤ : Submodule K V).IsPrincipal := by
  rw [← Module.rank_le_one_iff_top_isPrincipal, ← finrank_eq_rank, ← natCast_le, Nat.cast_one]
#align module.finrank_le_one_iff_top_is_principal Module.finrank_le_one_iff_top_isPrincipal

variable (K V) in
theorem lift_cardinal_mk_eq_lift_cardinal_mk_field_pow_lift_rank [Module.Free K V]
    [Module.Finite K V] : lift.{u} #V = lift.{v} #K ^ lift.{u} (Module.rank K V) := by
  haveI := nontrivial_of_invariantBasisNumber K
  obtain ⟨s, hs⟩ := Module.Free.exists_basis (R := K) (M := V)
  -- `Module.Finite.finite_basis` is in a much later file, so we copy its proof to here
  haveI : Finite s := by
    obtain ⟨t, ht⟩ := ‹Module.Finite K V›
    exact basis_finite_of_finite_spans _ t.finite_toSet ht hs
  have := lift_mk_eq'.2 ⟨hs.repr.toEquiv⟩
  rwa [Finsupp.equivFunOnFinite.cardinal_eq, mk_arrow, hs.mk_eq_rank'', lift_power, lift_lift,
    lift_lift, lift_umax'] at this

theorem cardinal_mk_eq_cardinal_mk_field_pow_rank (K V : Type u) [Ring K] [StrongRankCondition K]
    [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V] :
    #V = #K ^ Module.rank K V := by
  simpa using lift_cardinal_mk_eq_lift_cardinal_mk_field_pow_lift_rank K V
#align cardinal_mk_eq_cardinal_mk_field_pow_rank cardinal_mk_eq_cardinal_mk_field_pow_rank

variable (K V) in
theorem cardinal_lt_aleph0_of_finiteDimensional [Finite K] [Module.Free K V] [Module.Finite K V] :
    #V < ℵ₀ := by
  rw [← lift_lt_aleph0.{v, u}, lift_cardinal_mk_eq_lift_cardinal_mk_field_pow_lift_rank K V]
  exact power_lt_aleph0 (lift_lt_aleph0.2 (lt_aleph0_of_finite K))
    (lift_lt_aleph0.2 (rank_lt_aleph0 K V))
#align cardinal_lt_aleph_0_of_finite_dimensional cardinal_lt_aleph0_of_finiteDimensional

end Module

namespace Subalgebra

variable {F E : Type*} [CommRing F] [StrongRankCondition F] [Ring E] [Algebra F E]
  {S : Subalgebra F E}

theorem eq_bot_of_rank_le_one (h : Module.rank F S ≤ 1) [Module.Free F S] : S = ⊥ := by
  nontriviality E
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := F) (M := S)
  by_cases h1 : Module.rank F S = 1
  · refine bot_unique fun x hx ↦ Algebra.mem_bot.2 ?_
    rw [← b.mk_eq_rank'', eq_one_iff_unique, ← unique_iff_subsingleton_and_nonempty] at h1
    obtain ⟨h1⟩ := h1
    obtain ⟨y, hy⟩ := (bijective_algebraMap_of_linearEquiv (b.repr ≪≫ₗ
      Finsupp.LinearEquiv.finsuppUnique _ _ _).symm).surjective ⟨x, hx⟩
    exact ⟨y, congr(Subtype.val $(hy))⟩
  haveI := mk_eq_zero_iff.1 (b.mk_eq_rank''.symm ▸ lt_one_iff_zero.1 (h.lt_of_ne h1))
  haveI := b.repr.toEquiv.subsingleton
  exact False.elim <| one_ne_zero congr(S.val $(Subsingleton.elim 1 0))
#align subalgebra.eq_bot_of_rank_le_one Subalgebra.eq_bot_of_rank_le_one

theorem eq_bot_of_finrank_one (h : finrank F S = 1) [Module.Free F S] : S = ⊥ := by
  refine Subalgebra.eq_bot_of_rank_le_one ?_
  rw [finrank, toNat_eq_one] at h
  rw [h]
#align subalgebra.eq_bot_of_finrank_one Subalgebra.eq_bot_of_finrank_one

@[simp]
theorem rank_eq_one_iff [Nontrivial E] [Module.Free F S] : Module.rank F S = 1 ↔ S = ⊥ := by
  refine ⟨fun h ↦ Subalgebra.eq_bot_of_rank_le_one h.le, ?_⟩
  rintro rfl
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := F) (M := (⊥ : Subalgebra F E))
  refine le_antisymm ?_ ?_
  · have := lift_rank_range_le (Algebra.linearMap F E)
    rwa [← one_eq_range, rank_self, lift_one, lift_le_one_iff] at this
  · by_contra H
    rw [not_le, lt_one_iff_zero] at H
    haveI := mk_eq_zero_iff.1 (H ▸ b.mk_eq_rank'')
    haveI := b.repr.toEquiv.subsingleton
    exact one_ne_zero congr((⊥ : Subalgebra F E).val $(Subsingleton.elim 1 0))
#align subalgebra.rank_eq_one_iff Subalgebra.rank_eq_one_iff

@[simp]
theorem finrank_eq_one_iff [Nontrivial E] [Module.Free F S] : finrank F S = 1 ↔ S = ⊥ := by
  rw [← Subalgebra.rank_eq_one_iff]
  exact toNat_eq_iff one_ne_zero
#align subalgebra.finrank_eq_one_iff Subalgebra.finrank_eq_one_iff

theorem bot_eq_top_iff_rank_eq_one [Nontrivial E] [Module.Free F E] :
    (⊥ : Subalgebra F E) = ⊤ ↔ Module.rank F E = 1 := by
  haveI := Module.Free.of_equiv (Subalgebra.topEquiv (R := F) (A := E)).toLinearEquiv.symm
  -- Porting note: removed `subalgebra_top_rank_eq_submodule_top_rank`
  rw [← rank_top, Subalgebra.rank_eq_one_iff, eq_comm]
#align subalgebra.bot_eq_top_iff_rank_eq_one Subalgebra.bot_eq_top_iff_rank_eq_one

theorem bot_eq_top_iff_finrank_eq_one [Nontrivial E] [Module.Free F E] :
    (⊥ : Subalgebra F E) = ⊤ ↔ finrank F E = 1 := by
  haveI := Module.Free.of_equiv (Subalgebra.topEquiv (R := F) (A := E)).toLinearEquiv.symm
  rw [← finrank_top, ← subalgebra_top_finrank_eq_submodule_top_finrank,
    Subalgebra.finrank_eq_one_iff, eq_comm]
#align subalgebra.bot_eq_top_iff_finrank_eq_one Subalgebra.bot_eq_top_iff_finrank_eq_one

alias ⟨_, bot_eq_top_of_rank_eq_one⟩ := bot_eq_top_iff_rank_eq_one
#align subalgebra.bot_eq_top_of_rank_eq_one Subalgebra.bot_eq_top_of_rank_eq_one

alias ⟨_, bot_eq_top_of_finrank_eq_one⟩ := bot_eq_top_iff_finrank_eq_one
#align subalgebra.bot_eq_top_of_finrank_eq_one Subalgebra.bot_eq_top_of_finrank_eq_one

attribute [simp] bot_eq_top_of_finrank_eq_one bot_eq_top_of_rank_eq_one

end Subalgebra
