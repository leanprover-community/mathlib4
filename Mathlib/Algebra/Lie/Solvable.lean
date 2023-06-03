/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module algebra.lie.solvable
! leanprover-community/mathlib commit a50170a88a47570ed186b809ca754110590f9476
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.IdealOperations
import Mathlib.Order.Hom.Basic

/-!
# Solvable Lie algebras

Like groups, Lie algebras admit a natural concept of solvability. We define this here via the
derived series and prove some related results. We also define the radical of a Lie algebra and
prove that it is solvable when the Lie algebra is Noetherian.

## Main definitions

  * `lie_algebra.derived_series_of_ideal`
  * `lie_algebra.derived_series`
  * `lie_algebra.is_solvable`
  * `lie_algebra.is_solvable_add`
  * `lie_algebra.radical`
  * `lie_algebra.radical_is_solvable`
  * `lie_algebra.derived_length_of_ideal`
  * `lie_algebra.derived_length`
  * `lie_algebra.derived_abelian_of_ideal`

## Tags

lie algebra, derived series, derived length, solvable, radical
-/


universe u v w w₁ w₂

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

namespace LieAlgebra

/-- A generalisation of the derived series of a Lie algebra, whose zeroth term is a specified ideal.

It can be more convenient to work with this generalisation when considering the derived series of
an ideal since it provides a type-theoretic expression of the fact that the terms of the ideal's
derived series are also ideals of the enclosing algebra.

See also `lie_ideal.derived_series_eq_derived_series_of_ideal_comap` and
`lie_ideal.derived_series_eq_derived_series_of_ideal_map` below. -/
def derivedSeriesOfIdeal (k : ℕ) : LieIdeal R L → LieIdeal R L :=
  (fun I => ⁅I, I⁆)^[k]
#align lie_algebra.derived_series_of_ideal LieAlgebra.derivedSeriesOfIdeal

@[simp]
theorem derivedSeriesOfIdeal_zero : derivedSeriesOfIdeal R L 0 I = I :=
  rfl
#align lie_algebra.derived_series_of_ideal_zero LieAlgebra.derivedSeriesOfIdeal_zero

@[simp]
theorem derivedSeriesOfIdeal_succ (k : ℕ) :
    derivedSeriesOfIdeal R L (k + 1) I =
      ⁅derivedSeriesOfIdeal R L k I, derivedSeriesOfIdeal R L k I⁆ :=
  Function.iterate_succ_apply' (fun I => ⁅I, I⁆) k I
#align lie_algebra.derived_series_of_ideal_succ LieAlgebra.derivedSeriesOfIdeal_succ

/-- The derived series of Lie ideals of a Lie algebra. -/
abbrev derivedSeries (k : ℕ) : LieIdeal R L :=
  derivedSeriesOfIdeal R L k ⊤
#align lie_algebra.derived_series LieAlgebra.derivedSeries

theorem derivedSeries_def (k : ℕ) : derivedSeries R L k = derivedSeriesOfIdeal R L k ⊤ :=
  rfl
#align lie_algebra.derived_series_def LieAlgebra.derivedSeries_def

variable {R L}

-- mathport name: exprD
local notation "D" => derivedSeriesOfIdeal R L

theorem derivedSeriesOfIdeal_add (k l : ℕ) : D (k + l) I = D k (D l I) := by
  induction' k with k ih
  · rw [zero_add, derived_series_of_ideal_zero]
  · rw [Nat.succ_add k l, derived_series_of_ideal_succ, derived_series_of_ideal_succ, ih]
#align lie_algebra.derived_series_of_ideal_add LieAlgebra.derivedSeriesOfIdeal_add

@[mono]
theorem derivedSeriesOfIdeal_le {I J : LieIdeal R L} {k l : ℕ} (h₁ : I ≤ J) (h₂ : l ≤ k) :
    D k I ≤ D l J := by
  revert l; induction' k with k ih <;> intro l h₂
  · rw [le_zero_iff] at h₂ ; rw [h₂, derived_series_of_ideal_zero]; exact h₁
  · have h : l = k.succ ∨ l ≤ k := by rwa [le_iff_eq_or_lt, Nat.lt_succ_iff] at h₂
    cases h
    · rw [h, derived_series_of_ideal_succ, derived_series_of_ideal_succ]
      exact LieSubmodule.mono_lie _ _ _ _ (ih (le_refl k)) (ih (le_refl k))
    · rw [derived_series_of_ideal_succ]; exact le_trans (LieSubmodule.lie_le_left _ _) (ih h)
#align lie_algebra.derived_series_of_ideal_le LieAlgebra.derivedSeriesOfIdeal_le

theorem derivedSeriesOfIdeal_succ_le (k : ℕ) : D (k + 1) I ≤ D k I :=
  derivedSeriesOfIdeal_le (le_refl I) k.le_succ
#align lie_algebra.derived_series_of_ideal_succ_le LieAlgebra.derivedSeriesOfIdeal_succ_le

theorem derivedSeriesOfIdeal_le_self (k : ℕ) : D k I ≤ I :=
  derivedSeriesOfIdeal_le (le_refl I) (zero_le k)
#align lie_algebra.derived_series_of_ideal_le_self LieAlgebra.derivedSeriesOfIdeal_le_self

theorem derivedSeriesOfIdeal_mono {I J : LieIdeal R L} (h : I ≤ J) (k : ℕ) : D k I ≤ D k J :=
  derivedSeriesOfIdeal_le h (le_refl k)
#align lie_algebra.derived_series_of_ideal_mono LieAlgebra.derivedSeriesOfIdeal_mono

theorem derivedSeriesOfIdeal_antitone {k l : ℕ} (h : l ≤ k) : D k I ≤ D l I :=
  derivedSeriesOfIdeal_le (le_refl I) h
#align lie_algebra.derived_series_of_ideal_antitone LieAlgebra.derivedSeriesOfIdeal_antitone

theorem derivedSeriesOfIdeal_add_le_add (J : LieIdeal R L) (k l : ℕ) :
    D (k + l) (I + J) ≤ D k I + D l J := by
  let D₁ : LieIdeal R L →o LieIdeal R L :=
    { toFun := fun I => ⁅I, I⁆
      monotone' := fun I J h => LieSubmodule.mono_lie I J I J h h }
  have h₁ : ∀ I J : LieIdeal R L, D₁ (I ⊔ J) ≤ D₁ I ⊔ J := by
    simp [LieSubmodule.lie_le_right, LieSubmodule.lie_le_left, le_sup_of_le_right]
  rw [← D₁.iterate_sup_le_sup_iff] at h₁
  exact h₁ k l I J
#align lie_algebra.derived_series_of_ideal_add_le_add LieAlgebra.derivedSeriesOfIdeal_add_le_add

theorem derivedSeries_of_bot_eq_bot (k : ℕ) : derivedSeriesOfIdeal R L k ⊥ = ⊥ := by
  rw [eq_bot_iff]; exact derived_series_of_ideal_le_self ⊥ k
#align lie_algebra.derived_series_of_bot_eq_bot LieAlgebra.derivedSeries_of_bot_eq_bot

theorem abelian_iff_derived_one_eq_bot : IsLieAbelian I ↔ derivedSeriesOfIdeal R L 1 I = ⊥ := by
  rw [derived_series_of_ideal_succ, derived_series_of_ideal_zero,
    LieSubmodule.lie_abelian_iff_lie_self_eq_bot]
#align lie_algebra.abelian_iff_derived_one_eq_bot LieAlgebra.abelian_iff_derived_one_eq_bot

theorem abelian_iff_derived_succ_eq_bot (I : LieIdeal R L) (k : ℕ) :
    IsLieAbelian (derivedSeriesOfIdeal R L k I) ↔ derivedSeriesOfIdeal R L (k + 1) I = ⊥ := by
  rw [add_comm, derived_series_of_ideal_add I 1 k, abelian_iff_derived_one_eq_bot]
#align lie_algebra.abelian_iff_derived_succ_eq_bot LieAlgebra.abelian_iff_derived_succ_eq_bot

end LieAlgebra

namespace LieIdeal

open LieAlgebra

variable {R L}

theorem derivedSeries_eq_derivedSeriesOfIdeal_comap (k : ℕ) :
    derivedSeries R I k = (derivedSeriesOfIdeal R L k I).comap I.incl := by
  induction' k with k ih
  · simp only [derived_series_def, comap_incl_self, derived_series_of_ideal_zero]
  · simp only [derived_series_def, derived_series_of_ideal_succ] at ih ⊢; rw [ih]
    exact
      comap_bracket_incl_of_le I (derived_series_of_ideal_le_self I k)
        (derived_series_of_ideal_le_self I k)
#align lie_ideal.derived_series_eq_derived_series_of_ideal_comap LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap

theorem derivedSeries_eq_derivedSeriesOfIdeal_map (k : ℕ) :
    (derivedSeries R I k).map I.incl = derivedSeriesOfIdeal R L k I := by
  rw [derived_series_eq_derived_series_of_ideal_comap, map_comap_incl, inf_eq_right]
  apply derived_series_of_ideal_le_self
#align lie_ideal.derived_series_eq_derived_series_of_ideal_map LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_map

theorem derivedSeries_eq_bot_iff (k : ℕ) :
    derivedSeries R I k = ⊥ ↔ derivedSeriesOfIdeal R L k I = ⊥ := by
  rw [← derived_series_eq_derived_series_of_ideal_map, map_eq_bot_iff, ker_incl, eq_bot_iff]
#align lie_ideal.derived_series_eq_bot_iff LieIdeal.derivedSeries_eq_bot_iff

theorem derivedSeries_add_eq_bot {k l : ℕ} {I J : LieIdeal R L} (hI : derivedSeries R I k = ⊥)
    (hJ : derivedSeries R J l = ⊥) : derivedSeries R (↥(I + J)) (k + l) = ⊥ := by
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hI hJ ⊢
  rw [← le_bot_iff]
  let D := derived_series_of_ideal R L; change D k I = ⊥ at hI ; change D l J = ⊥ at hJ
  calc
    D (k + l) (I + J) ≤ D k I + D l J := derived_series_of_ideal_add_le_add I J k l
    _ ≤ ⊥ := by rw [hI, hJ]; simp
#align lie_ideal.derived_series_add_eq_bot LieIdeal.derivedSeries_add_eq_bot

theorem derivedSeries_map_le (k : ℕ) : (derivedSeries R L' k).map f ≤ derivedSeries R L k := by
  induction' k with k ih
  · simp only [derived_series_def, derived_series_of_ideal_zero, le_top]
  · simp only [derived_series_def, derived_series_of_ideal_succ] at ih ⊢
    exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie _ _ _ _ ih ih)
#align lie_ideal.derived_series_map_le LieIdeal.derivedSeries_map_le

theorem derivedSeries_map_eq (k : ℕ) (h : Function.Surjective f) :
    (derivedSeries R L' k).map f = derivedSeries R L k := by
  induction' k with k ih
  · change (⊤ : LieIdeal R L').map f = ⊤
    rw [← f.ideal_range_eq_map]
    exact f.ideal_range_eq_top_of_surjective h
  · simp only [derived_series_def, map_bracket_eq f h, ih, derived_series_of_ideal_succ]
#align lie_ideal.derived_series_map_eq LieIdeal.derivedSeries_map_eq

end LieIdeal

namespace LieAlgebra

/-- A Lie algebra is solvable if its derived series reaches 0 (in a finite number of steps). -/
class IsSolvable : Prop where
  solvable : ∃ k, derivedSeries R L k = ⊥
#align lie_algebra.is_solvable LieAlgebra.IsSolvable

instance isSolvableBot : IsSolvable R ↥(⊥ : LieIdeal R L) :=
  ⟨⟨0, Subsingleton.elim _ ⊥⟩⟩
#align lie_algebra.is_solvable_bot LieAlgebra.isSolvableBot

instance isSolvableAdd {I J : LieIdeal R L} [hI : IsSolvable R I] [hJ : IsSolvable R J] :
    IsSolvable R ↥(I + J) := by
  obtain ⟨k, hk⟩ := id hI; obtain ⟨l, hl⟩ := id hJ
  exact ⟨⟨k + l, LieIdeal.derivedSeries_add_eq_bot hk hl⟩⟩
#align lie_algebra.is_solvable_add LieAlgebra.isSolvableAdd

end LieAlgebra

variable {R L}

namespace Function

open LieAlgebra

theorem Injective.lieAlgebra_isSolvable [h₁ : IsSolvable R L] (h₂ : Injective f) :
    IsSolvable R L' := by
  obtain ⟨k, hk⟩ := id h₁
  use k
  apply LieIdeal.bot_of_map_eq_bot h₂; rw [eq_bot_iff, ← hk]
  apply LieIdeal.derivedSeries_map_le
#align function.injective.lie_algebra_is_solvable Function.Injective.lieAlgebra_isSolvable

theorem Surjective.lieAlgebra_isSolvable [h₁ : IsSolvable R L'] (h₂ : Surjective f) :
    IsSolvable R L := by
  obtain ⟨k, hk⟩ := id h₁
  use k
  rw [← LieIdeal.derivedSeries_map_eq k h₂, hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]
#align function.surjective.lie_algebra_is_solvable Function.Surjective.lieAlgebra_isSolvable

end Function

theorem LieHom.isSolvable_range (f : L' →ₗ⁅R⁆ L) [h : LieAlgebra.IsSolvable R L'] :
    LieAlgebra.IsSolvable R f.range :=
  f.surjective_rangeRestrict.lieAlgebra_isSolvable
#align lie_hom.is_solvable_range LieHom.isSolvable_range

namespace LieAlgebra

theorem solvable_iff_equiv_solvable (e : L' ≃ₗ⁅R⁆ L) : IsSolvable R L' ↔ IsSolvable R L := by
  constructor <;> intro h
  · exact e.symm.injective.lie_algebra_is_solvable
  · exact e.injective.lie_algebra_is_solvable
#align lie_algebra.solvable_iff_equiv_solvable LieAlgebra.solvable_iff_equiv_solvable

theorem le_solvable_ideal_solvable {I J : LieIdeal R L} (h₁ : I ≤ J) (h₂ : IsSolvable R J) :
    IsSolvable R I :=
  (LieIdeal.homOfLe_injective h₁).lieAlgebra_isSolvable
#align lie_algebra.le_solvable_ideal_solvable LieAlgebra.le_solvable_ideal_solvable

variable (R L)

instance (priority := 100) ofAbelianIsSolvable [IsLieAbelian L] : IsSolvable R L := by
  use 1
  rw [← abelian_iff_derived_one_eq_bot, lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv]
  infer_instance
#align lie_algebra.of_abelian_is_solvable LieAlgebra.ofAbelianIsSolvable

/-- The (solvable) radical of Lie algebra is the `Sup` of all solvable ideals. -/
def radical :=
  sSup { I : LieIdeal R L | IsSolvable R I }
#align lie_algebra.radical LieAlgebra.radical

/-- The radical of a Noetherian Lie algebra is solvable. -/
instance radicalIsSolvable [IsNoetherian R L] : IsSolvable R (radical R L) := by
  have hwf := LieSubmodule.wellFounded_of_noetherian R L L
  rw [← CompleteLattice.isSupClosedCompact_iff_wellFounded] at hwf
  refine' hwf { I : LieIdeal R L | IsSolvable R I } ⟨⊥, _⟩ fun I hI J hJ => _
  · exact LieAlgebra.isSolvableBot R L
  · apply LieAlgebra.isSolvableAdd R L; exacts [hI, hJ]
#align lie_algebra.radical_is_solvable LieAlgebra.radicalIsSolvable

/-- The `→` direction of this lemma is actually true without the `is_noetherian` assumption. -/
theorem LieIdeal.solvable_iff_le_radical [IsNoetherian R L] (I : LieIdeal R L) :
    IsSolvable R I ↔ I ≤ radical R L :=
  ⟨fun h => le_sSup h, fun h => le_solvable_ideal_solvable h inferInstance⟩
#align lie_algebra.lie_ideal.solvable_iff_le_radical LieAlgebra.LieIdeal.solvable_iff_le_radical

theorem center_le_radical : center R L ≤ radical R L :=
  have h : IsSolvable R (center R L) := by infer_instance
  le_sSup h
#align lie_algebra.center_le_radical LieAlgebra.center_le_radical

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
natural number `k` (the number of inclusions).

For a non-solvable ideal, the value is 0. -/
noncomputable def derivedLengthOfIdeal (I : LieIdeal R L) : ℕ :=
  sInf { k | derivedSeriesOfIdeal R L k I = ⊥ }
#align lie_algebra.derived_length_of_ideal LieAlgebra.derivedLengthOfIdeal

/-- The derived length of a Lie algebra is the derived length of its 'top' Lie ideal.

See also `lie_algebra.derived_length_eq_derived_length_of_ideal`. -/
noncomputable abbrev derivedLength : ℕ :=
  derivedLengthOfIdeal R L ⊤
#align lie_algebra.derived_length LieAlgebra.derivedLength

theorem derivedSeries_of_derivedLength_succ (I : LieIdeal R L) (k : ℕ) :
    derivedLengthOfIdeal R L I = k + 1 ↔
      IsLieAbelian (derivedSeriesOfIdeal R L k I) ∧ derivedSeriesOfIdeal R L k I ≠ ⊥ := by
  rw [abelian_iff_derived_succ_eq_bot]
  let s := { k | derived_series_of_ideal R L k I = ⊥ }; change Inf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s
  have hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := by
    intro k₁ k₂ h₁₂ h₁
    suffices derived_series_of_ideal R L k₂ I ≤ ⊥ by exact eq_bot_iff.mpr this
    change derived_series_of_ideal R L k₁ I = ⊥ at h₁ ; rw [← h₁]
    exact derived_series_of_ideal_antitone I h₁₂
  exact Nat.sInf_upward_closed_eq_succ_iff hs k
#align lie_algebra.derived_series_of_derived_length_succ LieAlgebra.derivedSeries_of_derivedLength_succ

theorem derivedLength_eq_derivedLengthOfIdeal (I : LieIdeal R L) :
    derivedLength R I = derivedLengthOfIdeal R L I := by
  let s₁ := { k | derivedSeries R I k = ⊥ }
  let s₂ := { k | derived_series_of_ideal R L k I = ⊥ }
  change Inf s₁ = Inf s₂
  congr; ext k; exact I.derived_series_eq_bot_iff k
#align lie_algebra.derived_length_eq_derived_length_of_ideal LieAlgebra.derivedLength_eq_derivedLengthOfIdeal

variable {R L}

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
`k-1`th term in the derived series (and is therefore an Abelian ideal contained in `I`).

For a non-solvable ideal, this is the zero ideal, `⊥`. -/
noncomputable def derivedAbelianOfIdeal (I : LieIdeal R L) : LieIdeal R L :=
  match derivedLengthOfIdeal R L I with
  | 0 => ⊥
  | k + 1 => derivedSeriesOfIdeal R L k I
#align lie_algebra.derived_abelian_of_ideal LieAlgebra.derivedAbelianOfIdeal

theorem abelian_derivedAbelianOfIdeal (I : LieIdeal R L) : IsLieAbelian (derivedAbelianOfIdeal I) :=
  by
  dsimp only [derived_abelian_of_ideal]
  cases' h : derived_length_of_ideal R L I with k
  · exact is_lie_abelian_bot R L
  · rw [derivedSeries_of_derivedLength_succ] at h ; exact h.1
#align lie_algebra.abelian_derived_abelian_of_ideal LieAlgebra.abelian_derivedAbelianOfIdeal

theorem derived_length_zero (I : LieIdeal R L) [hI : IsSolvable R I] :
    derivedLengthOfIdeal R L I = 0 ↔ I = ⊥ := by
  let s := { k | derived_series_of_ideal R L k I = ⊥ }; change Inf s = 0 ↔ _
  have hne : s ≠ ∅ := by
    obtain ⟨k, hk⟩ := id hI
    refine' Set.Nonempty.ne_empty ⟨k, _⟩
    rw [derived_series_def, LieIdeal.derivedSeries_eq_bot_iff] at hk ; exact hk
  simp [hne]
#align lie_algebra.derived_length_zero LieAlgebra.derived_length_zero

theorem abelian_of_solvable_ideal_eq_bot_iff (I : LieIdeal R L) [h : IsSolvable R I] :
    derivedAbelianOfIdeal I = ⊥ ↔ I = ⊥ := by
  dsimp only [derived_abelian_of_ideal]
  cases' h : derived_length_of_ideal R L I with k
  · rw [derived_length_zero] at h ; rw [h]; rfl
  · obtain ⟨h₁, h₂⟩ := (derivedSeries_of_derivedLength_succ R L I k).mp h
    have h₃ : I ≠ ⊥ := by intro contra; apply h₂; rw [contra]; apply derived_series_of_bot_eq_bot
    change derived_series_of_ideal R L k I = ⊥ ↔ I = ⊥
    constructor <;> contradiction
#align lie_algebra.abelian_of_solvable_ideal_eq_bot_iff LieAlgebra.abelian_of_solvable_ideal_eq_bot_iff

end LieAlgebra
