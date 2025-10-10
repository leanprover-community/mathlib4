/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.IdealOperations
import Mathlib.Order.Hom.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Solvable Lie algebras

Like groups, Lie algebras admit a natural concept of solvability. We define this here via the
derived series and prove some related results. We also define the radical of a Lie algebra and
prove that it is solvable when the Lie algebra is Noetherian.

## Main definitions

  * `LieAlgebra.derivedSeriesOfIdeal`
  * `LieAlgebra.derivedSeries`
  * `LieAlgebra.IsSolvable`
  * `LieAlgebra.isSolvableAdd`
  * `LieAlgebra.radical`
  * `LieAlgebra.radicalIsSolvable`
  * `LieAlgebra.derivedLengthOfIdeal`
  * `LieAlgebra.derivedLength`
  * `LieAlgebra.derivedAbelianOfIdeal`

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

See also `LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap` and
`LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_map` below. -/
def derivedSeriesOfIdeal (k : ℕ) : LieIdeal R L → LieIdeal R L :=
  (fun I => ⁅I, I⁆)^[k]

@[simp]
theorem derivedSeriesOfIdeal_zero : derivedSeriesOfIdeal R L 0 I = I :=
  rfl

@[simp]
theorem derivedSeriesOfIdeal_succ (k : ℕ) :
    derivedSeriesOfIdeal R L (k + 1) I =
      ⁅derivedSeriesOfIdeal R L k I, derivedSeriesOfIdeal R L k I⁆ :=
  Function.iterate_succ_apply' (fun I => ⁅I, I⁆) k I

/-- The derived series of Lie ideals of a Lie algebra. -/
abbrev derivedSeries (k : ℕ) : LieIdeal R L :=
  derivedSeriesOfIdeal R L k ⊤

theorem derivedSeries_def (k : ℕ) : derivedSeries R L k = derivedSeriesOfIdeal R L k ⊤ :=
  rfl

variable {R L}

local notation "D" => derivedSeriesOfIdeal R L

theorem derivedSeriesOfIdeal_add (k l : ℕ) : D (k + l) I = D k (D l I) := by
  induction k with
  | zero => rw [Nat.zero_add, derivedSeriesOfIdeal_zero]
  | succ k ih => rw [Nat.succ_add k l, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ, ih]

@[gcongr, mono]
theorem derivedSeriesOfIdeal_le {I J : LieIdeal R L} {k l : ℕ} (h₁ : I ≤ J) (h₂ : l ≤ k) :
    D k I ≤ D l J := by
  induction k generalizing l with
  | zero => rw [le_zero_iff] at h₂; rw [h₂, derivedSeriesOfIdeal_zero]; exact h₁
  | succ k ih =>
    have h : l = k.succ ∨ l ≤ k := by rwa [le_iff_eq_or_lt, Nat.lt_succ_iff] at h₂
    rcases h with h | h
    · rw [h, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ]
      exact LieSubmodule.mono_lie (ih (le_refl k)) (ih (le_refl k))
    · rw [derivedSeriesOfIdeal_succ]; exact le_trans (LieSubmodule.lie_le_left _ _) (ih h)

theorem derivedSeriesOfIdeal_succ_le (k : ℕ) : D (k + 1) I ≤ D k I :=
  derivedSeriesOfIdeal_le (le_refl I) k.le_succ

theorem derivedSeriesOfIdeal_le_self (k : ℕ) : D k I ≤ I :=
  derivedSeriesOfIdeal_le (le_refl I) (zero_le k)

theorem derivedSeriesOfIdeal_mono {I J : LieIdeal R L} (h : I ≤ J) (k : ℕ) : D k I ≤ D k J :=
  derivedSeriesOfIdeal_le h (le_refl k)

theorem derivedSeriesOfIdeal_antitone {k l : ℕ} (h : l ≤ k) : D k I ≤ D l I :=
  derivedSeriesOfIdeal_le (le_refl I) h

theorem derivedSeriesOfIdeal_add_le_add (J : LieIdeal R L) (k l : ℕ) :
    D (k + l) (I + J) ≤ D k I + D l J := by
  let D₁ : LieIdeal R L →o LieIdeal R L :=
    { toFun := fun I => ⁅I, I⁆
      monotone' := fun I J h => LieSubmodule.mono_lie h h }
  have h₁ : ∀ I J : LieIdeal R L, D₁ (I ⊔ J) ≤ D₁ I ⊔ J := by
    simp [D₁, LieSubmodule.lie_le_right, LieSubmodule.lie_le_left, le_sup_of_le_right]
  rw [← D₁.iterate_sup_le_sup_iff] at h₁
  exact h₁ k l I J

theorem derivedSeries_of_bot_eq_bot (k : ℕ) : derivedSeriesOfIdeal R L k ⊥ = ⊥ := by
  rw [eq_bot_iff]; exact derivedSeriesOfIdeal_le_self ⊥ k

theorem abelian_iff_derived_one_eq_bot : IsLieAbelian I ↔ derivedSeriesOfIdeal R L 1 I = ⊥ := by
  rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    LieSubmodule.lie_abelian_iff_lie_self_eq_bot]

theorem abelian_iff_derived_succ_eq_bot (I : LieIdeal R L) (k : ℕ) :
    IsLieAbelian (derivedSeriesOfIdeal R L k I) ↔ derivedSeriesOfIdeal R L (k + 1) I = ⊥ := by
  rw [add_comm, derivedSeriesOfIdeal_add I 1 k, abelian_iff_derived_one_eq_bot]

open TensorProduct in
@[simp] theorem derivedSeriesOfIdeal_baseChange {A : Type*} [CommRing A] [Algebra R A] (k : ℕ) :
    derivedSeriesOfIdeal A (A ⊗[R] L) k (I.baseChange A) =
      (derivedSeriesOfIdeal R L k I).baseChange A := by
  induction k with
  | zero => simp
  | succ k ih => simp only [derivedSeriesOfIdeal_succ, ih, LieSubmodule.lie_baseChange]

open TensorProduct in
@[simp] theorem derivedSeries_baseChange {A : Type*} [CommRing A] [Algebra R A] (k : ℕ) :
    derivedSeries A (A ⊗[R] L) k = (derivedSeries R L k).baseChange A := by
  rw [derivedSeries_def, derivedSeries_def, ← derivedSeriesOfIdeal_baseChange,
    LieSubmodule.baseChange_top]

end LieAlgebra

namespace LieIdeal

open LieAlgebra

variable {R L}

theorem derivedSeries_eq_derivedSeriesOfIdeal_comap (k : ℕ) :
    derivedSeries R I k = (derivedSeriesOfIdeal R L k I).comap I.incl := by
  induction k with
  | zero => simp only [derivedSeries_def, comap_incl_self, derivedSeriesOfIdeal_zero]
  | succ k ih =>
    simp only [derivedSeries_def, derivedSeriesOfIdeal_succ] at ih ⊢; rw [ih]
    exact comap_bracket_incl_of_le I (derivedSeriesOfIdeal_le_self I k)
      (derivedSeriesOfIdeal_le_self I k)

theorem derivedSeries_eq_derivedSeriesOfIdeal_map (k : ℕ) :
    (derivedSeries R I k).map I.incl = derivedSeriesOfIdeal R L k I := by
  rw [derivedSeries_eq_derivedSeriesOfIdeal_comap, map_comap_incl, inf_eq_right]
  apply derivedSeriesOfIdeal_le_self

theorem derivedSeries_eq_bot_iff (k : ℕ) :
    derivedSeries R I k = ⊥ ↔ derivedSeriesOfIdeal R L k I = ⊥ := by
  rw [← derivedSeries_eq_derivedSeriesOfIdeal_map, map_eq_bot_iff, ker_incl, eq_bot_iff]

theorem derivedSeries_add_eq_bot {k l : ℕ} {I J : LieIdeal R L} (hI : derivedSeries R I k = ⊥)
    (hJ : derivedSeries R J l = ⊥) : derivedSeries R (I + J) (k + l) = ⊥ := by
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hI hJ ⊢
  rw [← le_bot_iff]
  let D := derivedSeriesOfIdeal R L; change D k I = ⊥ at hI; change D l J = ⊥ at hJ
  calc
    D (k + l) (I + J) ≤ D k I + D l J := derivedSeriesOfIdeal_add_le_add I J k l
    _ ≤ ⊥ := by rw [hI, hJ]; simp

theorem derivedSeries_map_le (k : ℕ) : (derivedSeries R L' k).map f ≤ derivedSeries R L k := by
  induction k with
  | zero => simp only [derivedSeries_def, derivedSeriesOfIdeal_zero, le_top]
  | succ k ih =>
    simp only [derivedSeries_def, derivedSeriesOfIdeal_succ] at ih ⊢
    exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie ih ih)

theorem derivedSeries_map_eq (k : ℕ) (h : Function.Surjective f) :
    (derivedSeries R L' k).map f = derivedSeries R L k := by
  induction k with
  | zero =>
    change (⊤ : LieIdeal R L').map f = ⊤
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  | succ k ih => simp only [derivedSeries_def, map_bracket_eq f h, ih, derivedSeriesOfIdeal_succ]

theorem derivedSeries_succ_eq_top_iff (n : ℕ) :
    derivedSeries R L (n + 1) = ⊤ ↔ derivedSeries R L 1 = ⊤ := by
  simp only [derivedSeries_def]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [derivedSeriesOfIdeal_succ]
    refine ⟨fun h ↦ ?_, fun h ↦ by rwa [ih.mpr h]⟩
    rw [← ih, eq_top_iff]
    conv_lhs => rw [← h]
    exact LieSubmodule.lie_le_right _ _

theorem derivedSeries_eq_top (n : ℕ) (h : derivedSeries R L 1 = ⊤) :
    derivedSeries R L n = ⊤ := by
  cases n
  · rfl
  · rwa [derivedSeries_succ_eq_top_iff]

private theorem coe_derivedSeries_eq_int_aux (R₁ R₂ L : Type*) [CommRing R₁] [CommRing R₂]
    [LieRing L] [LieAlgebra R₁ L] [LieAlgebra R₂ L] (k : ℕ)
    (ih : ∀ (x : L), x ∈ derivedSeriesOfIdeal R₁ L k ⊤ ↔ x ∈ derivedSeriesOfIdeal R₂ L k ⊤) :
    let I := derivedSeriesOfIdeal R₂ L k ⊤; let S : Set L := {⁅a, b⁆ | (a ∈ I) (b ∈ I)}
    (Submodule.span R₁ S : Set L) ≤ (Submodule.span R₂ S : Set L) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  | add y z hy₁ hz₁ hy₂ hz₂ => exact Submodule.add_mem _ hy₂ hz₂
  | smul_mem c y hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      rw [← smul_lie]
      refine Submodule.subset_span ⟨c • a, ?_, b, hb, rfl⟩
      rw [← ih] at ha ⊢
      exact Submodule.smul_mem _ _ ha

theorem coe_derivedSeries_eq_int (k : ℕ) :
    (derivedSeries R L k : Set L) = (derivedSeries ℤ L k : Set L) := by
  rw [← LieSubmodule.coe_toSubmodule, ← LieSubmodule.coe_toSubmodule, derivedSeries_def,
    derivedSeries_def]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ]
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.lieIdeal_oper_eq_linear_span']
    rw [Set.ext_iff] at ih
    simp only [SetLike.mem_coe, LieSubmodule.mem_toSubmodule] at ih
    simp only [ih]
    apply le_antisymm
    · exact coe_derivedSeries_eq_int_aux _ _ L k ih
    · simp

end LieIdeal

namespace LieAlgebra

/-- A Lie algebra is solvable if its derived series reaches 0 (in a finite number of steps). -/
@[mk_iff isSolvable_iff_int]
class IsSolvable : Prop where
  mk_int ::
  solvable_int : ∃ k, derivedSeries ℤ L k = ⊥

instance isSolvableBot : IsSolvable (⊥ : LieIdeal R L) :=
  ⟨⟨0, Subsingleton.elim _ ⊥⟩⟩

lemma isSolvable_iff : IsSolvable L ↔ ∃ k, derivedSeries R L k = ⊥ := by
  simp [isSolvable_iff_int, SetLike.ext'_iff, LieIdeal.coe_derivedSeries_eq_int]

lemma IsSolvable.solvable [IsSolvable L] : ∃ k, derivedSeries R L k = ⊥ :=
  (isSolvable_iff R L).mp ‹_›

variable {R L} in
lemma IsSolvable.mk {k : ℕ} (h : derivedSeries R L k = ⊥) : IsSolvable L :=
  (isSolvable_iff R L).mpr ⟨k, h⟩

instance isSolvableAdd {I J : LieIdeal R L} [IsSolvable I] [IsSolvable J] :
    IsSolvable (I + J) := by
  obtain ⟨k, hk⟩ := IsSolvable.solvable R I
  obtain ⟨l, hl⟩ := IsSolvable.solvable R J
  exact IsSolvable.mk (LieIdeal.derivedSeries_add_eq_bot hk hl)

theorem derivedSeries_lt_top_of_solvable [IsSolvable L] [Nontrivial L] :
    derivedSeries R L 1 < ⊤ := by
  obtain ⟨n, hn⟩ := IsSolvable.solvable (R := R) (L := L)
  rw [lt_top_iff_ne_top]
  intro contra
  rw [LieIdeal.derivedSeries_eq_top n contra] at hn
  exact top_ne_bot hn

open TensorProduct in
instance {A : Type*} [CommRing A] [Algebra R A] [IsSolvable L] : IsSolvable (A ⊗[R] L) := by
  obtain ⟨k, hk⟩ := IsSolvable.solvable R L
  rw [isSolvable_iff A]
  use k
  rw [derivedSeries_baseChange, hk, LieSubmodule.baseChange_bot]

open TensorProduct in
variable {A : Type*} [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A] in
theorem isSolvable_tensorProduct_iff : IsSolvable (A ⊗[R] L) ↔ IsSolvable L := by
  refine ⟨?_, fun _ ↦ inferInstance⟩
  rw [isSolvable_iff A, isSolvable_iff R]
  rintro ⟨k, h⟩
  use k
  rw [eq_bot_iff] at h ⊢
  intro x hx
  rw [derivedSeries_baseChange] at h
  specialize h <| Submodule.tmul_mem_baseChange_of_mem 1 hx
  rw [LieSubmodule.mem_bot] at h ⊢
  rwa [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h

end LieAlgebra

variable {R L}

namespace Function

open LieAlgebra

theorem Injective.lieAlgebra_isSolvable [hL : IsSolvable L] (h : Injective f) :
    IsSolvable L' := by
  rw [isSolvable_iff R] at hL ⊢
  apply hL.imp
  intro k hk
  apply LieIdeal.bot_of_map_eq_bot h; rw [eq_bot_iff, ← hk]
  apply LieIdeal.derivedSeries_map_le

instance (A : LieIdeal R L) [IsSolvable L] : IsSolvable A :=
  A.incl_injective.lieAlgebra_isSolvable

theorem Surjective.lieAlgebra_isSolvable [hL' : IsSolvable L'] (h : Surjective f) :
    IsSolvable L := by
  rw [isSolvable_iff R] at hL' ⊢
  apply hL'.imp
  intro k hk
  rw [← LieIdeal.derivedSeries_map_eq k h, hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]

end Function

instance LieHom.isSolvable_range (f : L' →ₗ⁅R⁆ L) [LieAlgebra.IsSolvable L'] :
    LieAlgebra.IsSolvable f.range :=
  f.surjective_rangeRestrict.lieAlgebra_isSolvable

namespace LieAlgebra

theorem solvable_iff_equiv_solvable (e : L' ≃ₗ⁅R⁆ L) : IsSolvable L' ↔ IsSolvable L := by
  constructor <;> intro h
  · exact e.symm.injective.lieAlgebra_isSolvable
  · exact e.injective.lieAlgebra_isSolvable

theorem le_solvable_ideal_solvable {I J : LieIdeal R L} (h₁ : I ≤ J) (_ : IsSolvable J) :
    IsSolvable I :=
  (LieIdeal.inclusion_injective h₁).lieAlgebra_isSolvable

variable (R L)

instance (priority := 100) ofAbelianIsSolvable [IsLieAbelian L] : IsSolvable L := by
  use 1
  rw [← abelian_iff_derived_one_eq_bot, lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv]
  infer_instance

/-- The (solvable) radical of Lie algebra is the `sSup` of all solvable ideals. -/
def radical :=
  sSup { I : LieIdeal R L | IsSolvable I }

/-- The radical of a Noetherian Lie algebra is solvable. -/
instance radicalIsSolvable [IsNoetherian R L] : IsSolvable (radical R L) := by
  have hwf := LieSubmodule.wellFoundedGT_of_noetherian R L L
  rw [← CompleteLattice.isSupClosedCompact_iff_wellFoundedGT] at hwf
  refine hwf { I : LieIdeal R L | IsSolvable I } ⟨⊥, ?_⟩ fun I hI J hJ => ?_
  · exact LieAlgebra.isSolvableBot R L
  · rw [Set.mem_setOf_eq] at hI hJ ⊢
    apply LieAlgebra.isSolvableAdd R L

/-- The `→` direction of this lemma is actually true without the `IsNoetherian` assumption. -/
theorem LieIdeal.solvable_iff_le_radical [IsNoetherian R L] (I : LieIdeal R L) :
    IsSolvable I ↔ I ≤ radical R L :=
  ⟨fun h => le_sSup h, fun h => le_solvable_ideal_solvable h inferInstance⟩

theorem center_le_radical : center R L ≤ radical R L :=
  have h : IsSolvable (center R L) := inferInstance
  le_sSup h

instance [IsSolvable L] : IsSolvable (⊤ : LieSubalgebra R L) := by
  rwa [solvable_iff_equiv_solvable LieSubalgebra.topEquiv]

@[simp] lemma radical_eq_top_of_isSolvable [IsSolvable L] :
    radical R L = ⊤ := by
  rw [eq_top_iff]
  have h : IsSolvable (⊤ : LieSubalgebra R L) := inferInstance
  exact le_sSup h

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
natural number `k` (the number of inclusions).

For a non-solvable ideal, the value is 0. -/
noncomputable def derivedLengthOfIdeal (I : LieIdeal R L) : ℕ :=
  sInf { k | derivedSeriesOfIdeal R L k I = ⊥ }

/-- The derived length of a Lie algebra is the derived length of its 'top' Lie ideal.

See also `LieAlgebra.derivedLength_eq_derivedLengthOfIdeal`. -/
noncomputable abbrev derivedLength : ℕ :=
  derivedLengthOfIdeal R L ⊤

theorem derivedSeries_of_derivedLength_succ (I : LieIdeal R L) (k : ℕ) :
    derivedLengthOfIdeal R L I = k + 1 ↔
      IsLieAbelian (derivedSeriesOfIdeal R L k I) ∧ derivedSeriesOfIdeal R L k I ≠ ⊥ := by
  rw [abelian_iff_derived_succ_eq_bot]
  let s := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s
  have hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := by
    intro k₁ k₂ h₁₂ h₁
    suffices derivedSeriesOfIdeal R L k₂ I ≤ ⊥ by exact eq_bot_iff.mpr this
    change derivedSeriesOfIdeal R L k₁ I = ⊥ at h₁; rw [← h₁]
    exact derivedSeriesOfIdeal_antitone I h₁₂
  exact Nat.sInf_upward_closed_eq_succ_iff hs k

theorem derivedLength_eq_derivedLengthOfIdeal (I : LieIdeal R L) :
    derivedLength R I = derivedLengthOfIdeal R L I := by
  let s₁ := { k | derivedSeries R I k = ⊥ }
  let s₂ := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s₁ = sInf s₂
  congr; ext k; exact I.derivedSeries_eq_bot_iff k

variable {R L}

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
`k-1`th term in the derived series (and is therefore an Abelian ideal contained in `I`).

For a non-solvable ideal, this is the zero ideal, `⊥`. -/
noncomputable def derivedAbelianOfIdeal (I : LieIdeal R L) : LieIdeal R L :=
  match derivedLengthOfIdeal R L I with
  | 0 => ⊥
  | k + 1 => derivedSeriesOfIdeal R L k I

instance : Unique {x // x ∈ (⊥ : LieIdeal R L)} :=
  inferInstanceAs <| Unique {x // x ∈ (⊥ : Submodule R L)}

theorem abelian_derivedAbelianOfIdeal (I : LieIdeal R L) :
    IsLieAbelian (derivedAbelianOfIdeal I) := by
  dsimp only [derivedAbelianOfIdeal]
  rcases h : derivedLengthOfIdeal R L I with - | k
  · dsimp; infer_instance
  · rw [derivedSeries_of_derivedLength_succ] at h; exact h.1

theorem derivedLength_zero (I : LieIdeal R L) [IsSolvable I] :
    derivedLengthOfIdeal R L I = 0 ↔ I = ⊥ := by
  let s := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = 0 ↔ _
  have hne : s ≠ ∅ := by
    obtain ⟨k, hk⟩ := IsSolvable.solvable R I
    refine Set.Nonempty.ne_empty ⟨k, ?_⟩
    rw [derivedSeries_def, LieIdeal.derivedSeries_eq_bot_iff] at hk; exact hk
  simp [s, hne]

theorem abelian_of_solvable_ideal_eq_bot_iff (I : LieIdeal R L) [h : IsSolvable I] :
    derivedAbelianOfIdeal I = ⊥ ↔ I = ⊥ := by
  dsimp only [derivedAbelianOfIdeal]
  split
  · simp_all only [derivedLength_zero]
  · rename_i k h
    obtain ⟨_, h₂⟩ := (derivedSeries_of_derivedLength_succ R L I k).mp h
    have h₃ : I ≠ ⊥ := by rintro rfl; apply h₂; apply derivedSeries_of_bot_eq_bot
    simp only [h₂, h₃]

end LieAlgebra
