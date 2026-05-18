/-
Copyright (c) 2026 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib

/-! # Generalized Euclidean Domains

This formalizes the general definition of Euclidean rings
suggested by [Pierre Samuel, *On Euclidean Rings*][Samuel-1970],
using the *minimal* ordinal-valued Euclidean algorithm.

-/

universe u

variable (R : Type u) [Semiring R]

/-- The natural euclidean filtration on a semiring -/
def Nat.EuclideanFiltration (n : ℕ) : Set R :=
  Nat.recOn (motive := fun _ ↦ Set R) n
    {0}
    (fun _ s ↦ {0} ∪ {a | ∀ x : R, ∃ q r, r ∈ s ∧ x = q * a + r})

/-- A semiring is Nat-euclidean in the sense of Samuel if `Nat.EuclideanFiltration` is exhaustive -/
class IsNatEuclidean : Prop where
  eq_univ : ⋃ n, Nat.EuclideanFiltration R n = Set.univ

variable {R}

namespace Nat

open ENat

@[simp]
theorem EuclideanFiltration_mem_zero {r : R} :
    r ∈ EuclideanFiltration R 0 ↔ r = 0 := by
  simp [EuclideanFiltration]

@[simp]
theorem EuclideanFiltration_zero_mem {n : ℕ} :
    0 ∈ EuclideanFiltration R n := by
  induction n <;> simp [Nat.EuclideanFiltration]

@[simp]
theorem EuclideanFiltration_succ {r : R} {n : ℕ} :
    r ∈ EuclideanFiltration R (n + 1) ↔ r = 0 ∨
      ∀ x, ∃ q, ∃ s ∈ EuclideanFiltration R n, x = q * r + s := by
  simp [EuclideanFiltration]

theorem EuclideanFiltration_mono :
    Monotone (EuclideanFiltration R) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
    intro r hr
    rw [EuclideanFiltration_mem_zero] at hr
    simp [hr]
  | succ n hind =>
    intro r hr
    simp only [EuclideanFiltration_succ] at hr ⊢
    by_cases hr0 : r = 0
    · simp [hr0]
    · right
      intro x
      obtain ⟨q, s, hs, hx⟩ := Or.resolve_left hr hr0 x
      exact ⟨q, s, hind hs, hx⟩

end Nat

namespace ENat

open Nat

noncomputable def EuclideanLevel (r : R) : ℕ∞ :=
  sInf { n : ℕ∞ | ∃ h : n < ⊤, r ∈ EuclideanFiltration R (n.lift h) }

theorem EuclideanLevel_def {r : R} :
    EuclideanLevel r = sInf { n : ℕ∞ | ∃ h : n < ⊤, r ∈ EuclideanFiltration R (n.lift h) } :=
  rfl

theorem EuclideanLevel_eq_top_iff {r : R} :
    EuclideanLevel r = ⊤ ↔ ∀ n, r ∉ EuclideanFiltration R n := by
  simp only [EuclideanLevel_def, sInf_eq_top, Set.mem_setOf_eq, forall_exists_index]
  constructor
  · intro h n hn
    simpa using h n (by simp) hn
  · intro h m hm hr
    simpa using h (m.lift hm) hr

theorem _root_.isNatEuclidean_iff_forall_euclideanLevel_ne_top :
    IsNatEuclidean R ↔ ∀ r : R, EuclideanLevel r < ⊤ := by
  simp only [lt_top_iff_ne_top, ne_eq, EuclideanLevel_eq_top_iff]
  push Not
  constructor
  · rintro ⟨hR⟩
    simpa [Set.eq_univ_iff_forall] using hR
  · exact fun _ ↦ ⟨by simpa [Set.eq_univ_iff_forall]⟩

theorem EuclideanLevel_isLeast {r : R} (hr : EuclideanLevel r < ⊤) :
    IsLeast { n : ℕ∞ | ∃ h : n < ⊤, r ∈ EuclideanFiltration R (n.lift h) } (EuclideanLevel r) :=
    by
  have := WellFoundedLT.exists_minimal inferInstance
      { n : ℕ∞ | ∃ h : n < ⊤, r ∈ EuclideanFiltration R (n.lift h) } (by
      by_contra! h
      simp [EuclideanLevel_def, h] at hr)
  obtain ⟨m, hm⟩ := this
  rw [← minimal_iff_isLeast]
  suffices EuclideanLevel r = m by rwa [this]
  exact IsLeast.csInf_eq (by rwa [← minimal_iff_isLeast])

theorem EuclideanLevel_le_iff {r : R} {n : ℕ} :
    EuclideanLevel r ≤ n ↔ r ∈ EuclideanFiltration R n := by
  constructor
  · intro hr
    have h : EuclideanLevel r < ⊤ := lt_of_le_of_lt hr (coe_lt_top n)
    obtain ⟨h', hr'⟩ := (EuclideanLevel_isLeast h).1
    apply EuclideanFiltration_mono _ hr'
    rwa [← coe_lift _ h, coe_le_coe] at hr
  · simp only [EuclideanLevel_def, sInf_le_iff, mem_lowerBounds,
      Set.mem_setOf_eq, forall_exists_index]
    intro hr b hb
    exact hb n (by simp) hr

theorem EuclideanLevel_eq_zero_iff {r : R} :
    EuclideanLevel r = 0 ↔ r = 0 := by
  rw [← bot_eq_zero', eq_bot_iff, bot_eq_zero', ← coe_zero , EuclideanLevel_le_iff]
  simp

theorem EuclideanLevel_le_one_iff [IsDedekindFiniteMonoid R] {r : R} :
    EuclideanLevel r ≤ 1 ↔ r = 0 ∨ IsUnit r := by
  rw [← coe_one, EuclideanLevel_le_iff]
  simp only [EuclideanFiltration_succ, EuclideanFiltration_mem_zero, exists_eq_left, add_zero]
  apply or_congr Iff.rfl
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h 1
    exact IsUnit.of_mul_eq_one_right q hq.symm
  · rw [isUnit_iff_exists]
    rintro ⟨b, hb, hb'⟩ x
    use x * b
    rw [mul_assoc, hb', mul_one]

theorem EuclideanLevel_eq_one_iff [Nontrivial R] [IsDedekindFiniteMonoid R] {r : R} :
    EuclideanLevel r = 1 ↔ IsUnit r := by
  constructor
  · intro h
    apply Or.resolve_left (EuclideanLevel_le_one_iff.mp h.le)
    rw [← EuclideanLevel_eq_zero_iff]
    simp [h]
  · intro h
    apply le_antisymm
    · simp [EuclideanLevel_le_one_iff, h]
    · rw [← not_lt]
      intro h'
      suffices r = 0 by simp [this] at h
      rwa [← EuclideanLevel_eq_zero_iff, ← lt_one_iff_eq_zero]

end ENat

namespace Nat

/-- The `ℕ`-valued `EuclideanLevel` for Nat-Euclidean semirings -/
noncomputable def EuclideanLevel [IsNatEuclidean R] (r : R) : ℕ :=
  (ENat.EuclideanLevel r).lift (isNatEuclidean_iff_forall_euclideanLevel_ne_top.mp inferInstance _)

end Nat

namespace Ordinal

open WithTop Order

variable (R) in
def EuclideanFiltration (o : Ordinal.{u}) : Set R :=
  limitRecOn (motive := fun _ ↦ Set R) o
    {0}
    (fun _ s ↦ s ∪ {a | ∀ x : R, ∃ q r, r ∈ s ∧ x = q * a + r})
    (fun o _ f ↦ ⋃ (o') (h : o' < o), f o' h)

variable (R) in
/-- A semiring is Ordinal-euclidean in the sense of Samuel
if `Nat.EuclideanFiltration` is exhaustive -/
class _root_.IsOrdinalEuclidean : Prop where
  eq_univ : ⋃ n, EuclideanFiltration R n = Set.univ

@[simp]
theorem EuclideanFiltration_mem_zero {r : R} :
    r ∈ EuclideanFiltration R 0 ↔ r = 0 := by
  simp [EuclideanFiltration, limitRecOn_zero]

@[simp]
theorem EuclideanFiltration_zero_mem {n : Ordinal} :
    0 ∈ EuclideanFiltration R n := by
  simp only [EuclideanFiltration]
  induction n using Ordinal.limitRecOn with
  | zero => simp
  | succ n hn => rw [limitRecOn_succ]; simp [hn]
  | limit n hn hn' =>
    rw [limitRecOn_limit _ _ _ _ hn]
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨0, IsSuccLimit.pos hn, hn' _ hn.pos⟩

@[simp]
theorem EuclideanFiltration_succ {r : R} {n : Ordinal} :
    r ∈ EuclideanFiltration R (succ n) ↔ r ∈ EuclideanFiltration R n ∨
      ∀ x, ∃ q, ∃ s ∈ EuclideanFiltration R n, x = q * r + s := by
  simp only [EuclideanFiltration, limitRecOn_succ]
  simp

theorem EuclideanFiltration_limit {r : R} {n : Ordinal} (hn : IsSuccLimit n) :
    r ∈ EuclideanFiltration R n ↔ ∃ n' < n, r ∈ EuclideanFiltration R n' := by
  simp [EuclideanFiltration, limitRecOn_limit _ _ _ _ hn]

theorem EuclideanFiltration_mono :
    Monotone (EuclideanFiltration R) := by
  intro x y h
  induction y using Ordinal.limitRecOn generalizing x with
  | zero =>
    simp only [nonpos_iff_eq_zero] at h
    simp [h]
  | succ y hy =>
    rw [Order.le_succ_iff_eq_or_le] at h
    rcases h with (h | h)
    · simp [h]
    · intro r hr
      specialize hy h hr
      rw [EuclideanFiltration_succ]
      exact (Or.inl hy)
  | limit y hy hrec =>
    intro r hr
    rw [le_iff_lt_or_eq] at h
    rcases h with (h | h)
    · rw [EuclideanFiltration_limit hy]
      exact ⟨x, h, hr⟩
    · rwa [← h]

end Ordinal

namespace WithTop.Ordinal

open Ordinal WithTop

noncomputable def EuclideanLevel (r : R) : WithTop Ordinal :=
  sInf { n : WithTop Ordinal.{u} | ∃ h : n ≠ ⊤, r ∈ Ordinal.EuclideanFiltration R (n.untop h) }

theorem EuclideanLevel_def {r : R} :
    EuclideanLevel r = sInf { n : WithTop Ordinal.{u} |
      ∃ h : n ≠ ⊤, r ∈ Ordinal.EuclideanFiltration R (n.untop h) } :=
  rfl

theorem EuclideanLevel_eq_top_iff {r : R} :
    EuclideanLevel r = ⊤ ↔ ∀ n : Ordinal.{u}, r ∉ Ordinal.EuclideanFiltration R n := by
  simp only [EuclideanLevel_def, sInf_eq_top, Set.mem_setOf_eq, forall_exists_index]
  constructor
  · intro h n hn
    simpa using h n (by simp) hn
  · intro h m hm hr
    simpa using h (m.untop hm) hr

theorem _root_.isOrdinalEuclidean_iff_forall_euclideanLevel_ne_top :
    IsOrdinalEuclidean R ↔ ∀ r : R, EuclideanLevel r ≠ ⊤ := by
  simp only [ne_eq, EuclideanLevel_eq_top_iff]
  push Not
  constructor
  · rintro ⟨hR⟩
    simpa [Set.eq_univ_iff_forall] using hR
  · exact fun _ ↦ ⟨by simpa [Set.eq_univ_iff_forall]⟩

theorem EuclideanLevel_isLeast {r : R} (hr : EuclideanLevel r ≠ ⊤) :
    IsLeast { n | ∃ h : n ≠ ⊤, r ∈ Ordinal.EuclideanFiltration R (n.untop h) } (EuclideanLevel r) :=
    by
  have := WellFoundedLT.exists_minimal inferInstance
      { n : WithTop Ordinal.{u} | ∃ h : n ≠ ⊤, r ∈ Ordinal.EuclideanFiltration R (n.untop h) } (by
      by_contra! h
      simp [EuclideanLevel_def, h] at hr)
  obtain ⟨m, hm⟩ := this
  rw [← minimal_iff_isLeast]
  have : EuclideanLevel r = m := IsLeast.csInf_eq (by rwa [← minimal_iff_isLeast])
  rwa [this]

theorem EuclideanLevel_le_iff {r : R} {n : Ordinal} :
    EuclideanLevel r ≤ n ↔ r ∈ Ordinal.EuclideanFiltration R n := by
  constructor
  · intro hr
    have h : EuclideanLevel r ≠ ⊤ := fun h ↦ by simp [h] at hr
    obtain ⟨h, hr'⟩ := (EuclideanLevel_isLeast h).1
    apply Ordinal.EuclideanFiltration_mono _ hr'
    rwa [← coe_le_coe, coe_untop]
  · simp only [EuclideanLevel_def, sInf_le_iff, mem_lowerBounds,
      Set.mem_setOf_eq, forall_exists_index]
    intro hr b hb
    exact hb n (by simp) hr

theorem EuclideanLevel_eq_zero_iff {r : R} :
    EuclideanLevel r = 0 ↔ r = 0 := by
  rw [← bot_eq_zero', eq_bot_iff, bot_eq_zero', ← WithTop.coe_zero
  , EuclideanLevel_le_iff]
  simp

theorem EuclideanLevel_le_one_iff [IsDedekindFiniteMonoid R] {r : R} :
    EuclideanLevel r ≤ 1 ↔ r = 0 ∨ IsUnit r := by
  rw [← WithTop.coe_one, EuclideanLevel_le_iff]
  rw [← zero_add (1 : Ordinal), ← Order.succ_eq_add_one, Ordinal.EuclideanFiltration_succ]
  simp only [Ordinal.EuclideanFiltration_mem_zero, exists_eq_left, add_zero]
  apply or_congr Iff.rfl
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h 1
    exact IsUnit.of_mul_eq_one_right q hq.symm
  · rw [isUnit_iff_exists]
    rintro ⟨b, hb, hb'⟩ x
    use x * b
    rw [mul_assoc, hb', mul_one]

theorem EuclideanLevel_eq_one_iff [Nontrivial R] [IsDedekindFiniteMonoid R] {r : R} :
    EuclideanLevel r = 1 ↔ IsUnit r := by
  constructor
  · intro h
    apply Or.resolve_left (EuclideanLevel_le_one_iff.mp h.le)
    rw [← EuclideanLevel_eq_zero_iff]
    simp [h]
  · intro h
    apply le_antisymm
    · simp [EuclideanLevel_le_one_iff, h]
    · rw [← not_lt]
      intro h'
      suffices r = 0 by simp [this] at h
      have hr : EuclideanLevel r ≠ ⊤ := by
        rw [ne_eq, eq_top_iff, not_le]
        exact lt_top_of_lt h'
      rw [← WithTop.coe_one, ← WithTop.coe_untop _ hr, coe_lt_coe, Order.lt_one_iff] at h'
      rw [← EuclideanLevel_eq_zero_iff, ← WithTop.coe_untop _ hr, h', coe_zero]

end WithTop.Ordinal

namespace Ordinal

/-- The `ℕ`-valued `EuclideanLevel` for Nat-Euclidean semirings -/
noncomputable def EuclideanLevel [IsOrdinalEuclidean R] (r : R) : Ordinal :=
  (WithTop.Ordinal.EuclideanLevel r).untop
    (isOrdinalEuclidean_iff_forall_euclideanLevel_ne_top.mp inferInstance _)

end Ordinal

