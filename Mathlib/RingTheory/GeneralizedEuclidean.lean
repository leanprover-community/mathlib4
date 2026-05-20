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

variable {R}

namespace Nat

open ENat

@[simp]
theorem mem_euclideanFiltration_zero_iff {r : R} :
    r ∈ EuclideanFiltration R 0 ↔ r = 0 := by
  simp [EuclideanFiltration]

@[simp]
theorem zero_mem_euclideanFiltration {n : ℕ} :
    0 ∈ EuclideanFiltration R n := by
  induction n <;> simp [Nat.EuclideanFiltration]

@[simp]
theorem mem_euclideanFiltration_succ_iff {r : R} {n : ℕ} :
    r ∈ EuclideanFiltration R (n + 1) ↔ r = 0 ∨
      ∀ x, ∃ q, ∃ s ∈ EuclideanFiltration R n, x = q * r + s := by
  simp [EuclideanFiltration]

theorem euclideanFiltration_mono :
    Monotone (EuclideanFiltration R) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
    intro r hr
    rw [mem_euclideanFiltration_zero_iff] at hr
    simp [hr]
  | succ n hind =>
    intro r hr
    simp only [mem_euclideanFiltration_succ_iff] at hr ⊢
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

theorem euclideanLevel_def {r : R} :
    EuclideanLevel r = sInf { n : ℕ∞ | ∃ h : n < ⊤, r ∈ EuclideanFiltration R (n.lift h) } :=
  rfl

theorem euclideanLevel_eq_top_iff {r : R} :
    EuclideanLevel r = ⊤ ↔ ∀ n, r ∉ EuclideanFiltration R n := by
  simp only [euclideanLevel_def, sInf_eq_top, Set.mem_setOf_eq, forall_exists_index]
  constructor
  · intro h n hn
    simpa using h n (by simp) hn
  · intro h m hm hr
    simpa using h (m.lift hm) hr

theorem isLeast_euclideanLevel {r : R} (hr : EuclideanLevel r < ⊤) :
    IsLeast { n : ℕ∞ | ∃ h : n < ⊤, r ∈ EuclideanFiltration R (n.lift h) } (EuclideanLevel r) :=
    by
  have := WellFoundedLT.exists_minimal inferInstance
      { n : ℕ∞ | ∃ h : n < ⊤, r ∈ EuclideanFiltration R (n.lift h) } (by
      by_contra! h
      simp [euclideanLevel_def, h] at hr)
  obtain ⟨m, hm⟩ := this
  rw [← minimal_iff_isLeast]
  suffices EuclideanLevel r = m by rwa [this]
  exact IsLeast.csInf_eq (by rwa [← minimal_iff_isLeast])

theorem euclideanLevel_le_iff {r : R} {n : ℕ} :
    EuclideanLevel r ≤ n ↔ r ∈ EuclideanFiltration R n := by
  constructor
  · intro hr
    have h : EuclideanLevel r < ⊤ := lt_of_le_of_lt hr (coe_lt_top n)
    obtain ⟨h', hr'⟩ := (isLeast_euclideanLevel h).1
    apply euclideanFiltration_mono _ hr'
    rwa [← coe_lift _ h, coe_le_coe] at hr
  · simp only [euclideanLevel_def, sInf_le_iff, mem_lowerBounds,
      Set.mem_setOf_eq, forall_exists_index]
    intro hr b hb
    exact hb n (by simp) hr

theorem euclideanLevel_eq_zero_iff {r : R} :
    EuclideanLevel r = 0 ↔ r = 0 := by
  rw [← bot_eq_zero', eq_bot_iff, bot_eq_zero', ← coe_zero , euclideanLevel_le_iff]
  simp

theorem euclideanLevel_le_one_iff [IsDedekindFiniteMonoid R] {r : R} :
    EuclideanLevel r ≤ 1 ↔ r = 0 ∨ IsUnit r := by
  rw [← coe_one, euclideanLevel_le_iff]
  simp only [mem_euclideanFiltration_succ_iff, mem_euclideanFiltration_zero_iff,
    exists_eq_left, add_zero]
  apply or_congr Iff.rfl
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h 1
    exact IsUnit.of_mul_eq_one_right q hq.symm
  · rw [isUnit_iff_exists]
    rintro ⟨b, hb, hb'⟩ x
    use x * b
    rw [mul_assoc, hb', mul_one]

theorem euclideanLevel_eq_one_iff [Nontrivial R] [IsDedekindFiniteMonoid R] {r : R} :
    EuclideanLevel r = 1 ↔ IsUnit r := by
  constructor
  · intro h
    apply Or.resolve_left (euclideanLevel_le_one_iff.mp h.le)
    rw [← euclideanLevel_eq_zero_iff]
    simp [h]
  · intro h
    apply le_antisymm
    · simp [euclideanLevel_le_one_iff, h]
    · rw [← not_lt]
      intro h'
      suffices r = 0 by simp [this] at h
      rwa [← euclideanLevel_eq_zero_iff, ← lt_one_iff_eq_zero]

end ENat

variable (R) in
/-- A semiring is Nat-euclidean in the sense of Samuel if `Nat.EuclideanFiltration` is exhaustive -/
class IsNatEuclidean : Prop where
  iUnion_eq_univ : ⋃ n, Nat.EuclideanFiltration R n = Set.univ

theorem _root_.isNatEuclidean_iff_iUnion_euclideanFiltration_eq_univ :
    IsNatEuclidean R ↔ ⋃ n, Nat.EuclideanFiltration R n = Set.univ :=
  ⟨fun h ↦ h.iUnion_eq_univ, fun h ↦ ⟨h⟩⟩

theorem _root_.isNatEuclidean_iff_forall_euclideanLevel_ne_top :
    IsNatEuclidean R ↔ ∀ r : R, ENat.EuclideanLevel r < ⊤ := by
  simp [isNatEuclidean_iff_iUnion_euclideanFiltration_eq_univ,
    lt_top_iff_ne_top, ne_eq, ENat.euclideanLevel_eq_top_iff,
    Set.eq_univ_iff_forall]

namespace Nat

variable [IsNatEuclidean R]

/-- The `ℕ`-valued `EuclideanLevel` for Nat-Euclidean semirings -/
noncomputable def EuclideanLevel (r : R) : ℕ :=
  (ENat.EuclideanLevel r).lift (isNatEuclidean_iff_forall_euclideanLevel_ne_top.mp inferInstance _)

theorem coe_EuclideanLevel {r : R} :
    ENat.EuclideanLevel r = EuclideanLevel r := by
  simp [EuclideanLevel]

theorem euclideanLevel_eq_zero_iff {r : R} :
    EuclideanLevel r = 0 ↔ r = 0 := by
  rw [← ENat.coe_inj, ← coe_EuclideanLevel, ENat.coe_zero, ENat.euclideanLevel_eq_zero_iff]

theorem euclideanLevel_le_iff {r : R} {n : ℕ} :
    EuclideanLevel r ≤ n ↔ r ∈ EuclideanFiltration R n := by
  rw [← ENat.coe_le_coe, ← coe_EuclideanLevel, ENat.euclideanLevel_le_iff]

theorem mem_euclideanFiltration (r : R) :
    r ∈ EuclideanFiltration R (EuclideanLevel r) := by
  simp [← euclideanLevel_le_iff]

theorem _root_.IsNatEuclidean.exists_mul_add (a b : R) (hb : b ≠ 0) :
    ∃ q r, a = q * b + r ∧ EuclideanLevel r < EuclideanLevel b := by
  rw [ne_eq, ← euclideanLevel_eq_zero_iff] at hb
  have := mem_euclideanFiltration b
  rw [← succ_pred_eq_of_ne_zero hb, mem_euclideanFiltration_succ_iff,
    ← euclideanLevel_eq_zero_iff] at this
  replace this := Or.resolve_left this hb
  obtain ⟨q, s, hs, hx⟩ := this a
  refine ⟨q, s, hx, ?_⟩
  apply lt_of_le_pred (zero_lt_of_ne_zero hb)
  rwa [euclideanLevel_le_iff]

theorem _root_.IsNatEuclidean.isPrincipalIdealRing {R : Type*} [Ring R] [IsNatEuclidean R] :
    IsPrincipalIdealRing R where
  principal I := by
    have aux (m) :
      m ∈ EuclideanLevel '' I.carrier \ {0} ↔ ∃ x ∈ I, m = EuclideanLevel x ∧ m ≠ 0 := by
        simp; aesop
    by_cases hI : I = 0
    · refine ⟨0, by simpa⟩
    have := WellFoundedLT.exists_minimal inferInstance (EuclideanLevel '' I.carrier \ {0} ) (by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      use EuclideanLevel a
      rw [aux, ne_eq, euclideanLevel_eq_zero_iff]
      simp only [ha0, not_false_eq_true, and_true]
      refine ⟨a, ha, rfl⟩)
    obtain ⟨m, hm⟩ := this
    rw [minimal_iff_isLeast] at hm
    have hmI := (aux _).mp hm.1
    obtain ⟨a, haI, ham, hm0⟩ := hmI
    have ha : a ≠ 0 := by rwa [ne_eq, ← euclideanLevel_eq_zero_iff, ← ham]
    use a
    apply le_antisymm _ (by simpa using haI)
    intro b hb
    obtain ⟨q, r, hr, hqr⟩ := IsNatEuclidean.exists_mul_add b a ha
    rw [Submodule.mem_span_singleton]
    suffices r = 0 by exact ⟨q, by simp [hr, this]⟩
    contrapose hqr
    rw [not_lt, ← ham]
    exact (mem_lowerBounds.mp hm.2) (EuclideanLevel r) (by
      suffices ∃ x ∈ I, EuclideanLevel x = EuclideanLevel r by
        simpa [euclideanLevel_eq_zero_iff, hqr] using this
      refine ⟨r, ?_, rfl⟩
      rw [add_comm, ← sub_eq_iff_eq_add] at hr
      rw [← hr]
      exact I.sub_mem hb (Ideal.mul_mem_left I q haI))

end Nat

namespace Ordinal

open WithTop Order

variable (R) in
def EuclideanFiltration (o : Ordinal.{u}) : Set R :=
  limitRecOn (motive := fun _ ↦ Set R) o
    {0}
    (fun _ s ↦ {0} ∪ {a | ∀ x : R, ∃ q r, r ∈ s ∧ x = q * a + r})
    (fun o _ f ↦ ⋃ (o') (h : o' < o), f o' h)

theorem euclideanFiltration_def (o : Ordinal.{u}) :
  EuclideanFiltration R o = limitRecOn (motive := fun _ ↦ Set R) o
    {0}
    (fun _ s ↦ {0} ∪ {a | ∀ x : R, ∃ q r, r ∈ s ∧ x = q * a + r})
    (fun o _ f ↦ ⋃ (o') (h : o' < o), f o' h) :=
  rfl

@[simp]
theorem mem_euclideanFiltration_zero_iff {r : R} :
    r ∈ EuclideanFiltration R 0 ↔ r = 0 := by
  simp [euclideanFiltration_def, limitRecOn_zero]

@[simp]
theorem zero_mem_euclideanFiltration {n : Ordinal} :
    0 ∈ EuclideanFiltration R n := by
  simp only [euclideanFiltration_def]
  induction n using Ordinal.limitRecOn with
  | zero => simp
  | succ n hn => rw [limitRecOn_succ]; simp
  | limit n hn hn' =>
    rw [limitRecOn_limit _ _ _ _ hn]
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨0, IsSuccLimit.pos hn, hn' _ hn.pos⟩

@[simp]
theorem mem_euclideanFiltration_succ_iff {r : R} {n : Ordinal} :
    r ∈ EuclideanFiltration R (succ n) ↔ r = 0 ∨
      ∀ x, ∃ q, ∃ s ∈ EuclideanFiltration R n, x = q * r + s := by
  simp only [EuclideanFiltration, limitRecOn_succ]
  simp

theorem mem_euclideanFiltration_limit_iff {r : R} {n : Ordinal} (hn : IsSuccLimit n) :
    r ∈ EuclideanFiltration R n ↔ ∃ n' < n, r ∈ EuclideanFiltration R n' := by
  simp [EuclideanFiltration, limitRecOn_limit _ _ _ _ hn]

theorem euclideanFiltration_limit {n : Ordinal} (hn : IsSuccLimit n) :
    EuclideanFiltration R n = ⋃ n' < n, EuclideanFiltration R n' := by
  ext r
  simp [mem_euclideanFiltration_limit_iff hn]

theorem euclideanFiltration_coe_nat (n : ℕ) :
    Ordinal.EuclideanFiltration R n = Nat.EuclideanFiltration R n := by
  induction n with
  | zero => ext; simp [mem_euclideanFiltration_zero_iff]
  | succ n hn =>
    ext r
    have : (succ n : Ordinal) = Order.succ n := by simp
    rw [← succ_eq_add_one, ← this, mem_euclideanFiltration_succ_iff, succ_eq_add_one,
      Nat.mem_euclideanFiltration_succ_iff, hn]

theorem euclideanFiltration_subset_succ (n : Ordinal) :
    EuclideanFiltration R n ⊆ EuclideanFiltration R (succ n) := by
  induction n using Ordinal.limitRecOn with
  | zero =>
    intro r hr
    simp only [mem_euclideanFiltration_zero_iff] at hr
    simp [hr]
  | succ n hn =>
    intro r hr
    rw [mem_euclideanFiltration_succ_iff] at hr ⊢
    rcases hr with (hr | hr)
    · simp [hr]
    · right
      intro x
      obtain ⟨q, s, hs, hx⟩ := hr x
      exact ⟨q, s, hn hs, hx⟩
  | limit n hn hrec =>
    intro r hr
    rw [mem_euclideanFiltration_limit_iff hn] at hr
    obtain ⟨n', hn', hr⟩ := hr
    replace hr := hrec n' hn' hr
    rw [mem_euclideanFiltration_succ_iff] at hr ⊢
    rcases hr with (hr | hr)
    · simp [hr]
    · right
      intro x
      obtain ⟨q, s, hs, hx⟩ := hr x
      refine ⟨q, s, ?_, hx⟩
      rw [mem_euclideanFiltration_limit_iff hn]
      exact ⟨n', hn', hs⟩

theorem euclideanFiltration_mono :
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
    · exact le_trans (hy h) (euclideanFiltration_subset_succ y)
  | limit y hy hrec =>
    intro r hr
    rw [le_iff_lt_or_eq] at h
    rcases h with (h | h)
    · rw [mem_euclideanFiltration_limit_iff hy]
      exact ⟨x, h, hr⟩
    · rwa [← h]

end Ordinal

namespace WithTop.Ordinal

open Ordinal WithTop

noncomputable def EuclideanLevel (r : R) : WithTop Ordinal :=
  sInf { n : WithTop Ordinal.{u} | ∃ h : n ≠ ⊤, r ∈ Ordinal.EuclideanFiltration R (n.untop h) }

theorem euclideanLevel_def {r : R} :
    EuclideanLevel r = sInf { n : WithTop Ordinal.{u} |
      ∃ h : n ≠ ⊤, r ∈ Ordinal.EuclideanFiltration R (n.untop h) } :=
  rfl

theorem euclideanLevel_eq_top_iff {r : R} :
    EuclideanLevel r = ⊤ ↔ ∀ n : Ordinal.{u}, r ∉ Ordinal.EuclideanFiltration R n := by
  simp only [euclideanLevel_def, sInf_eq_top, Set.mem_setOf_eq, forall_exists_index]
  constructor
  · intro h n hn
    simpa using h n (by simp) hn
  · intro h m hm hr
    simpa using h (m.untop hm) hr

theorem isLeast_euclideanLevel {r : R} (hr : EuclideanLevel r ≠ ⊤) :
    IsLeast { n | ∃ h : n ≠ ⊤, r ∈ Ordinal.EuclideanFiltration R (n.untop h) } (EuclideanLevel r) :=
    by
  have := WellFoundedLT.exists_minimal inferInstance
      { n : WithTop Ordinal.{u} | ∃ h : n ≠ ⊤, r ∈ Ordinal.EuclideanFiltration R (n.untop h) } (by
      by_contra! h
      simp [euclideanLevel_def, h] at hr)
  obtain ⟨m, hm⟩ := this
  rw [← minimal_iff_isLeast]
  have : EuclideanLevel r = m := IsLeast.csInf_eq (by rwa [← minimal_iff_isLeast])
  rwa [this]

theorem euclideanLevel_le_iff {r : R} {n : Ordinal} :
    EuclideanLevel r ≤ n ↔ r ∈ Ordinal.EuclideanFiltration R n := by
  constructor
  · intro hr
    have h : EuclideanLevel r ≠ ⊤ := fun h ↦ by simp [h] at hr
    obtain ⟨h, hr'⟩ := (isLeast_euclideanLevel h).1
    apply Ordinal.euclideanFiltration_mono _ hr'
    rwa [← coe_le_coe, coe_untop]
  · simp only [euclideanLevel_def, sInf_le_iff, mem_lowerBounds,
      Set.mem_setOf_eq, forall_exists_index]
    intro hr b hb
    exact hb n (by simp) hr

theorem euclideanLevel_eq_zero_iff {r : R} :
    EuclideanLevel r = 0 ↔ r = 0 := by
  rw [← bot_eq_zero', eq_bot_iff, bot_eq_zero', ← WithTop.coe_zero
  , euclideanLevel_le_iff]
  simp

theorem euclideanLevel_le_one_iff [IsDedekindFiniteMonoid R] {r : R} :
    EuclideanLevel r ≤ 1 ↔ r = 0 ∨ IsUnit r := by
  rw [← WithTop.coe_one, euclideanLevel_le_iff]
  rw [← zero_add (1 : Ordinal), ← Order.succ_eq_add_one, Ordinal.mem_euclideanFiltration_succ_iff]
  simp only [Ordinal.mem_euclideanFiltration_zero_iff, exists_eq_left, add_zero]
  apply or_congr Iff.rfl
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h 1
    exact IsUnit.of_mul_eq_one_right q hq.symm
  · rw [isUnit_iff_exists]
    rintro ⟨b, hb, hb'⟩ x
    use x * b
    rw [mul_assoc, hb', mul_one]

theorem euclideanLevel_eq_one_iff [Nontrivial R] [IsDedekindFiniteMonoid R] {r : R} :
    EuclideanLevel r = 1 ↔ IsUnit r := by
  constructor
  · intro h
    apply Or.resolve_left (euclideanLevel_le_one_iff.mp h.le)
    rw [← euclideanLevel_eq_zero_iff]
    simp [h]
  · intro h
    apply le_antisymm
    · simp [euclideanLevel_le_one_iff, h]
    · rw [← not_lt]
      intro h'
      suffices r = 0 by simp [this] at h
      have hr : EuclideanLevel r ≠ ⊤ := by
        rw [ne_eq, eq_top_iff, not_le]
        exact lt_top_of_lt h'
      rw [← WithTop.coe_one, ← WithTop.coe_untop _ hr, coe_lt_coe, Order.lt_one_iff] at h'
      rw [← euclideanLevel_eq_zero_iff, ← WithTop.coe_untop _ hr, h', coe_zero]

end WithTop.Ordinal

namespace Ordinal

open Order WithTop.Ordinal

variable (R) in
/-- A semiring is Ordinal-euclidean in the sense of Samuel
if `Ordinal.EuclideanFiltration` is exhaustive -/
class _root_.IsOrdinalEuclidean : Prop where
  iUnion_eq_univ : ⋃ n, EuclideanFiltration R n = Set.univ

theorem _root_.isOrdinalEuclidean_iff_iUnion_euclideanFiltration_eq_univ :
    IsOrdinalEuclidean R ↔ ⋃ n, Ordinal.EuclideanFiltration R n = Set.univ :=
  ⟨fun h ↦ h.iUnion_eq_univ, fun h ↦ ⟨h⟩⟩

theorem _root_.isOrdinalEuclidean_iff_forall_euclideanLevel_ne_top :
    IsOrdinalEuclidean R ↔ ∀ r : R, EuclideanLevel r ≠ ⊤ := by
  simp [isOrdinalEuclidean_iff_iUnion_euclideanFiltration_eq_univ,
    ne_eq, WithTop.Ordinal.euclideanLevel_eq_top_iff, Set.eq_univ_iff_forall]

theorem _root_.isNatEuclidean_iff_euclideanFiltration_omega :
    IsNatEuclidean R ↔ EuclideanFiltration R ω = Set.univ := by
  rw [isNatEuclidean_iff_iUnion_euclideanFiltration_eq_univ,
    euclideanFiltration_limit isSuccLimit_omega0]
  suffices ⋃ n, Nat.EuclideanFiltration R n = ⋃ n' < ω, EuclideanFiltration R n' by
    simp [this]
  have := Set.BijOn.iUnion_congr (s := Set.univ) (t := {n' | n' < ω})
    (Nat.EuclideanFiltration R) (Ordinal.EuclideanFiltration R) (h := fun n ↦ n)
  simp only [euclideanFiltration_coe_nat, implies_true, Set.mem_univ, Set.iUnion_true,
    Set.mem_setOf_eq, forall_const] at this
  apply this
  refine ⟨fun _ _ ↦ by simp, fun n _ p _ ↦ by simp, fun n' hn' ↦ ?_⟩
  simp only [Set.mem_setOf_eq] at hn'
  simp only [Set.image_univ, Set.mem_range]
  rcases Ordinal.eq_natCast_or_omega0_le n' with (⟨n, rfl⟩ | h)
  · exact ⟨n, rfl⟩
  · exfalso
    rw [← not_le] at hn'
    exact hn' h

variable [IsOrdinalEuclidean R]

/-- The `Ordinal`-valued `EuclideanLevel` for Ordinal-Euclidean semirings -/
noncomputable def EuclideanLevel (r : R) : Ordinal :=
  (WithTop.Ordinal.EuclideanLevel r).untop
    (isOrdinalEuclidean_iff_forall_euclideanLevel_ne_top.mp inferInstance _)

theorem coe_EuclideanLevel {r : R} :
    WithTop.Ordinal.EuclideanLevel r = EuclideanLevel r := by
  simp [EuclideanLevel]

theorem euclideanLevel_eq_zero_iff {r : R} :
    EuclideanLevel r = 0 ↔ r = 0 := by
  rw [← WithTop.coe_inj, ← coe_EuclideanLevel, WithTop.coe_zero,
    WithTop.Ordinal.euclideanLevel_eq_zero_iff]

theorem euclideanLevel_le_iff {r : R} {n : Ordinal} :
    EuclideanLevel r ≤ n ↔ r ∈ EuclideanFiltration R n := by
  rw [← WithTop.coe_le_coe, ← coe_EuclideanLevel, WithTop.Ordinal.euclideanLevel_le_iff]

theorem mem_euclideanFiltration (r : R) :
    r ∈ EuclideanFiltration R (EuclideanLevel r) := by
  simp [← euclideanLevel_le_iff]

theorem _root_.IsOrdinalEuclidean.exists_mul_add (a b : R) (hb : b ≠ 0) :
    ∃ q r, a = q * b + r ∧ EuclideanLevel r < EuclideanLevel b := by
  rcases (EuclideanLevel b).zero_or_succ_or_isSuccLimit with (hb' | ⟨b', hb'⟩ | hb')
  · apply False.elim (hb ?_)
    rwa [← euclideanLevel_eq_zero_iff]
  · have := mem_euclideanFiltration b
    rw [← hb', mem_euclideanFiltration_succ_iff] at this
    obtain ⟨q, s, hs, hx⟩ := Or.resolve_left this hb a
    rw [← hb']
    rw [← euclideanLevel_le_iff] at hs
    exact ⟨q, s, hx, lt_of_le_of_lt hs (lt_succ b')⟩
  · have := mem_euclideanFiltration b
    rw [mem_euclideanFiltration_limit_iff hb'] at this
    obtain ⟨n', hn', this⟩ := this
    replace this := euclideanFiltration_subset_succ _ this
    rw [mem_euclideanFiltration_succ_iff] at this
    replace this := Or.resolve_left this hb
    obtain ⟨q, s, hs, ha⟩ := this a
    use q, s, ha
    rw [← euclideanLevel_le_iff] at hs
    apply lt_of_le_of_lt hs hn'

theorem _root_.IsOrdinalEuclidean.isPrincipalIdealRing
    {R : Type*} [Ring R] [IsOrdinalEuclidean R] :
    IsPrincipalIdealRing R where
  principal I := by
    by_cases hI : I = 0
    · refine ⟨0, by simpa⟩
    have := WellFoundedLT.exists_minimal inferInstance (EuclideanLevel '' I.carrier \ {0} ) (by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      rw [ne_eq, ← euclideanLevel_eq_zero_iff] at ha0
      use EuclideanLevel a
      simp only [Submodule.carrier_eq_coe, Set.mem_diff, Set.mem_image, SetLike.mem_coe,
        Set.mem_singleton_iff, ha0, not_false_eq_true, and_true]
      exact ⟨a, ha, rfl⟩)
    obtain ⟨m, hm⟩ := this
    rw [minimal_iff_isLeast] at hm
    have hmI := hm.1
    simp only [Submodule.carrier_eq_coe, Set.mem_diff, Set.mem_image, SetLike.mem_coe,
      Set.mem_singleton_iff] at hmI
    obtain ⟨a, haI, ham⟩ := hmI.1
    replace hmI := hmI.2
    have ha : a ≠ 0 := by
      rwa [ne_eq, ← euclideanLevel_eq_zero_iff, ham]
    use a
    apply le_antisymm _ (by simpa using haI)
    intro b hb
    obtain ⟨q, r, hr, hqr⟩ := IsOrdinalEuclidean.exists_mul_add b a ha
    rw [Submodule.mem_span_singleton]
    suffices r = 0 by exact ⟨q, by simp [hr, this]⟩
    contrapose hqr
    rw [not_lt, ham]
    exact (mem_lowerBounds.mp hm.2) (EuclideanLevel r) (by
      suffices ∃ x ∈ I, EuclideanLevel x = EuclideanLevel r by
        simpa [euclideanLevel_eq_zero_iff, hqr] using this
      refine ⟨r, ?_, rfl⟩
      rw [add_comm, ← sub_eq_iff_eq_add] at hr
      rw [← hr]
      exact I.sub_mem hb (Ideal.mul_mem_left I q haI))

end Ordinal
