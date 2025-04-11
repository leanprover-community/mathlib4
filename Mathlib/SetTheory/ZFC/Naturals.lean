/-
Copyright (c) 2025 Vicnent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vicnent Trélat
-/
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Algebra.Ring.Defs

/-! # ZFC Natural numbers

This file defines the natural numbers in ZF set theory. The definition is based on the construction
of the Von Neumann ordinals, where each natural number is represented as the set of all smaller
natural numbers.

The set of all natural numbers is defined as the smallest inductive set. Because of the axiom of
separation, the definition relies on the existence of an infinite set, which is provided by the
`some_inf` constant. It can be shown that the choice of `some_inf` does not affect the definition of
the natural numbers and leads to isomorphic definitions.

The file also includes the definition of the `ZFNat` type for ZF natural numbers, and provides
various properties and usual arithmetic operations on natural numbers.

-/

noncomputable section

namespace ZFSet

/-! ## Preliminary definitions -/

section Preamble

/--
A set `x` is transitive if every element of `x` is a subset of `x`:
`∀ y ∈ x, y ⊆ x`.
-/
def transitive (x : ZFSet) := ∀ y ∈ x, y ⊆ x

/--
An inductive set is defined as a set that contains the empty set `∅` and is closed
under successor.

The "successor" of a set `x` is defined as the insertion of `x` into itself.
-/
def inductive_set (E : ZFSet) : Prop := ∅ ∈ E ∧ ∀ n, n ∈ E → insert n n ∈ E

theorem trans_imp_insert_trans {x : ZFSet} : transitive x → transitive (insert x x) := by
  intro trans
  intro y
  rw [mem_insert_iff]
  rintro ⟨rfl | _⟩
  · simp_rw [subset_def, mem_insert_iff]
    exact fun _ => Or.inr
  · simp_rw [subset_def, mem_insert_iff]
    exact fun _ _ => Or.inr (trans y ‹_› ‹_›)

theorem inductive_sep {S} (P : ZFSet → Prop) (ind : inductive_set S)
  (h₀ : P ∅) (h₁ : ∀ n ∈ S, P n → P (insert n n)) : inductive_set <| S.sep P := by
  unfold inductive_set at *
  simp_rw [mem_sep]
  apply And.intro
  · exact ⟨ind.left, h₀⟩
  · rintro n ⟨_,_⟩
    apply And.intro
    · exact ind.right n ‹_›
    · exact h₁ n ‹_› ‹_›

theorem inductive_imp_transitive {E : ZFSet} (h : inductive_set E) :
  inductive_set (E.sep transitive) := by
  unfold inductive_set
  rcases h with ⟨_, hind⟩
  apply And.intro <;> simp_rw [mem_sep]
  · exact ⟨‹_›, by intro; rw [imp_iff_or_not]; exact Or.inr <| not_mem_empty _⟩
  · rintro n ⟨_,_⟩
    apply And.intro
    · exact hind n ‹_›
    · exact trans_imp_insert_trans ‹_›

notation "ω" => omega

/-- The first Von Neumann ordinal `ω` is an inductive set. -/
theorem omega_inductive : inductive_set ω := ⟨omega_zero, fun _ => omega_succ⟩

/-- Witness for an infinite set, meant to be used for definitional purpose only. -/
private abbrev some_inf := @Classical.choose _ inductive_set ⟨_, omega_inductive⟩

/-- The set `some_inf` is inductive. -/
private lemma inductive_some_inf : inductive_set some_inf := Classical.choose_spec _

private lemma some_inf_nonempty : some_inf ≠ ∅ := by
  intro h
  let h' := inductive_some_inf.left
  rw [h] at h'
  exact (ZFSet.not_mem_empty ∅) h'

private lemma some_inf_mem_sep_inductive_set : some_inf ∈ some_inf.powerset.sep inductive_set := by
  simp only [mem_sep, mem_powerset, subset_refl, true_and]
  exact inductive_some_inf

end Preamble

/-! ## Natural numbers -/

section Naturals

/--
The set of natural numbers `Nat` is defined as the smallest inductive set.
This definition avoids the use of `ω`, even though `ω` may be thought of as `ℕ`.
-/
def Nat : ZFSet := ⋂₀ ((powerset some_inf).sep inductive_set)

/-- The type of natural numbers `ZFNat` is defined as the subtype of `Nat`. -/
abbrev ZFNat := {x // x ∈ Nat}

namespace ZFNat

/--
`some_inf` is an inductive subset of `some_inf`:
`some_inf ∈ { a ⊆ some_inf | inductive_set a }`.
-/
private theorem some_inf_mem_powerset_some_inf_ind :
  some_inf ∈ some_inf.powerset.sep inductive_set :=
  mem_sep.mpr ⟨mem_powerset.mpr fun _ => id, inductive_some_inf⟩

/-- `Nat` is an infinite inductive set. -/
theorem Nat_subset_some_inf : Nat ⊆ some_inf := by
  intro n hn
  unfold Nat at hn
  rw [mem_sInter] at hn
  · have aux :
      n ∈ (⋃₀ (powerset some_inf).sep inductive_set : ZFSet) ∧
      (fun b => ∀ c, c ∈ (powerset some_inf).sep inductive_set → b ∈ c) n := by
        simp only [mem_sUnion, mem_sep, and_imp] at *
        exact ⟨
          ⟨some_inf,
            ⟨mem_powerset.mpr fun _ => id, inductive_some_inf⟩,
            hn some_inf (mem_powerset.mpr fun _ => id) (inductive_some_inf)⟩,
          fun _ _ _ => hn _ ‹_› ‹_›⟩
    simp only [mem_sep, mem_powerset, and_self, and_imp, implies_true, mem_sUnion] at aux
    obtain ⟨⟨_, ⟨left, _⟩, _⟩, _⟩ := aux
    apply left
    assumption
  · exact ⟨some_inf, some_inf_mem_powerset_some_inf_ind⟩

theorem zero_in_Nat : ∅ ∈ Nat := by
  unfold Nat
  rw [mem_sInter]
  · intro x hx
    rw [mem_sep] at hx
    exact hx.right.left
  · exact ⟨some_inf, some_inf_mem_powerset_some_inf_ind⟩

instance nat_zero : Zero ZFNat := ⟨∅, zero_in_Nat⟩
lemma nat_zero_eq : (0 : ZFNat) = ⟨∅, zero_in_Nat⟩ := rfl

instance nat_lt : LT ZFNat := ⟨fun x y => x.val ∈ y.val⟩
instance nat_le : LE ZFNat := ⟨fun x y => x < y ∨ x = y⟩

theorem not_lt_zero {n : ZFNat} : ¬ n < 0 := fun _ => not_mem_empty _ ‹_›
theorem zero_lt_ne_zero {n : ZFNat} : 0 < n → n ≠ 0 := by
  intro h h'
  subst h'
  absurd not_lt_zero h
  trivial

/-- Any inductive set contains zero. -/
lemma zero_mem_inductive {a} (h : inductive_set a) : ↑(0 : ZFNat).val ∈ a := h.left

/-- Any inductive set containing an element also contains its successor. -/
theorem insert_mem_inductive {a n} (h : inductive_set a) (h' : n ∈ a) : insert n n ∈ a :=
  h.right n h'

theorem some_inf_powerset_sep_inductive_nonempty : (some_inf.powerset.sep inductive_set).Nonempty :=
  ⟨some_inf, some_inf_mem_powerset_some_inf_ind⟩

/-- Any inductive set is a subset of `some_inf`. -/
theorem inductive_subset_some_inf_contains_Nat {a} (h : inductive_set a) (h' : a ⊆ some_inf) :
  Nat ⊆ a := by
  intro n hn
  unfold Nat at hn
  rw [mem_sInter] at hn
  · have aux :
      n ∈ (⋃₀ (powerset some_inf).sep inductive_set : ZFSet) ∧
      (fun b => ∀ c, c ∈ (powerset some_inf).sep inductive_set → b ∈ c) n := by
        simp only [mem_sUnion, mem_sep, and_imp] at *
        exact ⟨
          ⟨some_inf,
            ⟨mem_powerset.mpr fun _ => id, inductive_some_inf⟩,
            hn some_inf (mem_powerset.mpr fun _ => id) (inductive_some_inf)⟩,
            fun _ _ _ => hn _ ‹_› ‹_›⟩
    simp only [mem_sep, mem_powerset, and_self, and_imp, implies_true, mem_sUnion] at aux
    exact aux.2 _ h' h
  · exact some_inf_powerset_sep_inductive_nonempty

theorem succ_mem_Nat' {n} (h : n ∈ Nat) : insert n n ∈ Nat := by
  have all_sub_ind : ∀ a, a ∈ some_inf.powerset.sep inductive_set → insert n n ∈ a := by
    intro a ha
    rw [mem_sep] at ha
    exact ha.2.2 n (inductive_subset_some_inf_contains_Nat ha.2 (mem_powerset.mp ha.1) h)
  unfold Nat
  rw [mem_sInter]
  · exact (all_sub_ind · ·)
  · exact some_inf_powerset_sep_inductive_nonempty

/--
The successor function `succ` is build from the insertion of a set into itself embedded into the
`ZFNat` type.
-/
def succ (n : ZFNat) : ZFNat :=
  let ⟨n, h⟩ := n
  have p : insert n n ∈ Nat := succ_mem_Nat' h
  ⟨insert n n, p⟩

instance nat_one : One ZFNat := ⟨succ 0⟩

theorem nat_one_eq : 1 = succ 0 := rfl

theorem succ_ne_zero : ∀ n, succ n ≠ 0 := by
  rintro ⟨n, hn⟩ h
  rw [succ, nat_zero_eq, Subtype.mk.injEq, ZFSet.ext_iff] at h
  simp only [mem_insert_iff, not_mem_empty, iff_false, not_or] at h
  exact h n |>.1 rfl

theorem succ_inj_aux {m n a : ZFSet} (h : insert m m = insert n n) (h' : a ∈ m) : a ∈ n := by
  have d' : a ∈ m ∨ a = m ↔ a ∈ n ∨ a = n := by
    have : a ∈ insert m m ↔ a ∈ n ∨ a = n := by
      rw [h, mem_insert_iff]
      exact Or.comm
    rw [mem_insert_iff, _root_.or_comm] at this
    assumption
  let h'' := mem_insert m m
  rw [h] at h''
  simp only [mem_insert_iff] at h''
  rcases h'' with rfl | h''
  · assumption
  · rcases d'.mp (Or.inl h') with _ | rfl
    · assumption
    · absurd mem_asymm h''
      assumption

theorem succ_inj_aux' {m n : ZFSet} (h : insert m m = insert n n) : m = n :=
  ext fun _ => ⟨succ_inj_aux h, succ_inj_aux <| Eq.symm h⟩

theorem succ_inj {m n} (h : succ m = succ n) : m = n := by
  let ⟨m, hm⟩ := m
  let ⟨n, hn⟩ := n
  simp only [succ, Subtype.mk.injEq] at *
  ext1
  exact ⟨succ_inj_aux h, succ_inj_aux (Eq.symm h)⟩

/-- Any inductive set `a` separated by an inductive predicate `P` is inductive. -/
theorem sep_of_ind_is_ind (P : ZFSet → Prop) {a} (h : inductive_set a)
  (h₀ : P ∅) (ih : ∀ n, n ∈ a → P n → P (insert n n)) : inductive_set (a.sep P) := by
  unfold inductive_set at *
  apply And.intro
  · exact mem_sep.mpr ⟨h.left, h₀⟩
  · simp only [mem_sep, and_imp]
    intros
    exact ⟨h.right _ ‹_›, ih _ ‹_› ‹_›⟩

/-! ## Recursion on natural numbers -/

section Recursion

theorem succ_subrelation_mem' :
  Subrelation (fun x y => insert x x = y) (fun x y : ZFSet => x ∈ y) := by
  intro _ _ _
  subst_eqs
  rw [mem_insert_iff]
  left
  rfl

theorem succ_wf' : @WellFounded ZFSet (fun x y => insert x x = y) := by
  apply Subrelation.wf
  · exact succ_subrelation_mem'
  · exact mem_wf

open Function in
theorem mem_wf' : @WellFounded ZFNat (·.1 ∈ ·.1) := by
  have : (fun x y : ZFNat => x.1 ∈ y.1) = ((fun x y : ZFSet => x ∈ y) on Subtype.val) := rfl
  rw [this]
  apply WellFounded.onFun
  exact mem_wf

/-- The relation built over the successor function is a subrelation of the membership relation. -/
theorem succ_subrelation_mem : Subrelation (succ · = ·) (·.1 ∈ ·.1) := by
  intro _ _ _
  simp only [succ] at *
  subst_eqs
  rw [mem_insert_iff]
  left
  rfl

theorem succ_wf : @WellFounded ZFNat (succ · = ·) := by
  apply Subrelation.wf
  · exact succ_subrelation_mem
  · exact mem_wf'

/--
The induction principle for sets in `Nat`. This principle is meant to be used for definitional
purposes only.
-/
lemma ind {P : ZFSet → Prop} (n : ZFSet)
  (h : n ∈ Nat) (zero : P ∅) (succ : ∀ n ∈ Nat, P n → P (insert n n)) : P n := by
  have : Nat.sep P |>.inductive_set := by
    unfold inductive_set
    apply And.intro
    · exact mem_sep.mpr ⟨zero_in_Nat, ‹_›⟩
    · simp only [mem_sep, and_imp]
      intros
      exact ⟨succ_mem_Nat' ‹_›, succ _ ‹_› ‹_›⟩
  let p := inductive_subset_some_inf_contains_Nat this
  let p' := fun x (_ : x ∈ Nat.sep P) => Nat_subset_some_inf (sep_subset_self ‹_›)
  simp_rw [subset_def, mem_sep] at p
  simp only [mem_sep] at p'
  exact p p' h |>.right

/-- The (weak) induction principle for natural numbers. -/
theorem induction {P : ZFNat → Prop} (n : ZFNat)
  (zero : P 0) (succ : ∀ n, P n → P (succ n)) : P n := by classical
  let ⟨n, hn⟩ := n
  let P' x := if hx : x ∈ Nat then P ⟨x, hx⟩ else unreachable!
  have : P' n = P ⟨n, hn⟩ := dif_pos hn
  rw [← this]
  apply @ind P' n hn
  · unfold P'
    simpa [hn, zero_in_Nat, nat_zero_eq] using zero
  · intro m hm hm'
    unfold P' at *
    simp [hm] at hm'
    simp [succ_mem_Nat' hm]
    exact succ ⟨m, hm⟩ hm'

@[cases_eliminator]
theorem cases {P : ZFNat → Prop} (n : ZFNat) (zero : P 0) (succ : ∀ n, P (succ n)) : P n :=
  induction n zero fun n _ => succ n

theorem every_nat_transitive {n : ZFSet} (h : n ∈ Nat) : transitive n := by
  unfold transitive
  apply ind _ h
  · intros _ _
    exact False.elim (not_mem_empty _ ‹_›)
  · intros _ _ ih _ hy
    intro _ _
    rw [mem_insert_iff] at hy ⊢
    rcases hy with rfl | _
    · exact Or.inr ‹_›
    · exact Or.inr (ih _ ‹_› ‹_›)

theorem lt_succ {n : ZFNat} : n < succ n := mem_insert _ _
theorem le_succ {n : ZFNat} : n ≤ succ n := Or.inl lt_succ

theorem lt_trans {x y z : ZFNat} : x < y → y < z → x < z :=
  fun _ _ => every_nat_transitive z.2 _ ‹_› ‹_›

theorem lt_irrefl {n : ZFNat} : ¬ n < n := fun _ => mem_irrefl _ ‹_›
theorem lt_imp_ne {n m : ZFNat} : n < m → n ≠ m := fun _ _ => by
  subst_eqs
  absurd lt_irrefl ‹_›
  trivial

theorem le_trans {x y z : ZFNat} : x ≤ y → y ≤ z → x ≤ z := by
  rintro (_ | rfl)  (_ | rfl)
  · left; exact lt_trans ‹_› ‹_›
  · left; assumption
  · left; assumption
  · right; rfl

theorem le_antisymm {x y : ZFNat} : x ≤ y → y ≤ x → x = y := by
  rintro (h | rfl) (_ | _)
  · absurd lt_irrefl <| lt_trans ‹_› ‹_›
    trivial
  · symm; assumption
  · trivial
  · trivial

theorem lt_le_iff {n m} : n ≤ m ↔ n < succ m := by
  dsimp [nat_le, ]
  apply Iff.intro
  · rintro (_ | rfl)
    · exact lt_trans ‹_› lt_succ
    · exact lt_succ
  · intro h
    let ⟨n, hn⟩ := n
    let ⟨m, hm⟩ := m
    dsimp [nat_lt, succ] at *
    rw [mem_insert_iff] at h
    rcases h with rfl | _
    · right; rfl
    · left; assumption

theorem lt_mono {x y : ZFNat} : x < y → x.succ < y.succ := by
  intro h
  induction y using induction with
  | zero =>
    absurd not_lt_zero h
    trivial
  | succ y ih =>
    rcases lt_le_iff.mpr h with (h | rfl)
    · exact lt_trans (ih h) lt_succ
    · exact lt_succ

theorem succ_lt_mono {x y : ZFNat} : succ x < succ y → x < y := by
  intro h
  induction y using induction with
  | zero =>
    rcases lt_le_iff.mpr h with (h | h)
    · absurd not_lt_zero h; trivial
    · absurd succ_ne_zero x h; trivial
  | succ y ih =>
    rcases lt_le_iff.mpr h with (h | h)
    · exact lt_trans (ih h) lt_succ
    · replace h := succ_inj h
      subst h
      exact lt_succ

theorem le_mono {x y : ZFNat} : x ≤ y → x.succ ≤ y.succ := by
  rintro (h | rfl)
  · left
    induction y using induction with
    | zero =>
      absurd not_lt_zero h
      trivial
    | succ y ih =>
      rcases lt_le_iff.mpr h with (h | rfl)
      · exact lt_trans (ih h) lt_succ
      · exact lt_succ
  · right; rfl

theorem succ_le_mono {x y : ZFNat} : x.succ ≤ y.succ → x ≤ y := by
  rintro (h | h)
  · left
    induction y using induction with
    | zero =>
      rcases lt_le_iff.mpr h with (h | h)
      · absurd not_lt_zero h; trivial
      · absurd succ_ne_zero x h; trivial
    | succ y ih =>
      rcases lt_le_iff.mpr h with (h | h)
      · exact lt_trans (ih h) lt_succ
      · rw [← h]; exact lt_succ
  · replace h := succ_inj h; subst h; right; rfl

theorem le_lt_iff {n m} : succ n ≤ m ↔ n < m := by
  rw [lt_le_iff]
  apply Iff.intro
  · intro; exact succ_lt_mono ‹_›
  · exact lt_mono

theorem le_total {x y : ZFNat} : x ≤ y ∨ y ≤ x := by
  induction x using induction with
  | zero =>
    left
    induction y using induction with
    | zero => right; rfl
    | succ _ ih => exact le_trans ih (le_succ)
  | succ x ih =>
    induction y using induction with
    | zero =>
      rcases ih with ((h | _) | (_ | _))
      · absurd not_lt_zero h; trivial
      · subst_eqs; right; exact le_succ
      · right; left; exact lt_trans ‹_› lt_succ
      · subst_eqs; right; left; exact lt_succ
    | succ y ih' =>
      rcases ih with (h | _) | (h | _)
      · rcases ih' (Or.inl <| lt_le_iff.mpr h) with l | (r | rfl)
        · left; left; exact lt_le_iff.mp l
        · right; right; congr; exact le_antisymm (lt_le_iff.mpr r) (lt_le_iff.mpr h)
        · replace h := lt_le_iff.mpr h
          left
          apply le_mono
          exact h
      · subst_eqs; right; exact le_succ
      · right
        simp only [lt_le_iff]
        exact lt_trans (lt_trans h lt_succ) lt_succ
      · subst_eqs
        right
        exact le_succ

theorem lt_iff_le_not_le {x y : ZFNat} : x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  apply Iff.intro
  · intro
    apply And.intro
    · left
      assumption
    · rintro (_ | rfl)
      · exact lt_irrefl (lt_trans ‹_› ‹_›)
      · exact lt_irrefl ‹_›
  · rintro ⟨h | rfl, h'⟩
    · assumption
    · simp only [nat_le, or_true] at h'
      contradiction

/-- The (strong) induction principle for natural numbers. -/
theorem strong_induction {P : ZFNat → Prop} (n : ZFNat)
  (ind : ∀ n, (∀ m, m < n → P m) → P n) : P n := by
  let Q x := ∀ m < x, P m
  have aux {x} : Q x := by
    induction x using induction with
    | zero =>
      intros _ _
      exact False.elim (not_lt_zero ‹_›)
    | succ n ih =>
      intros m hm
      unfold Q at ih
      by_cases h : m = n
      · subst h
        exact ind _ ih
      · have h' : m < n := by
          rcases lt_le_iff.mpr hm with (_ | rfl)
          · assumption
          · contradiction
        exact ih m h'
  exact ind _ aux

theorem not_zero_imp_succ {n : ZFNat} : n ≠ 0 → ∃ m, n = succ m := by
  induction n using induction with
  | zero => intro h; contradiction
  | succ n _ =>
    intro
    exact exists_apply_eq_apply' succ n

lemma sUnion_insert_nat {x : ZFSet} (h : x ∈ Nat) : (⋃₀ (insert x x) : ZFSet) = x := by
  apply ind _ h
  · rw [sUnion_insert, sUnion_empty]
    ext1
    simp only [mem_union, not_mem_empty, or_self]
  · intros n _ ih
    rw [sUnion_insert, ih]
    ext1
    simp only [mem_union, mem_insert_iff, or_self_right]

theorem pred_in_Nat' ⦃x : ZFSet⦄ (h : x ∈ Nat) : (⋃₀ x : ZFSet) ∈ Nat := by
  apply ind _ h
  · rw [sUnion_empty]
    exact zero_in_Nat
  · intros
    rw [sUnion_insert_nat] <;> assumption

/-- The predecessor function on natural numbers, defined directly as the union of a set. -/
def pred (x : ZFNat) : ZFNat := x.map sUnion pred_in_Nat'

theorem pred_eq (n : ZFNat) : pred n = ⟨⋃₀ n.val, pred_in_Nat' n.property⟩ := rfl

@[simp]
theorem pred_zero : pred 0 = 0 := by
  unfold pred
  rw [nat_zero_eq, Subtype.map, Subtype.mk.injEq, sUnion_empty]

@[simp]
theorem pred_one : pred 1 = 0 := by
  unfold pred
  rw [nat_one_eq, nat_zero_eq, Subtype.map, Subtype.mk.injEq]
  dsimp [succ]
  rw [LawfulSingleton.insert_empty_eq, sUnion_singleton]

@[simp]
theorem pred_succ {n : ZFNat} : pred (succ n) = n := by
  let ⟨_, _⟩ := n
  simp only [pred, succ, Subtype.map]
  congr
  exact sUnion_insert_nat ‹_›

@[simp]
theorem succ_pred {n : ZFNat} (h : n ≠ 0) : succ (pred n) = n := by
  induction n using strong_induction with
  | ind n ih =>
    obtain ⟨m, hm⟩ := not_zero_imp_succ h
    subst hm
    by_cases h' : m = 0 <;> subst_eqs <;> rw [pred_succ]

private theorem succ_lift_eq {x : ZFNat} : ↑(succ x) = insert x.val x.val := by rfl

private theorem succ_eq (n : ZFSet) (n_Nat : n ∈ Nat) :
  ⟨insert n n, succ_mem_Nat' n_Nat⟩ = succ ⟨n, n_Nat⟩ := by rfl

/--
The recursion principle for sets in `Nat`. This principle is meant to be used for definitional
purposes only.
-/
def rec'.{u} {motive : ZFSet → Sort u} (n : ZFSet) (h : n ∈ Nat)
  (zero : motive ∅) (succ : Π x ∈ Nat, motive x → motive (insert x x)) : motive n := by
  apply succ_wf.fix (C := fun x => motive x.val) (x := ⟨n, h⟩)
  intro x ih
  by_cases x_eq_0 : x = 0
  · subst x_eq_0
    exact zero
  · specialize ih _ (succ_pred x_eq_0)
    specialize succ (pred x) (pred x).2 ih
    conv at succ =>
      arg 1
      rw [← succ_lift_eq, succ_pred x_eq_0]
    assumption

/-- Provides the base case of the recursion principle for sets in `Nat`. -/
theorem rec'_zero.{u} {motive : ZFSet → Sort u}
  (zero : motive ∅) (succ : Π x ∈ Nat, motive x → motive (insert x x)) :
  ZFNat.rec' ∅ zero_in_Nat zero succ = zero := by
    unfold ZFNat.rec' WellFounded.fix
    beta_reduce
    rw [WellFounded.fixFEq, dite_cond_eq_true]
    exact eq_self _


/-- Provides the inductive step of the recursion principle for sets in `Nat`. -/
theorem rec'_succ.{u} {motive : ZFSet → Sort u} (n : ZFSet) (n_Nat : n ∈ Nat)
  (zero : motive ∅) (succ : Π x ∈ Nat, motive x → motive (insert x x)) :
  rec' (insert n n) (succ_mem_Nat' n_Nat) zero succ = succ n n_Nat (rec' n n_Nat zero succ) := by
    unfold ZFNat.rec' WellFounded.fix
    beta_reduce
    rw [WellFounded.fixFEq, dite_cond_eq_false]
    · apply cast_eq_iff_heq.mpr
      · congr
        · conv => enter [1, 1]; rw [succ_eq _ n_Nat, pred_succ]
        · exact proof_irrel_heq ..
        · conv =>
            left
            conv => arg 1; rw [succ_eq _ n_Nat]
            rw [pred_succ]
        · exact proof_irrel_heq ..
        · apply succ_pred
          rw [succ_eq _ n_Nat]
          exact succ_ne_zero _
      · apply eq_false
        intro h
        rw [succ_eq _ n_Nat] at h
        exact succ_ne_zero _ h

/--
The recursion principle for natural numbers. This recursor allows inductive
definitions over natural numbers to be defined in a more natural way.
-/
@[induction_eliminator]
def rec.{u} {motive : ZFNat → Sort u} (n : ZFNat)
  (zero : motive 0) (succ : Π x, motive x → motive (succ x)) : motive n := by classical
  let ⟨n, hn⟩ := n
  let motive' (x : ZFSet) := if hx : x ∈ Nat then motive ⟨x, hx⟩ else unreachable!
  have : motive' n = motive ⟨n, hn⟩ := dif_pos hn
  rw [← this]
  apply @ZFNat.rec' motive' n hn
  · unfold motive'
    simpa [hn, zero_in_Nat, nat_zero_eq] using zero
  · intro m hm hm'
    unfold motive' at *
    simp [hm] at hm'
    simp [succ_mem_Nat' hm]
    exact succ ⟨m, hm⟩ hm'

/--
The induction principle of `ZFNat` is a universe-specialized version of the recursion principle.
-/
@[simp]
theorem induction_is_rec_into_Prop {motive : ZFNat → Prop} :
  induction = ZFNat.rec (motive := motive) := rfl

theorem rec_zero.{u} {motive : ZFNat → Sort u}
  (zero : motive 0) (succ : Π x, motive x → motive (succ x)) :
  rec 0 zero succ = zero := by conv => arg 1; simp [ZFNat.rec, ZFNat.rec'_zero]

theorem rec_succ.{u} {motive : ZFNat → Sort u} (n : ZFNat)
  (zero : motive 0) (succ' : Π x, motive x → motive (succ x)) :
  rec (succ n) zero succ' = succ' n (ZFNat.rec n zero succ') := by
    simp [ZFNat.rec, succ, ZFNat.rec'_succ _ n.property]

end Recursion

/--
The predecessor function `pred'` on natural numbers, defined inductively.
This definition is equivalent to `pred`, as proven by `pred'_eq_pred`.
-/
protected abbrev pred' (m : ZFNat) : ZFNat := ZFNat.rec m 0 (fun x _ : ZFNat => x)

/-- The definitions of `pred` and `pred'` are equivalent. -/
lemma pred'_eq_pred : pred = ZFNat.pred' := by
  ext1 n
  induction n with
  | zero => rw [pred_zero, ZFNat.pred', ZFNat.rec_zero]
  | succ _ _ => rw [pred_succ, ZFNat.pred', ZFNat.rec_succ]

/-! ## Arithmetic -/

section Inequalities

theorem zero_lt_succ {n : ZFNat} : 0 < n.succ := by
  induction n with
  | zero => exact lt_succ
  | succ n ih => exact lt_trans ih lt_succ

theorem pos_of_ne_zero {n : ZFNat} : 0 ≠ n → 0 < n := by
  induction n with
  | zero => intro h; nomatch h
  | succ x ih =>
    intro
    exact zero_lt_succ

instance : LinearOrder ZFNat where
  le := nat_le.le
  le_refl _ := Or.inr rfl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total _ _ := le_total
  decidableLE := fun _ _ => Classical.propDecidable ((· ≤ ·) _ _)
  lt_iff_le_not_le _ _ := lt_iff_le_not_le

instance : IsStrictTotalOrder ZFNat (·<·) where
  trichotomous x y := by
    rcases @le_total x y with (h | rfl) | h | rfl
    · left; assumption
    · right; left; rfl
    · right; right; assumption
    · right; left; rfl
  irrefl _ := lt_irrefl
  trans _ _ _ := lt_trans

end Inequalities

section Arithmetic

/-- The addition function on natural numbers, defined inductively. -/
protected abbrev add (n m : ZFNat) : ZFNat := ZFNat.rec n m (fun _ : ZFNat => succ)

instance add_inst : Add ZFNat := ⟨ZFNat.add⟩
lemma add_inst_eq {n m : ZFNat} : n + m = n.add m := rfl

lemma add_one_eq_succ {n : ZFNat} : n + 1 = succ n := by
  dsimp [add_inst_eq]
  induction n with
  | zero => rw [ZFNat.add, ZFNat.rec_zero, nat_one_eq]
  | succ _ ih => rw [ZFNat.add, ZFNat.rec_succ, ← ZFNat.add, ih]

lemma add_one_eq_succ' {n : ZFNat} : 1 + n = succ n := by
  rw [add_inst_eq, ZFNat.add, nat_one_eq, rec_succ, rec_zero]

@[simp]
lemma add_zero {n : ZFNat} : n + 0 = n := by
  dsimp [add_inst_eq]
  induction n with
  | zero => rw [ZFNat.add, rec_zero]
  | succ _ ih => rw [ZFNat.add, rec_succ, ← ZFNat.add, ih]

@[simp]
lemma zero_add {n : ZFNat} : 0 + n = n := by
  rw [add_inst_eq, ZFNat.add, rec_zero]

lemma add_succ {n m : ZFNat} : succ n + m = succ (n + m) := rec_succ n m fun _ => succ

lemma succ_add {n m : ZFNat} : succ (n + m) = n + succ m := by
  induction n with
  | zero => rw [add_inst_eq, add_inst_eq, ZFNat.add, rec_zero, ZFNat.add, rec_zero]
  | succ n ih =>
    rw [add_succ, ih]
    dsimp [add_inst_eq]
    conv => rhs; rw [ZFNat.add, rec_succ]

lemma add_comm (n m : ZFNat) : n + m = m + n := by
  induction n with
  | zero => rw [add_zero, add_inst_eq, ZFNat.add, rec_zero]
  | succ n ih => rw [← succ_add, add_succ, ih]

@[simp]
lemma add_assoc (n m k : ZFNat) : n + (m + k) = n + m + k := by
  induction n with
  | zero => rw [zero_add, zero_add]
  | succ _ ih => rw [add_succ, add_succ, add_succ, ih]

lemma add_left_comm (n m k : ZFNat) : n + (m + k) = m + (n + k) := by
  rw [add_assoc, add_assoc, add_comm n]

lemma add_right_comm (n m k : ZFNat) : (n + m) + k = (n + k) + m := by
  rw [← add_assoc, add_comm m, add_assoc]

theorem add_left_cancel {n m k : ZFNat} : n + m = n + k ↔ m = k := by
  induction n with
  | zero => simp only [zero_add, imp_self]
  | succ n ih =>
    simp [add_succ]
    apply Iff.intro
    · intro h
      exact ih.mp (succ_inj h)
    · intro h
      rw [h]

theorem add_right_cancel {n m k : ZFNat} : n + m = k + m ↔ n = k := by
  rw [add_comm n, add_comm k]
  exact add_left_cancel

theorem eq_zero_of_add_eq_zero : ∀ {n m : ZFNat}, n + m = 0 → n = 0 ∧ m = 0 := by
  intro n m
  induction n generalizing m with
  | zero => simp only [zero_add, true_and, imp_self]
  | succ n ih =>
    intro h
    rw [add_succ, succ_add] at h
    absurd succ_ne_zero m (ih h).right
    trivial

theorem eq_zero_of_add_eq_zero_left {n m : ZFNat} (h : n + m = 0) : m = 0 :=
  eq_zero_of_add_eq_zero h |>.right

@[simp] theorem add_left_eq_self  {a b : ZFNat} : a + b = b ↔ a = 0 := by
  conv => lhs; rhs; rw [← @zero_add b]
  rw [add_right_cancel]
@[simp] theorem add_right_eq_self {a b : ZFNat} : a + b = a ↔ b = 0 := by
  conv => lhs; rhs; rw [← @add_zero a]
  rw [add_left_cancel]
@[simp] theorem self_eq_add_right {a b : ZFNat} : a = a + b ↔ b = 0 := by
  conv => lhs; lhs; rw [← @add_zero a]
  rw [add_left_cancel]
  exact eq_comm
@[simp] theorem self_eq_add_left  {a b : ZFNat} : a = b + a ↔ b = 0 := by
  conv => lhs; lhs; rw [← @zero_add a]
  rw [add_right_cancel]
  exact eq_comm

theorem lt_of_succ_le {n m : ZFNat} (h : succ n ≤ m) : n < m := le_lt_iff.mp ‹_›
theorem succ_le_of_lt {n m : ZFNat} (h : n < m) : succ n ≤ m := le_lt_iff.mpr ‹_›

theorem le.dest {n m : ZFNat} : n ≤ m → ∃ k, n + k = m := by
  intro h
  induction n with
  | zero => exact ⟨m, zero_add⟩
  | succ n ih =>
    rcases h with h | rfl
    · have : n < m := by
        apply lt_trans (lt_succ)
        assumption
      let ⟨k, hk⟩ := ih (Or.inl this)
      exact ⟨pred k, by
        rwa [← add_one_eq_succ, ← add_assoc, add_one_eq_succ', ZFNat.succ_pred]
        intro
        subst_eqs
        rw [add_zero] at this
        exact lt_irrefl this⟩
    · exact ⟨0, add_zero⟩

theorem le_succ_of_le {n m : ZFNat} (h : n ≤ m) : n ≤ succ m := le_trans h le_succ

@[simp] theorem le_add_right (n k : ZFNat) : n ≤ n + k := by
  induction k with
  | zero => rw [add_zero]
  | succ _ ih =>
    rw [add_comm, add_succ, ← add_comm]
    exact le_succ_of_le ih

@[simp] theorem le_add_left (n m : ZFNat): n ≤ m + n := add_comm .. ▸ le_add_right ..

theorem le.intro {n m k : ZFNat} (h : n + k = m) : n ≤ m := h ▸ le_add_right n k

theorem zero_le {n : ZFNat} : 0 ≤ n := by
  induction n with
  | zero => right; rfl
  | succ n ih => exact le_trans ih le_succ

theorem le_of_add_le_add_left {a b c : ZFNat} (h : a + b ≤ a + c) : b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [← add_assoc] at hd
    exact add_left_cancel.mp hd

theorem add_le_add_left {n m : ZFNat} (h : n ≤ m) (k : ZFNat) : k + n ≤ k + m :=
  match le.dest h with
  | ⟨w, hw⟩ =>
    have : k + (n + w) = k + m     := congrArg _ hw
    le.intro <| (Eq.symm <| add_assoc k n w).trans this

@[simp] theorem add_le_add_iff_left {n m k : ZFNat} : n + m ≤ n + k ↔ m ≤ k :=
  ⟨le_of_add_le_add_left, fun h => add_le_add_left h _⟩

theorem lt_of_add_lt_add_right {n m k : ZFNat} : k + n < m + n → k < m := by
  induction n with
  | zero => simp_rw [add_zero]; exact id
  | succ n ih =>
    simp_rw [← succ_add]
    intro h
    apply succ_lt_mono at h
    exact ih h

theorem add_lt_add_left {n m : ZFNat} (h : n < m) (k : ZFNat) : k + n < k + m :=
  lt_of_succ_le <| succ_add ▸ add_le_add_left (succ_le_of_lt h) k

theorem add_lt_add_right {n m : ZFNat} (h : n < m) (k : ZFNat) : n + k < m + k :=
  add_comm k m ▸ add_comm k n ▸ add_lt_add_left h k

theorem lt_add_of_pos_right {n k : ZFNat} (h : 0 < k) : n < n + k := by
  let this := add_zero ▸ add_lt_add_left h n;
  exact this

theorem lt_of_add_lt_add_left {n m k : ZFNat} : n + k < n + m → k < m := by
  rw [add_comm n, add_comm n]; exact lt_of_add_lt_add_right

@[simp] theorem add_lt_add_iff_left {k n m : ZFNat} : k + n < k + m ↔ n < m :=
  ⟨lt_of_add_lt_add_left, fun _ => add_lt_add_left ‹_› _⟩

@[simp] theorem add_lt_add_iff_right {k n m : ZFNat} : n + k < m + k ↔ n < m :=
  ⟨lt_of_add_lt_add_right, fun _ => add_lt_add_right ‹_› _⟩

theorem add_le_add_right {n m : ZFNat} (h : n ≤ m) (k : ZFNat) : n + k ≤ m + k :=
  add_comm .. ▸ add_comm m k ▸ add_le_add_left h k

theorem add_lt_add_of_le_of_lt {a b c d : ZFNat} (hle : a ≤ b) (hlt : c < d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_right hle _) (add_lt_add_left hlt _)

theorem add_lt_add_of_lt_of_le {a b c d : ZFNat} (hlt : a < b) (hle : c ≤ d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_left hle _) (add_lt_add_right hlt _)

theorem lt_add_of_pos_left {k n : ZFNat} : 0 < k → n < k + n :=
  add_comm .. ▸ lt_add_of_pos_right

theorem pos_of_lt_add_right {n k : ZFNat} (h : n < n + k) : 0 < k := by
  apply lt_of_add_lt_add_left
  rw [add_zero]
  assumption

theorem pos_of_lt_add_left {n k : ZFNat} : n < k + n → 0 < k := by
  rw [add_comm]; exact pos_of_lt_add_right

@[simp] theorem lt_add_right_iff_pos {n k : ZFNat} : n < n + k ↔ 0 < k :=
  ⟨pos_of_lt_add_right, lt_add_of_pos_right⟩

@[simp] theorem lt_add_left_iff_pos {n k : ZFNat} : n < k + n ↔ 0 < k :=
  ⟨pos_of_lt_add_left, lt_add_of_pos_left⟩

theorem add_pos_left {m : ZFNat} (h : 0 < m) (n : ZFNat) : 0 < m + n :=
  lt_of_lt_of_le h (le_add_right ..)

theorem add_pos_right {n : ZFNat} (m : ZFNat) (h : 0 < n) : 0 < m + n :=
  lt_of_lt_of_le h (le_add_left ..)

theorem pred_le_pred {n m : ZFNat} : n ≤ m → (pred n) ≤ (pred m) := by
  intro h
  induction n <;> induction m
  · right; rfl
  · simp only [pred_zero, pred_succ]
    rcases h with (_ | _)
    · exact lt_le_iff.mpr ‹_›
    · absurd (succ_ne_zero _ (Eq.symm ‹_›))
      trivial
  · rcases h with (h | h)
    · absurd not_lt_zero h
      trivial
    · rw [h]
  · simp only [pred_succ]
    exact succ_le_mono h

theorem le_of_succ_le_succ {n m : ZFNat} : (succ n) ≤ (succ m) → n ≤ m := by
  intro h
  replace h := pred_le_pred h
  simp only [pred_succ] at h
  assumption

theorem lt_of_succ_lt_succ {n m : ZFNat} : succ n < succ m → n < m := by
  intro h
  rcases le_of_succ_le_succ (Or.inl h) with (h | rfl)
  · assumption
  · absurd lt_irrefl h
    trivial

theorem add_self_ne_one {n : ZFNat} : n + n ≠ 1 := by
  intro h
  induction n with
  | zero =>
    simp only [zero_add, nat_one_eq] at h
    absurd succ_ne_zero _ (Eq.symm h)
    trivial
  | succ n _ =>
    rw [add_succ, ← succ_add, nat_one_eq] at h
    absurd succ_ne_zero _ (succ_inj h)
    trivial

protected abbrev sub (n m : ZFNat) : ZFNat := ZFNat.rec m n (fun _ => pred)
instance sub_inst : Sub ZFNat := ⟨ZFNat.sub⟩
lemma sub_inst_eq {n m : ZFNat} : n - m = n.sub m := rfl

@[simp]
theorem sub_zero {n : ZFNat} : n - 0 = n := by
  rw [sub_inst_eq, ZFNat.sub, ZFNat.rec_zero]

theorem sub_one_eq_pred {n : ZFNat} : n - 1 = pred n := by
  rw [sub_inst_eq, ZFNat.sub, nat_one_eq, ZFNat.rec_succ, ZFNat.rec_zero]

theorem succ_mono {n m : ZFNat} : n < m ↔ succ n < succ m :=
  ⟨lt_mono, lt_of_succ_lt_succ⟩

theorem sub_succ (n m : ZFNat) : n - succ m = pred (n - m) := by
  rw [sub_inst_eq, ZFNat.sub, ZFNat.rec_succ, ← ZFNat.sub]
  rfl

@[simp]
theorem zero_sub {n : ZFNat} : 0 - n = 0 := by
  induction n with
  | zero => rw [sub_zero]
  | succ n ih => rw [sub_succ, ih, pred_zero]

theorem succ_sub_succ (n m : ZFNat) : succ n - succ m = n - m := by
  induction m with
  | zero      => rw [← nat_one_eq, sub_one_eq_pred, pred_succ, sub_zero]
  | succ m ih => rw [sub_succ, ih, ← sub_succ]

theorem succ_sub_self (n : ZFNat) : succ n - n = 1 := by
  induction n with
  | zero => rw [sub_zero, nat_one_eq]
  | succ n ih => rw [succ_sub_succ, ih]

theorem sub_self {n : ZFNat} : n - n = 0 := by
  induction n with
  | zero => rw [sub_zero]
  | succ n _ => rw [sub_succ, succ_sub_self, pred_one]

theorem sub_add_distrib {n m k : ZFNat} : n - (m + k) = n - m - k := by
  induction k with
  | zero => rw [add_zero, sub_zero]
  | succ k ih => rw [← succ_add, sub_succ, ih, ← sub_succ]

theorem sub_ne_zero_of_lt {a b : ZFNat} : a < b → b - a ≠ 0 := by
  intro h
  induction a generalizing b with
  | zero => rw [sub_zero]; exact zero_lt_ne_zero h
  | succ a ih =>
    induction b with
    | zero => exact absurd h not_lt_zero
    | succ b _ => rw [succ_sub_succ]; exact ih <| succ_mono.mpr h

theorem le_of_succ_le {n m : ZFNat} (_ : succ n ≤ m) : n ≤ m := le_trans le_succ ‹_›
theorem lt_of_succ_lt {n m : ZFNat} (h : succ n < m) : n < m := by
  rcases le_of_succ_le (.inl h) with (h | rfl)
  · assumption
  · absurd lt_irrefl (lt_trans lt_succ h); trivial
theorem le_of_lt {n m : ZFNat} : n < m → n ≤ m := Or.inl

theorem add_sub_of_le {a b : ZFNat} (h : a ≤ b) : a + (b - a) = b := by
  induction a with
  | zero => rw [sub_zero, zero_add]
  | succ a ih =>
    have hne : b - a ≠ 0 := by
      apply sub_ne_zero_of_lt
      exact lt_of_succ_le ‹_›
    have : a ≤ b := le_of_succ_le ‹_›
    rw [sub_succ, add_succ, succ_add, succ_pred hne, ih this]

theorem sub_one_cancel {a b : ZFNat} : 0 < a → 0 < b → a - 1 = b - 1 → a = b := by
  intro ha hb h
  rw [← succ_pred (zero_lt_ne_zero ha), ← succ_pred (zero_lt_ne_zero hb)]
  simpa only [← sub_one_eq_pred, ← add_one_eq_succ, add_right_cancel]

@[simp]
theorem sub_add_cancel {n m : ZFNat} (h : m ≤ n) : n - m + m = n := by
  rw [add_comm, add_sub_of_le h]

theorem add_sub_add_right (n k m : ZFNat) : (n + k) - (m + k) = n - m := by
  induction k with
  | zero => simp_rw [add_zero]
  | succ k ih => rwa [← succ_add, ← succ_add, succ_sub_succ]

theorem add_sub_add_left (k n m : ZFNat) : (k + n) - (k + m) = n - m := by
  rw [add_comm k n, add_comm k m, add_sub_add_right]

@[simp] theorem add_sub_cancel (n m : ZFNat) : n + m - m = n :=
  suffices n + m - (0 + m) = n by rw [zero_add] at this; assumption
  by rw [add_sub_add_right, sub_zero]

theorem add_sub_cancel_left (n m : ZFNat) : n + m - n = m := by
  have : n + m - (n + 0) = m := by rw [add_sub_add_left, sub_zero]
  rwa [add_zero] at this

theorem add_sub_assoc {m k : ZFNat} (h : k ≤ m) (n : ZFNat) : n + m - k = n + (m - k) := by
 rcases le.dest h with ⟨l, rfl⟩
 rw [add_assoc, add_comm n, ← add_assoc, add_sub_cancel_left k, add_comm k, add_sub_cancel]

theorem eq_add_of_sub_eq {a b c : ZFNat} (hle : b ≤ a) (h : a - b = c) : a = c + b := by
  rw [h.symm, sub_add_cancel hle]

theorem sub_eq_of_eq_add {a b c : ZFNat} (h : a = c + b) : a - b = c := by
  rw [h, add_sub_cancel]

theorem add_eq_add_sub_eq_sub {a b c d : ZFNat} : a + b = c + d → a - c = d - b := by
  intro h
  have : a = c + d - b := ZFNat.sub_eq_of_eq_add h.symm |>.symm
  subst this
  rw [←ZFNat.sub_add_distrib, ZFNat.add_comm b c, ZFNat.add_sub_add_left c d b]

theorem sub_factor {m k n : ZFNat} (_ : k ≤ m) (_ : m ≤ n) : n - m + k = n - (m - k) := by
  symm
  apply sub_eq_of_eq_add
  rw [← add_assoc, ← add_sub_assoc, add_comm k, add_sub_assoc, sub_self, add_zero, add_comm,
    ← add_sub_assoc, add_comm, add_sub_assoc, sub_self, add_zero]
  · trivial
  · assumption
  · trivial
  · assumption

theorem sub_add_comm {m n k : ZFNat} (h : m ≤ n) : n - m + k = n + k - m := by
  rw [add_comm, add_comm n k, add_sub_assoc h k]

theorem succ_le_succ {n m : ZFNat} : n ≤ m → succ n ≤ succ m
  | .inl _ => .inl <| succ_mono.mp ‹_›
  | .inr _ => .inr <| congrArg succ ‹_›

theorem succ_le_succ_iff {a b : ZFNat} : succ a ≤ succ b ↔ a ≤ b where
  mp := le_of_succ_le_succ
  mpr := succ_le_succ

theorem le_zero_imp_eq {n : ZFNat} : n ≤ 0 → n = 0 := by
  rintro (h | rfl)
  · exact absurd h not_lt_zero
  · rfl

/-- The multiplication function on natural numbers, defined inductively. -/
protected abbrev mul (n m : ZFNat) : ZFNat := ZFNat.rec n 0 (fun _ => (· + m))
instance mul_inst : Mul ZFNat := ⟨ZFNat.mul⟩
lemma mul_inst_eq {n m : ZFNat} : n * m = n.mul m := rfl

@[simp]
lemma mul_zero {n : ZFNat} : n * 0 = 0 := by
  dsimp [mul_inst_eq]
  induction n using induction with
  | zero => rw [ZFNat.mul, rec_zero]
  | succ _ ih => rw [ZFNat.mul, rec_succ, ← ZFNat.mul, ih, add_zero]

@[simp]
lemma zero_mul {n : ZFNat} : 0 * n = 0 := by
  rw [mul_inst_eq, ZFNat.mul, rec_zero]

@[simp]
lemma mul_one {n : ZFNat} : n * 1 = n := by
  dsimp [mul_inst_eq]
  induction n using induction with
  | zero => rw [ZFNat.mul, rec_zero]
  | succ _ ih => rw [ZFNat.mul, rec_succ, ← ZFNat.mul, ih, add_one_eq_succ]

@[simp]
lemma one_mul {n : ZFNat} : 1 * n = n := by
  rw [mul_inst_eq, ZFNat.mul, nat_one_eq, rec_succ, rec_zero, zero_add]

lemma mul_succ {n m : ZFNat} : (n + 1) * m = n * m + m := by
  induction n with
  | zero => rw [zero_add, one_mul, zero_mul, zero_add]
  | succ n ih => rw [add_one_eq_succ, mul_inst_eq, ZFNat.mul, rec_succ, rec_succ, ← ZFNat.mul,
    ← mul_inst_eq, ← ih, add_one_eq_succ]

lemma succ_mul {n m : ZFNat} : (succ n) * m = n * m + m := by
  rw [← add_one_eq_succ, mul_succ]

lemma left_distrib {n m k : ZFNat} : n * (m + k) = n * m + n * k := by
  induction n with
  | zero => rw [zero_mul, zero_mul, zero_add, zero_mul]
  | succ n ih =>
    rw [← add_one_eq_succ]
    conv_rhs => rw [mul_succ, mul_succ, add_assoc, ← add_assoc, ← add_assoc, add_comm m, add_assoc,
      add_assoc, ← ih, ← add_assoc, add_comm k m, ← mul_succ]

lemma mul_comm (n m : ZFNat) : n * m = m * n := by
  induction n using induction with
  | zero => rw [zero_mul, mul_zero]
  | succ n ih => rw [← add_one_eq_succ, mul_succ, ih, left_distrib, mul_one]

lemma succ_mul' {n m : ZFNat} : m * (succ n) = m * n + m := by
  rw [mul_comm, succ_mul, mul_comm]

lemma right_distrib {n m k : ZFNat} : (n + m) * k = n * k + m * k := by
  rw [mul_comm, left_distrib, mul_comm m, mul_comm k]

lemma mul_assoc (n m k : ZFNat) : n * m * k = n * (m * k) := by
  induction n using induction with
  | zero => rw [zero_mul, zero_mul, zero_mul]
  | succ n ih =>
    rw [← add_one_eq_succ]
    conv =>
      rhs
      rw [right_distrib, one_mul, ← ih, ← right_distrib, ← mul_succ]

lemma mul_left_comm (n m k : ZFNat) : n * (m * k) = m * (n * k) := by
  rw [← mul_assoc, mul_comm n m, mul_assoc]

lemma two_mul (n : ZFNat) : (1 + 1) * n = n + n := by rw [mul_succ, one_mul]
lemma mul_two (n : ZFNat) : n * (1 + 1) = n + n := by rw [mul_comm, two_mul]

lemma sub_lt_eq_zero {n m : ZFNat} (h : n ≤ m) : n - m = 0 := by
  induction m using induction with
  | zero => rw [le_zero_imp_eq h, sub_zero]
  | succ _ ih =>
    rcases h with _ | rfl
    · rw [sub_succ, ih]
      · exact pred_zero
      · exact lt_le_iff.mpr ‹_›
    · rw [sub_self]

theorem add_lt_trans {n m p q : ZFNat} : n < m → p < q → n + p < m + q := by
  intros h h'
  exact lt_trans (add_lt_add_left h' n) (add_lt_add_right h q)

theorem pos_mul_pos {k n : ZFNat} (h : 0 < k) : 0 < k*n → 0 < n := by
  intro h'
  induction n with
  | zero => rwa [mul_zero] at h'
  | succ m ih =>
    obtain ⟨l, rfl⟩ := not_zero_imp_succ (zero_lt_ne_zero h)
    rcases lt_le_iff.mpr h with (_ | rfl)
    · by_contra contr
      rw [not_lt] at contr
      replace contr := le_zero_imp_eq contr
      nomatch succ_ne_zero m contr
    · rw [← nat_one_eq, one_mul] at h'
      assumption

theorem mul_lt_mono {n m k : ZFNat} (h : 0 < k) : n < m → k*n < k*m := by
  intro h'
  induction m using induction with
  | zero => nomatch not_lt_zero h'
  | succ m ih =>
    rw [← add_one_eq_succ, left_distrib, mul_one]
    rcases lt_le_iff.mpr h' with (h' | rfl)
    · let this := add_lt_add_of_le_of_lt (@zero_le k) (ih h')
      rwa [zero_add, add_comm] at this
    · conv => lhs; rw [← @zero_add (k*n), add_comm]
      exact add_lt_add_left h (k*n)

theorem mul_le_mono {k m n : ZFNat} : n ≤ m → k*n ≤ k*m := by
  intro h
  induction k using induction with
  | zero => rw [zero_mul, zero_mul]
  | succ k ih =>
    rw [succ_mul, succ_mul]
    by_contra contr
    rw [not_le, add_comm, add_comm _ n] at contr
    rcases ih with _ | l
    · nomatch lt_irrefl <| lt_trans (add_lt_add_of_le_of_lt h ‹_›) contr
    · rcases h with _ | rfl
      · rw [l] at contr
        nomatch lt_irrefl <| lt_trans (lt_of_add_lt_add_right contr) ‹_›
      · nomatch lt_irrefl ‹_›

theorem mul_lt_cancel {k m n : ZFNat} : k*n < k*m → n < m := by
  contrapose
  rw [not_lt, not_lt]
  exact mul_le_mono

lemma lt_mul_iff {n m k : ZFNat} : n < m ↔ (k+1)*n < (k+1)*m := by
  apply Iff.intro
  · induction k using induction with
    | zero => rw [zero_add, one_mul, one_mul]; exact id
    | succ k ih =>
      intro
      rw [← add_one_eq_succ, mul_succ, mul_succ (m:=m)]
      exact add_lt_trans (ih ‹_›) ‹_›
  · exact mul_lt_cancel

lemma left_distrib_mul_sub_one {n m : ZFNat} : n * (m - 1) = n * m - n := by
  induction m using induction with
  | zero => rw [zero_sub, mul_zero, zero_sub]
  | succ _ _ =>
    rw [nat_one_eq, succ_sub_succ, sub_zero, succ_mul', add_sub_assoc, sub_self, add_zero]
    right
    rfl

lemma left_distrib_mul_sub_aux {n m k : ZFNat} (h : k < m) : n * (m - k) = n * m - n * k := by
  induction k with
  | zero => rw [sub_zero, mul_zero, sub_zero]
  | succ k ih =>
    rw [mul_comm n k.succ, succ_mul, mul_comm k n, sub_add_distrib]
    specialize ih (lt_trans lt_succ h)
    rw [← ih, ← left_distrib_mul_sub_one, ← sub_add_distrib, add_one_eq_succ]

lemma sub_eq_zero_imp_le {a b : ZFNat} : a - b = 0 ↔ a ≤ b := by
  apply Iff.intro
  · intro h
    induction b with
    | zero => rw [sub_zero] at h; right; assumption
    | succ b ih =>
      induction a with
      | zero => exact zero_le
      | succ a _ =>
        apply le_mono
        rw [succ_sub_succ] at h
        by_contra contr
        rw [not_le] at contr
        absurd sub_ne_zero_of_lt contr
        assumption
  · intro
    exact sub_lt_eq_zero ‹_›

lemma sub_eq_zero_mul {n a b : ZFNat} : a - b = 0 → n * a - n * b = 0 := by
  intro
  induction n with
  | zero => rw [zero_mul, zero_mul, sub_zero]
  | succ _ _ => exact sub_eq_zero_imp_le.mpr (mul_le_mono (sub_eq_zero_imp_le.mp ‹_›))

lemma left_distrib_mul_sub {n m k : ZFNat} : n * (m - k) = n * m - n * k := by
  rcases @le_total m k with (h | rfl) | _ | rfl
  · replace h := sub_lt_eq_zero (Or.inl h)
    rw [h, mul_zero, sub_eq_zero_mul h]
  · rw [sub_self, sub_self, mul_zero]
  · exact left_distrib_mul_sub_aux ‹_›
  · rw [sub_self, sub_self, mul_zero]

lemma right_distrib_mul_sub {n m k : ZFNat} : (m - k)*n = m*n - k*n := by
  rw [mul_comm, left_distrib_mul_sub, mul_comm, mul_comm k]

lemma add_eq_zero_iff {n m : ZFNat} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
  constructor
  · intro h
    induction n with
    | zero =>
      rw [zero_add] at h
      exact ⟨rfl, h⟩
    | succ n ih =>
      induction m with
      | zero =>
        rw [add_zero] at h
        exact ⟨h, rfl⟩
      | succ m ih' =>
        rw [add_succ] at h
        nomatch succ_ne_zero _ h
  · rintro ⟨rfl, rfl⟩
    rw [zero_add]

lemma mul_eq_zero_iff {n m : ZFNat} : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · intro h
    induction n with
    | zero => left; rfl
    | succ n ih =>
      induction m with
      | zero => right; rfl
      | succ m ih' =>
        rw [←add_one_eq_succ, mul_succ, add_eq_zero_iff] at h
        nomatch succ_ne_zero _ h.2
  · rintro (rfl | rfl)
    · rw [zero_mul]
    · rw [mul_zero]

lemma eq_le_le_iff {n m : ZFNat} : n = m ↔ n ≤ m ∧ m ≤ n := by
  constructor
  · rintro rfl
    exact ⟨le_refl _, le_refl _⟩
  · rintro ⟨n_le_m, m_le_n⟩
    rcases n_le_m with n_le_m | rfl
    · rcases m_le_n with m_le_n | rfl
      · nomatch lt_irrefl <| lt_trans n_le_m m_le_n
      · rfl
    · rfl

lemma mul_left_cancel_iff {n m k : ZFNat} (k_pos : k ≠ 0) : k * m = k * n ↔ m = n := by
  constructor
  · induction n generalizing m with
    | zero =>
      intro hm
      rw [mul_zero, mul_eq_zero_iff] at hm
      rcases hm with rfl | rfl
      · contradiction
      · rfl
    | succ n ih =>
      intro eq
      cases m with
      | zero =>
        symm at eq
        rw [mul_zero, mul_eq_zero_iff] at eq
        rcases eq with rfl | eq
        · contradiction
        · nomatch succ_ne_zero _ eq
      | succ m =>
        congr
        rw [eq_le_le_iff]
        and_intros
        · have := zero_add ▸ @ZFNat.sub_eq_of_eq_add (k * m.succ) (k * n.succ) 0 <| eq
          rw [←left_distrib_mul_sub, mul_eq_zero_iff] at this
          rcases this with rfl | this
          · contradiction
          · rwa [ZFNat.succ_sub_succ, ZFNat.sub_eq_zero_imp_le] at this
        · have := zero_add ▸ @ZFNat.sub_eq_of_eq_add (k * n.succ) (k * m.succ) 0 <| eq.symm
          rw [←left_distrib_mul_sub, mul_eq_zero_iff] at this
          rcases this with rfl | this
          · contradiction
          · rwa [ZFNat.succ_sub_succ, ZFNat.sub_eq_zero_imp_le] at this
  · rintro rfl
    rfl

lemma mul_right_cancel_iff {n m k : ZFNat} (k_pos : k ≠ 0) : m * k = n * k ↔ m = n := by
  rw [mul_comm m k, mul_comm n k]
  exact mul_left_cancel_iff k_pos

/-- The power function on natural numbers, defined inductively. -/
protected abbrev pow (n p : ZFNat) : ZFNat := ZFNat.rec p 1 (fun _  => (· * n))
instance pow_inst : HomogeneousPow ZFNat := ⟨ZFNat.pow⟩
lemma pow_inst_eq {n p : ZFNat} : n ^ p = n.pow p := rfl

lemma pow_zero {n : ZFNat} : n ^ 0 = 1 := by
  dsimp [pow_inst_eq]
  rw [ZFNat.pow, rec_zero]

lemma pow_one {n : ZFNat} : n ^ 1 = n := by
  rw [pow_inst_eq, ZFNat.pow, nat_one_eq, rec_succ, rec_zero, ← nat_one_eq, one_mul]

end Arithmetic

/--
Induction principle for `ZFNat`, using natural notations.

Declared as an induction eliminator.
-/
@[induction_eliminator]
theorem induction' {P : ZFNat → Prop} (n : ZFNat)
  (zero : P 0) (succ : ∀ n, P n → P (n + 1)) : P n := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [← add_one_eq_succ]
    exact succ n ih

private abbrev nsmul : ℕ → ZFNat → ZFNat
  | 0, _ => 0
  | n+1, m => m + nsmul n m

instance : Semiring ZFNat where
  add := .add
  add_assoc _ _ _ := by rw [add_assoc]
  zero := 0
  zero_add _ := zero_add
  add_zero _ := add_zero
  nsmul := ZFSet.ZFNat.nsmul
  nsmul_zero _ := rfl
  nsmul_succ _ _ := add_comm _ _
  add_comm := add_comm
  mul := .mul
  left_distrib _ _ _ := left_distrib
  right_distrib _ _ _:= right_distrib
  zero_mul _ := zero_mul
  mul_zero _ := mul_zero
  mul_assoc _ _ _ := by rw [mul_assoc]
  one := 1
  one_mul _ := one_mul
  mul_one _ := mul_one

instance : CommSemiring ZFNat where
  mul_comm := mul_comm

instance : IsLeftCancelAdd ZFNat where
  add_left_cancel x y z := by rw [ZFNat.add_left_cancel]; intro; trivial

def toNat (n : ZFNat) : ℕ := ZFNat.rec n 0 (fun _ => Nat.succ)
def ofNat (n : ℕ) : ZFNat := nsmul n 1

theorem toNat_is_id {n : ℕ} : (n : ZFNat).toNat = n := by
  induction n with
  | zero => apply ZFNat.rec_zero
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, ZFNat.add_one_eq_succ, ZFNat.toNat,
    ZFNat.rec_succ, ← ZFNat.toNat, ih]

end ZFNat

theorem Nat.is_transitive : transitive Nat := by
  intro n hn
  apply ZFNat.rec' n hn
  case zero => exact empty_subset Nat
  case succ =>
    intros x hx hx' z hz
    rw [mem_insert_iff] at hz
    rcases hz with rfl | hz
    · assumption
    · exact hx' hz

/-- `Nat` is an inductive set. -/
theorem Nat.is_inductive : inductive_set Nat where
  left := ZFNat.zero_in_Nat
  right := fun _ _ => ZFNat.succ_mem_Nat' ‹_›

end Naturals
end ZFSet
end
