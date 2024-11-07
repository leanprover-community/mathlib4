/-
Copyright (c) 2024 Haitian Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitian Wang, Malvin Gattinger
-/
import Mathlib.Tactic.Linarith
import Mathlib.Data.Multiset.Basic
import Mathlib.Logic.Relation

/-!
# Dershowitz-Manna ordering

In this file we define the _Dershowitz-Manna ordering_ on multisets. Specifically, for two multisets
`M` and `N` in a partial order `(S, <)`, `M` is smaller than `N` in the Dershowitz-Manna ordering if
`M` can be obtained from `N` by replacing one or more elements in `N` by some finite number of
elements from `S`, each of which is smaller (in the underling ordering over `S`) than one of the
replaced elements from `N`. We prove that, given a well-founded partial order on the underlying set,
the Dershowitz-Manna ordering defined over multisets is also well-founded.

## Main results

- `Multiset.IsDershowitzMannaLT` : the standard definition fo the `Dershowitz-Manna ordering`.
- `Multiset.wellFounded_isDershowitzMannaLT` : the main theorem about the
`Dershowitz-Manna ordering` being well-founded.
- `Multiset.TransLT_eq_isDershowitzMannaLT` : two definitions of the `Dershowitz-Manna ordering`
are equivalent.

## References

* [Wikipedia, Dershowitz–Manna ordering*]
(https://en.wikipedia.org/wiki/Dershowitz%E2%80%93Manna_ordering)

* [CoLoR](https://github.com/fblanqui/color), a Coq library on rewriting theory and termination.
  Our code here is inspired by their formalization and the theorem is called `mOrd_wf` in the file
  [MultisetList.v](https://github.com/fblanqui/color/blob/1.8.5/Util/Multiset/MultisetOrder.v).

-/

namespace Multiset

variable {α : Type*} [Preorder α]

/-- The standard Dershowitz–Manna ordering. -/
def IsDershowitzMannaLT (M N : Multiset α) : Prop :=
  ∃ (X Y Z : Multiset α),
      Z ≠ ∅
    ∧ M = X + Y
    ∧ N = X + Z
    ∧ (∀ y ∈ Y, ∃ z ∈ Z, y < z)

/-- A special case of `IsDershowitzMannaLT`. The transitive closure of it is used to define
an equivalent (proved later) version of the ordering. -/
private def OneStepLT [LT α] (M N : Multiset α) : Prop :=
  ∃ X Y a,
      M = X + Y
    ∧ N = X + {a}
    ∧ ∀ y ∈ Y, y < a

open Relation

/-- The transitive closure of `OneStepLT` and is equivalent to `IsDershowitzMannaLT`
(proved later). -/
private def TransLT [LT α] : Multiset α → Multiset α → Prop := TransGen OneStepLT

/-- A special case of `IsDershowitzMannaLT`. -/
private lemma isDershowitzMannaLT_of_oneStepLT {M N : Multiset α}
    (h : OneStepLT M N) : IsDershowitzMannaLT M N := by
  rcases h with ⟨X, Y, a, M_def, N_def, ys_lt_a⟩
  use X, Y, {a}, by simp, M_def, N_def
  · simpa

private lemma isDershowitzMannaLT_singleton_insert [DecidableEq α] {a : α} {M N : Multiset α}
    (h : OneStepLT N (a ::ₘ M)) :
    ∃ M', N = a ::ₘ M' ∧ OneStepLT M' M ∨ N = M + M' ∧ ∀ x ∈ M', x < a := by
  rcases h with ⟨X, Y, a0, h1, h0, h2⟩
  by_cases hyp : a = a0
  · exists Y; right; apply And.intro
    · rw [h1, add_left_inj]
      rw [add_comm, singleton_add] at h0
      simp_all
    · simp_all
  exists (Y + (M - {a0}))
  left
  constructor
  · rw [h1]
    have : X = (M - {a0} + {a}) := by
      rw [add_comm, singleton_add] at *
      ext b
      simp only [ext, count_cons] at h0
      by_cases h : b = a
      · have := h0 b
        simp_all only [ite_true, ite_false, add_zero, sub_singleton, count_cons_self, ne_eq,
          not_false_eq_true, count_erase_of_ne]
      have := h0 b
      simp [sub_singleton]
      simp_all only [↓reduceIte, add_zero, ne_eq, not_false_eq_true, count_cons_of_ne]
      split at this
      next h_1 =>
        simp_all only [count_erase_self, add_tsub_cancel_right]
      next h_1 => simp_all only [add_zero, ne_eq, not_false_eq_true, count_erase_of_ne]
    subst this
    rw [add_comm]
    nth_rewrite 2 [add_comm]
    rw [singleton_add, add_cons]
  · unfold OneStepLT
    refine ⟨M - {a0}, Y, a0, ?_, ?_, h2⟩
    · change Y + (M - {a0}) = (M - {a0}) + Y
      rw [add_comm]
    · change M = M - {a0} + {a0}
      have this0 : M = X + {a0} - {a} := by
        rw [← h0, sub_singleton, erase_cons_head]
      have a0M : a0 ∈ M := by
        rw [this0, sub_singleton, mem_erase_of_ne]
        rw [mem_add, mem_singleton]
        · apply Or.inr
          rfl
        · exact fun h ↦ hyp (Eq.symm h)
      rw [add_comm]
      simp_all [singleton_add]

private lemma acc_cons [DecidableEq α] (a : α) (M0 : Multiset α)
    (_ : ∀ b M , LT.lt b a → Acc OneStepLT M → Acc OneStepLT (b ::ₘ M))
    (_ : Acc OneStepLT M0)
    (_ : ∀ M, OneStepLT M M0 → Acc OneStepLT (a ::ₘ M)) :
    Acc OneStepLT (a ::ₘ M0) := by
  constructor
  intros N N_lt
  change Acc OneStepLT N
  rcases (isDershowitzMannaLT_singleton_insert N_lt) with ⟨x, H, h0⟩
  case h.intro.inr h =>
    rcases h with ⟨H, h0⟩
    rw [H]
    clear H
    induction x using Multiset.induction with
    | empty =>
      simpa
    | cons h =>
      simp_all only [mem_cons, or_true, implies_true, true_implies, forall_eq_or_imp,
        add_cons]
  case h.intro.inl.intro =>
    simp_all

private lemma acc_cons_of_acc [DecidableEq α] (a : α)
    (H : ∀ (b : α), ∀ M, LT.lt b a → Acc OneStepLT M → Acc OneStepLT (b ::ₘ M)) :
    ∀ M, Acc OneStepLT M → Acc OneStepLT (a ::ₘ M) := by
  intros M h0
  induction h0 with
  | intro x wfH wfh2 =>
    apply acc_cons
    · simpa
    · constructor; simpa only
    · simpa only

private lemma acc_cons_of_acc_of_lt [DecidableEq α] :
    ∀ (a:α), Acc LT.lt a → ∀ M, Acc OneStepLT M → Acc OneStepLT (a ::ₘ M) := by
  intro w w_a
  induction w_a with
  | intro x _ ih =>
      intro M accM1
      apply @acc_cons_of_acc α _ _ _ _ _ accM1
      simp_all

/-- If all elements of a multiset `M` are accessible with `LT.lt`, then the multiset `M` is
accessible given the `OneStepLT` relation. -/
private lemma acc_of_acc_lt [DecidableEq α] :
    ∀ (M : Multiset α), (∀x, x ∈ M → Acc LT.lt x) → Acc OneStepLT M  := by
  intros M wf_el
  induction M using Multiset.induction_on with
  | empty =>
    constructor
    intro y y_lt
    absurd y_lt
    rintro ⟨X, Y, a, _, nonsense, _⟩
    have contra : a ∈ (0 : Multiset α):= by
      simp_all only [mem_add, mem_singleton, or_true]
    contradiction
  | cons _ _ ih =>
    apply acc_cons_of_acc_of_lt
    · apply wf_el
      simp_all
    · apply ih
      intros
      apply wf_el
      simp_all

/-- If `LT.lt` is well-founded, then `OneStepLT` is well-founded. -/
private lemma isDershowitzMannaLT_singleton_wf [DecidableEq α]
    (wf_lt : WellFoundedLT α) : WellFounded (OneStepLT : Multiset α → Multiset α → Prop) := by
  constructor
  intros a
  apply acc_of_acc_lt
  intros x _
  apply wf_lt.induction x
  intros y h
  apply Acc.intro y
  assumption

/-- `IsDershowitzMannaLT` is transitive. -/
lemma isDershowitzMannaLT.trans {α} [dec : DecidableEq α] [Preorder α] :
    ∀ (M N P : Multiset α) ,
    IsDershowitzMannaLT N M → IsDershowitzMannaLT P N → IsDershowitzMannaLT P M := by
  intros M N P LTNM LTPN
  rcases LTNM with ⟨X1, Y1, Z1, Z1_ne, N1_def, M1_def, Ord1⟩
  rcases LTPN with ⟨X2, Y2, Z2, _, P2_def, N2_def, Ord2⟩
  refine ⟨X1 ∩ X2, Y2 + (Y1 - Z2), Z1 + (Z2 - Y1), ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [empty_eq_zero] at *
    rw [← card_pos]
    rw [← card_pos] at Z1_ne
    simp only [_root_.map_add, add_pos_iff]
    left
    exact Z1_ne
  · rw [P2_def]
    have : X1 ∩ X2 + (Y2 + (Y1 - Z2)) = X1 ∩ X2 + (Y1 - Z2) + Y2 := by
      have : (Y2 + (Y1 - Z2)) = (Y1 - Z2) + Y2 := by rw [add_comm]
      rw [this, add_assoc]
    rw [this]
    have : X1 ∩ X2 + (Y1 - Z2) = X2 ∩ X1 + (Y1 - Z2) := by
      rw [inter_comm]
    rw [this, inter_add_sub_of_add_eq_add]
    rw [add_comm, ← N2_def, N1_def]
    apply add_comm
  · rw [M1_def]
    have : X1 ∩ X2 + (Z1 + (Z2 - Y1)) = X1 ∩ X2 + (Z2 - Y1) + Z1 := by
      have : (Z1 + (Z2 - Y1)) = (Z2 - Y1) + Z1 := by rw [add_comm]
      rw [this, add_assoc]
    rw [this, add_left_inj, inter_add_sub_of_add_eq_add]
    rw [add_comm, ← N1_def, N2_def]
    apply add_comm
  · intros y y_in_union
    by_cases y_in : y ∈ Y2
    · rcases (Ord2 y y_in) with ⟨z, z_in_Z2, y_lt_z⟩
      by_cases z_in : z ∈ Y1
      · rcases (Ord1 z z_in) with ⟨z', z'_in_Z1, z_lt_z'⟩
        use z'
        constructor
        · rw [mem_add]
          constructor
          exact z'_in_Z1
        · exact lt_trans y_lt_z z_lt_z'
      · use z
        constructor
        · rw [add_comm, mem_add]
          constructor
          rwa [mem_sub, count_eq_zero_of_not_mem, count_pos]
          exact z_in
        · exact y_lt_z
    · have y_in : y ∈ (Y1 - Z2) := by simp_all only [mem_add, false_or]
      have y_in_Y1 : y ∈ Y1 := by
        have : Y1 - Z2 ≤ Y1 := by
          simp_all [tsub_le_iff_right, le_add_iff_nonneg_right,
        zero_le]
        apply mem_of_le
        exact this
        exact y_in
      let ⟨w, ⟨left_1, right⟩⟩ := (Ord1 y) y_in_Y1
      subst P2_def M1_def N2_def
      simp_all only [empty_eq_zero, ne_eq, mem_add, or_true]
      use w
      tauto

private lemma transLT_of_isDershowitzMannaLT [dec : DecidableEq α]
    [DecidableRel (fun (x : α) (y : α) => x < y)] (M N : Multiset α)
    (DMLTMN : IsDershowitzMannaLT M N) : TransLT M N := by
  rcases DMLTMN with ⟨X, Y, Z, Z_not_empty, MXY, NXZ, h⟩
  unfold TransLT
  revert X Y M N
  induction Z using strongInductionOn
  case ih Z IH =>
    intro M N X Y M_def N_def Y_lt_Z
    cases em (card Z = 0)
    · simp_all
    cases em (card Z = 1)
    case inl hyp' hyp=>
      rw [card_eq_one] at hyp
      rcases hyp with ⟨z,Z_def⟩
      apply TransGen.single
      rw [Z_def] at N_def
      refine ⟨X, Y, z, M_def, N_def, ?_⟩
      simp only [Z_def, mem_singleton, exists_eq_left] at Y_lt_Z
      exact Y_lt_Z
    case inr hyp' hyp =>
      have : ∃ a, a ∈ Z := by
        rw [← Z.card_pos_iff_exists_mem]
        cases Z_empty : card Z
        tauto
        simp
      rcases this with ⟨z,z_in_Z⟩
      let newZ := Z.erase z
      have newZ_nonEmpty : newZ ≠ ∅ := by
        have : ∀ (n : ℕ), n ≠ 0 → n ≠ 1 → n ≥ 2 := by
          intros n h0 h1
          cases n
          case zero => contradiction
          case succ m =>
            cases m
            case zero => contradiction
            case succ n =>
              apply Nat.succ_le_succ
              simp_all
        have : 0 < card (erase Z z) := by
          subst M_def N_def
          simp_all only
          [empty_eq_zero, ne_eq, card_eq_zero, not_false_eq_true, ge_iff_le, card_erase_of_mem,
          Nat.pred_eq_sub_one, tsub_pos_iff_lt]
          apply this
          · simp_all only [card_eq_zero, not_false_eq_true]
          · simp_all only [not_false_eq_true]
        rw [card_pos] at this
        simp_all only [empty_eq_zero, ne_eq, not_false_eq_true]
      have newZ_sub_Z : newZ < Z := by simp (config := {zetaDelta := true}); exact z_in_Z
      let f : α → Multiset α := fun z => Y.filter (fun y => y < z) -- DecidableRel
      let N' := X + newZ + f z
      apply @transitive_transGen _ _ _ N'
      -- step from `N'` to `M`
      · apply IH newZ newZ_sub_Z newZ_nonEmpty
        change M = (X + f z) + (Y - f z)
        · ext a
          have count_lt := count_le_of_le a (filter_le (fun y => y < z) Y)
          rw [M_def]
          simp_all only [empty_eq_zero, ne_eq, card_eq_zero, not_false_eq_true,
            count_add, count_sub]
          let y := count a Y
          let x := count a X
          let fz := count a (filter (fun x => x < z) Y)
          change x + y = x + fz + (y - fz)
          change fz ≤ y at count_lt
          have : y = fz + (y - fz) := by simp_all only [add_tsub_cancel_of_le]
          linarith
        · unfold_let N'
          rw [add_assoc, add_assoc, add_comm newZ (f z)]
        · intro y y_in
          let Y_lt_Z := Y_lt_Z y
          have y_in_Y : y ∈ Y := by
            have Yfy_le_Y : Y - f z ≤ Y:= by simp (config := {zetaDelta := true})
            apply mem_of_le Yfy_le_Y
            exact y_in
          let Y_lt_Z := Y_lt_Z y_in_Y
          rcases Y_lt_Z with ⟨t, t_in_Z, y_lt_t⟩
          use t
          constructor
          · by_cases t_in_newZ : t ∈ newZ
            · exact t_in_newZ
            · exfalso
              have : t = z := by
                have : Z = newZ + {z} := by
                  unfold_let newZ
                  rw [add_comm, singleton_add]
                  simp [cons_erase z_in_Z]
                rw [this, mem_add] at t_in_Z
                have : t ∈ ( {z} : Multiset α) := Or.resolve_left t_in_Z t_in_newZ
                rwa [← mem_singleton]
              have y_in_fz : y ∈ f z := by
                unfold_let f; simp; rw [← this]; exact ⟨y_in_Y, y_lt_t⟩
              have y_notin_Yfz : y ∉ Y - f z := by
                by_contra
                let neg_f : α → Multiset α := fun y' => Y.filter (fun x => ¬ x < y')
                have : Y - f z = neg_f z := by
                  have fz_negfz_Y : f z + neg_f z = Y := filter_add_not _ _
                  rw [← fz_negfz_Y, add_tsub_cancel_left]
                have y_in_neg_fz : y ∈ neg_f z := this ▸ y_in
                subst_eqs
                unfold_let neg_f at *
                simp_all only [mem_filter]
              exact y_notin_Yfz y_in
          · exact y_lt_t
      -- single step `N` to `N'`
      · have : OneStepLT N' N := by
          refine ⟨X + newZ, f z, z, ?_, ?_, ?_ ⟩
          · rfl
          · have newZ_z_Z: newZ + {z} = Z := by
              unfold_let newZ; rw [add_comm, singleton_add]
              apply cons_erase z_in_Z
            have : X + newZ + {z} = X + (newZ + {z}) := by apply add_assoc
            rw [this, newZ_z_Z]
            exact N_def
          · unfold_let f; intro z z_in; simp at z_in; exact z_in.2
        apply TransGen.single
        exact this

/-- `TransLT` and `IsDershowitzMannaLT` are equivalent. -/
private lemma transLT_eq_isDershowitzMannaLT [DecidableEq α] [@DecidableRel α (· < ·)] :
    (TransLT : Multiset α → Multiset α → Prop) =
    (IsDershowitzMannaLT : Multiset α → Multiset α → Prop) := by
  funext X Y
  apply propext
  constructor
  · intros TransLT
    induction TransLT
    case single Z TransLT =>
      rcases TransLT with ⟨W, U, y, X_def, Z_def, U_lt_y⟩
      use W, U, {y}
      simp_all
    case tail _ aih bih =>
      apply isDershowitzMannaLT.trans _ _ _ _ bih
      apply isDershowitzMannaLT_of_oneStepLT
      assumption
  · apply transLT_of_isDershowitzMannaLT

/-- The desired theorem: If `LT.lt` is well-founded, then `IsDershowitzMannaLT` is well-founded. -/
theorem wellFounded_isDershowitzMannaLT [DecidableEq α]
    [DecidableRel (fun (x : α) (y : α) => x < y)] (wf_lt :  WellFoundedLT α) :
    WellFounded (IsDershowitzMannaLT : Multiset α → Multiset α → Prop) := by
  rw [← transLT_eq_isDershowitzMannaLT]
  apply WellFounded.transGen
  exact (isDershowitzMannaLT_singleton_wf wf_lt)

instance instWellFoundedisDershowitzMannaLT [DecidableEq α] [wf_lt : WellFoundedLT α]
    [DecidableRel (fun (x : α) (y : α) => x < y)]  :
    WellFoundedRelation (Multiset α) := ⟨IsDershowitzMannaLT, wellFounded_isDershowitzMannaLT wf_lt⟩

end Multiset
