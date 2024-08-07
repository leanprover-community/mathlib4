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

In this file we define the _Dershowitz-Manna ordering_ on multisets.
We prove that, given a well-founded partial order on the underlying set,
the Dershowitz-Manna ordering defined over multisets is also well-founded.

## Main results

- `MultisetDMLT` :  the standard definition fo the `Dershowitz-Manna ordering`.
- `dm_wf` :       the main theorem about the `Dershowitz-Manna ordering` being well-founded.
- `TransLT_eq_DMLT` : two definitions of the `Dershowitz-Manna ordering` are equivalent.

## References

* [Wikipedia, Dershowitz–Manna ordering*]
(https://en.wikipedia.org/wiki/Dershowitz%E2%80%93Manna_ordering)

* [CoLoR](https://github.com/fblanqui/color), a Coq library on rewriting theory and termination.
  Our code here is inspired by their formalization and the theorem is called `mOrd_wf` in the file
  [MultisetList.v](https://github.com/fblanqui/color/blob/1.8.5/Util/Multiset/MultisetOrder.v).

-/

variable {α : Type*}

/-- The standard Dershowitz–Manna ordering: -/
inductive MultisetDMLT [DecidableEq α] [Preorder α] (M N : Multiset α) : Prop :=
  | DMLT : ∀ (X Y Z : Multiset α),
    Y ≠ ∅ →
    M = Z + X →
    N = Z + Y →
    (∀ x ∈ X, ∃ y ∈ Y, x < y) → MultisetDMLT M N

/-- MultisetRedLT is a special case of MultisetDMLT. The transitive closure of it is used to define
    an equivalent (proved later) version of the ordering. -/
inductive MultisetRedLT [DecidableEq α] [LT α] (M N : Multiset α) : Prop :=
  | RedLT : ∀ (X Y : Multiset α) (a : α) ,
    (M = X + Y) →
    (N = X + {a}) →
    (∀ y, y ∈ Y → y < a) → MultisetRedLT M N

open Relation

/-- MultisetTransLT is the transitive closure of MultisetRedLT and is equivalent to MultisetDMLT
    (proved later). -/
def MultisetTransLT [DecidableEq α] [LT α] : Multiset α → Multiset α → Prop :=
    TransGen MultisetRedLT

/-- A shorthand notation: AccM defines the accessibility relation given MultisetRedLT. -/
def AccM [DecidableEq α] [Preorder α] : Multiset α → Prop := Acc MultisetRedLT

/- MultisetRedLT is a special case of MultisetDMLT. -/
theorem dmLT_of_redLT [DecidableEq α] [Preorder α] (M N : Multiset α) (h : MultisetRedLT M N):
    MultisetDMLT M N := by
  rcases h with ⟨X, Y, a, M_def, N_def, ys_lt_a⟩
  apply MultisetDMLT.DMLT Y {a} X _ M_def N_def
  · simpa
  · simp

/- Some useful lemmas about Multisets and the defined relations, some of which should be added to
   'mathlib4/Mathlib/Data/Multiset/Basic.lean': -/

lemma not_redLT_zero [DecidableEq α] [LT α] (M: Multiset α) : ¬ MultisetRedLT M 0 := by
  intro h
  cases h with
  | RedLT X Y a M nonsense _ =>
    have contra : a ∈ (0 : Multiset α):= by
      rw [nonsense]
      simp_all only [Multiset.mem_add, Multiset.mem_singleton, or_true]
    contradiction

-- Should be added to 'mathlib4/Mathlib/Data/Multiset/Basic.lean'
lemma mul_singleton_erase [DecidableEq α] {a : α} {M : Multiset α} :
    M - {a} = M.erase a := by
  ext
  simp [Multiset.erase_singleton, Multiset.count_singleton]
  split <;> simp_all

-- Should be added to 'mathlib4/Mathlib/Data/Multiset/Basic.lean'
lemma in_of_ne_of_cons_erase [DecidableEq α] {a a0: α} {M X : Multiset α}
    (H : M = (a0 ::ₘ X).erase a) (hyp : ¬ a = a0) : a0 ∈ M := by
  rw [H, Multiset.mem_erase_of_ne fun h ↦ hyp <| id <| Eq.symm h, Multiset.mem_cons]
  tauto

-- Should be added to 'mathlib4/Mathlib/Data/Multiset/Basic.lean'
lemma singleton_add_sub_of_cons_add [DecidableEq α] {a a0: α} {M X : Multiset α}
    (H : a ::ₘ M = X + {a0}) : M = X + {a0} - {a} := by
  by_cases hyp : a = a0
  · rw [hyp, add_comm] at H
    simp_all [Multiset.singleton_add]
  · have a0_a: a0 ≠ a := by rw [eq_comm] at hyp; exact hyp
    ext b
    simp [Multiset.count_cons, Multiset.count_singleton, Multiset.count_add]
    have H : Multiset.count b (a ::ₘ M) = Multiset.count b (X + {a0}) := by simp_all only
    [Multiset.count_add]
    by_cases ba : b = a
    · rw [ba] at *
      have : (a ::ₘ M).count a = M.count a + 1 := by simp
      simp_all
    by_cases ba0 : b = a0
    · have : (a ::ₘ M).count a0 = X.count a0 + 1 := by
        subst_eqs
        rw [add_comm, Multiset.singleton_add] at H
        simp_all
      have : M.count a0 = Multiset.count a0 (a ::ₘ M) := by
        have : a0 ≠ a := by simp_all
        rw [Multiset.count_cons_of_ne this M]
      simp_all
    · have : M.count b = (a ::ₘ M).count b := by
        have : b ≠ a := by simp_all
        rw [Multiset.count_cons_of_ne this M]
      rw [this]
      simp_all

lemma red_insert [DecidableEq α] [LT α] {a : α} {M N : Multiset α} (h : MultisetRedLT N (a ::ₘ M)) :
    ∃ M',
      N = (a ::ₘ M') ∧ (MultisetRedLT M' M) ∨ (N = M + M') ∧ (∀ x : α, x ∈ M' → x < a) := by
  rcases h with ⟨X, Y, a0, h1, h0, h2⟩
  by_cases hyp : a = a0
  · exists Y; right; apply And.intro
    · rw [h1, add_left_inj]
      rw [add_comm, Multiset.singleton_add] at h0
      simp_all
    · simp_all
  · exists (Y + (M - {a0}))
    left
    constructor --; apply And.intro
    · rw [h1]
      have : X = (M - {a0} + {a}) := by
        rw [add_comm, Multiset.singleton_add] at *
        ext b
        simp [Multiset.ext, Multiset.count_cons] at h0
        by_cases h : b = a
        · have := h0 b
          aesop
        · have := h0 b
          simp [mul_singleton_erase]
          aesop
      subst this
      rw [add_comm]
      nth_rewrite 2 [add_comm]
      rw [Multiset.singleton_add, Multiset.add_cons]
    · constructor
      · change Y + (M - {a0}) = (M - {a0}) + Y
        rw [add_comm]
      · change M = M - {a0} + {a0}
        have this0: M = X + {a0} - {a} := by apply singleton_add_sub_of_cons_add; exact h0
        have a0M: a0 ∈ M := by
          apply in_of_ne_of_cons_erase
          · change M = Multiset.erase (a0 ::ₘ X) a
            rw [mul_singleton_erase, add_comm] at this0
            exact this0
          · exact hyp
        rw [add_comm]
        simp_all [Multiset.singleton_add]
      exact h2

lemma acc_cons [DecidableEq α] [Preorder α] (a : α) (M0 : Multiset α)
    (_ : ∀ b M , LT.lt b a → AccM M → AccM (b ::ₘ M))
    (_ : AccM M0)
    (_ : ∀ M, MultisetRedLT M M0 → AccM (a ::ₘ M)) :
    AccM (a ::ₘ M0) := by
  constructor
  intros N N_lt
  change AccM N
  rcases (red_insert N_lt) with ⟨x, H, h0⟩
  case h.intro.inr h =>
    rcases h with ⟨H, h0⟩
    rw [H]
    clear H -- Needed to make simp_all below safe.
    induction x using Multiset.induction with
    | empty =>
      simpa
    | cons h =>
      simp_all only [Multiset.mem_cons, or_true, implies_true, true_implies, forall_eq_or_imp,
        Multiset.add_cons]
  case h.intro.inl.intro =>
    simp_all

lemma acc_cons_of_acc [DecidableEq α] [Preorder α] (a : α)
    (H : ∀ (b : α), ∀ M, LT.lt b a → AccM M → AccM (b ::ₘ M)) :
    ∀ M, AccM M → AccM (a ::ₘ M) := by
  unfold AccM
  intros M h0
  induction h0 with
  | intro x wfH wfh2 =>
    apply acc_cons
    · simpa
    · constructor
      simpa
    · simpa

lemma acc_cons_of_acc_of_lt [DecidableEq α] [Preorder α] :
    ∀ (a:α), Acc LT.lt a → ∀ M, AccM M → AccM (a ::ₘ M) := by
  intro w w_a
  induction w_a with
  | intro x _ ih =>
      intro M accM1
      apply @acc_cons_of_acc α _ _ _ _ _ accM1
      simp_all

/- If all elements of a multiset `M` are accessible with `LT.lt`, then the multiset M is
accessible given the `MultisetRedLT` relation. -/
lemma acc_of_acc_lt [DecidableEq α] [Preorder α] :
    ∀ (M : Multiset α), (∀x, x ∈ M → Acc LT.lt x) → AccM M  := by
  intros M wf_el
  induction M using Multiset.induction_on with
  | empty =>
    constructor
    intro y y_lt
    absurd y_lt
    apply not_redLT_zero
  | cons _ _ ih =>
    apply acc_cons_of_acc_of_lt
    · apply wf_el
      simp_all
    · apply ih
      intros
      apply wf_el
      simp_all

/- If `LT.lt` is well-founded, then `MultisetRedLT` is well-founded. -/
lemma redLT_wf [DecidableEq α] [Preorder α]
    (wf_lt : WellFoundedLT α) : WellFounded (MultisetRedLT : Multiset α → Multiset α → Prop) := by
  constructor
  intros a
  apply acc_of_acc_lt
  intros x _
  apply wf_lt.induction x
  intros y h
  apply Acc.intro y
  assumption

/- If `MultisetRedLT` is well-founded, then its transitive closure `MultisetTransLT` is also
well-founded. -/
lemma transLT_wf [DecidableEq α] [LT α]
    (h : WellFounded (MultisetRedLT : Multiset α → Multiset α → Prop)) :
    WellFounded (MultisetTransLT : Multiset α → Multiset α → Prop) := by
  unfold MultisetTransLT
  apply WellFounded.transGen
  assumption

-- Should be added to 'mathlib4/Mathlib/Data/Multiset/Basic.lean'
lemma inter_add_sub_of_eq {α} [dec : DecidableEq α] {M N P Q: Multiset α} (h : M + N = P + Q) :
    N = N ∩ Q + (P - M) := by
  ext x
  rw [Multiset.count_add, Multiset.count_inter, Multiset.count_sub]
  have h0 : M.count x + N.count x = P.count x + Q.count x := by
    rw [Multiset.ext] at h
    simp_all only [Multiset.mem_add, Multiset.count_add]
  by_cases l_u : M.count x ≤ P.count x
  · have : N.count x ≥ Q.count x := by linarith
    simp_all only [ge_iff_le, min_eq_right]
    have := tsub_add_cancel_of_le l_u
    linarith
  · simp_all only [not_le, gt_iff_lt]
    have : Multiset.count x N ≤ Multiset.count x Q := by linarith
    have := le_of_lt l_u
    simp_all

-- Should be added to 'mathlib4/Mathlib/Data/Multiset/Basic.lean'
lemma mem_sub_of_not_mem_of_mem {α} [DecidableEq α] (x : α) (X Y: Multiset α) (x_in_X : x ∈ X)
    (x_notin_Y : x ∉ Y) : x ∈ X - Y  := by
  have : Multiset.count x X ≥ 1 := by
    rw [← Multiset.one_le_count_iff_mem] at x_in_X
    exact x_in_X
  rw [← Multiset.one_le_count_iff_mem, Multiset.count_sub]
  simp_all only [not_false_eq_true, Multiset.count_eq_zero_of_not_mem, tsub_zero]

-- `MultisetDMLT` is transitive.
lemma dmlt_trans {α} [pre : Preorder α] [dec : DecidableEq α]:
    ∀ (M N P : Multiset α) , MultisetDMLT N M → MultisetDMLT P N → MultisetDMLT P M := by
  intros M N P LTNM LTPN
  rcases LTNM with ⟨Y1, X1, Z1, X1_ne, N1_def, M1_def, Ord1⟩
  rcases LTPN with ⟨Y2, X2, Z2, _, P2_def, N2_def, Ord2⟩
  apply MultisetDMLT.DMLT (Y2 + (Y1 - X2)) (X1 + (X2 - Y1)) (Z1 ∩ Z2)
  · simp_all only [Multiset.empty_eq_zero, ne_eq, add_eq_zero_iff, false_and, not_false_eq_true]
  · rw [P2_def]
    have : Z1 ∩ Z2 + (Y2 + (Y1 - X2)) = Z1 ∩ Z2 + (Y1 - X2) + Y2 := by
      have : (Y2 + (Y1 - X2)) = (Y1 - X2) + Y2 := by rw [add_comm]
      rw [this, add_assoc]
    rw [this]
    have : Z1 ∩ Z2 + (Y1 - X2) = Z2 ∩ Z1 + (Y1 - X2) := by
      rw [Multiset.inter_comm]
    rw [this,← inter_add_sub_of_eq]
    rw [add_comm, ← N2_def, N1_def]
    apply add_comm
  · rw [M1_def]
    have : Z1 ∩ Z2 + (X1 + (X2 - Y1)) = Z1 ∩ Z2 + (X2 - Y1) + X1 := by
      have : (X1 + (X2 - Y1)) = (X2 - Y1) + X1 := by rw [add_comm]
      rw [this, add_assoc]
    rw [this, add_left_inj]
    apply inter_add_sub_of_eq
    rw [add_comm, ← N1_def, N2_def]
    apply add_comm
  · intros y y_in_union
    by_cases y_in : y ∈ Y2
    · rcases (Ord2 y y_in) with ⟨x, x_in_X2, y_lt_x⟩
      by_cases x_in : x ∈ Y1
      · rcases (Ord1 x x_in) with ⟨x', x'_in_X1, x_lt_x'⟩
        use x'
        constructor
        · rw [Multiset.mem_add]
          constructor
          exact x'_in_X1
        · exact lt_trans y_lt_x x_lt_x'
      · use x
        constructor
        · rw [add_comm, Multiset.mem_add]
          constructor
          apply mem_sub_of_not_mem_of_mem
          exact x_in_X2
          exact x_in
        · exact y_lt_x
    · have y_in : y ∈ (Y1 - X2) := by simp_all only [Multiset.mem_add, false_or]
      let h := (Ord1 y)
      have y_in_Y1 : y ∈ Y1 := by
        have : Y1 - X2 ≤ Y1 := by simp_all only [tsub_le_iff_right, le_add_iff_nonneg_right,
        zero_le]
        apply Multiset.mem_of_le
        exact this
        exact y_in
      let _ := h y_in_Y1
      aesop

lemma transLT_of_dmLT [dec : DecidableEq α] [Preorder α]
    [DecidableRel (fun (x : α) (y: α) => x < y)] (M N : Multiset α) (DMLTMN : MultisetDMLT M N) :
    MultisetTransLT M N := by
  -- intros M N LTXY
  cases DMLTMN
  case DMLT X Y Z Y_not_empty MZX NZY h =>
    unfold MultisetTransLT
    revert Z X M N
    induction Y using Multiset.strongInductionOn
    case ih Y IH =>
      intro M N X Z M_def N_def X_lt_Y
      cases em (Multiset.card Y = 0)
      · simp_all
      cases em (Multiset.card Y = 1)
      case inl hyp' hyp=>
        rw [Multiset.card_eq_one] at hyp
        rcases hyp with ⟨y,Y'_def⟩
        apply TransGen.single
        rw [Y'_def] at N_def
        apply @MultisetRedLT.RedLT α _ _ M N Z X y M_def N_def
        simp [Y'_def] at X_lt_Y
        exact X_lt_Y
      case inr hyp' hyp =>
        have : ∃ a, a ∈ Y := by
          rw [← Y.card_pos_iff_exists_mem]
          cases foo : Multiset.card Y
          tauto
          simp
        rcases this with ⟨y,claim⟩
        let newY := Y.erase y
        have newY_nonEmpty : newY ≠ ∅ := by
          have : ∀ (n : ℕ), n ≠ 0 → n ≠ 1 → n ≥ 2 := by
            intros n h0 h1
            cases n
            case zero => contradiction
            case succ m =>
              cases m
              case zero => contradiction
              case succ n=>
                apply Nat.succ_le_succ
                simp_all only [le_add_iff_nonneg_left, zero_le]
          have : 0 < Multiset.card (Multiset.erase Y y) := by aesop
          rw [Multiset.card_pos] at this
          simp_all only [Multiset.empty_eq_zero, ne_eq, not_false_eq_true]
        have newY_sub_Y : newY < Y := by simp (config := {zetaDelta := true}); exact claim
        let f : α → Multiset α := fun y' => X.filter (fun x => x < y') -- DecidableRel
        let N' := Z + newY + f y
        apply @transitive_transGen _ _ _ N'
        -- step from N' to M
        · apply IH newY newY_sub_Y newY_nonEmpty
          change M = (Z + f y) + (X - f y)
          · ext a
            have count_lt := Multiset.count_le_of_le a (Multiset.filter_le (fun x => x < y) X)
            rw [M_def]
            simp_all only [Multiset.empty_eq_zero, ne_eq, Multiset.card_eq_zero, not_false_eq_true,
              Multiset.count_add, Multiset.count_sub]
            let x := Multiset.count a X
            let z := Multiset.count a Z
            let fx := Multiset.count a (Multiset.filter (fun x => x < y) X)
            change z + x = z + fx + (x - fx)
            change fx ≤ x at count_lt
            have : x = fx + (x - fx) := by simp_all only [add_tsub_cancel_of_le]
            linarith
          · unfold_let N'
            rw [add_assoc, add_assoc, add_comm newY (f y)]
          · intro x x_in
            let X_lt_Y := X_lt_Y x
            have x_in_X : x ∈ X := by
              have Xfy_le_X : X - f y ≤ X:= by simp (config := {zetaDelta := true})
              apply Multiset.mem_of_le Xfy_le_X
              exact x_in
            let X_lt_Y := X_lt_Y x_in_X
            rcases X_lt_Y with ⟨t, t_in_Y, x_lt_t⟩
            use t
            constructor
            · by_cases t_in_newY : t ∈ newY
              · exact t_in_newY
              · exfalso
                have : t = y := by
                  have : Y = newY + {y} := by
                    unfold_let newY
                    rw [add_comm, Multiset.singleton_add]
                    simp [Multiset.cons_erase claim]
                  rw [this, Multiset.mem_add] at t_in_Y
                  have : t ∈ ( {y} : Multiset α) := Or.resolve_left t_in_Y t_in_newY
                  rwa [← Multiset.mem_singleton]
                have x_in_fy : x ∈ f y := by
                  unfold_let f; simp; rw [← this]; exact ⟨x_in_X, x_lt_t⟩
                have x_notin_Xfy : x ∉ X - f y := by
                  by_contra
                  let neg_f : α → Multiset α := fun y' => X.filter (fun x => ¬ x < y')
                  have : X - f y = neg_f y := by
                    have fy_negfy_X : f y + neg_f y = X := Multiset.filter_add_not _ _
                    rw [← fy_negfy_X, add_tsub_cancel_left]
                  have x_in_neg_fy : x ∈ neg_f y := this ▸ x_in
                  subst_eqs
                  unfold_let neg_f at *
                  simp_all only [Multiset.mem_filter]
                exact x_notin_Xfy x_in
            · exact x_lt_t
        -- single step N to N'
        · have : MultisetRedLT N' N := by
            apply MultisetRedLT.RedLT (Z + newY) (f y) y
            · rfl
            · have newY_y_Y: newY + {y} = Y := by
                unfold_let newY; rw [add_comm, Multiset.singleton_add]
                apply Multiset.cons_erase claim
              have : Z + newY + {y} = Z + (newY + {y}) := by apply add_assoc
              rw [this, newY_y_Y]
              exact N_def
            · unfold_let f; intro z z_in; simp at z_in; exact z_in.2
          apply TransGen.single
          exact this

/- MultisetTransLT and MultisetDMLT are equivalent. -/
lemma transLT_eq_dmLT [DecidableEq α] [Preorder α] [DecidableRel (fun (x : α) (y: α) => x < y)]:
    (MultisetTransLT : Multiset α → Multiset α → Prop) =
    (MultisetDMLT : Multiset α → Multiset α → Prop) := by
  funext X Y
  apply propext
  constructor
  · -- TransLT → DMLT:
    intros TransLT
    induction TransLT with
    | single TransLT =>
      rcases TransLT with ⟨Z, X, y, a_def, b_def, X_lt_y⟩
      use X
      · simp
      · simpa
    | tail _ aih bih => -- it suffices to show MultisetDMLT is transitive
      apply dmlt_trans _ _ _ _ bih
      apply dmLT_of_redLT
      assumption
  · -- DMLT → TransLT:
    apply transLT_of_dmLT

/- The desired theorem: If `LT.lt` is well-founded, then `MultisetDMLT` is well-founded. -/
theorem dmLT_wf [DecidableEq α] [Preorder α] [DecidableRel (fun (x : α) (y : α) => x < y)]
    (wf_lt :  WellFoundedLT α) :WellFounded (MultisetDMLT : Multiset α → Multiset α → Prop) := by
  rw [← transLT_eq_dmLT]
  exact transLT_wf (redLT_wf wf_lt)
