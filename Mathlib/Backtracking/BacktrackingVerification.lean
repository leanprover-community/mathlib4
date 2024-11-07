/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Vector.Defs
import Batteries.Data.List.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith.Frontend

/-!
# Marginis
/- We formally verify the method known as recursive backtracking
for a monotone predicate P and another predicate Q at the leaves. -/

A vector of length L monus k, thought of as a possible suffix for a word of length L
in which the first k bits are unspecified
For example, a Gap 10 10 has length 10 - 10.

[This is a rewrite to replace `by induction` by `match with`.]

-/

open scoped Classical -- this does not prevent us from also using `by decide`

/-- A predicate `P` preserved under suffixes, with an optional condition `Q` at the leaves. -/
structure MonoPred (b:Nat) where
  /-- The predicate to be checked recursively. -/
  P : List (Fin b) → Prop
  preserved_under_suffixes (u v : List (Fin b)): u <:+ v → P v → P u
  /-- The optional predicate at the leaves. -/
  Q (l: List (Fin b)) : Prop := True

/-- A predicate `P` with an optional condition `Q` at the leaves. -/
structure MonoPred_unverified (b:Nat) where
  /-- The predicate to be checked (recursively if it is monotone). -/
  P : List (Fin b) → Prop
  /-- The optional predicate at the leaves. -/
  Q : List (Fin b) → Prop := fun _ ↦ True -- we can specify an extra condition that is not monotone

open Mathlib

/-- A vector `k` entries away from full length `L`. -/
def Gap (b L k : ℕ) : Type := Vector (Fin b) (L - k)

/-- Note that `Gap_cons` requires the use of L.succ instead of just L. -/
def Gap_cons {n L b:ℕ} (a:Fin b) (w : Gap b L.succ n.succ)
    (h: ¬ n ≥ L.succ) : Gap b L.succ n :=
  ⟨a :: w.1, by
      rw [List.length_cons, Vector.length_val,Nat.succ_sub_succ_eq_sub]
      exact .symm <| Nat.succ_sub <| Nat.not_lt.mp h⟩

/-- The empty "gap", with possible length overflow. -/
def Gap_nil {k b L : ℕ} (h : k ≥ L) : Gap b L k := ⟨List.nil, (Nat.sub_eq_zero_of_le h).symm⟩

/-- The empty "gap". -/
def Gap_nil' (b n : ℕ) : Gap b n n := ⟨[], by simp⟩

/-- The number of strings satisfying `P ∧ Q`, where
`P` is a monotone predicate and `Q` is a predicate at the leaves.-/
def num_by_backtracking {k b L:ℕ} (P Q : List (Fin b) → Prop) [DecidablePred P] [DecidablePred Q]
    (w : Gap b L.succ k) : ℕ := match k with
    | 0 =>  ((if (P w.1 ∧ Q w.1) then 1 else 0))
    | Nat.succ n =>
        (ite (P w.1)) (dite (n ≥ L.succ)
          (fun h ↦ num_by_backtracking P Q (Gap_nil h) )
          fun h ↦ List.sum <|List.ofFn fun a ↦ num_by_backtracking P Q <|Gap_cons a w h
        ) 0

/-- The list `w` is a suffix of `a :: w`, in the setting of the `Gap` types. -/
theorem cons_suffix {b:ℕ} {L n_1: ℕ} {a : Fin b} (h: ¬n_1 ≥ Nat.succ L)
    (w : Vector (Fin b) (Nat.succ L -  (Nat.succ n_1))) :
    w.1 <:+ (Gap_cons a w h).1 := by exists [a]

/-- Preservation under suffices for `M.P`, for the `Gap` types.-/
lemma still_holds {b L z: ℕ } {M: MonoPred b} {w: Gap b (Nat.succ L) (Nat.succ z)}
    {h: ¬z ≥ Nat.succ L} {a : Fin b} (H: M.P (Gap_cons a w h).1) :
    M.P w.1 := M.preserved_under_suffixes w.1 (Gap_cons a w h).1 (cons_suffix _ _) H


/-- Simplifying a list defined by a vacuous `ite`. -/
lemma if_replicate {b : ℕ} (P : Fin b → Prop) (c : Fin b → ℕ) [DecidablePred P]
    (h : ∀ a, ¬ P a):
    List.ofFn (fun a ↦ if P a then c a else 0) = List.replicate b 0 :=
  List.eq_replicate_iff.mpr (by
    simp only [List.length_ofFn, List.forall_mem_ofFn_iff, ite_eq_right_iff, true_and];tauto)

/-- Simplifying a gap defined by a vacuous `ite`. -/
lemma if_replicate₀ {b L : ℕ} {M : MonoPred b} [DecidablePred M.P] [DecidablePred M.Q]
    {w : Gap b L.succ (Nat.succ 0)} (H : ¬M.P w.1) :
    List.ofFn (fun a => ite (M.P (Gap_cons a w (Nat.not_add_one_le_zero L)).1
    ∧ M.Q (Gap_cons a w (Nat.not_add_one_le_zero L)).1) 1 0)
    = List.replicate b 0 :=
  if_replicate _ _ (fun a => by
    rw [not_and]
    exact fun h => False.elim <|H <|still_holds h)

/-- Simplifying a gap defined by a vacuous `ite` involving `num_by_backtracking`. -/
lemma if_replicate₁ {b L : ℕ} {M : MonoPred b} [DecidablePred M.P] [DecidablePred M.Q]
    {n_1 : ℕ} (hnL : ¬n_1 + 1 ≥ L.succ) {w : Gap b L.succ (n_1 + 1).succ} (H : ¬M.P w.1) :
    (List.ofFn fun a ↦
        if M.P (Gap_cons a w hnL).1 then
          (if h : n_1 ≥ L.succ then num_by_backtracking M.P M.Q (Gap_nil h)
          else (List.ofFn fun a_1 ↦ num_by_backtracking M.P M.Q
            (Gap_cons a_1 (Gap_cons a w hnL) h)).sum)
        else 0) =
    List.replicate b 0 :=
  if_replicate _ _ (fun a => by
    contrapose H
    simp only [Decidable.not_not] at *
    exact still_holds H)

/-- Writing `num_by_backtracking` as a sum of values of itself. -/
theorem branch_out {b n L : ℕ} (M:MonoPred b) [DecidablePred M.P] [DecidablePred M.Q]
    (hnL: ¬ n ≥ L.succ) (w : Gap b L.succ n.succ) :
    num_by_backtracking M.P M.Q (w)
    = List.sum (List.ofFn (fun a ↦ num_by_backtracking M.P M.Q (Gap_cons a w hnL))) := by
  cases n with
  | zero =>
    unfold num_by_backtracking
    split_ifs with H
    · congr
    · rw [if_replicate₀ H]
      exact .symm <|List.sum_const_nat b 0
  | succ n_1 =>
    unfold num_by_backtracking
    by_cases H : (M.P w.1)
    · rw [if_pos H, dif_neg hnL]
      congr
    · rw [if_neg H, if_replicate₁ hnL H]
      simp

/-- Subtype extensionality. -/
theorem subtype_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x):
    {x : α // P x} =  {x : α // Q x} :=
  congrArg Subtype (funext (fun x => propext (h x)))

/-- Fintype.card extensionality. -/
theorem fincard_ext {α:Type} {P Q : α → Prop} (h : ∀ x, P x ↔ Q x)
    [Fintype {x : α // P x}][Fintype {x : α // Q x}] :
    Fintype.card {x : α // P x} = Fintype.card {x : α // Q x} := by
  simp_rw [subtype_ext P Q h]

/-- Two vectors are equal if they have the same length and one is a suffix of the other. -/
theorem Vector_eq_of_suffix_of_length_eq {L b:ℕ} {w : Vector (Fin b) L}
    {v : Vector (Fin b) L} (hv : w.1 <:+ v.1) : w.1 = v.1 :=
  List.IsSuffix.eq_of_length hv <| Eq.trans w.2 <| .symm v.2


/-- If `i≠j` then `i::w` and `j::w` can't be suffixes of the same vector `v`.-/
theorem disjoint_branch''  {L b n : ℕ} {M : MonoPred b} (w: Vector (Fin b) (L.succ-n.succ))
    (h : ¬ n ≥ L.succ) {i j : Fin b} (hp: i ≠ j) : Disjoint
    (fun v  : Vector (Fin b) L.succ ↦ (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons i w h).1 <:+ v.1 )
    (fun v  : Vector (Fin b) L.succ ↦ (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons j w h).1 <:+ v.1 ) := by
  intro S h0S h1S v hSv
  obtain ⟨t₁,ht₁⟩ := (h0S v hSv).2
  obtain ⟨t₀,ht₀⟩ := (h1S v hSv).2
  have : t₁ ++ [i] ++ w.1 = t₀ ++ [j] ++ w.1 := calc
                        _ = t₁ ++  i  :: w.1 := (List.append_cons t₁ i w.1).symm
                        _ = v.1              := ht₁
                        _ = t₀ ++ j :: w.1   := ht₀.symm
                        _ = _                := (List.append_cons t₀ j w.1)
  have : (t₁ ++ [i]).getLast (by simp)
       = (t₀ ++ [j]).getLast (by simp) :=
        List.getLast_congr _ _ ((List.append_left_inj w.1).mp this)
  simp only [List.getLast_append] at this
  exact hp this

/-- If `y = t ++ x` and `y` is longer than `x` then `t` is nonempty. -/
lemma list_get_ne_nil {α: Type} {x y t: List α} (ht: t ++ x = y) (hl: x.length < y.length) :
    t ≠ [] := fun hc => (lt_self_iff_false x.length).mp <| (List.nil_append _ ▸ hc ▸ ht) ▸ hl


/-- For vectors `t,y,x`, if `y = t ++ x` and `y` is longer than `x` then `t` is nonempty. -/
theorem Vector_append_succ_ne_nil {L n b: ℕ}
    {w: Vector (Fin b) (Nat.succ L - Nat.succ n)}
    {v: Vector (Fin b) (Nat.succ L)} {t: List (Fin b)} (ht: t ++ w.1 = v.1) :
    t ≠ List.nil := by
  intro hc
  rw [hc, List.nil_append] at ht
  apply congr_arg List.length at ht
  simp only [Vector.length_val, Nat.succ_sub_succ_eq_sub] at ht
  exact Nat.not_succ_le_self L <| ht ▸ (Nat.sub_le L n)

/-- The reverse of a nonempty list is also nonempty. -/
theorem List_reverse_ne_nil {α : Type} {t : List α} (hlong : t ≠ []) : t.reverse ≠ [] := by
  simp only [ne_eq, List.reverse_eq_nil_iff] at *;tauto

/-- Reversing a list constructor. -/
theorem List_reverse_cons {α : Type} {s t: List α} {a: α} (hs: t.reverse = a :: s) :
    t = s.reverse ++ [a] := by
  apply congrArg List.reverse at hs
  rw [List.reverse_reverse, List.reverse_cons] at hs
  exact hs


/-- If `x` and `y` have `w` as a prefix and are of the same length as `w`, then `x=y`. -/
lemma prefix_of_same {L b: ℕ} (w: Vector (Fin b) L) :
    ∀ x y : {v : Vector (Fin b) L // w.1 <:+ v.1}, x.1 = y.1 := fun x y => SetCoe.ext <| by
  rw [← Vector_eq_of_suffix_of_length_eq x.2,
    ← Vector_eq_of_suffix_of_length_eq y.2]

/-- The sum of a list of values of a function. -/
lemma list_sum_ofFn_succ {n:ℕ} (f:Fin n.succ → ℕ):
    List.sum (List.ofFn (fun i ↦ f i)) = List.sum (List.ofFn (fun i : Fin n ↦ f i)) + f n := by
  repeat (rw [List.sum_ofFn])
  simp only [Fin.coe_eq_castSucc, Fin.natCast_eq_last]
  exact Fin.sum_univ_castSucc f

/-- If a sequence of `n+1` sets are pairwise disjoint, then the union
  of the first `n` is disjoint from the last set. -/
lemma disjoint_from_last {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop}
    (h: ∀ (i j : Fin (Nat.succ n_1)), i ≠ j → Disjoint (p i) (p j)) :
    Disjoint (fun x : α ↦ ∃ i, p (Fin.castSucc i) x) (fun x : α ↦ p (n_1) x) := by
  intro S hS₀ hS₁ x hSx
  obtain ⟨i,hi⟩ := hS₀ x hSx
  have : (Fin.castSucc i).1 ≠ n_1 := fun hc => by
    have := hc ▸ i.2
    simp_all
  have : (Fin.castSucc i) ≠ n_1 := fun _ => by simp_all

  have hi: (fun y ↦ y=x) ≤ p (Fin.castSucc i) := fun y hy => hy ▸ hi
  have hj: (fun y ↦ y=x) ≤ p n_1              := fun y hy => hS₁ y (hy ▸ hSx)
  exact h (Fin.castSucc i) n_1 this hi hj x rfl

/-- One of the propositions `p_0,...,p_n` holds iff either the `or` statement of
  the first `n` holds, or `p_n` holds. -/
lemma distinguish_from_last {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop} (x : α) :
    (∃ i, p (Fin.castSucc i) x) ∨ p (n_1) x ↔ ∃ i, p i x := by
  constructor;
  · intro ha
    cases ha with
    |inl h => obtain ⟨i,hi⟩ := h;exists i;norm_cast
    |inr   => exists n_1
  · intro ha; obtain ⟨i,hi⟩ := ha; by_cases hin:(i=n_1)
    · right
      simp_all
    · left
      exists Fin.castPred i (by simp_all)

/-- If some sets are disjoint, then the cardinality of their union is the sum
  of their cardinalities. -/
theorem Fintype_card_subtype_of_disjoint {α:Type} [Fintype α] {n:ℕ} (p : Fin n → α → Prop)
    [Fintype {x:α // ∃ i, p i x}] [∀ i, Fintype {x:α // p i x}]
    (h : ∀ i j, i ≠ j → Disjoint (p i) (p j)) :
    List.sum (List.ofFn (fun i ↦ Fintype.card {x:α // p i x}))
      = Fintype.card {x:α // ∃ i, p i x} := by
  induction n with
  |zero => simp
  |succ n_1 n_ih =>
    rw [list_sum_ofFn_succ]
    norm_cast
    have : ∀ (i j : Fin n_1), i ≠ j → Disjoint (p i.castSucc) (p j.castSucc) :=
      fun i j hij => h (Fin.castSucc i) (Fin.castSucc j) (by simp_all)
    rw [
      n_ih (fun i a ↦ p (Fin.castSucc i) a) this,
      ← Fintype.card_subtype_or_disjoint _ _ <|disjoint_from_last h
    ]
    exact fincard_ext distinguish_from_last

/-- If x is a proper suffix of y then
  some a :: x is a suffix of y. -/
lemma get_union {α :Type} {x y : List α} (h : x <:+ y) (hl : x.length < y.length) :
    ∃ a : α, a :: x <:+ y := by
  obtain ⟨t,ht⟩ := h
  obtain ⟨a,⟨s,hs⟩⟩ := List.exists_cons_of_ne_nil <|List_reverse_ne_nil <|list_get_ne_nil ht hl
  use a, s.reverse
  rw [List_reverse_cons hs, List.append_assoc, List.singleton_append] at ht
  exact ht

/-- If x is a proper suffix of y then
  some a :: x is a suffix of y, and vice versa. -/
theorem suffix_cons {b L n: ℕ} (w : Gap b (Nat.succ L) (Nat.succ n)) (v : Gap b (Nat.succ L) 0) :
    w.1 <:+ v.1 ↔ ∃ a, a :: w.1 <:+ v.1 := by
  constructor
  · intro h
    have : w.1.length < v.1.length := by
      rw [w.2, v.2, Nat.succ_sub_succ_eq_sub]
      exact Nat.sub_lt_succ L n
    exact get_union h this
  · exact fun ⟨a,⟨t,ht⟩⟩ => ⟨t ++ [a], by simp_all⟩

/-- Verifies recursive backtracking for `b`-ary trees with monotone predicates `P`,
   with a non-monotone `Q` at the leaves. -/
theorem backtracking_verification {k b L:ℕ} (bound : k ≤ L.succ) (M:MonoPred b)
    [DecidablePred M.P] [DecidablePred M.Q] (w : Vector (Fin b) (L.succ-k)):
    Fintype.card {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1}
    = num_by_backtracking M.P M.Q w := match k with
  | 0 => by
    have := subsingleton_iff.mpr (
        fun x y : {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1}
        ↦ SetCoe.ext (prefix_of_same w ⟨x.1,x.2.2⟩ ⟨y.1,y.2.2⟩)
      )
    unfold num_by_backtracking; split_ifs with hs
    · have := uniqueOfSubsingleton
        (⟨w,⟨hs, List.suffix_rfl⟩⟩ : {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1)
          ∧ w.1 <:+ v.1})
      exact Fintype.card_unique
    · have : ∀ v: Vector (Fin b) L.succ ,¬ ((M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1) := by
        intro v hc
        have : w = v := SetCoe.ext (Vector_eq_of_suffix_of_length_eq hc.2)
        subst this; tauto
      have := Subtype.isEmpty_of_false this
      exact Fintype.card_eq_zero
  | Nat.succ n => by
    have notg : ¬ (n ≥ L.succ) := Nat.not_le_of_lt bound
    rw [
      branch_out _ notg,
      ← funext (fun i : Fin b ↦
        backtracking_verification (Nat.le_of_lt bound) _ (Gap_cons i w notg))]
    rw [Fintype_card_subtype_of_disjoint _ (fun _ _ hij ↦ disjoint_branch'' w notg hij)];
    apply fincard_ext; intro x;
    rw [and_assoc,suffix_cons w x]
    tauto

/-- Gap has decidable equality. -/
instance {b L:ℕ} : DecidableEq (Gap b (Nat.succ L) 0) := by
  unfold Gap
  exact Subtype.instDecidableEq


/-- The lists with a given suffix satisfying conditions P (recursively) and Q. -/
def satisfy_and_have_suffix {k b :ℕ} {L:ℕ} (P: List (Fin b) → Prop) [DecidablePred P]
    (Q: List (Fin b) → Prop) [DecidablePred Q] (w : Gap b L.succ k) : Finset (Gap b L.succ 0) :=
  match k with
  | 0 => ((ite (P w.1 ∧ Q w.1) {w} ∅))
  | Nat.succ n =>
      (ite (P w.1))
      (
        dite (n ≥ L.succ)
        (fun h ↦ satisfy_and_have_suffix P Q (Gap_nil h))
        (
          fun h ↦ Finset.biUnion (Finset.univ : Finset (Fin b)) (
            (fun a ↦ (satisfy_and_have_suffix P Q (Gap_cons a w h)))
          )
        )
      )
      ∅

/-- `those_with_suffix` as a union of its own values.  -/
theorem branch_out_set (b:ℕ) {n L : ℕ} {M : MonoPred b} [DecidablePred M.P]
    [DecidablePred M.Q] (hnL: ¬ n ≥ L.succ) (w : Gap b L.succ n.succ) :
    satisfy_and_have_suffix M.P M.Q (w)
    = Finset.biUnion (Finset.univ : Finset (Fin b))
      (fun a ↦ satisfy_and_have_suffix M.P M.Q (Gap_cons a w hnL)) := match n with
  | 0 => by
    unfold satisfy_and_have_suffix;
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.add_succ_sub_one, Nat.add_zero, ge_iff_le,
      nonpos_iff_eq_zero, add_eq_zero, one_ne_zero, and_false, ↓reduceDIte, Nat.sub_zero]

    by_cases H : M.P w.1
    · rw [if_pos H]
      congr
    · symm
      have : ∀ a, ite (M.P (Gap_cons a w hnL).1 ∧ M.Q (Gap_cons a w hnL).1)
          ({Gap_cons a w hnL} : Finset _) ∅ = ∅ := by
          intro
          rw [ite_eq_right_iff, and_imp]
          exact fun h => False.elim <|H <|still_holds h
      rw [funext this]
      apply Finset.ext
      simp_all
  | Nat.succ k => by
    unfold satisfy_and_have_suffix; simp only [ge_iff_le, Nat.zero_eq, Nat.sub_zero]
    by_cases H : (M.P w.1)
    · rw [if_pos H, dif_neg hnL]; simp; congr
    · rw [if_neg H]; symm
      apply Finset.ext; intro v; constructor;
      · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
          Finset.not_mem_empty, forall_exists_index, imp_false]
        intro hv
        obtain ⟨a,ha⟩ := hv
        split_ifs at * with h₀
        · have := still_holds h₀
          tauto
        · have := still_holds h₀
          tauto
        · simp at ha
      · simp

/-- Gap is a fintype. -/
instance {b L:ℕ} : Fintype (Gap b (Nat.succ L) 0) := by
  unfold Gap
  exact Vector.fintype

/-- If `w` has full length and doesn't satisfy `P ∧ Q`, then none of its extensions
  (of the same length) do either. -/
theorem filter_suffix_empty {b L: ℕ} {P Q : List (Fin b) → Prop} [DecidablePred P] [DecidablePred Q]
    {w: Gap b (Nat.succ L) 0} (holds: ¬(P w.1 ∧ Q w.1)) :
    Finset.filter (fun v : Gap b L.succ 0 => P v.1 ∧ Q v.1 ∧ w.1 <:+ v.1) Finset.univ = ∅ :=
  Finset.ext <| fun a => by
  simp only [Nat.succ_eq_add_one, Nat.sub_zero, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.not_mem_empty, iff_false, not_and]
  exact fun hP hQ hc =>
    ((List.IsSuffix.eq_of_length hc (Eq.trans w.2 a.2.symm)) ▸ holds) <| And.intro hP hQ

/-- If `w` satisfies a predicate then the set of its extensions of the same length
  that do the same is `{w}`. -/
theorem filter_suffix_singleton {b L: ℕ} {P Q : List (Fin b) → Prop}
    [DecidablePred P] [DecidablePred Q] {w: Gap b (Nat.succ L) 0} (holds: (P w.1 ∧ Q w.1)) :
    {w} = Finset.filter (fun v : Gap b L.succ 0 => P v.1 ∧ Q v.1 ∧ w.1 <:+ v.1) Finset.univ := by
  apply Finset.ext
  intro a
  constructor
  · intro ha
    rw [Finset.mem_singleton] at ha
    subst ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨holds.1, ⟨holds.2,by exists []⟩⟩
  · simp only [Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton, and_imp]
    intro _ _ hs
    have : a.1 = w.1 := .symm <|List.IsSuffix.eq_of_length hs (by rw [w.2,a.2])
    exact Vector.eq _ _ this

open Finset

/-- `satisfy_and_have_suffix` is as advertised. -/
theorem verify_those_with_suffix {k b :ℕ} {L:ℕ} (bound : k ≤ L.succ) {M:MonoPred b}
    [DecidablePred M.P] [DecidablePred M.Q] (w : Gap b L.succ k) :
    satisfy_and_have_suffix M.P M.Q w = filter (
      fun v : Gap b L.succ 0 ↦ M.P v.1 ∧ M.Q v.1 ∧ w.1 <:+ v.1
    ) univ := match k with
  | 0 => by
    unfold satisfy_and_have_suffix
    simp only [Nat.zero_eq, Nat.sub_zero, filter_congr_decidable]
    split_ifs with h
    · exact filter_suffix_singleton h
    symm
    exact filter_suffix_empty h

  | Nat.succ n => by
    by_cases hLn: (L.succ ≤ n)
    · have : n.succ ≤ n := calc
                _ ≤ L.succ := bound
                _ ≤ n      := hLn
      exfalso; exact Nat.not_succ_le_self n this
    · let U := (univ : Finset (Gap b L.succ 0))

      have h₂ : filter (fun v => M.P v.1 ∧ M.Q v.1 ∧      w.1 <:+ v.1) U = Finset.biUnion univ
         (fun a ↦ filter (fun v => M.P v.1 ∧ M.Q v.1 ∧ a :: w.1 <:+ v.1) U) := by
        apply ext; simp only [Nat.sub_zero, filter_congr_decidable, mem_filter,
          mem_univ, true_and, mem_biUnion, exists_and_left, and_congr_right_iff]
        intro;rw [suffix_cons _ _];intros;tauto

      · rw [
          branch_out_set, h₂,
          funext (fun a ↦ verify_those_with_suffix (Nat.le_of_lt bound) (Gap_cons a w hLn))]
        rfl
