/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johnathon Kyle Armstrong
-/
module

public import Mathlib.GroupTheory.Coxeter.Inversion

import Mathlib.Tactic.Group

/-!
# Exchange and Deletion Properties for Coxeter Systems

This file proves the Exchange Property and the Deletion Property for an arbitrary
`CoxeterSystem M W` using the parity action on `W × Bool` and `CoxeterSystem.rightInvSeq`.

## Main results
* `CoxeterSystem.exchange`: If `ω` is reduced and `cs.IsRightDescent (cs.wordProd ω) i`, then
  `cs.wordProd ω * cs.simple i = cs.wordProd (ω.eraseIdx j)` for some `j < ω.length`.
* `CoxeterSystem.deletion`: If `ω` is not reduced (there exists `u` with `u.length < ω.length`
  and `cs.wordProd ω = cs.wordProd u`), then there exist `i < j < ω.length` such that
  `cs.wordProd ((ω.eraseIdx j).eraseIdx i) = cs.wordProd ω`.
-/

@[expose] public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B}

section ParityAction

private noncomputable def parityStep (cs : CoxeterSystem M W) [DecidableEq W] (i : B) :
    Equiv.Perm (W × Bool) where
  toFun p := (cs.simple i * p.1 * cs.simple i, if p.1 = cs.simple i then !p.2 else p.2)
  invFun p := (cs.simple i * p.1 * cs.simple i, if p.1 = cs.simple i then !p.2 else p.2)
  left_inv p := by
    rcases p with ⟨t, b⟩
    have hconj : cs.simple i * (cs.simple i * t * cs.simple i) * cs.simple i = t := by
      calc cs.simple i * (cs.simple i * t * cs.simple i) * cs.simple i
          = (cs.simple i * cs.simple i) * t * (cs.simple i * cs.simple i) := by group
        _ = t := by simp [cs.simple_mul_simple_self]
    have hiff : cs.simple i * t * cs.simple i = cs.simple i ↔ t = cs.simple i := by
      constructor
      · intro h
        calc t = cs.simple i * (cs.simple i * t * cs.simple i) * cs.simple i := hconj.symm
          _ = cs.simple i * cs.simple i * cs.simple i := by rw [h]
          _ = cs.simple i := by simp [cs.simple_mul_simple_self]
      · intro h
        subst h
        simp [cs.simple_mul_simple_self]
    ext <;> simp [hconj, hiff]
    split_ifs <;> simp
  right_inv p := by
    rcases p with ⟨t, b⟩
    have hconj : cs.simple i * (cs.simple i * t * cs.simple i) * cs.simple i = t := by
      calc cs.simple i * (cs.simple i * t * cs.simple i) * cs.simple i
          = (cs.simple i * cs.simple i) * t * (cs.simple i * cs.simple i) := by group
        _ = t := by simp [cs.simple_mul_simple_self]
    have hiff : cs.simple i * t * cs.simple i = cs.simple i ↔ t = cs.simple i := by
      constructor
      · intro h
        calc t = cs.simple i * (cs.simple i * t * cs.simple i) * cs.simple i := hconj.symm
          _ = cs.simple i * cs.simple i * cs.simple i := by rw [h]
          _ = cs.simple i := by simp [cs.simple_mul_simple_self]
      · intro h
        subst h
        simp [cs.simple_mul_simple_self]
    ext <;> simp [hconj, hiff]
    split_ifs <;> simp

private noncomputable def parityWord (cs : CoxeterSystem M W) [DecidableEq W] (ω : List B) :
    Equiv.Perm (W × Bool) :=
  (ω.map (parityStep cs)).prod

private lemma parityWord_cons (cs : CoxeterSystem M W) [DecidableEq W] (i : B) (ω : List B) :
    parityWord cs (i :: ω) = parityStep cs i * parityWord cs ω := by
  simp [parityWord]

private lemma parityWord_fst (cs : CoxeterSystem M W) [DecidableEq W]
    (ω : List B) (t : W) (b : Bool) :
    (parityWord cs ω (t, b)).1 = cs.wordProd ω * t * (cs.wordProd ω)⁻¹ := by
  induction ω with
  | nil => simp [parityWord]
  | cons i ω ih =>
    rw [parityWord_cons, Equiv.Perm.mul_apply, cs.wordProd_cons]
    simp only [parityStep, Equiv.coe_fn_mk, ih]
    rw [mul_inv_rev, cs.inv_simple]
    group

private lemma parityWord_snd (cs : CoxeterSystem M W) [DecidableEq W]
    (ω : List B) (t : W) (b : Bool) :
    (parityWord cs ω (t, b)).2 =
      xor (decide (Odd ((cs.rightInvSeq ω).count t))) b := by
  induction ω with
  | nil => simp [parityWord, CoxeterSystem.rightInvSeq]
  | cons i ω ih =>
    rw [parityWord_cons, Equiv.Perm.mul_apply]
    simp only [parityStep, Equiv.coe_fn_mk, parityWord_fst, ih, CoxeterSystem.rightInvSeq]
    have hEq :
        (cs.wordProd ω * t * (cs.wordProd ω)⁻¹ = cs.simple i) ↔
          (t = (cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω) := by
      constructor
      · intro h
        calc t = (cs.wordProd ω)⁻¹ * (cs.wordProd ω * t * (cs.wordProd ω)⁻¹) * cs.wordProd ω := by
              group
          _ = (cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω := by rw [h]
      · intro h
        rw [h]
        group
    by_cases ht : t = (cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω
    · have ht' : cs.wordProd ω * t * (cs.wordProd ω)⁻¹ = cs.simple i := hEq.mpr ht
      simp only [ht', ite_true]
      subst ht
      by_cases hodd : Odd ((cs.rightInvSeq ω).count
          ((cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω))
      · have heven : Even ((cs.rightInvSeq ω).count
            ((cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω) + 1) := by
          simpa [Nat.even_add_one] using hodd
        simp [hodd, Nat.not_odd_iff_even.mpr heven]
      · have hodd1 : Odd ((cs.rightInvSeq ω).count
            ((cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω) + 1) := by
          simpa [Nat.odd_add_one] using hodd
        simp [hodd, hodd1]
    · have ht' : cs.wordProd ω * t * (cs.wordProd ω)⁻¹ ≠ cs.simple i := fun h => ht (hEq.mp h)
      simp only [ht', ite_false]
      simp [Ne.symm ht]

private lemma alternatingWord_even_succ (i j : B) (k : ℕ) :
    CoxeterSystem.alternatingWord i j (2 * (k + 1)) =
      CoxeterSystem.alternatingWord i j (2 * k) ++ [i, j] := by
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
      CoxeterSystem.alternatingWord_succ, CoxeterSystem.alternatingWord_succ]
  simp [List.concat_eq_append, List.append_assoc]

private lemma alternatingWord_even_cons (i j : B) (k : ℕ) :
    CoxeterSystem.alternatingWord i j (2 * (k + 1)) =
      i :: j :: CoxeterSystem.alternatingWord i j (2 * k) := by
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
      CoxeterSystem.alternatingWord_succ', CoxeterSystem.alternatingWord_succ']
  simp [show ¬Even (2 * k + 1) from by rw [Nat.even_iff]; omega,
    show Even (2 * k) from by rw [Nat.even_iff]; omega]

private lemma alternatingWord_odd_add_even (i j : B) (m k : ℕ) :
    CoxeterSystem.alternatingWord i j (2 * m + (2 * k + 1)) =
      CoxeterSystem.alternatingWord j i (2 * m) ++
        CoxeterSystem.alternatingWord i j (2 * k + 1) := by
  induction m with
  | zero => simp [CoxeterSystem.alternatingWord]
  | succ m ih =>
    rw [show 2 * (m + 1) + (2 * k + 1) = (2 * m + (2 * k + 1)) + 1 + 1 by omega,
        CoxeterSystem.alternatingWord_succ', CoxeterSystem.alternatingWord_succ']
    have hodd : ¬Even (2 * m + (2 * k + 1)) := by rw [Nat.even_iff]; omega
    have heven : Even (2 * m + (2 * k + 1) + 1) := by rw [Nat.even_iff]; omega
    simp only [hodd, heven, ite_true, ite_false]
    rw [ih, alternatingWord_even_cons, List.cons_append, List.cons_append]

private lemma reverse_alternatingWord_even (i j : B) (k : ℕ) :
    (CoxeterSystem.alternatingWord i j (2 * k)).reverse =
      CoxeterSystem.alternatingWord j i (2 * k) := by
  induction k with
  | zero => simp [CoxeterSystem.alternatingWord]
  | succ k ih =>
    rw [alternatingWord_even_succ, List.reverse_append, ih, alternatingWord_even_cons]
    simp

private lemma wordProd_alternatingWord_two_mul (cs : CoxeterSystem M W) (i j : B) (k : ℕ) :
    cs.wordProd (alternatingWord i j (2 * k)) = (cs.simple i * cs.simple j) ^ k := by
  induction k with
  | zero => simp [alternatingWord]
  | succ k ih =>
    rw [alternatingWord_even_succ, cs.wordProd_append, ih,
      cs.wordProd_cons, cs.wordProd_cons, cs.wordProd_nil, mul_one, pow_succ]

private lemma parityWord_alternatingWord_two_mul (cs : CoxeterSystem M W) [DecidableEq W]
    (i j : B) (k : ℕ) :
    parityWord cs (alternatingWord i j (2 * k)) =
      (parityStep cs i * parityStep cs j) ^ k := by
  induction k with
  | zero => simp [alternatingWord, parityWord]
  | succ k ih =>
    rw [alternatingWord_even_succ, parityWord, List.map_append, List.prod_append]
    change parityWord cs (alternatingWord i j (2 * k)) *
        (parityStep cs i * (parityStep cs j * 1)) = _
    rw [ih, mul_one, pow_succ]

private lemma even_count_of_half_periodic {α : Type*} [DecidableEq α]
    (L : List α) (m : ℕ) (hlen : L.length = 2 * m)
    (hper : ∀ k (hk : k < m), L[k + m]'(by omega) = L[k]'(by omega)) (x : α) :
    Even (L.count x) := by
  have hsplit : L = L.take m ++ L.take m := by
    apply List.ext_getElem
    · simp [hlen]
      omega
    · intro idx h1 h2
      by_cases hlt : idx < m
      · rw [List.getElem_append_left (by simp [hlen]; omega), List.getElem_take]
      · have hge : m ≤ idx := by omega
        have hk : idx - m < m := by omega
        have htake : (L.take m).length = m := by simp [hlen]; omega
        rw [List.getElem_append_right (by omega)]
        have hidx : idx - (L.take m).length = idx - m := by rw [htake]
        simp only [hidx, List.getElem_take]
        have hidx' : idx - m + m = idx := by omega
        simpa [hidx'] using hper (idx - m) hk
  rw [hsplit, List.count_append, ← two_mul]
  exact ⟨(L.take m).count x, by omega⟩

private lemma parityStep_isLiftable (cs : CoxeterSystem M W) [DecidableEq W] :
    CoxeterMatrix.IsLiftable M (parityStep cs) := by
  intro i j
  by_cases hm : M i j = 0
  · simp [hm]
  · rw [← parityWord_alternatingWord_two_mul cs i j (M i j)]
    ext ⟨t, b⟩
    · simp only [parityWord_fst, Equiv.Perm.coe_one, id_eq]
      rw [wordProd_alternatingWord_two_mul, cs.simple_mul_simple_pow, one_mul, inv_one, mul_one]
    · simp only [parityWord_snd, Equiv.Perm.coe_one, id_eq]
      have hcount :
          (cs.rightInvSeq (alternatingWord i j (2 * M i j))).count t =
            (cs.leftInvSeq (alternatingWord j i (2 * M i j))).count t := by
        rw [← reverse_alternatingWord_even j i (M i j), cs.rightInvSeq_reverse, List.count_reverse]
      rw [hcount]
      have heven : Even ((cs.leftInvSeq (alternatingWord j i (2 * M i j))).count t) := by
        refine even_count_of_half_periodic _ (M i j) ?_ ?_ t
        · rw [cs.length_leftInvSeq, length_alternatingWord]
        · intro k hk
          rw [cs.getElem_leftInvSeq_alternatingWord j i (M i j) k (by omega),
              cs.getElem_leftInvSeq_alternatingWord j i (M i j) (k + M i j) (by omega)]
          rw [show 2 * (k + M i j) + 1 = 2 * M i j + (2 * k + 1) by omega,
              alternatingWord_odd_add_even, cs.wordProd_append,
              wordProd_alternatingWord_two_mul, cs.simple_mul_simple_pow', one_mul]
      simp [Nat.not_odd_iff_even.mpr heven]

private noncomputable def parityLift (cs : CoxeterSystem M W) [DecidableEq W] :
    W →* Equiv.Perm (W × Bool) :=
  cs.lift ⟨parityStep cs, parityStep_isLiftable cs⟩

private lemma parityLift_wordProd (cs : CoxeterSystem M W) [DecidableEq W] (ω : List B) :
    parityLift cs (cs.wordProd ω) = parityWord cs ω := by
  induction ω with
  | nil => simp [parityLift, parityWord]
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul, parityWord_cons, ih]
    congr 1
    exact cs.lift_apply_simple (parityStep_isLiftable cs) i

end ParityAction

/-- **Exchange Property** for a `CoxeterSystem`: if `ω` is reduced and `i` is a right descent
of `cs.wordProd ω`, then `cs.wordProd ω * cs.simple i = cs.wordProd (ω.eraseIdx j)` for some
`j < ω.length`. -/
theorem exchange (cs : CoxeterSystem M W)
    {ω : List B} (hω : cs.IsReduced ω) {i : B}
    (hd : cs.IsRightDescent (cs.wordProd ω) i) :
    ∃ j < ω.length, cs.wordProd ω * cs.simple i = cs.wordProd (ω.eraseIdx j) := by
  classical
  obtain ⟨ω', hω'red, hω'prod⟩ := cs.exists_isReduced (cs.wordProd ω * cs.simple i)
  have hlen : ω'.length + 1 = ω.length := by
    have h1 := cs.isRightDescent_iff.mp hd
    rw [hω'prod, hω'red, hω] at h1
    exact h1
  have hconcat_prod : cs.wordProd (ω'.concat i) = cs.wordProd ω := by
    rw [List.concat_eq_append, cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one,
      ← hω'prod, mul_assoc, cs.simple_mul_simple_self, mul_one]
  have hconcat_red : cs.IsReduced (ω'.concat i) := by
    rw [CoxeterSystem.IsReduced, hconcat_prod, List.length_concat, hlen]
    exact hω
  have hmem : cs.simple i ∈ cs.rightInvSeq (ω'.concat i) := by
    rw [cs.rightInvSeq_concat]
    simp
  have hcount_concat : (cs.rightInvSeq (ω'.concat i)).count (cs.simple i) = 1 := by
    rw [List.Nodup.count (hconcat_red.nodup_rightInvSeq)]
    simpa [List.concat_eq_append] using hmem
  have hpar :
      parityWord cs ω (cs.simple i, false) =
        parityWord cs (ω'.concat i) (cs.simple i, false) := by
    rw [← parityLift_wordProd, ← parityLift_wordProd, hconcat_prod]
  have hsnd := congrArg Prod.snd hpar
  simp only [parityWord_snd, Bool.xor_false, decide_eq_decide] at hsnd
  have hodd : Odd ((cs.rightInvSeq ω).count (cs.simple i)) := by
    rw [hsnd, hcount_concat]
    exact odd_one
  have hmemω : cs.simple i ∈ cs.rightInvSeq ω := by
    rw [← List.count_pos_iff]
    exact Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hodd)
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmemω
  have hjlen : j < ω.length := by simpa [cs.length_rightInvSeq] using hj
  refine ⟨j, hjlen, ?_⟩
  have hmul := cs.wordProd_mul_getD_rightInvSeq ω j
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hget] at hmul
  exact hmul

private lemma deletion_aux (cs : CoxeterSystem M W) :
    ∀ (k : ℕ) (ω : List B), ω.length = k →
      (∃ u : List B, u.length < ω.length ∧ cs.wordProd ω = cs.wordProd u) →
      ∃ i j : ℕ, i < j ∧ j < ω.length ∧
        cs.wordProd ((ω.eraseIdx j).eraseIdx i) = cs.wordProd ω := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro ω hlen ⟨u, hu_len, hu_prod⟩
    induction ω using List.reverseRecOn with
    | nil => simp at hu_len
    | append_singleton w' a _ =>
      by_cases hred : cs.IsReduced w'
      · have hlt : cs.length (cs.wordProd w' * cs.simple a) < w'.length + 1 := by
          have h1 : cs.length (cs.wordProd (w' ++ [a])) ≤ u.length := by
            rw [hu_prod]
            exact cs.length_wordProd_le u
          rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one] at h1
          simp only [List.length_append, List.length_singleton] at hu_len
          omega
        have hd : cs.IsRightDescent (cs.wordProd w') a := by
          rw [cs.isRightDescent_iff]
          rcases cs.length_mul_simple (cs.wordProd w') a with hinc | hdec
          · rw [hred] at hinc
            omega
          · exact hdec
        obtain ⟨j, hj, hdel⟩ := cs.exchange hred hd
        refine ⟨j, w'.length, hj, by simp, ?_⟩
        have her : (w' ++ [a]).eraseIdx w'.length = w' := by
          rw [List.eraseIdx_append_of_length_le (le_refl _)]
          simp
        rw [her, ← hdel, cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one]
      · obtain ⟨u', hu'red, hu'prod⟩ := cs.exists_isReduced (cs.wordProd w')
        have hu'lt : u'.length < w'.length := by
          have hle : u'.length ≤ w'.length := by
            rw [← hu'red, ← hu'prod]
            exact cs.length_wordProd_le w'
          rcases Nat.lt_or_eq_of_le hle with hlt | heq
          · exact hlt
          · exfalso
            apply hred
            rw [CoxeterSystem.IsReduced, hu'prod, hu'red, heq]
        have hk' : w'.length < k := by
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        obtain ⟨i, j, hij, hj, hdel⟩ := ih w'.length hk' w' rfl ⟨u', hu'lt, hu'prod⟩
        refine ⟨i, j, hij, by simp; omega, ?_⟩
        have h1 : (w' ++ [a]).eraseIdx j = w'.eraseIdx j ++ [a] :=
          List.eraseIdx_append_of_lt_length hj [a]
        have hjlen : i < (w'.eraseIdx j).length := by
          rw [List.length_eraseIdx_of_lt hj]
          omega
        have h2 : (w'.eraseIdx j ++ [a]).eraseIdx i = (w'.eraseIdx j).eraseIdx i ++ [a] :=
          List.eraseIdx_append_of_lt_length hjlen [a]
        rw [h1, h2, cs.wordProd_append, hdel, ← cs.wordProd_append]

/-- **Deletion Property** for a `CoxeterSystem`: if `ω` is not reduced (there exists a strictly
shorter word `u` with the same `wordProd`), then two letters at indices `i < j < ω.length` can
be erased without changing `cs.wordProd`. -/
theorem deletion (cs : CoxeterSystem M W) {ω : List B}
    (hω : ∃ u : List B, u.length < ω.length ∧ cs.wordProd ω = cs.wordProd u) :
    ∃ i j : ℕ, i < j ∧ j < ω.length ∧
      cs.wordProd ((ω.eraseIdx j).eraseIdx i) = cs.wordProd ω :=
  deletion_aux cs ω.length ω rfl hω

end CoxeterSystem
