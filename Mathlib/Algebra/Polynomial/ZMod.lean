/-
Copyright (c) 2025 Metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Metakunt
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.List.Intervals
import Mathlib.Data.List.ToFinsupp
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# ZMod Polynomials

This file defines an equivalence between ℕ and `(ZMod n)[X]`

## Main definitions

- `Polynomial.equiv_of_nat_of_polynomial_zmod`

-/

namespace Polynomial


private theorem exists_zmod_sol_some_aux (b n : ℕ) [NeZero n] (h : 2 ≤ b) :
  ∃ y : ℕ , 0 < y ∧ y < b ∧ (b.digits n)[(b.digits n).length - 1]? = some y := by
  have ne0 : n ≠ 0 := by exact Ne.symm (NeZero.ne' n)
  have hldig := Nat.getLast_digit_ne_zero b ne0
  let val := (b.digits n).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr ne0)
  use val
  constructor
  · exact Nat.zero_lt_of_ne_zero hldig
  · constructor
    · refine Nat.digits_lt_base h ?_ (m:=n)
      exact List.getLast_mem (Nat.digits_ne_nil_iff_ne_zero.mpr ne0)
    · have hl : (b.digits n).length - 1 < (b.digits n).length := by
        have hdg1 : 0 < (b.digits n).length := by
          have ne0 : 0 ≠ (b.digits n ).length := by
            have nempty := (Nat.digits_ne_nil_iff_ne_zero (b:=b)).mpr ne0
            contrapose! nempty
            exact  List.length_eq_zero_iff (l:=(b.digits n)).mp (nempty.symm)
          by_contra! hc
          simp only [nonpos_iff_eq_zero, List.length_eq_zero_iff] at hc
          rw [hc] at ne0
          exact ne0 rfl
        simp only [tsub_lt_self_iff, zero_lt_one, and_true, gt_iff_lt]
        exact hdg1
      simp only [hl, getElem?_pos, Option.some.injEq]
      have last_val := List.getElem_length_sub_one_eq_getLast hl
      rw [last_val]


private theorem length_digits_sup (n m : ℕ) (h : 2 ≤ n) (h2 : (List.map (Nat.cast (R := (ZMod n)))
    (n.digits m)).toFinsupp.support.Nonempty) :
    (List.map (Nat.cast (R:=(ZMod n))) (n.digits m)).toFinsupp.support.sup id + 1 =
    (n.digits m).length := by
  have mne0 : m ≠ 0 := by
    by_contra hc
    have digempty := Nat.digits_zero n
    rw [← hc] at digempty
    rw [digempty] at h2
    simp at h2
  have _ : NeZero m := NeZero.mk mne0

  have lengt1 : 1 ≤ (n.digits m).length := by
    by_contra hc
    simp only [not_le, Nat.lt_one_iff, List.length_eq_zero_iff] at hc
    rw[hc] at h2
    simp at h2

  have key : ((List.map (Nat.cast (R:=(ZMod n))) (n.digits m)).toFinsupp)
   ((n.digits m).length - 1 ) ≠ 0 := by
    simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.getElem?_map, ne_eq]
    have ⟨ y , hl, hr, hsome ⟩  := exists_zmod_sol_some_aux n m h
    rw [hsome]
    simp only [Option.map_some, Option.getD_some, ne_eq]
    by_contra hc
    have ⟨ z, divz ⟩ := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hc
    have split : z = 0 ∨ 0 < z := by exact Nat.eq_zero_or_pos z
    cases split with
    | inl hd =>
      contrapose! divz
      simp[hd]
      exact Nat.ne_zero_of_lt hl
    | inr hd =>
      contrapose! hr
      rw[divz]
      exact Nat.le_mul_of_pos_right n hd
  have key2 : ((n.digits m).length -1) ∈ (List.map (Nat.cast (R:=(ZMod n)))
    (n.digits m)).toFinsupp.support := by
    exact Finsupp.mem_support_iff.mpr key
  have fslesup := Finset.le_sup key2 (f:=id)
  have key3 : (List.map (Nat.cast (R:=(ZMod n))) (n.digits m)).toFinsupp.support.sup id =
    (n.digits m).length - 1 := by
    rw [le_antisymm_iff]
    constructor
    · simp only [Finset.sup_le_iff, Finsupp.mem_support_iff, List.toFinsupp_apply,
      List.getD_eq_getElem?_getD, List.getElem?_map, ne_eq, id_eq]
      by_contra! hc
      have ⟨ a, b, c ⟩ := hc
      clear hc
      have nma : (n.digits m)[a]? = none := by
        simp only [getElem?_eq_none_iff, not_lt]
        have ls :=Nat.sub_lt_iff_lt_add lengt1 (c:=a)
        exact Nat.le_of_pred_lt c
      rw [nma] at b
      simp at b
    · exact fslesup
  simp only [key3, lengt1, Nat.sub_add_cancel]

/-- Equivalence between `ℕ` and finitely supported functions on `(ZMod n)`. -/
def equiv_of_nat_of_finsupp_zmod (n : ℕ) (h : 2 ≤ n) : ℕ ≃ Finsupp ℕ (ZMod n) := by
  have _ : NeZero n := by exact NeZero.of_gt h
  exact {
    toFun a := List.toFinsupp (n.digits a)
    invFun b := if b=0 then 0 else (Nat.ofDigits n) (List.map (ZMod.val.comp b)
      (List.range ((Finset.sup b.support id) + 1)))
    left_inv := by
      rw[Function.LeftInverse]
      intro m
      simp only [List.pure_def, List.bind_eq_flatMap]

      -- I HATE THIS ONE, the case split didn't want to reduce the ifelse.
      have split : (@List.flatMap ℕ (ZMod n) (fun (a : ℕ) ↦
       [(a : (ZMod n))]) (n.digits m)).toFinsupp = 0 ∨
      ¬ (@List.flatMap ℕ (ZMod n) (fun (a : ℕ) ↦ [(a:(ZMod n))]) (n.digits m)).toFinsupp = 0 := by
        exact Classical.em ?_

      cases split with
      | inl hfs =>
        simp only [hfs, ↓reduceIte]
        symm
        by_contra! hn

        rw[← List.map_eq_flatMap] at hfs
        -- Define it like that so that you can always access the element.
        let lastIdx := (n.digits m).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hn)
        have ldne0 := Nat.getLast_digit_ne_zero n hn
        have all_zero := (Finsupp.ext_iff.mp) hfs
        have last_zero := all_zero (Nat.log n m)
        simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.getElem?_map,
          Finsupp.coe_zero, Pi.zero_apply] at last_zero
        have ⟨ s , h1 , h2 , h3 ⟩ : ∃ s : ℕ , 0 < s ∧ s < n ∧
          (n.digits m)[Nat.log n m]? = some s := by
          use lastIdx
          constructor
          · exact Nat.zero_lt_of_ne_zero ldne0
          · have hlen := Nat.digits_len n m h hn
            have nlen : Nat.log n m < (n.digits m).length := by
              rw [hlen]
              norm_num
            constructor
            · refine Nat.digits_lt_base h ?_ (m:=m)
              exact List.getLast_mem (Nat.digits_ne_nil_iff_ne_zero.mpr hn)
            · have leq := List.getElem?_eq_getElem nlen
              rw [leq]
              simp only [Option.some.injEq]
              have hmm: (n.digits m).length - 1 < (n.digits m).length := Nat.sub_one_lt_of_lt nlen
              have lzGetD := List.getElem_length_sub_one_eq_getLast hmm
              conv at lzGetD =>
                lhs
                lhs
                rw [hlen]
                simp only [add_tsub_cancel_right]
              rw [lzGetD]
        rw [h3] at last_zero
        simp only [Option.map_some, Option.getD_some] at last_zero
        simp only [ZMod.natCast_zmod_eq_zero_iff_dvd] at last_zero
        have ⟨ div1 ,hdiv1 ⟩ := last_zero
        contrapose! h2
        rw [hdiv1]
        refine Nat.le_mul_of_pos_right n ?_
        have split : div1 = 0 ∨ 0 < div1 := by exact Nat.eq_zero_or_pos div1
        cases split with
        | inl hl =>
          rw [hl] at hdiv1
          simp only [mul_zero] at hdiv1
          rw [hdiv1] at h1
          exact (Nat.mul_pos_iff_of_pos_right h1).mp h1
        | inr hr =>
          assumption
      | inr bh =>
        have fsn := Finsupp.support_nonempty_iff.mpr bh
        rw [← List.map_eq_flatMap] at fsn
        simp only [bh, ↓reduceIte]
        simp only [List.map_eq_flatMap.symm]
        have hk : (List.map (ZMod.val ∘ ⇑(List.map (Nat.cast (R:=(ZMod n))) (n.digits m)).toFinsupp)
        (List.range ((List.map (Nat.cast (R:=(ZMod n)))
         (n.digits m)).toFinsupp.support.sup id + 1))) = (n.digits m) := by
          ext j i
          rw [← List.Ico.zero_bot]
          have test : (List.map (ZMod.val ∘ ⇑(List.map (Nat.cast (R:=(ZMod n)))
           (n.digits m)).toFinsupp) (List.Ico 0 ((List.map (Nat.cast (R:=(ZMod n)))
            (n.digits m)).toFinsupp.support.sup id + 1)))[j]? =(n.digits m)[j]? := by
            simp only [List.getElem?_map]
            have split : j∈ ((n.digits m)).toFinsupp.support ∨ j∉ ((n.digits m)).toFinsupp.support
             := Decidable.em (j ∈ (n.digits m).toFinsupp.support)
            cases split with
            | inl hl =>
              simp only [Finsupp.mem_support_iff, List.toFinsupp_apply, List.getD_eq_getElem?_getD,
                ne_eq] at hl
              have jlelen: j < (n.digits m).length := by
                by_contra hcon
                simp only [not_lt] at hcon
                have ndmj : (n.digits m)[j]? = none := by exact List.getElem?_eq_none_iff.mpr hcon
                have ndmj2 : (n.digits m)[j]?.getD 0 = 0 := by simp only [ndmj, Option.getD_none]
                exact hl ndmj2
              have issome : (n.digits m)[j]?.isSome := by simp only [isSome_getElem?, jlelen]
              have exd : ∃ d: ℕ , (n.digits m)[j]? = some d := (Option.isSome_iff_exists.mp) issome
              have ⟨ d, hd ⟩ := exd
              have dltn : d < n := Nat.digits_lt_base h (List.mem_of_getElem? hd)
              have hico : (List.Ico 0 ((List.map (Nat.cast (R:=(ZMod n)))
              (n.digits m)).toFinsupp.support.sup id + 1))[j]? = some j := by
                refine (List.getElem_eq_iff ?_).mp ?_
                · rw [List.Ico.zero_bot]
                  have lmr := List.self_mem_range_succ (n:=j)
                  rw [← List.Ico.zero_bot]
                  rw [List.Ico.length]
                  simp only [tsub_zero, gt_iff_lt]
                  have jjd : j ≤ (List.map (Nat.cast (R:=(ZMod n)))
                    (n.digits m)).toFinsupp.support.sup id := by
                    have fallltl : ∀ le ∈ (List.map (Nat.cast (R:=(ZMod n)))
                      (n.digits m)).toFinsupp.support, le < (n.digits m).length := by
                      intro s hs
                      simp only [Finsupp.mem_support_iff, List.toFinsupp_apply,
                        List.getD_eq_getElem?_getD, List.getElem?_map, ne_eq] at hs
                      by_contra conell
                      simp only [not_lt] at conell
                      have isnoned : (n.digits m)[s]? = none :=
                        List.getElem?_eq_none_iff.mpr conell
                      rw [isnoned] at hs
                      simp only [Option.map_none, Option.getD_none, not_true_eq_false] at hs
                    have jjb : j ∈ (List.map (Nat.cast (R:=(ZMod n)))
                      (n.digits m)).toFinsupp.support := by
                      simp only [Finsupp.mem_support_iff, List.toFinsupp_apply,
                        List.getD_eq_getElem?_getD, List.getElem?_map, ne_eq]
                      rw [hd]
                      simp only [Option.map_some, Option.getD_some]
                      rw [hd] at hl
                      simp only [Option.getD_some] at hl
                      contrapose hl
                      simp only [Decidable.not_not]
                      simp only [Decidable.not_not] at hl
                      have vnCol := ZMod.val_natCast_of_lt dltn
                      rw [ZMod.val_natCast] at vnCol
                      rw [← vnCol]
                      have ⟨ d, hd ⟩ := (ZMod.natCast_zmod_eq_zero_iff_dvd d n).mp hl
                      rw [hd]
                      simp
                    have nonempty : (List.map (Nat.cast (R:=(ZMod n)))
                      (n.digits m)).toFinsupp.support.Nonempty := by
                      use j
                    refine Finset.le_sup_of_le jjb ?_
                    simp only [id_eq, le_refl]
                  exact Order.lt_add_one_iff.mpr jjd
                · conv =>
                    lhs
                    congr
                    rw [List.Ico.zero_bot]
                  simp only [List.getElem_range]
              rw [hico]
              simp only [Option.map_some, Function.comp_apply, List.toFinsupp_apply,
                List.getD_eq_getElem?_getD, List.getElem?_map]
              rw [hd]
              simp only [Option.map_some, Option.getD_some,  Option.some.injEq]
              exact ZMod.val_natCast_of_lt dltn
            | inr hr =>
              have split :
                (n.digits m).length ≤ j ∨ j < (n.digits m).length  := le_or_gt (n.digits m).length j
              cases split with
              | inl dfl =>
                have ndmjn : (n.digits m)[j]? = none := by simpa [hr]
                rw [ndmjn]
                have hico : (List.Ico 0 ((List.map (Nat.cast (R:=(ZMod n)))
                (n.digits m)).toFinsupp.support.sup id + 1))[j]? = none := by
                  rw[List.Ico.zero_bot]
                  simp only [getElem?_eq_none_iff, List.length_range, not_lt]
                  have supeql : (List.map  (Nat.cast (R:=(ZMod n)))
                   (n.digits m)).toFinsupp.support.sup id + 1 =
                      (n.digits m).length := length_digits_sup n m h fsn
                  rwa [supeql]
                rw [hico]
                simp only [Option.map_none]
              | inr dfl =>
                simp only [Finsupp.mem_support_iff, List.toFinsupp_apply,
                  List.getD_eq_getElem?_getD, ne_eq, Decidable.not_not] at hr
                have eqzero : (n.digits m)[j]? = some 0 := by
                  apply getElem?_eq_some_iff.mpr
                  use dfl
                  rw [Option.getD_eq_iff] at hr
                  cases hr with
                  | inl hs =>
                    have hi :=  List.getElem?_eq_getElem dfl
                    rw [hi] at hs
                    simp only [Option.some.injEq] at hs
                    assumption
                  | inr hs =>
                    obtain hsl := hs.1
                    contrapose! hsl
                    simp only [ne_eq, getElem?_eq_none_iff, not_lt, not_le]
                    assumption
                rw [eqzero]
                have eqico1 : (List.Ico 0 ((List.map (Nat.cast (R:=(ZMod n)))
                  (n.digits m)).toFinsupp.support.sup id + 1))[j]? = some j := by
                  have jltl : j < (List.map (Nat.cast (R:=(ZMod n)))
                   (n.digits m)).length := by rwa [List.length_map]
                  have je := List.getElem?_eq_getElem jltl
                  rw [List.Ico.zero_bot]
                  refine List.getElem?_range ?_
                  have jlej : j ≤ j := Nat.le_refl j
                  contrapose! jlej
                  have leneqsup : (List.map (Nat.cast (R:=(ZMod n))) (n.digits m)).length =
                (List.map (Nat.cast (R:=(ZMod n))) (n.digits m)).toFinsupp.support.sup id + 1 := by
                    rw [List.length_map]
                    exact (length_digits_sup n m h fsn).symm
                  calc
                    _ < _ := jltl
                    _ = _ := leneqsup
                    _ ≤ _ := jlej
                rw [eqico1]
                simp only [Option.map_some, Function.comp_apply, List.toFinsupp_apply,
                  List.getD_eq_getElem?_getD, List.getElem?_map, Option.some.injEq,
                  ZMod.val_eq_zero]
                rw [eqzero]
                simp only [Option.map_some, Nat.cast_zero, Option.getD_some]
          constructor
          · intro hh
            rw [← hh]
            exact id (Eq.symm test)
          · intro hh
            rw [← hh]
            exact test
        rw [hk]
        exact Nat.ofDigits_digits n m
    right_inv := by
      rw [Function.RightInverse,Function.LeftInverse]
      intro f
      have split : f = 0 ∨ f ≠ 0 := by exact eq_or_ne f 0
      cases split with
      | inl f0 =>
        simp only [f0, ↓reduceIte, Nat.digits_zero, List.pure_def, List.bind_eq_flatMap,
          List.flatMap_nil, List.toFinsupp_nil]
      | inr fne0 =>
        simp only [fne0, ↓reduceIte, List.pure_def, List.bind_eq_flatMap]
        ext j
        simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD]
        rw [← List.map_eq_flatMap]
        have tt : (n.digits (Nat.ofDigits n (List.map (ZMod.val ∘ ⇑f)
          (List.range (f.support.sup id + 1))))) =
        (List.map (ZMod.val ∘ ⇑f) (List.range (f.support.sup id + 1))) := by
          refine Nat.digits_ofDigits n h ?_ ?_ ?_
          · intro x hx
            simp only [List.mem_map, List.mem_range, Function.comp_apply] at hx
            have ⟨ a , ⟨ ha, hb ⟩ ⟩ := hx
            rw [← hb]
            exact ZMod.val_lt (f a)
          · intro li
            by_contra lh
            have lhl := List.getLast_eq_getElem li
            rw [lhl] at lh
            clear lhl
            simp only [List.length_map, List.length_range, add_tsub_cancel_right, List.getElem_map,
              List.getElem_range, Function.comp_apply, ZMod.val_eq_zero] at lh
            have nonemp  := (Finsupp.support_nonempty_iff (f:=f)).mpr fne0
            have smne := Finset.sup_mem_of_nonempty nonemp (f:=id)
            simp only [id_eq, Set.image_id', Finset.mem_coe, Finsupp.mem_support_iff, ne_eq] at smne
            trivial
        rw [tt]
        simp only [List.getElem?_map, Option.map_map]
        have split : f j = 0 ∨ f j ≠ 0 := eq_or_ne (f j) 0
        have hc : (Nat.cast ∘ ZMod.val ∘ ⇑f) = f := by
          rw [← Function.comp_assoc]
          simp only [ZMod.natCast_comp_val, ZMod.cast_id', CompTriple.comp_eq]
        rw [hc]
        cases split with
        | inl hl =>
          have split : (List.range (f.support.sup id + 1))[j]? = some j ∨
          (List.range (f.support.sup id + 1))[j]? = none := by
            by_contra hc22
            push_neg at hc22
            have ⟨ hc1, hc2 ⟩ := hc22
            have issom : (List.range (f.support.sup id + 1))[j]?.isSome := by
              contrapose! hc2
              have falsy : (List.range (f.support.sup id + 1))[j]?.isSome = false :=
                eq_false_of_ne_true hc2
              rw [← Option.not_isNone] at falsy
              simp only [Option.not_isNone, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
                at falsy
              assumption
            have exi : ∃ k ≠ j , (List.range (f.support.sup id + 1))[j]? = some k := by
              by_contra hexi
              push_neg at hexi
              have ⟨ k , hk ⟩ := (Option.isSome_iff_exists.mp) issom
              have hkj : k = j ∨ k ≠ j := eq_or_ne k j
              cases hkj with
              | inl hc =>
                rw [hc] at hk
                rw [hk] at hc1
                trivial
              | inr hc =>
                have mp := hexi k hc
                trivial
            have ⟨ hf , hhf ⟩ :=exi
            have lrjsome : (List.range (f.support.sup id + 1))[j]? = some j := by
              have split : j < (f.support.sup id + 1) ∨ (f.support.sup id + 1) ≤ j :=
               Nat.lt_or_ge j (f.support.sup id + 1)
              cases split with
              | inl hc =>
                have len : j < (List.range (f.support.sup id + 1)).length := by
                  rw[← List.Ico.zero_bot]
                  simpa
                rw [← List.getElem_eq_iff]
                · refine List.getElem_range ?_
                  assumption
              | inr hc =>
                have isnone : (List.range (f.support.sup id + 1))[j]? = none := by
                  refine List.getElem?_eq_none_iff.mpr ?_
                  rw [← List.Ico.zero_bot]
                  simpa
                trivial
            rw [hhf.2] at lrjsome
            simp at lrjsome
            exact hhf.1 lrjsome
          rw [hl]
          cases split with
          | inl hl1 =>
            rw [hl1]
            simpa only [Option.map_some, Option.getD_some]
          | inr hr1 =>
            rw [hr1]
            simp only [Option.map_none, Option.getD_none]
        | inr hr =>
          have jl : j < (f.support.sup id + 1) := by
            contrapose! hr
            have jns : j ∉ f.support := by
              by_contra hc
              have jl : j ≤ f.support.sup id := Finset.le_sup hc (f:=id)
              have c : j < j := calc
                j ≤ _ := jl
                _ < _ := lt_add_one (f.support.sup id)
                _ ≤ _ := hr
              exact (lt_self_iff_false j).mp c
            exact Finsupp.notMem_support_iff.mp jns
          have issome : (List.range (f.support.sup id + 1))[j]? = some j := by
            simp only [List.length_range, jl, getElem?_pos, List.getElem_range]
          rw [issome]
          simp only [Option.map_some, Option.getD_some]
  }

/-- Equivalence between `ℕ` and polynomials over `(ZMod n)`. -/
def equiv_of_nat_of_polynomial_zmod (n : ℕ) (h : 2 ≤ n) : ℕ ≃ Polynomial (ZMod n) where
  toFun a := .ofFinsupp (equiv_of_nat_of_finsupp_zmod n h a)
  invFun b := (equiv_of_nat_of_finsupp_zmod  n h).invFun b.toFinsupp
  left_inv :=  Function.LeftInverse.comp (congrFun rfl) (equiv_of_nat_of_finsupp_zmod n h).left_inv
  right_inv := Function.RightInverse.comp (congrFun rfl)
    (equiv_of_nat_of_finsupp_zmod n h).right_inv


-- C 1 + X ^ 2
--#eval (equiv_of_nat_of_polynomial_zmod 2 (by decide)) 5

end Polynomial
