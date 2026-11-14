/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
module

public import Mathlib.Computability.SingleOracle.Constructions.Option

/-!
# Construction of basic primitive recursive functions on lists

This file defines basic primitive recursive codes for basic functions on lists.

## Structure
(See Oracle.Single.Constructions.Primitive for more details.)

The major constructions in this file are `cListFoldl` and `cListZipWith`.

`cListFoldl` allows easy definitions of subsequent constructs, although `cListZipWith` still
requires a nontrivial proof.

In docstrings, `[c]` denotes the function computed by the code `c`, and `[c](x)` its value at `x`.

-/

@[expose] public section

open Nat Denumerable Encodable List

section list_nil
namespace Oracle.Single.Code
/-- This code defines the function `fun _ ↦ l2n []`. -/
def cListNil := zero
@[cp] theorem cListNil_prim : IsPrim cListNil := by unfold cListNil; apply_cp
@[simp, evp_simps] theorem cListNil_evp {O : ℕ → ℕ} {x} : evalp O cListNil x = l2n ([]) := by
  simp [cListNil]
@[simp, ev_simps] theorem cListNil_ev {O : ℕ → ℕ} {x} : eval O cListNil x = l2n ([]) := by
  simp [← evalp_eq_eval cListNil_prim]
end Oracle.Single.Code
end list_nil

section list_cons
namespace Oracle.Single.Code
/-- This code defines the function `fun ⟪a, l⟫ ↦ l2n (a :: n2l l)`. -/
def cListCons := succ
@[cp] theorem cListCons_prim : IsPrim cListCons := by unfold cListCons; apply_cp
@[simp, evp_simps] theorem cListCons_evp {O : ℕ → ℕ} {a lN} :
    evalp O cListCons ⟪a, lN⟫= l2n (cons a (n2l lN)) := by
  simp [cListCons]
@[simp, ev_simps] theorem cListCons_ev {O : ℕ → ℕ} {a lN} :
    eval O cListCons ⟪a, lN⟫= l2n (cons a (n2l lN)) := by
  simp [←evalp_eq_eval cListCons_prim]
end Oracle.Single.Code
end list_cons

section list_tail
namespace Oracle.Single.Code
/-- This code defines the function `fun l ↦ l2n (n2l l).tail`. -/
def cListTail := right.comp cPred
@[cp] theorem cListTail_prim : IsPrim cListTail := by unfold cListTail; apply_cp
@[simp, evp_simps] theorem cListTail_evp {O : ℕ → ℕ} {lN : ℕ} :
    evalp O cListTail lN = l2n (tail (n2l lN)) := by
  simp only [cListTail]
  by_cases hl : lN=0
  · simp [hl, Nat.right]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp, ev_simps] theorem cListTail_ev {O : ℕ → ℕ} {lN : ℕ} :
    eval O cListTail lN = l2n (tail (n2l lN)) := by
  simp [← evalp_eq_eval cListTail_prim]
end Oracle.Single.Code
end list_tail

section list_head?
namespace Oracle.Single.Code
/-- This code defines the function `fun l ↦ o2n (n2l l).head?`. -/
def cListHead? := cIfz.comp₃ cId zero <| succ.comp (left.comp cPred)
@[cp] theorem cListHead?_prim : IsPrim cListHead? := by unfold cListHead?; apply_cp
@[simp, evp_simps] theorem cListHead?_evp {O : ℕ → ℕ} {lN : ℕ} :
    evalp O cListHead? lN = o2n (head? (n2l lN)) := by
  simp only [cListHead?]
  by_cases hl : lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp, ev_simps] theorem cListHead?_ev {O : ℕ → ℕ} {lN : ℕ} :
  eval O cListHead? lN = o2n (head? (n2l lN)) := by simp [← evalp_eq_eval cListHead?_prim]
end Oracle.Single.Code
end list_head?

section list_headI
namespace Oracle.Single.Code
/-- This code defines the function `fun l ↦ (n2l l).headI`. -/
def cListHeadI := cIfz.comp₃ cId zero (left.comp cPred)
@[cp] theorem cListHeadI_prim : IsPrim cListHeadI := by unfold cListHeadI; apply_cp
@[simp, evp_simps] theorem cListHeadI_evp {O : ℕ → ℕ} {lN : ℕ} :
    evalp O cListHeadI lN = headI (n2l lN) := by
  simp only [cListHeadI]
  by_cases hl : lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp, ev_simps] theorem cListHeadI_ev {O : ℕ → ℕ} {lN : ℕ} :
    eval O cListHeadI lN = headI (n2l lN) := by
  simp [← evalp_eq_eval cListHeadI_prim]
end Oracle.Single.Code
end list_headI

section list_casesOn
namespace Oracle.Single.Code
/-- Given codes `cl`, `c`, `cg`, this code defines the function
`fun x ↦ List.casesOn (n2l [cl](x)) [c](x) (fun y ys ↦ [cg](⟪y, l2n ys⟫))`. -/
def cListCasesOn (cl c cg : Code) :=
  let x := left.comp (cPred.comp cl)
  let xs := right.comp (cPred.comp cl)
  cIfEqTe.comp₄ cl (cConst 0) c (cg.comp₂ x xs)
@[cp] theorem cListCasesOn_prim {cl cg} {c : Code}
    (hcl : IsPrim cl) (hc : IsPrim c) (hcg : IsPrim cg) :
    IsPrim (cListCasesOn cl c cg) := by
  unfold cListCasesOn; apply_cp
@[simp, evp_simps] theorem cListCasesOn_evp {O : ℕ → ℕ} {cl c cg input} :
    evalp O (cListCasesOn cl c cg) input =
  List.casesOn
  (n2l (evalp O cl input))
  (evalp O c input)
  (fun x xs => evalp O cg (Nat.pair x (l2n xs)))
 := by
  simp only [cListCasesOn, evp_simps]
  by_cases hl : (evalp O cl input)=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
end Oracle.Single.Code
end list_casesOn
section list_casesOn'
namespace Oracle.Single.Code
/-- Given codes `cl`, `c`, `cg`, this code defines the function
`fun x ↦ List.casesOn (n2l [cl](x)) [c](x) (fun _ ↦ [cg](x))`. -/
def cListCasesOn' (cl c cg : Code) :=
  cIfEqTe.comp₄ cl (cConst 0) c cg
@[cp] theorem cListCasesOn'_prim {cl cg} {c : Code}
    (hcl : IsPrim cl) (hc : IsPrim c) (hcg : IsPrim cg) :
    IsPrim (cListCasesOn' cl c cg) := by
  unfold cListCasesOn'; apply_cp
@[simp, evp_simps] theorem cListCasesOn'_evp {O : ℕ → ℕ} {cl c cg input} :
    evalp O (cListCasesOn' cl c cg) input =
    List.casesOn
      (n2l (evalp O cl input))
      (evalp O c input)
      (fun _ => evalp O cg input) := by
  simp only [cListCasesOn', evp_simps]
  by_cases hl : (evalp O cl input)=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
end Oracle.Single.Code
end list_casesOn'

section list_drop
namespace Oracle.Single.Code
/-- This code defines the function `fun ⟪i, l⟫ ↦ l2n ((n2l l).drop i)`. -/
def cListDrop :=
  (
    prec
    cId <|
    cListTail.comp (right.comp right)
  ).comp cFlip
@[cp] theorem cListDrop_prim : IsPrim cListDrop := by unfold cListDrop; apply_cp
@[simp, evp_simps] theorem cListDrop_evp {O : ℕ → ℕ} {lN i : ℕ} :
    evalp O cListDrop (Nat.pair i lN) = l2n (drop i (n2l lN)) := by
  simp only [cListDrop, evp_simps]
  by_cases hl : lN=0
  · simp only [unpaired, hl, unpair_pair, list_ofNat_zero, drop_nil, encode_list_nil]
    induction i with
    | zero => simp
    | succ n ih => simp [ih]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec];
    simp only [unpaired, unpair_pair, list_ofNat_succ, unpair1_to_l, ofNat_nat,
      unpair2_to_r]
    induction i with
    | zero => simp
    | succ n ih => simp [ih]
@[simp, ev_simps] theorem cListDrop_ev {O : ℕ → ℕ} {lN i : ℕ} :
    eval O cListDrop (Nat.pair i lN) = l2n (drop i (n2l lN)) := by
  simp [← evalp_eq_eval cListDrop_prim]
end Oracle.Single.Code
end list_drop

section list_getElem?
namespace Oracle.Single.Code
/-- This code defines the function `fun ⟪l, i⟫ ↦ o2n (n2l l)[i]?`. -/
def cListGetElem? := cListHead?.comp (cListDrop.comp cFlip)
@[cp] theorem cListGetElem?_prim : IsPrim cListGetElem? := by
  unfold cListGetElem?; apply_cp
@[simp, evp_simps] theorem cListGetElem?_evp {O : ℕ → ℕ} {lN i : ℕ} :
  evalp O cListGetElem? ⟪lN, i⟫ = o2n (n2l lN)[i]? := by simp [cListGetElem?]
@[simp, ev_simps] theorem cListGetElem?_ev {O : ℕ → ℕ} {lN i : ℕ} :
    eval O cListGetElem? ⟪lN, i⟫ = o2n (n2l lN)[i]? := by
  simp [← evalp_eq_eval cListGetElem?_prim]
end Oracle.Single.Code
end list_getElem?

section list_getD
namespace Oracle.Single.Code
/-- This code defines the function `fun ⟪l, i, d⟫ ↦ (n2l l).getD i d`. -/
def cListGetD :=
  cOptGetD.comp₂ (cListGetElem?.comp₂ left (left.comp right)) (right.comp right)
@[cp] theorem cListGetD_prim : IsPrim cListGetD := by unfold cListGetD; apply_cp
@[simp, evp_simps] theorem cListGetD_evp {O : ℕ → ℕ} {lN i d : ℕ} :
  evalp O cListGetD ⟪lN, i, d⟫ = (n2l lN).getD i d := by simp [cListGetD]
@[simp, ev_simps] theorem cListGetD_ev {O : ℕ → ℕ} {lN i d : ℕ} :
  eval O cListGetD ⟪lN, i, d⟫ = (n2l lN).getD i d := by simp [← evalp_eq_eval cListGetD_prim]
end Oracle.Single.Code
end list_getD

section list_getI
namespace Oracle.Single.Code
/-- This code defines the function `fun ⟪l, i⟫ ↦ (n2l l).getI i`. -/
def cListGetI := cPred.comp cListGetElem?
@[cp] theorem cListGetI_prim : IsPrim cListGetI := by unfold cListGetI; apply_cp
@[simp, evp_simps] theorem cListGetI_evp {O : ℕ → ℕ} {lN i : ℕ} :
    evalp O cListGetI ⟪lN, i⟫ = ((n2l lN).getI i) := by
  simp [cListGetI]
  by_cases hl : i < (n2l lN).length <;> simp [hl, getI]
@[simp, ev_simps] theorem cListGetI_ev {O : ℕ → ℕ} {lN i : ℕ} :
  eval O cListGetI ⟪lN, i⟫ = ((n2l lN).getI i) := by simp [← evalp_eq_eval cListGetI_prim]
end Oracle.Single.Code
end list_getI

section list_get
namespace Oracle.Single.Code
/-- This code defines the function `fun ⟪l, i⟫ ↦ (n2l l)[i]` (for `i < (n2l l).length`). -/
def cListGet := cListGetI
@[cp] theorem cListGet_prim : IsPrim cListGet := by unfold cListGet; apply_cp
@[simp, evp_simps] theorem cListGet_evp {O : ℕ → ℕ} {lN i : ℕ} (h : i < (n2l lN).length) :
    evalp O cListGet ⟪lN, i⟫ = (n2l lN)[i] := by
  simp only [cListGet, evp_simps]
  simp only [getI, default_eq_zero, getD_eq_getElem?_getD]
  by_cases hl : i < (n2l lN).length
  · simp [hl]
  · contradiction
@[simp, ev_simps] theorem cListGet_ev {O : ℕ → ℕ} {lN i : ℕ} (h : i < (n2l lN).length) :
    eval O cListGet ⟪lN, i⟫ = (n2l lN)[i] := by
  simp [← evalp_eq_eval cListGet_prim]
  simp [h]
end Oracle.Single.Code
end list_get

/-
`foldl :: (a -> b -> a) -> a -> [b] -> a`
`foldl fn acc [] = acc`
`foldl fn acc (x : xs) = foldl fn (fn acc x) xs`
-/
section list_foldl
namespace Oracle.Single.Code
/-- Auxiliary code for `cListFoldl`: one step of the fold. -/
def cListFoldlAux (c : Code) :=
  let x := left.comp (cPred.comp right)
  let xs := right.comp (cPred.comp right)
  cListCasesOn' right cId (pair (c.comp₂ left x) (xs))
/-- Given a code `c`, this code defines the function
`fun ⟪init, l⟫ ↦ (n2l l).foldl (fun a b ↦ [c](⟪a, b⟫)) init`. -/
def cListFoldl (c : Code) := left.comp ((cNatIterate (cListFoldlAux c)).comp₂ cId right)
@[cp] theorem cListFoldl_prim {c : Code} (hc : IsPrim c) : IsPrim (cListFoldl c) := by
  rewrite [cListFoldl, cListFoldlAux]; apply_cp
@[simp, evp_simps] theorem cListFoldlAux_evp {O : ℕ → ℕ} {c : Code} {init lN : ℕ} :
    evalp O (cListFoldlAux c) ⟪init, lN⟫ =
    if (n2l lN) = []
      then ⟪init, lN⟫
      else Nat.pair (evalp O c (Nat.pair init (n2l lN).headI)) (l2n (tail (n2l lN))) := by
  simp only [cListFoldlAux]
  by_cases hl : lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp, evp_simps] theorem cListFoldl_evp {O : ℕ → ℕ} {c : Code} {init lN : ℕ} :
  evalp O (cListFoldl c) ⟪init, lN⟫ =
  foldl
    (fun a b => evalp O c ⟪a,b⟫)
    init
    (n2l lN) := by
  simp only [cListFoldl, evp_simps]
  suffices ∀ n,
      (evalp O c.cListFoldlAux)^[n] ⟪init, lN⟫ =
      ⟪((n2l lN).take n).foldl (fun a b => evalp O c ⟪a,b⟫) init, l2n ((n2l lN).drop n)⟫ by
    rw [this]
    rw (config := {occs := .pos [1]}) [show lN=(l2n (n2l lN)) from by simp]
    rw [take_of_length_le (length_le_encode _)]
    simp
  introv
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hl : lN=0
    · simp? [hl] says
        simp only [hl, Function.iterate_succ, Function.comp_apply, cListFoldlAux_evp,
          list_ofNat_zero, ↓reduceIte, take_nil, foldl_nil, drop_nil, encode_list_nil]
      have fixedp : evalp O c.cListFoldlAux ⟪init, 0⟫ = ⟪init, 0⟫ := by simp
      apply Function.iterate_fixed fixedp
    · simp only [Function.iterate_succ']
      by_cases hl2 : (n2l lN).length ≤ n
      · simpa [ih, hl2, take_of_length_le hl2, take_of_length_le (le_add_right_of_le hl2)]
        using le_add_right_of_le hl2
      · simp? [ih, hl2] says
          simp only [Function.comp_apply, ih, cListFoldlAux_evp, ofNat_encode, drop_eq_nil_iff,
          hl2, ↓reduceIte, tail_drop, pair_eq_pair, and_true]
        have lgt_1 : (n2l lN).length ≥ n+1 := gt_of_not_le hl2
        have take_rw_aux : (n2l lN)[n] = (drop n (n2l lN)).headI := by
          have ln_gt_0 : length (drop n (n2l lN)) > 0 := lt_length_drop lgt_1
          have hdrop := @getElem_drop ℕ (n2l lN) n 0 ln_gt_0
          simp only [add_zero] at hdrop
          rcases exists_cons_of_length_pos ln_gt_0 with ⟨_,_,hkt⟩
          simp [hkt]
          simp_all only [encode_list_cons, encode_nat, succ_eq_add_one, not_le, getElem_cons_zero]
        have take_rw :
            (take (n + 1) (n2l lN)) = (take n (n2l lN)) ++ [(drop n (n2l lN)).headI] := by
          rw [show (take (n + 1) (n2l lN)) = (take n (n2l lN)) ++ [(n2l lN)[n]] from by simp]
          rw [take_rw_aux]
        rw [take_rw]
        simp
end Oracle.Single.Code
end list_foldl

section list_reverse
namespace Oracle.Single.Code
-- Note that reverse = foldl (flip ( : )) [].
/-- This code defines the function `fun l ↦ l2n (n2l l).reverse`. -/
def cListReverse := (cListFoldl (cListCons.comp cFlip)).comp₂ cListNil cId
@[cp] theorem cListReverse_prim : IsPrim cListReverse := by unfold cListReverse; apply_cp
@[simp, evp_simps] theorem cListReverse_evp {O : ℕ → ℕ} {lN} :
    evalp O cListReverse lN =  l2n (reverse (n2l lN)) := by
  simp only [cListReverse, evp_simps]
  have aux : ∀ l r,
      foldl (fun (s : ℕ) (b : ℕ) => l2n (b :: (n2l s))) r l = l2n (reverseAux l (n2l r)) :=
    fun l => by induction l with
    | nil => simp [*, reverseAux]
    | cons head tail ih => simp [*, reverseAux, -encode_list_cons]
  rw [aux (n2l lN) (l2n [])]
  simp
@[simp, ev_simps] theorem cListReverse_ev {O : ℕ → ℕ} {lN} :
    eval O cListReverse lN =  l2n (reverse (n2l lN)) := by
  simp [← evalp_eq_eval cListReverse_prim]
end Oracle.Single.Code
end list_reverse

/-
`foldr :: (a -> b -> b) -> b -> [a] -> b`
`foldr fn acc [] = acc`
`foldr fn acc (x : xs) = fn x (foldr fn acc xs)`
-/
section list_foldr
namespace Oracle.Single.Code
/-- Given a code `c`, this code defines the function
`fun ⟪init, l⟫ ↦ (n2l l).foldr (fun a b ↦ [c](⟪a, b⟫)) init`. -/
def cListFoldr (c : Code) := (cListFoldl (c.comp cFlip)).comp₂ left (cListReverse.comp right)
@[cp] theorem cListFoldr_prim {c : Code} (hc : IsPrim c) : IsPrim (cListFoldr c) := by
  unfold cListFoldr; apply_cp
@[simp, evp_simps] theorem cListFoldr_evp {O : ℕ → ℕ} {c : Code} {init lN : ℕ} :
  evalp O (cListFoldr c) ⟪init, lN⟫ = foldr
    (fun a b => evalp O c ⟪a,b⟫)
    init
    (n2l lN) := by
  simp [cListFoldr]
end Oracle.Single.Code
end list_foldr

-- https : //hackage.haskell.org/package/ghc-internal-9.1201.0/docs/src/GHC.Internal.Data.Foldable.html#length
section list_length
namespace Oracle.Single.Code
/-- This code defines the function `fun l ↦ (n2l l).length`. -/
def cListLength := (cListFoldl (succ.comp left)).comp₂ zero cId
@[cp] theorem cListLength_prim : IsPrim cListLength := by unfold cListLength; apply_cp
@[simp, evp_simps] theorem cListLength_evp {O : ℕ → ℕ} {lN : ℕ} :
  evalp O cListLength lN = length (n2l lN) := by simp [cListLength]
@[simp, ev_simps] theorem cListLength_ev {O : ℕ → ℕ} {lN : ℕ} :
  eval O cListLength lN = length (n2l lN) := by simp [← evalp_eq_eval cListLength_prim]
end Oracle.Single.Code
end list_length

section list_getLast?
namespace Oracle.Single.Code
/-- This code defines the function `fun l ↦ o2n (n2l l).getLast?`. -/
def cListGetLast? := cListGetElem?.comp₂ cId (cPred.comp <| cListLength.comp cId)
@[cp] theorem cListGetLast?_prim : IsPrim cListGetLast? := by
  unfold cListGetLast?; apply_cp
@[simp, evp_simps] theorem cListGetLast?_evp {O : ℕ → ℕ} {lN : ℕ} :
    evalp O cListGetLast? lN = o2n (getLast? (n2l lN)) := by
  simpa [cListGetLast?] using Eq.symm getLast?_eq_getElem?
@[simp, ev_simps] theorem cListGetLast?_ev {O : ℕ → ℕ} {lN : ℕ} :
    eval O cListGetLast? lN = o2n (getLast? (n2l lN)) := by
  simp [← evalp_eq_eval cListGetLast?_prim]
end Oracle.Single.Code
end list_getLast?

section list_getLastI
namespace Oracle.Single.Code
/-- This code defines the function `fun l ↦ (n2l l).getLastI`. -/
def cListGetLastI := cOptIget.comp cListGetLast?
@[cp] theorem cListGetLastI_prim : IsPrim cListGetLastI := by
  unfold cListGetLastI; apply_cp
@[simp, evp_simps] theorem cListGetLastI_evp {O : ℕ → ℕ} {lN : ℕ} :
    evalp O cListGetLastI lN = getLastI (n2l lN) := by
  simp [cListGetLastI, getLastI_eq_getLast?_getD]
@[simp, ev_simps] theorem cListGetLastI_ev {O : ℕ → ℕ} {lN : ℕ} :
  eval O cListGetLastI lN = getLastI (n2l lN) := by simp [← evalp_eq_eval cListGetLastI_prim]
end Oracle.Single.Code
end list_getLastI

/-
(++) []     ys = ys
(++) (x : xs) ys = x : xs ++ ys
-/
section list_append
namespace Oracle.Single.Code
/-- This code defines the function `fun ⟪l₁, l₂⟫ ↦ l2n (n2l l₁ ++ n2l l₂)`. -/
def cListAppend := (cListFoldr (cListCons)).comp cFlip
@[cp] theorem cListAppend_prim : IsPrim cListAppend := by unfold cListAppend; apply_cp
@[simp, evp_simps] theorem cListAppend_evp {O : ℕ → ℕ} {l1N l2N} :
    evalp O cListAppend ⟪l1N, l2N⟫ = l2n ((n2l l1N) ++ (n2l l2N)) := by
  simp only [cListAppend, evp_simps]
  induction (n2l l1N) with
  | nil => simp
  | cons head tail ih => simp [ih, -encode_list_cons, -encode_list_nil]
@[simp, ev_simps] theorem cListAppend_ev {O : ℕ → ℕ} {l1N l2N} :
    eval O cListAppend ⟪l1N, l2N⟫ = l2n ((n2l l1N) ++ (n2l l2N)) := by
  simp [← evalp_eq_eval cListAppend_prim]
end Oracle.Single.Code
end list_append

section list_singleton
namespace Oracle.Single.Code
/-- Given a code `c`, this code defines the function `fun x ↦ l2n [[c](x)]`. -/
def cListSingleton (c : Code) := cListCons.comp₂ c cListNil
@[cp] theorem cListSingleton_prim {c : Code} (hc : IsPrim c) :
  IsPrim (cListSingleton c) := by unfold cListSingleton; apply_cp
@[simp, evp_simps] theorem cListSingleton_evp {O : ℕ → ℕ} {c x} :
    evalp O (cListSingleton c) x = l2n ([evalp O c x]) := by
  simp [cListSingleton]
end Oracle.Single.Code
end list_singleton

section list_concat
namespace Oracle.Single.Code
/-- This code defines the function `fun ⟪l, i⟫ ↦ l2n (n2l l ++ [i])`. -/
def cListConcat := cListAppend.comp₂ left (cListSingleton right)
@[cp] theorem cListConcat_prim : IsPrim cListConcat := by unfold cListConcat; apply_cp
@[simp, evp_simps] theorem cListConcat_evp {O : ℕ → ℕ} {lN i : ℕ} :
    evalp O cListConcat ⟪lN, i⟫ = l2n ((n2l lN)++[i]) := by
  simp [cListConcat, -encode_list_cons, -encode_list_nil]
@[simp, ev_simps] theorem cListConcat_ev {O : ℕ → ℕ} {lN i : ℕ} :
  eval O cListConcat ⟪lN, i⟫ = l2n ((n2l lN)++[i]) := by simp [← evalp_eq_eval cListConcat_prim]
end Oracle.Single.Code
end list_concat

-- https : //hackage.haskell.org/package/ghc-internal-9.1201.0/docs/src/GHC.Internal.Base.html#map
section list_map
namespace Oracle.Single.Code
/-- Given a code `c`, this code defines the function `fun l ↦ l2n ((n2l l).map [c])`. -/
def cListMap (c : Code) :=
  (cListFoldr (cListCons.comp₂ (c.comp left) right)).comp₂ (cListNil) (cId)
@[cp] theorem cListMap_prim {c : Code} (hc : IsPrim c) : IsPrim (cListMap c) := by
  unfold cListMap; apply_cp
@[simp, evp_simps] theorem cListMap_evp {O : ℕ → ℕ} {c : Code} {lN : ℕ} :
    evalp O (cListMap c) lN = l2n ((n2l lN).map (evalp O c)) := by
  simp only [cListMap, evp_simps]
  induction (n2l lN) with
  | nil => simp
  | cons head tail ih => simp [ih, -encode_list_cons, -encode_list_nil]
end Oracle.Single.Code
end list_map

section list_zipWith
namespace Oracle.Single.Code
/-
zipL :: [a] -> [b] -> [(a,b)]
zipL xs ys = reverse <| fst <| foldl step ([], ys) xs
  where
    step (acc, y : ys') x = ((x,y) : acc, ys')
    step (acc, [])    _ = (acc, [])
-/
/-- Auxiliary code for `cListZipWith`. -/
def cListZipWithAux (c : Code) :=
  let yys' := right.comp left
  let ys' := cListTail.comp  yys'
  let y   := cListHeadI.comp yys'
  let x   := right
  let acc := left.comp left
  let step :=
    cListCasesOn'
    yys'
    left
    (pair (cListCons.comp₂ (c.comp₂ x y) acc) ys')
  (cListFoldl step).comp₂ (pair cListNil right) left
/-- Given a code `c`, this code defines the function
`fun ⟪l₁, l₂⟫ ↦ zipWith (fun x y ↦ [c](⟪x, y⟫)) l₁ l₂`. -/
def cListZipWith (c : Code) := cListReverse.comp <| left.comp (cListZipWithAux c)

@[cp] theorem cListZipWithAux_prim {c : Code} (hc : IsPrim c) :
  IsPrim (cListZipWithAux c) := by unfold cListZipWithAux; apply_cp
@[cp] theorem cListZipWith_prim {c : Code} (hc : IsPrim c) : IsPrim (cListZipWith c) := by
  unfold cListZipWith; apply_cp
theorem cListZipWith_evp_aux_2 {a b c : List ℕ} {f : ℕ → ℕ → ℕ} (h : a.length ≤ b.length) :
    zipWith f (b++c) a = zipWith f b a := by
  -- rw `b` => `take a.length b ++ drop a.length b`
  rewrite [(take_append_drop a.length b).symm]
  -- rw `take a.length b ++ drop a.length b ++ c` => `take a.length b ++ (drop a.length b ++ c)`
  rewrite [append_assoc (take a.length b) (drop a.length b) c]
  have aux7 : (take a.length b).length = a.length := length_take_of_le h
  have aux6 := @zipWith_append ℕ ℕ ℕ f (take a.length b) (drop a.length b ++ c) a [] aux7
  have aux8 := @zipWith_append ℕ ℕ ℕ f (take a.length b) (drop a.length b) a [] aux7
  simp at aux6 aux8
  simp [aux6, aux8]
theorem zipWith_flip {α β γ : Type} {f : α → β → γ} {a : List α} {b : List β} :
    zipWith f a b = zipWith (flip f) b a := by
  induction a generalizing b with
  | nil => simp
  | cons _ _ xih =>
    induction b with
    | nil => simp
    | cons _ _ yih => simp [xih, flip]

theorem cListZipWith_evp_aux_1 {a b c : List ℕ} {f : ℕ → ℕ → ℕ} (h : a.length ≤ b.length) :
    zipWith f a (b++c) = zipWith f a b := by
  rw [zipWith_flip]
  rw (config := {occs := .pos [2]}) [zipWith_flip]
  exact cListZipWith_evp_aux_2 h

theorem cListZipWith_evp_aux_3 {f : ℕ → ℕ → ℕ} {head} {tail : List ℕ} {l2N head2 list2}
    (hh : tail.length < (n2l l2N).length) (hl2 : drop tail.length (n2l l2N) = head2 :: list2) :
    (f head (head2 :: list2).headI :: (zipWith f tail.reverse (n2l l2N)).reverse) =
    (zipWith f (tail.reverse ++ [head]) (n2l l2N)).reverse := by
  simp only [headI_cons]
  have aux5 : (n2l l2N) = (take tail.length (n2l l2N)) ++ [head2] ++ list2 := by
    rw (config := {occs := .pos [1]}) [Eq.symm (take_append_drop tail.length (n2l l2N))]
    rw [append_assoc, hl2]
    simp
  have aux7 :
      let l₁ := tail.reverse ++ [head]
      let l₂ := take tail.length (n2l l2N) ++ [head2] ++ list2
      let l₁' := zipWith f (tail.reverse) (take tail.length (n2l l2N))
      let l₂' : List ℕ := [f head head2]
      ∃ ws xs ys zs, ws.length = ys.length ∧ l₁ = ws ++ xs ∧ l₂ = ys ++ zs ∧ l₁' =
      zipWith f ws ys ∧ l₂' = zipWith f xs zs := by
    let ws := tail.reverse
    let ys := take tail.length (n2l l2N)
    let xs := [head]
    let zs := [head2] ++ list2
    use ws,xs,ys,zs
    constructor
    · simpa [ws,ys] using le_of_succ_le hh
    · exact ⟨rfl, append_assoc (take tail.length (n2l l2N)) [head2] list2, rfl, rfl⟩
  have aux9 : tail.reverse.length ≤ (take tail.length (n2l l2N)).length := by
    simp only [length_reverse, length_take, le_inf_iff, le_refl, true_and]
    exact le_of_succ_le hh
  rw (config := {occs := .pos [2]}) [aux5]
  rw [zipWith_eq_append_iff.mpr aux7]
  rw (config := {occs := .pos [1]}) [aux5]
  rw [append_assoc (take tail.length (n2l l2N)) [head2] list2]
  simpa using cListZipWith_evp_aux_1 aux9
theorem cListZipWithAux_evp {O c l1N l2N} :
    evalp O (cListZipWithAux c) ⟪l1N, l2N⟫ =
    Nat.pair
      ((zipWith (fun x y => evalp O c ⟪x,y⟫) l1N l2N).reverse)
      (drop (n2l l1N).length (n2l l2N)) := by
  let f := fun x y => evalp O c ⟪x,y⟫
  simp only [cListZipWithAux, evp_simps]
  induction h : (n2l l1N).reverse generalizing l1N with
  | nil => simp_all
  | cons head tail ih =>
    have a0 : (n2l l1N) = (tail.reverse).concat head := by
      rw [concat_eq_append, ←reverse_reverse (n2l l1N), h]
      exact reverse_cons
    rw [a0]
    simp only [Pi.natCast_apply, cast_id] at ih
    replace ih := ih (show (n2l (l2n tail.reverse)).reverse = tail from by simp)
    simp only [Pi.natCast_apply, cast_id, concat_eq_append, foldl_append, foldl_cons, foldl_nil,
      length_append, length_reverse, length_cons, length_nil, zero_add]
    simp only [ofNat_encode, length_reverse] at ih
    rw [ih]
    clear a0
    simp only [pair_r, ofNat_encode, pair_l, tail_drop]
    by_cases hh : drop tail.length (n2l l2N) = ([] : List ℕ)
    · simp only [hh]
      rw [show drop (tail.length + 1) (n2l l2N) = [] from by simp at hh ⊢; omega]
      have aux4 := drop_eq_nil_iff.mp hh
      rw [show tail.length = tail.reverse.length from length_reverse.symm] at aux4
      simp [cListZipWith_evp_aux_2 aux4]
    · -- this is the case where l2N is longer than l1N.
      rcases ne_nil_iff_exists_cons.mp hh with ⟨head2, list2, hl2⟩
      -- now we have `drop tail.length (n2l l2N) = head2 :: list2`
      simp only [hl2]
      simp only [drop_eq_nil_iff, not_le] at hh
      have main :
          (f head (head2 :: list2).headI :: (zipWith f tail.reverse (n2l l2N)).reverse) =
          (zipWith f (tail.reverse ++ [head]) (n2l l2N)).reverse :=
        cListZipWith_evp_aux_3 hh hl2
      rw [main]

@[simp, evp_simps] theorem cListZipWith_evp {O : ℕ → ℕ} {c l1N l2N} :
    evalp O (cListZipWith c) ⟪l1N, l2N⟫ =
    zipWith (fun x y => evalp O c ⟪x,y⟫) l1N l2N := by
  simp [cListZipWith, cListZipWithAux_evp]
end Oracle.Single.Code
end list_zipWith

section list_range
namespace Oracle.Single.Code
/-- This code defines the function `fun n ↦ l2n (List.range n)`. -/
def cListRange :=
  let prev_list := right.comp right
  let i := (left.comp right)
  (prec
  (cListNil)
  (cListConcat.comp₂ prev_list i)).comp₂ zero cId
@[cp] theorem cListRange_prim : IsPrim cListRange := by unfold cListRange; apply_cp
@[simp, evp_simps] theorem cListRange_evp {O : ℕ → ℕ} {n} :
    evalp O cListRange n = l2n (range n) := by
  simp only [cListRange, evp_simps]
  simp only [unpaired, encode_list_nil, unpair_pair]
  induction n with
  | zero => simp
  | succ n ih =>
    simpa [-encode_list_cons, -encode_list_nil, ih] using Eq.symm range_succ
@[simp, ev_simps] theorem cListRange_ev {O : ℕ → ℕ} {n} :
  eval O cListRange n = l2n (range n) := by simp [← evalp_eq_eval cListRange_prim]
end Oracle.Single.Code
end list_range

section list_replicate
namespace Oracle.Single.Code
/-- This code defines the function `fun ⟪n, x⟫ ↦ l2n (List.replicate n x)`. -/
def cListReplicate :=
  let prev_list := right.comp right
  let x := left
  (prec
  (cListNil)
  (cListConcat.comp₂ prev_list x)).comp cFlip
@[cp] theorem cListReplicate_prim : IsPrim cListReplicate := by
  unfold cListReplicate; apply_cp
@[simp, evp_simps] theorem cListReplicate_evp {O : ℕ → ℕ} {n x} :
    evalp O cListReplicate ⟪n,x⟫ = l2n (replicate n x) := by
  simp only [cListReplicate, evp_simps]
  simp only [unpaired, encode_list_nil, unpair_pair]
  induction n with
  | zero => simp
  | succ n ih =>
    simpa [-encode_list_cons, -encode_list_nil, ih] using Eq.symm replicate_succ'
@[simp, ev_simps] theorem cListReplicate_ev {O : ℕ → ℕ} {n x} :
    eval O cListReplicate ⟪n,x⟫ = l2n (replicate n x) := by
  simp [← evalp_eq_eval cListReplicate_prim]
end Oracle.Single.Code
end list_replicate

section list_map'
namespace Oracle.Single.Code
/--
`evalp O (cListMap' c) ⟪lN, aux⟫ = ((n2l lN).map (fun ele => evalp O c (Nat.pair ele aux)))`
-/
def cListMap' (c : Code) :=
  let lN := left
  let aux := right
  (cListMap c).comp
  ((cListZipWith cId).comp₂ lN (cListReplicate.comp₂ (cListLength.comp lN) aux))
@[cp] theorem cListMap'_prim {c : Code} (hc : IsPrim c) : IsPrim (cListMap' c) := by
  unfold cListMap'; apply_cp
@[simp, evp_simps] theorem cListMap'_evp {O : ℕ → ℕ} {c lN aux} :
    evalp O (cListMap' c) ⟪lN, aux⟫ =
    ((n2l lN).map (fun ele => evalp O c (Nat.pair ele aux))) := by
  simp only [cListMap', evp_simps]
  simp only [ofNat_encode, map_zipWith, encode_inj]
  induction (n2l lN) with
  | nil => simp [Nat.pair]
  | cons head tail ih => simpa [replicate_succ] using ih
end Oracle.Single.Code
end list_map'

@[simp] theorem getLastI_append {x} {y : ℕ} : (x++[y]).getLastI = y := by
  simp [getLastI_eq_getLast?_getD]

/-
we construct a version of foldr where the function takes an extra parameter as input.
`evalp O (cListFoldrParam c) ⟪param, init, lN⟫ =
  (
    foldr
    (fun a b => evalp O c ⟪param, a, b⟫)
    init
    lN.n2l
  )`.
This is used in the construction of a simple set.
-/
section list_foldr_param
namespace Oracle.Single.Code
/-- Auxiliary code for `cListFoldrParam`. -/
def cListFoldrParamAux (c : Code) :=
  let param := left
  let init := left.comp right
  let lN := right.comp right
  (cListFoldr <|
  (pair (left.comp left) <| c.comp₃ (left.comp left) (right.comp left) (right.comp right))).comp₂
  (pair param init)
  ((cListZipWith cId).comp₂ (cListReplicate.comp₂ (cListLength.comp lN) (param)) lN)
/-- Given a code `c`, this code defines the function
`fun ⟪p, init, l⟫ ↦ (n2l l).foldr (fun a b ↦ [c](⟪p, a, b⟫)) init`. -/
def cListFoldrParam (c : Code) := right.comp (cListFoldrParamAux c)
@[cp] theorem cListFoldrParamAux_prim {c : Code} (hc : IsPrim c) :
  IsPrim (cListFoldrParamAux c) := by unfold cListFoldrParamAux; apply_cp 60
@[cp] theorem cListFoldrParam_prim {c : Code} (hc : IsPrim c) :
    IsPrim (cListFoldrParam c) := by
  rewrite [cListFoldrParam]
  apply_cp
lemma cListFoldrParamAux_2 {f : ℕ → ℕ} {param init lst} :
    foldr
      (fun a b ↦ ⟪a.left, f ⟪a.left, a.right, b.right⟫⟫)
      ⟪param,init⟫
      (zipWith (fun (x y : ℕ) ↦ ⟪x,y⟫) (replicate lst.length param) lst) =
    ⟪param,foldr (fun a b ↦ f ⟪param,⟪a,b⟫⟫) init lst⟫ := by
  induction lst with
  | nil => simp
  | cons head tail ih =>
    simp only [length_cons, foldr_cons]
    have :
      (zipWith (fun x y ↦ ⟪x,y⟫) (replicate (tail.length + 1) param) (head :: tail)) =
      ⟪param, head⟫ :: (zipWith (fun x y ↦ ⟪x,y⟫) (replicate tail.length param) tail) := rfl
    rewrite [this]
    simp [ih]
@[simp, evp_simps] theorem cListFoldrParamAux_evp {O : ℕ → ℕ} {c param init lN} :
    evalp O (cListFoldrParamAux c) ⟪param, init, lN⟫ =
    Nat.pair param
    (
      foldr
      (fun a b => evalp O c ⟪param, a, b⟫)
      init
      lN.n2l
    ) := by
  simpa [cListFoldrParamAux, evp_simps] using cListFoldrParamAux_2
@[simp, evp_simps] theorem cListFoldrParam_evp {O : ℕ → ℕ} {c param init lN} :
  evalp O (cListFoldrParam c) ⟪param, init, lN⟫ =
  foldr
    (fun a b => evalp O c ⟪param, a, b⟫)
    init
    lN.n2l := by
    simp [cListFoldrParam]
end Oracle.Single.Code
end list_foldr_param
