/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Mathlib.Computability.SingleOracle.Constructions.Option

/-!
# Construction of basic primitive recursive functions on lists

This file defines basic primitive recursive codes for basic functions on lists.

## Structure
(See Oracle.Single.Constructions.Primitive for more details.)

The major constructions in this file are `c_list_foldl` and `c_list_zipWith`.

`c_list_foldl` allows easy definitions of subsequent constructs, although `c_list_zipWith` still
requires a nontrivial proof.

-/

open Nat Denumerable Encodable List

section list_nil
namespace Oracle.Single.Code
def c_list_nil := zero
@[cp] theorem c_list_nil_prim : code_prim c_list_nil := by unfold c_list_nil; apply_cp
@[simp, evp_simps] theorem c_list_nil_evp {O : ℕ → ℕ} {x} : evalp O c_list_nil x = l2n ([]) := by
  simp [c_list_nil]
@[simp, ev_simps] theorem c_list_nil_ev {O : ℕ → ℕ} {x} : eval O c_list_nil x = l2n ([]) := by
  simp [← evalp_eq_eval c_list_nil_prim]
end Oracle.Single.Code
end list_nil

section list_cons
namespace Oracle.Single.Code
def c_list_cons := succ
@[cp] theorem c_list_cons_prim : code_prim c_list_cons := by unfold c_list_cons; apply_cp
@[simp, evp_simps] theorem c_list_cons_evp {O : ℕ → ℕ} {a lN} :
    evalp O c_list_cons ⟪a, lN⟫= l2n (cons a (n2l lN)) := by
  simp [c_list_cons]
@[simp, ev_simps] theorem c_list_cons_ev {O : ℕ → ℕ} {a lN} :
    eval O c_list_cons ⟪a, lN⟫= l2n (cons a (n2l lN)) := by
  simp [←evalp_eq_eval c_list_cons_prim]
end Oracle.Single.Code
end list_cons

section list_tail
namespace Oracle.Single.Code
def c_list_tail := right.comp c_pred
@[cp] theorem c_list_tail_prim : code_prim c_list_tail := by unfold c_list_tail; apply_cp
@[simp, evp_simps] theorem c_list_tail_evp {O : ℕ → ℕ} {lN : ℕ} :
    evalp O c_list_tail lN = l2n (tail (n2l lN)) := by
  simp only [c_list_tail]
  by_cases hl : lN=0
  · simp [hl, Nat.right]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp, ev_simps] theorem c_list_tail_ev {O : ℕ → ℕ} {lN : ℕ} :
    eval O c_list_tail lN = l2n (tail (n2l lN)) := by
  simp [← evalp_eq_eval c_list_tail_prim]
end Oracle.Single.Code
end list_tail

section list_head?
namespace Oracle.Single.Code
def c_list_head? := c_ifz.comp₃ c_id zero <| succ.comp (left.comp c_pred)
@[cp] theorem c_list_head?_prim : code_prim c_list_head? := by unfold c_list_head?; apply_cp
@[simp, evp_simps] theorem c_list_head?_evp {O : ℕ → ℕ} {lN : ℕ} :
    evalp O c_list_head? lN = o2n (head? (n2l lN)) := by
  simp only [c_list_head?]
  by_cases hl : lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp, ev_simps] theorem c_list_head?_ev {O : ℕ → ℕ} {lN : ℕ} :
  eval O c_list_head? lN = o2n (head? (n2l lN)) := by simp [← evalp_eq_eval c_list_head?_prim]
end Oracle.Single.Code
end list_head?

section list_headI
namespace Oracle.Single.Code
def c_list_headI := c_ifz.comp₃ c_id zero (left.comp c_pred)
@[cp] theorem c_list_headI_prim : code_prim c_list_headI := by unfold c_list_headI; apply_cp
@[simp, evp_simps] theorem c_list_headI_evp {O : ℕ → ℕ} {lN : ℕ} :
    evalp O c_list_headI lN = headI (n2l lN) := by
  simp only [c_list_headI]
  by_cases hl : lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp, ev_simps] theorem c_list_headI_ev {O : ℕ → ℕ} {lN : ℕ} :
    eval O c_list_headI lN = headI (n2l lN) := by
  simp [← evalp_eq_eval c_list_headI_prim]
end Oracle.Single.Code
end list_headI

section list_casesOn
namespace Oracle.Single.Code
def c_list_casesOn (cl c cg : Code) :=
  let x := left.comp (c_pred.comp cl)
  let xs := right.comp (c_pred.comp cl)
  c_if_eq_te.comp₄ cl (c_const 0) c (cg.comp₂ x xs)
@[cp] theorem c_list_casesOn_prim {cl cg} {c : Code}
    (hcl : code_prim cl) (hc : code_prim c) (hcg : code_prim cg) :
    code_prim (c_list_casesOn cl c cg) := by
  unfold c_list_casesOn; apply_cp
@[simp, evp_simps] theorem c_list_casesOn_evp {O : ℕ → ℕ} {cl c cg input} :
    evalp O (c_list_casesOn cl c cg) input =
  List.casesOn
  (n2l (evalp O cl input))
  (evalp O c input)
  (fun x xs => evalp O cg (Nat.pair x (l2n xs)))
 := by
  simp only [c_list_casesOn, evp_simps]
  by_cases hl : (evalp O cl input)=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
end Oracle.Single.Code
end list_casesOn
section list_casesOn'
namespace Oracle.Single.Code
def c_list_casesOn' (cl c cg : Code) :=
  c_if_eq_te.comp₄ cl (c_const 0) c cg
@[cp] theorem c_list_casesOn'_prim {cl cg} {c : Code}
    (hcl : code_prim cl) (hc : code_prim c) (hcg : code_prim cg) :
    code_prim (c_list_casesOn' cl c cg) := by
  unfold c_list_casesOn'; apply_cp
@[simp, evp_simps] theorem c_list_casesOn'_evp {O : ℕ → ℕ} {cl c cg input} :
    evalp O (c_list_casesOn' cl c cg) input =
    List.casesOn
      (n2l (evalp O cl input))
      (evalp O c input)
      (fun _ => evalp O cg input) := by
  simp only [c_list_casesOn', evp_simps]
  by_cases hl : (evalp O cl input)=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
end Oracle.Single.Code
end list_casesOn'

section list_drop
namespace Oracle.Single.Code
def c_list_drop :=
  (
    prec
    c_id <|
    c_list_tail.comp (right.comp right)
  ).comp c_flip
@[cp] theorem c_list_drop_prim : code_prim c_list_drop := by unfold c_list_drop; apply_cp
@[simp, evp_simps] theorem c_list_drop_evp {O : ℕ → ℕ} {lN i : ℕ} :
    evalp O c_list_drop (Nat.pair i lN) = l2n (drop i (n2l lN)) := by
  simp only [c_list_drop, evp_simps]
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
@[simp, ev_simps] theorem c_list_drop_ev {O : ℕ → ℕ} {lN i : ℕ} :
    eval O c_list_drop (Nat.pair i lN) = l2n (drop i (n2l lN)) := by
  simp [← evalp_eq_eval c_list_drop_prim]
end Oracle.Single.Code
end list_drop

section list_getElem?
namespace Oracle.Single.Code
def c_list_getElem? := c_list_head?.comp (c_list_drop.comp c_flip)
@[cp] theorem c_list_getElem?_prim : code_prim c_list_getElem? := by
  unfold c_list_getElem?; apply_cp
@[simp, evp_simps] theorem c_list_getElem?_evp {O : ℕ → ℕ} {lN i : ℕ} :
  evalp O c_list_getElem? ⟪lN, i⟫ = o2n (n2l lN)[i]? := by simp [c_list_getElem?]
@[simp, ev_simps] theorem c_list_getElem?_ev {O : ℕ → ℕ} {lN i : ℕ} :
    eval O c_list_getElem? ⟪lN, i⟫ = o2n (n2l lN)[i]? := by
  simp [← evalp_eq_eval c_list_getElem?_prim]
end Oracle.Single.Code
end list_getElem?

section list_getD
namespace Oracle.Single.Code
def c_list_getD :=
  c_opt_getD.comp₂ (c_list_getElem?.comp₂ left (left.comp right)) (right.comp right)
@[cp] theorem c_list_getD_prim : code_prim c_list_getD := by unfold c_list_getD; apply_cp
@[simp, evp_simps] theorem c_list_getD_evp {O : ℕ → ℕ} {lN i d : ℕ} :
  evalp O c_list_getD ⟪lN, i, d⟫ = (n2l lN).getD i d := by simp [c_list_getD]
@[simp, ev_simps] theorem c_list_getD_ev {O : ℕ → ℕ} {lN i d : ℕ} :
  eval O c_list_getD ⟪lN, i, d⟫ = (n2l lN).getD i d := by simp [← evalp_eq_eval c_list_getD_prim]
end Oracle.Single.Code
end list_getD

section list_getI
namespace Oracle.Single.Code
def c_list_getI := c_pred.comp c_list_getElem?
@[cp] theorem c_list_getI_prim : code_prim c_list_getI := by unfold c_list_getI; apply_cp
@[simp, evp_simps] theorem c_list_getI_evp {O : ℕ → ℕ} {lN i : ℕ} :
    evalp O c_list_getI ⟪lN, i⟫ = ((n2l lN).getI i) := by
  simp [c_list_getI]
  by_cases hl : i < (n2l lN).length <;> simp [hl, getI]
@[simp, ev_simps] theorem c_list_getI_ev {O : ℕ → ℕ} {lN i : ℕ} :
  eval O c_list_getI ⟪lN, i⟫ = ((n2l lN).getI i) := by simp [← evalp_eq_eval c_list_getI_prim]
end Oracle.Single.Code
end list_getI

section list_get
namespace Oracle.Single.Code
def c_list_get := c_list_getI
@[cp] theorem c_list_get_prim : code_prim c_list_get := by unfold c_list_get; apply_cp
@[simp, evp_simps] theorem c_list_get_evp {O : ℕ → ℕ} {lN i : ℕ} (h : i < (n2l lN).length) :
    evalp O c_list_get ⟪lN, i⟫ = (n2l lN)[i] := by
  simp only [c_list_get, evp_simps]
  simp only [getI, default_eq_zero, getD_eq_getElem?_getD]
  by_cases hl : i < (n2l lN).length
  · simp [hl]
  · contradiction
@[simp, ev_simps] theorem c_list_get_ev {O : ℕ → ℕ} {lN i : ℕ} (h : i < (n2l lN).length) :
    eval O c_list_get ⟪lN, i⟫ = (n2l lN)[i] := by
  simp [← evalp_eq_eval c_list_get_prim]
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
def c_list_foldl_aux (c : Code) :=
  let x := left.comp (c_pred.comp right)
  let xs := right.comp (c_pred.comp right)
  c_list_casesOn' right c_id (pair (c.comp₂ left x) (xs))
def c_list_foldl_aux2 (c : Code) := (c_nat_iterate (c_list_foldl_aux c)).comp₂ c_id right
def c_list_foldl (c : Code) := left.comp (c_list_foldl_aux2 c)
@[cp] theorem c_list_foldl_prim {c : Code} (hc : code_prim c) : code_prim (c_list_foldl c) := by
  rewrite [c_list_foldl, c_list_foldl_aux2, c_list_foldl_aux]; apply_cp
@[simp, evp_simps] theorem c_list_foldl_aux_evp {O : ℕ → ℕ} {c : Code} {init lN : ℕ} :
    evalp O (c_list_foldl_aux c) ⟪init, lN⟫ =
    if (n2l lN) = []
      then ⟪init, lN⟫
      else Nat.pair (evalp O c (Nat.pair init (n2l lN).headI)) (l2n (tail (n2l lN))) := by
  simp only [c_list_foldl_aux]
  by_cases hl : lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp, evp_simps] theorem c_list_foldl_evp {O : ℕ → ℕ} {c : Code} {init lN : ℕ} :
  evalp O (c_list_foldl c) ⟪init, lN⟫ =
  foldl
    (fun a b => evalp O c ⟪a,b⟫)
    init
    (n2l lN) := by
  simp only [c_list_foldl,c_list_foldl_aux2, evp_simps]
  suffices ∀ n,
      (evalp O c.c_list_foldl_aux)^[n] ⟪init, lN⟫ =
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
        simp only [hl, Function.iterate_succ, Function.comp_apply, c_list_foldl_aux_evp,
          list_ofNat_zero, ↓reduceIte, take_nil, foldl_nil, drop_nil, encode_list_nil]
      have fixedp : evalp O c.c_list_foldl_aux ⟪init, 0⟫ = ⟪init, 0⟫ := by simp
      apply Function.iterate_fixed fixedp
    · simp only [Function.iterate_succ']
      by_cases hl2 : (n2l lN).length ≤ n
      · simpa [ih, hl2, take_of_length_le hl2, take_of_length_le (le_add_right_of_le hl2)]
        using le_add_right_of_le hl2
      · simp? [ih, hl2] says
          simp only [Function.comp_apply, ih, c_list_foldl_aux_evp, ofNat_encode, drop_eq_nil_iff,
          hl2, ↓reduceIte, tail_drop, pair_eq_pair, and_true]
        have lgt_1 : (n2l lN).length ≥ n+1 := gt_of_not_le hl2
        have take_rw_aux : (n2l lN)[n] = (drop n (n2l lN)).headI := by
          have ln_gt_0 : length (drop n (n2l lN)) > 0 := lt_length_drop lgt_1
          have hdrop := @getElem_drop ℕ (n2l lN) n 0 ln_gt_0
          simp only [add_zero] at hdrop
          rcases exists_cons_of_length_pos ln_gt_0 with ⟨_,_,hkt⟩
          simp [hkt]
          simp_all only [encode_list_cons, encode_nat, succ_eq_add_one, not_le, getElem_cons_zero]
          subst hdrop
          rfl
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
def c_list_reverse := (c_list_foldl (c_list_cons.comp c_flip)).comp₂ c_list_nil c_id
@[cp] theorem c_list_reverse_prim : code_prim c_list_reverse := by unfold c_list_reverse; apply_cp
@[simp, evp_simps] theorem c_list_reverse_evp {O : ℕ → ℕ} {lN} :
    evalp O c_list_reverse lN =  l2n (reverse (n2l lN)) := by
  simp only [c_list_reverse, evp_simps]
  have aux : ∀ l r,
      foldl (fun (s : ℕ) (b : ℕ) => l2n (b :: (n2l s))) r l = l2n (reverseAux l (n2l r)) :=
    fun l => by induction l with
    | nil => simp [*, reverseAux]
    | cons head tail ih => simp [*, reverseAux, -encode_list_cons]
  rw [aux (n2l lN) (l2n [])]
  simp
@[simp, ev_simps] theorem c_list_reverse_ev {O : ℕ → ℕ} {lN} :
    eval O c_list_reverse lN =  l2n (reverse (n2l lN)) := by
  simp [← evalp_eq_eval c_list_reverse_prim]
end Oracle.Single.Code
end list_reverse

/-
`foldr :: (a -> b -> b) -> b -> [a] -> b`
`foldr fn acc [] = acc`
`foldr fn acc (x : xs) = fn x (foldr fn acc xs)`
-/
section list_foldr
namespace Oracle.Single.Code
def c_list_foldr (c : Code) := (c_list_foldl (c.comp c_flip)).comp₂ left (c_list_reverse.comp right)
@[cp] theorem c_list_foldr_prim {c : Code} (hc : code_prim c) : code_prim (c_list_foldr c) := by
  unfold c_list_foldr; apply_cp
@[simp, evp_simps] theorem c_list_foldr_evp {O : ℕ → ℕ} {c : Code} {init lN : ℕ} :
  evalp O (c_list_foldr c) ⟪init, lN⟫ = foldr
    (fun a b => evalp O c ⟪a,b⟫)
    init
    (n2l lN) := by
  simp [c_list_foldr]
end Oracle.Single.Code
end list_foldr

-- https : //hackage.haskell.org/package/ghc-internal-9.1201.0/docs/src/GHC.Internal.Data.Foldable.html#length
section list_length
namespace Oracle.Single.Code
def c_list_length := (c_list_foldl (succ.comp left)).comp₂ zero c_id
@[cp] theorem c_list_length_prim : code_prim c_list_length := by unfold c_list_length; apply_cp
@[simp, evp_simps] theorem c_list_length_evp {O : ℕ → ℕ} {lN : ℕ} :
  evalp O c_list_length lN = length (n2l lN) := by simp [c_list_length]
@[simp, ev_simps] theorem c_list_length_ev {O : ℕ → ℕ} {lN : ℕ} :
  eval O c_list_length lN = length (n2l lN) := by simp [← evalp_eq_eval c_list_length_prim]
end Oracle.Single.Code
end list_length

section list_getLast?
namespace Oracle.Single.Code
def c_list_getLast? := c_list_getElem?.comp₂ c_id (c_pred.comp <| c_list_length.comp c_id)
@[cp] theorem c_list_getLast?_prim : code_prim c_list_getLast? := by
  unfold c_list_getLast?; apply_cp
@[simp, evp_simps] theorem c_list_getLast?_evp {O : ℕ → ℕ} {lN : ℕ} :
    evalp O c_list_getLast? lN = o2n (getLast? (n2l lN)) := by
  simpa [c_list_getLast?] using Eq.symm getLast?_eq_getElem?
@[simp, ev_simps] theorem c_list_getLast?_ev {O : ℕ → ℕ} {lN : ℕ} :
    eval O c_list_getLast? lN = o2n (getLast? (n2l lN)) := by
  simp [← evalp_eq_eval c_list_getLast?_prim]
end Oracle.Single.Code
end list_getLast?

section list_getLastI
namespace Oracle.Single.Code
def c_list_getLastI := c_opt_iget.comp c_list_getLast?
@[cp] theorem c_list_getLastI_prim : code_prim c_list_getLastI := by
  unfold c_list_getLastI; apply_cp
@[simp, evp_simps] theorem c_list_getLastI_evp {O : ℕ → ℕ} {lN : ℕ} :
    evalp O c_list_getLastI lN = getLastI (n2l lN) := by
  simp [c_list_getLastI, getLastI_eq_getLast?_getD]
@[simp, ev_simps] theorem c_list_getLastI_ev {O : ℕ → ℕ} {lN : ℕ} :
  eval O c_list_getLastI lN = getLastI (n2l lN) := by simp [← evalp_eq_eval c_list_getLastI_prim]
end Oracle.Single.Code
end list_getLastI

/-
(++) []     ys = ys
(++) (x : xs) ys = x : xs ++ ys
-/
section list_append
namespace Oracle.Single.Code
def c_list_append := (c_list_foldr (c_list_cons)).comp c_flip
@[cp] theorem c_list_append_prim : code_prim c_list_append := by unfold c_list_append; apply_cp
@[simp, evp_simps] theorem c_list_append_evp {O : ℕ → ℕ} {l1N l2N} :
    evalp O c_list_append ⟪l1N, l2N⟫ = l2n ((n2l l1N) ++ (n2l l2N)) := by
  simp only [c_list_append, evp_simps]
  induction (n2l l1N) with
  | nil => simp
  | cons head tail ih => simp [ih, -encode_list_cons, -encode_list_nil]
@[simp, ev_simps] theorem c_list_append_ev {O : ℕ → ℕ} {l1N l2N} :
    eval O c_list_append ⟪l1N, l2N⟫ = l2n ((n2l l1N) ++ (n2l l2N)) := by
  simp [← evalp_eq_eval c_list_append_prim]
end Oracle.Single.Code
end list_append

section list_singleton
namespace Oracle.Single.Code
def c_list_singleton (c : Code) := c_list_cons.comp₂ c c_list_nil
@[cp] theorem c_list_singleton_prim {c : Code} (hc : code_prim c) :
  code_prim (c_list_singleton c) := by unfold c_list_singleton; apply_cp
@[simp, evp_simps] theorem c_list_singleton_evp {O : ℕ → ℕ} {c x} :
    evalp O (c_list_singleton c) x = l2n ([evalp O c x]) := by
  simp [c_list_singleton]
end Oracle.Single.Code
end list_singleton

section list_concat
namespace Oracle.Single.Code
def c_list_concat := c_list_append.comp₂ left (c_list_singleton right)
@[cp] theorem c_list_concat_prim : code_prim c_list_concat := by unfold c_list_concat; apply_cp
@[simp, evp_simps] theorem c_list_concat_evp {O : ℕ → ℕ} {lN i : ℕ} :
    evalp O c_list_concat ⟪lN, i⟫ = l2n ((n2l lN)++[i]) := by
  simp [c_list_concat, -encode_list_cons, -encode_list_nil]
@[simp, ev_simps] theorem c_list_concat_ev {O : ℕ → ℕ} {lN i : ℕ} :
  eval O c_list_concat ⟪lN, i⟫ = l2n ((n2l lN)++[i]) := by simp [← evalp_eq_eval c_list_concat_prim]
end Oracle.Single.Code
end list_concat

-- https : //hackage.haskell.org/package/ghc-internal-9.1201.0/docs/src/GHC.Internal.Base.html#map
section list_map
namespace Oracle.Single.Code
def c_list_map (c : Code) :=
  (c_list_foldr (c_list_cons.comp₂ (c.comp left) right)).comp₂ (c_list_nil) (c_id)
@[cp] theorem c_list_map_prim {c : Code} (hc : code_prim c) : code_prim (c_list_map c) := by
  unfold c_list_map; apply_cp
@[simp, evp_simps] theorem c_list_map_evp {O : ℕ → ℕ} {c : Code} {lN : ℕ} :
    evalp O (c_list_map c) lN = l2n ((n2l lN).map (evalp O c)) := by
  simp only [c_list_map, evp_simps]
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
def c_list_zipWith_aux (c : Code) :=
  let yys' := right.comp left
  let ys' := c_list_tail.comp  yys'
  let y   := c_list_headI.comp yys'
  let x   := right
  let acc := left.comp left
  let step :=
    c_list_casesOn'
    yys'
    left
    (pair (c_list_cons.comp₂ (c.comp₂ x y) acc) ys')
  (c_list_foldl step).comp₂ (pair c_list_nil right) left
def c_list_zipWith (c : Code) := c_list_reverse.comp <| left.comp (c_list_zipWith_aux c)

@[cp] theorem c_list_zipWith_aux_prim {c : Code} (hc : code_prim c) :
  code_prim (c_list_zipWith_aux c) := by unfold c_list_zipWith_aux; apply_cp
@[cp] theorem c_list_zipWith_prim {c : Code} (hc : code_prim c) : code_prim (c_list_zipWith c) := by
  unfold c_list_zipWith; apply_cp
theorem c_list_zipWith_evp_aux_2 {a b c : List ℕ} {f : ℕ → ℕ → ℕ} (h : a.length ≤ b.length) :
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

theorem c_list_zipWith_evp_aux_1 {a b c : List ℕ} {f : ℕ → ℕ → ℕ} (h : a.length ≤ b.length) :
    zipWith f a (b++c) = zipWith f a b := by
  rw [zipWith_flip]
  rw (config := {occs := .pos [2]}) [zipWith_flip]
  exact c_list_zipWith_evp_aux_2 h

theorem c_list_zipWith_evp_aux_3 {f : ℕ → ℕ → ℕ} {head} {tail : List ℕ} {l2N head2 list2}
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
  simpa using c_list_zipWith_evp_aux_1 aux9
theorem c_list_zipWith_aux_evp {O c l1N l2N} :
    evalp O (c_list_zipWith_aux c) ⟪l1N, l2N⟫ =
    Nat.pair
      ((zipWith (fun x y => evalp O c ⟪x,y⟫) l1N l2N).reverse)
      (drop (n2l l1N).length (n2l l2N)) := by
  let f := fun x y => evalp O c ⟪x,y⟫
  simp only [c_list_zipWith_aux, evp_simps]
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
      simp [c_list_zipWith_evp_aux_2 aux4]
    · -- this is the case where l2N is longer than l1N.
      rcases ne_nil_iff_exists_cons.mp hh with ⟨head2, list2, hl2⟩
      -- now we have `drop tail.length (n2l l2N) = head2 :: list2`
      simp only [hl2]
      simp only [drop_eq_nil_iff, not_le] at hh
      have main :
          (f head (head2 :: list2).headI :: (zipWith f tail.reverse (n2l l2N)).reverse) =
          (zipWith f (tail.reverse ++ [head]) (n2l l2N)).reverse :=
        c_list_zipWith_evp_aux_3 hh hl2
      rw [main]

@[simp, evp_simps] theorem c_list_zipWith_evp {O : ℕ → ℕ} {c l1N l2N} :
    evalp O (c_list_zipWith c) ⟪l1N, l2N⟫ =
    zipWith (fun x y => evalp O c ⟪x,y⟫) l1N l2N := by
  simp [c_list_zipWith, c_list_zipWith_aux_evp]
end Oracle.Single.Code
end list_zipWith

section list_range
namespace Oracle.Single.Code
def c_list_range :=
  let prev_list := right.comp right
  let i := (left.comp right)
  (prec
  (c_list_nil)
  (c_list_concat.comp₂ prev_list i)).comp₂ zero c_id
@[cp] theorem c_list_range_prim : code_prim c_list_range := by unfold c_list_range; apply_cp
@[simp, evp_simps] theorem c_list_range_evp {O : ℕ → ℕ} {n} :
    evalp O c_list_range n = l2n (range n) := by
  simp only [c_list_range, evp_simps]
  simp only [unpaired, encode_list_nil, unpair_pair]
  induction n with
  | zero => simp
  | succ n ih =>
    simpa [-encode_list_cons, -encode_list_nil, ih] using Eq.symm range_succ
@[simp, ev_simps] theorem c_list_range_ev {O : ℕ → ℕ} {n} :
  eval O c_list_range n = l2n (range n) := by simp [← evalp_eq_eval c_list_range_prim]
end Oracle.Single.Code
end list_range

section list_replicate
namespace Oracle.Single.Code
def c_list_replicate :=
  let prev_list := right.comp right
  let x := left
  (prec
  (c_list_nil)
  (c_list_concat.comp₂ prev_list x)).comp c_flip
@[cp] theorem c_list_replicate_prim : code_prim c_list_replicate := by
  unfold c_list_replicate; apply_cp
@[simp, evp_simps] theorem c_list_replicate_evp {O : ℕ → ℕ} {n x} :
    evalp O c_list_replicate ⟪n,x⟫ = l2n (replicate n x) := by
  simp only [c_list_replicate, evp_simps]
  simp only [unpaired, encode_list_nil, unpair_pair]
  induction n with
  | zero => simp
  | succ n ih =>
    simpa [-encode_list_cons, -encode_list_nil, ih] using Eq.symm replicate_succ'
@[simp, ev_simps] theorem c_list_replicate_ev {O : ℕ → ℕ} {n x} :
    eval O c_list_replicate ⟪n,x⟫ = l2n (replicate n x) := by
  simp [← evalp_eq_eval c_list_replicate_prim]
end Oracle.Single.Code
end list_replicate

section list_map'
namespace Oracle.Single.Code
/--
`evalp O (c_list_map' c) ⟪lN, aux⟫ = ((n2l lN).map (fun ele => evalp O c (Nat.pair ele aux)))`
-/
def c_list_map' (c : Code) :=
  let lN := left
  let aux := right
  (c_list_map c).comp
  ((c_list_zipWith c_id).comp₂ lN (c_list_replicate.comp₂ (c_list_length.comp lN) aux))
@[cp] theorem c_list_map'_prim {c : Code} (hc : code_prim c) : code_prim (c_list_map' c) := by
  unfold c_list_map'; apply_cp
@[simp, evp_simps] theorem c_list_map'_evp {O : ℕ → ℕ} {c lN aux} :
    evalp O (c_list_map' c) ⟪lN, aux⟫ =
    ((n2l lN).map (fun ele => evalp O c (Nat.pair ele aux))) := by
  simp only [c_list_map', evp_simps]
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
`evalp O (c_list_foldr_param c) ⟪param, init, lN⟫ =
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
def c_list_foldr_param_aux (c : Code) :=
  let param := left
  let init := left.comp right
  let lN := right.comp right
  (c_list_foldr <|
  (pair (left.comp left) <| c.comp₃ (left.comp left) (right.comp left) (right.comp right))).comp₂
  (pair param init)
  ((c_list_zipWith c_id).comp₂ (c_list_replicate.comp₂ (c_list_length.comp lN) (param)) lN)
def c_list_foldr_param (c : Code) := right.comp (c_list_foldr_param_aux c)
@[cp] theorem c_list_foldr_param_aux_prim {c : Code} (hc : code_prim c) :
  code_prim (c_list_foldr_param_aux c) := by unfold c_list_foldr_param_aux; apply_cp 60
@[cp] theorem c_list_foldr_param_prim {c : Code} (hc : code_prim c) :
    code_prim (c_list_foldr_param c) := by
  rewrite [c_list_foldr_param]
  apply_cp
lemma c_list_foldr_param_aux_2 {f : ℕ → ℕ} {param init lst} :
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
@[simp, evp_simps] theorem c_list_foldr_param_aux_evp {O : ℕ → ℕ} {c param init lN} :
    evalp O (c_list_foldr_param_aux c) ⟪param, init, lN⟫ =
    Nat.pair param
    (
      foldr
      (fun a b => evalp O c ⟪param, a, b⟫)
      init
      lN.n2l
    ) := by
  simpa [c_list_foldr_param_aux, evp_simps] using c_list_foldr_param_aux_2
@[simp, evp_simps] theorem c_list_foldr_param_evp {O : ℕ → ℕ} {c param init lN} :
  evalp O (c_list_foldr_param c) ⟪param, init, lN⟫ =
  foldr
    (fun a b => evalp O c ⟪param, a, b⟫)
    init
    lN.n2l := by
    simp [c_list_foldr_param]
end Oracle.Single.Code
end list_foldr_param
