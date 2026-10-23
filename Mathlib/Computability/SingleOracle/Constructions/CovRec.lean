/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
module

public import Mathlib.Computability.SingleOracle.Constructions.List
public import Mathlib.Data.List.GetD -- for getI_eq_getElem

/-!
# CovRec.lean

This file defines constructs to work with course-of-values recursion
(using only primitive recursive codes).

Course-of-values recursion allows a recursive definition of f(x) in terms of f(0), f(1), ... f(x-1),
unlike primitive recursion which only exposes f(x-1).

The main definition is `cCovRec`, which has a similar interface to `prec`, but exposes the list of
all previous computations f(0), f(1), ... f(x-1) instead of f(x-1).

We also define several theorems `cCovRec_evp_*`, which simplify interactions with `cCovRec`.

This file also contains two examples using course-of-values recursion; division and an example on
parsing codes.

## Notation/quirks

 - Where `x`, `y` are naturals, `⟪x, y⟫ = Nat.pair x y`.

 ## Main declarations

- `cCovRec`: Code implementing course-of-values recursion, with a similar interface to `prec`.
- `cDiv`: Code implementing `Nat.div`.
- `cReplaceOracle`: Code that parses codes.

-/

@[expose] public section

open Oracle.Single.Code
open List Nat

section efl_prec
namespace Oracle.Single.Code
/--
A specialised code used as an auxiliary for `cCovRec`.
Given an input of the form ``⟪x, i, list⟫``, the code `cEflPrec c` computes
`list.append (eval c input)`.
(The form above is what you would expect in the inductive case in primitive recursion.)
-/
def cEflPrec := fun c ↦ cListConcat.comp (pair (cId.comp (right.comp right)) c)
@[cp] theorem cEflPrec_prim {c} (h : IsPrim c) : IsPrim <| cEflPrec c := by
  unfold cEflPrec; apply_cp
@[simp, evp_simps] theorem cEflPrec_evp {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    evalp O (cEflPrec c) x = l2n ((n2l x.right.right).concat (evalp O c x)) := by
  simp [cEflPrec]
end Oracle.Single.Code
end efl_prec

-- course of values recursion.
section cov_rec
namespace Oracle.Single.Code
/--
Code for course-of-values recursion.

base case:
  `eval (cCovRec cf cg) (x, 0)` = `[eval cf x]` (list with one element)

inductive case:
  let `l` be the list of previous values, from `j=0` to `i`.
  Then `eval (cCovRec cf cg) (x, i+1) = l.append <| eval cg (x, i, l)`.
-/
def cCovRec (cf cg : Code) :=
  prec
  (cListConcat.comp₂ cListNil cf)
  (cEflPrec cg)
@[cp] theorem cCovRec_prim {c1 c2} (hc1 : IsPrim c1) (hc2 : IsPrim c2) :
    IsPrim (cCovRec c1 c2) := by
  unfold cCovRec; apply_cp
@[evp_simps] theorem cCovRec_evp_size_positive {O cf cg x i} :
    0 < (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫)).length := by
  unfold cCovRec
  induction i <;> simp
@[simp, evp_simps] theorem cCovRec_evp_size {O cf cg x i} :
    (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫)).length = i + 1 := by
  unfold cCovRec
  simp [evalp]
  induction i
  · simp
  · simpa
theorem cCovRec_evp_indt {O cf cg x i} :
    evalp O (cCovRec cf cg) ⟪x, i+1⟫ =
    (l2n <| List.concat
    (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫))
    (evalp O cg ⟪x, i, evalp O (cCovRec cf cg) ⟪x,i⟫⟫)) := by
  rw [cCovRec]
  rw [evalp]
  simp
@[simp, evp_simps] theorem cCovRec_evp_base_I {O cf cg x} :
    getLastI (n2l (evalp O (cCovRec cf cg) ⟪x,0⟫)) = evalp O cf x := by
  unfold cCovRec
  simp [getLastI]
@[evp_simps] theorem cCovRec_evp_get0 {O cf cg x i} :
    (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫))[0] = evalp O cf x := by
  induction i with
  | zero => unfold cCovRec; simp [evalp]
  | succ i h => simp [cCovRec_evp_indt, h]
@[evp_simps] theorem cCovRec_evp_get0_I {O cf cg x i} :
    getI (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫)) 0 = evalp O cf x := by
  induction i with
  | zero => unfold cCovRec; simp [evalp, getI]
  | succ i h => simp [cCovRec_evp_indt]; simp [getI, cCovRec_evp_get0]
@[simp, evp_simps] theorem cCovRec_indt_last {O cf cg x i} :
    getLastI (evalp O (cCovRec cf cg) ⟪x, i+1⟫) =
    evalp O cg ⟪x, i, evalp O (cCovRec cf cg) ⟪x,i⟫⟫ := by
  rw [cCovRec_evp_indt]
  simp
theorem cCovRec_evp_last {O cf cg x i} :
    getLastI (evalp O (cCovRec cf cg) ⟪x,i⟫) =
    (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫))[i] := by
  rw [getLastI_eq_getLast?_getD]
  rw [getLast?_eq_getElem?]
  simp [cCovRec_evp_size]
theorem cCovRec_evp_last_I {O cf cg x i} :
    getLastI (evalp O (cCovRec cf cg) ⟪x,i⟫) =
    getI (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫)) i := by
  rw [cCovRec_evp_last]
  exact (getI_eq_getElem _ _).symm
theorem cCovRec_evp_get_aux {O cf cg x j i} (h : j ≤ i) :
    (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫))[j]'(by simp [cCovRec_evp_size]; omega) =
    (n2l (evalp O (cCovRec cf cg) ⟪x, i+1⟫))[j]'(by simp [cCovRec_evp_size]; omega) := by
  simpa [cCovRec_evp_indt] using getElem_append_left' _ _
theorem cCovRec_evp_get_aux_I {O cf cg x j i} (h : j ≤ i) :
    getI (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫)) j =
    getI (n2l (evalp O (cCovRec cf cg) ⟪x, i+1⟫)) j := by
  simp [cCovRec_evp_indt]
  have bounds1: j<(n2l (evalp O (cCovRec cf cg) ⟪x,i⟫)).length := by
    simp [lt_add_one_of_le h]
  have bounds2:
      j < ((n2l (evalp O (cf.cCovRec cg) ⟪x,i⟫) ++
      [evalp O cg ⟪x, i, evalp O (cCovRec cf cg) ⟪x,i⟫⟫])).length := by
    simp; omega
  simp [getI]
  grind

@[simp, evp_simps] theorem cCovRec_evp_get {O cf cg x j i} (h : j ≤ i) :
    (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫))[j]'(by simp [cCovRec_evp_size]; omega) =
    getLastI (evalp O (cCovRec cf cg) ⟪x, j⟫) := by
  rw [cCovRec_evp_last]
  induction i with
  | zero => simp only [show j=0 from eq_zero_of_le_zero h]
  | succ n ih =>
    cases le_or_eq_of_le_succ h with
    | inr h1 => simp only [h1]
    | inl h1 =>
      rw [← ih h1]
      rw [← cCovRec_evp_get_aux]
      exact h1
@[simp, evp_simps] theorem cCovRec_evp_getI {O cf cg x j i} (h : j ≤ i) :
    getI (n2l (evalp O (cCovRec cf cg) ⟪x,i⟫)) j =
    getLastI (evalp O (cCovRec cf cg) ⟪x, j⟫) := by
  rw [← @cCovRec_evp_get O cf cg x j i h]
  exact getI_eq_getElem _ _

end Oracle.Single.Code
end cov_rec

section div
def divFlipAux : ℕ → ℕ → ℕ :=
  fun d n => if d = 0 then 0 else (if n<d then 0 else (divFlipAux d (n-d)) + 1)
open Nat in
theorem divFlipAux_eq_div_flip : divFlipAux = (flip ((· / ·) : ℕ → ℕ → ℕ)) := by
  funext d n
  simp only [flip]
  cases d
  · simp [divFlipAux]
  · expose_names
    induction n using Nat.strong_induction_on with
    | h n h =>
    unfold divFlipAux
    cases Nat.lt_or_ge (n) (n_1+1) with
    | inl h2 => simpa [h2] using Eq.symm (div_eq_of_lt h2)
    | inr h2 =>
      rw [h]
      · have h3 : (n-(n_1+1)*1)/(n_1+1) = n/(n_1+1)-1 := sub_mul_div n (n_1 + 1) 1
        have h4 : 0 < n/(n_1+1) := Nat.div_pos_iff.mpr ⟨zero_lt_succ n_1, h2⟩
        have h5 : (n-(n_1+1)*1)/(n_1+1) +1 = n/(n_1+1) :=
          Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add h).mp) h4 (_root_.id (Eq.symm h3)))
        simpa [Nat.not_lt.mpr h2] using h5
      simpa using zero_lt_of_lt h2

namespace Oracle.Single.Code
/-
This example serves as a blueprint for using `cCovRec` in proofs.

We construct division, using this recursive form:
  `n/d= if d=0 then 0 else (n-d)/d+1.`

We define a "flipped" version `cDivFlipAux`, where the divisor `d` comes first and dividend `n`
second. This is because in the interface for `cCovRec`, the second argument is the "inductive"
one. (In our recursive form of division above, the recursive call is made with respect to the
dividend and the divisor stays the same.)

For this specific example, one can bypass defining the auxiliary function `cDivFlipAux` and
write a shorter proof; see https://github.com/hyeoniuwu/CiL/blob/99fd356e7835d1856fb73306df7828f96b42a85c/Computability/Constructions.lean#L758.

However, I've written the "longer" way, which is more efficient. For more complex constructions,
this longer way becomes necessary.

The reason for explicitly defining the auxiliary function (the function without c_l_get_last.comp
attached) is to be able to rewrite the "unfolded" definitions in the recursive case with the shorter
function name.

The let-bindings allow for more organised/performant proofs, and also helps readability in the
construction. This is especially true for more complex `cCovRec` constructions, such as
`cReplaceOracleAux` later.

All let bindings are used in the inductive case of course-of-values recursion.

Recall that the interface for the inductive case is designed like `prec`; in
`cCovRec cf cg ⟪x, i+1⟫`, the input that the code `cg` will get looks like:
`⟪x, i, evalp O (cCovRec cf cg) ⟪x,i⟫⟫`.

That expression can become very large, and is repeated throughout the goal. So, we
we will rewrite all instances of that recursive input to `cri`.

-/
/-- `evalp O cDivFlip ⟪d, n⟫ = n/d`. -/
def cDivFlipAux :=
  let dividend := succ.comp <| left.comp right
  let divisor := left
  let list_of_prev_values := right.comp right
  cCovRec
  -- base case: if dividend is 0, return 0
  (cConst 0) <|
  -- recursive case:
  cIfz.comp₂ divisor <| -- in general, test if the divisor is zero
  pair (cConst 0) <| -- if so, return 0
  -- if dividend < divisor, return 0
  cIfLtTe.comp₄ dividend divisor (cConst 0) <|
  -- else return (dividend-divisor)/divisor+1
  (succ.comp (cListGetI.comp₂ list_of_prev_values (cSub.comp₂ dividend divisor)))
def cDivFlip := cListGetLastI.comp cDivFlipAux
def cDiv := cDivFlip.comp (cFlip)

theorem cDivFlip_evp_aux_aux {O d n} :
    evalp O cDivFlip ⟪d+1, n+1⟫ =
    if n<d then 0 else evalp O cDivFlip ⟪d+1, n-d⟫ + 1 := by
  rw (config := {occs := .pos [1]}) [cDivFlip]
  unfold cDivFlipAux
  lift_lets; extract_lets; expose_names
  -- we will simplify the input in the recursive case to `cri`.
  let (eq := hinp) inp := evalp O cDivFlipAux ⟪d+1, n⟫
  unfold cDivFlipAux at hinp; lift_lets at hinp
  let (eq := hcri) cri := ⟪d+1, n, inp⟫
  -- show that the code let-bindings correspond to our let-bindings
  have hdivisor : evalp O divisor cri = d+1 := by simp [hcri, divisor]
  have hdividend : evalp O dividend cri = n+1 := by simp [hcri, dividend]
  have hlist_of_prev_values :
      evalp O list_of_prev_values cri = evalp O cDivFlipAux ⟪d+1, n⟫ := by
    simp [hcri, inp, list_of_prev_values]
  -- simplify unfolding covrec, rewrite with hcri then simplify
  -- with the correspondence theorems above
  simp only [cCovRec_indt_last, evp_simps]
  simp only [← hinp, ← hcri]
  simp [hdivisor, hdividend, hlist_of_prev_values, cDivFlip, cDivFlipAux]

theorem cDivFlip_evp_aux {O : ℕ → ℕ} : evalp O cDivFlip = unpaired2 divFlipAux := by
  funext dn
  let d := dn.left
  let n := dn.right
  have dn_eq : dn = Nat.pair d n := Eq.symm (pair_unpair dn)
  rw [dn_eq]
  induction n using Nat.strong_induction_on with
  | h n ih =>
  -- induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero => simp [divFlipAux_eq_div_flip,flip, cDivFlip, cDivFlipAux, evalp]
  | succ n' =>
    cases hd : d with
    | zero => simp [divFlipAux_eq_div_flip,flip,cDivFlip, cDivFlipAux, evalp]
    | succ d' =>
      rw [cDivFlip_evp_aux_aux]
      unfold divFlipAux;
      rw [hd] at ih
      simp [ih (n'-d') (sub_lt_succ n' d')]

@[simp, evp_simps] theorem cDivFlip_evp {O : ℕ → ℕ} :
    evalp O cDivFlip = unpaired2 (flip ((· / ·) : ℕ → ℕ → ℕ)) := by
  rw [cDivFlip_evp_aux]
  simp [divFlipAux_eq_div_flip]
@[simp, evp_simps] theorem cDiv_evp {O a b} : evalp O cDiv ⟪a,b⟫ = a/b := by
  unfold cDiv
  simp [evalp]
  simp [flip]

@[cp] theorem cDiv_prim : IsPrim cDiv := by
  unfold cDiv;
  unfold cDivFlip;
  unfold cDivFlipAux;
  apply_cp 40

@[simp, ev_simps] theorem cDiv_ev {O a b} : eval O cDiv ⟪a,b⟫ = a/b := by
  rw [← evalp_eq_eval cDiv_prim];
  simp only [PFun.coe_val, cDiv_evp, Part.coe_some]
  exact Eq.symm (Part.some_div_some a b)
end Oracle.Single.Code
end div

section mod
namespace Oracle.Single.Code
def cMod := cSub.comp₂ left (cMul.comp₂ right cDiv)
@[cp] theorem cMod_prim : IsPrim cMod := by unfold cMod; apply_cp
@[simp, evp_simps] theorem cMod_evp {O : ℕ → ℕ} :
    evalp O cMod = unpaired2 ((· % ·) : ℕ → ℕ → ℕ) := by
  simp only [cMod, comp₂_evp, evalp, cMul_evp, cSub_evp]
  funext mn
  let m := mn.left
  let n := mn.right
  have mn_eq : mn = ⟪m, n⟫ := Eq.symm (pair_unpair mn)
  rw [mn_eq]
  apply Nat.sub_eq_of_eq_add
  simp [add_comm (m % n), Nat.div_add_mod]

@[simp, ev_simps] theorem cMod_ev {O : ℕ → ℕ} :
    eval O cMod = unpaired2 ((· % ·) : ℕ → ℕ → ℕ) := by
  rw [← evalp_eq_eval cMod_prim]; simp only [cMod_evp]
end Oracle.Single.Code
end mod

section div2
namespace Oracle.Single.Code
def cDiv2 := cDiv.comp₂ cId (cConst 2)
@[cp] theorem cDiv2_prim : IsPrim cDiv2 := by unfold cDiv2; apply_cp
@[simp, evp_simps] theorem cDiv2_evp {O : ℕ → ℕ} : evalp O cDiv2 = div2 := by
  funext x; simpa [cDiv2, evp_simps] using Eq.symm (div2_val x)
@[simp, ev_simps] theorem cDiv2_ev {O : ℕ → ℕ} : eval O cDiv2 = div2 := by
  simp [← evalp_eq_eval cDiv2_prim]
end Oracle.Single.Code
end div2

section mod2
namespace Oracle.Single.Code
def cMod2 := cMod.comp₂ cId (cConst 2)
@[cp] theorem cMod2_prim : IsPrim cMod2 := by unfold cMod2; apply_cp
@[simp, evp_simps] theorem cMod2_evp {O : ℕ → ℕ} : evalp O cMod2 = fun x ↦ x%2 := by simp [cMod2]
@[simp, ev_simps] theorem cMod2_ev {O : ℕ → ℕ} : eval O cMod2 = (fun x : ℕ ↦ x%2) := by
  simp [← evalp_eq_eval cMod2_prim]
end Oracle.Single.Code
end mod2

section replaceOracle
namespace Oracle.Single.Code
/-! ### parsing codes with cCovRec
#### Structure of section
  · `cReplaceOracleAux` : main body of construction, using cCovRec
  · `cReplaceOracle` : to see why this is defined separately, see comments on `cDivFlipAux`
  · `cReplaceOracle_prim` : show `cReplaceOracle` is primrec
  · `cReplaceOracle_evp_aux` : shows that the code has correct behaviour on the non-inductive
    codes i.e `zero`, `succ`, `left`, `right` and `oracle`. This is much easier than e.g. `prec`,
    which required inductive reasoning on previous codes.
  · `bounds*` : the `cCovRec` construction accesses previous
    computations by looking that up on a list. to know that the lookup succeeded (and thus simplify
    using the `cCovRec_evp*` theorems), we need to know that the index is smaller than the current
    input. These bounds theorem show exactly that.
  · `cReplaceOracle_evp_aux_nMod4` : shows behaviour of the codes on the inductive codes i.e
    `pair`, `comp`, `prec` and `rfind'`. One thing to note is that this theorem does not show
    correctness by itself; it only demonstrates that evaluating `cReplaceOracle` on an inductive
    code, can be simplified to evaluating `cReplaceOracle` on smaller codes. To show correctness,
    one would need to use strong induction on codes, which we do next.
  · `cReplaceOracle_evp` : shows that the code has correct behaviour on evaluation, using strong
    induction. The proof requires basically no interaction with `evalp`, as that has all been done
    in the previous theorems.
-/

/--
Given a code `c`, `replaceOracle o c` replaces all instances of the code `oracle` with the code
`o` instead.

Examples:
replaceOracle c oracle = c
replaceOracle c succ = succ
replaceOracle c (prec zero oracle) = prec zero c
-/
def replaceOracle (o : Code) : Code → Code
| Code.zero        => Code.zero
| Code.succ        => Code.succ
| Code.left        => Code.left
| Code.right       => Code.right
| Code.oracle      => o
| Code.pair cf cg  => Code.pair (replaceOracle o cf) (replaceOracle o cg)
| Code.comp cf cg  => Code.comp (replaceOracle o cf) (replaceOracle o cg)
| Code.prec cf cg  => Code.prec (replaceOracle o cf) (replaceOracle o cg)
| Code.rfind' cf   => Code.rfind' (replaceOracle o cf)

/--
`eval cReplaceOracle (o,code) = replaceOracle o code`.
-/
def cReplaceOracleAux :=
  let o              := left
  let input_to_decode := succ.comp (left.comp right)
  let comp_hist      := right.comp right
  let n              := cSub.comp₂ input_to_decode (cConst 5)
  let m              := cDiv2.comp <| cDiv2.comp n
  let lookup (c')    := cListGetI.comp₂ comp_hist c'
  let ml             := lookup (left.comp m)
  let mr             := lookup (right.comp m)
  let mp             := lookup m
  let nMod4          := cMod.comp₂ n (cConst 4)
  let pair_code   :=
    cAdd.comp₂ (             cMul2.comp <|              cMul2.comp (pair ml mr)) (cConst 5)
  let comp_code   :=
    cAdd.comp₂ (succ.comp <| cMul2.comp <|              cMul2.comp (pair ml mr)) (cConst 5)
  let prec_code   :=
    cAdd.comp₂ (             cMul2.comp <| succ.comp <| cMul2.comp (pair ml mr)) (cConst 5)
  let rfind'_code :=
    cAdd.comp₂ (succ.comp <| cMul2.comp <| succ.comp <| cMul2.comp mp          ) (cConst 5)
  cCovRec
  -- base case, when code = 0.
  (cConst 0) <|
  -- recursive case:
  cIfEqTe.comp₄ input_to_decode (cConst 1) (cConst 1) <|
  cIfEqTe.comp₄ input_to_decode (cConst 2) (cConst 2) <|
  cIfEqTe.comp₄ input_to_decode (cConst 3) (cConst 3) <|
  cIfEqTe.comp₄ input_to_decode (cConst 4) o           <|
  cIfEqTe.comp₄ nMod4           (cConst 0) pair_code   <|
  cIfEqTe.comp₄ nMod4           (cConst 1) comp_code   <|
  cIfEqTe.comp₄ nMod4           (cConst 2) prec_code   <|
                                               rfind'_code

def cReplaceOracle := cListGetLastI.comp cReplaceOracleAux
/-
The most efficient way to show `IsPrim (cReplaceOracle)` is by showing the primitiveness of
each let-binding.

If one were to instead unfold all let-bindings, there are performance penalties.
-/
@[cp] theorem cReplaceOracle_prim : IsPrim (cReplaceOracle) := by
  unfold cReplaceOracle;
  unfold cReplaceOracleAux
  extract_lets;
  expose_names;
  have cp_o : IsPrim o := by apply_cp
  have cp_input_to_decode : IsPrim input_to_decode := by apply_cp
  have cp_comp_hist : IsPrim comp_hist := by apply_cp
  have cp_n : IsPrim n := by apply_cp
  have cp_m : IsPrim m := by apply_cp
  have cp_ml : IsPrim ml := by apply_cp
  have cp_mr : IsPrim mr := by apply_cp
  have cp_mp : IsPrim mp := by apply_cp
  have cp_nMod4 : IsPrim nMod4 := by apply_cp
  have cp_pair_code : IsPrim pair_code := by apply_cp
  have cp_comp_code : IsPrim comp_code := by apply_cp
  have cp_prec_code : IsPrim prec_code := by apply_cp
  have cp_rfind'_code : IsPrim rfind'_code := by apply_cp
  apply_cp 40

theorem cReplaceOracle_evp_aux {O o x} (hx : x ≤ 4) :
    evalp O (cReplaceOracle) ⟪o, x⟫ = c2n (replaceOracle (n2c o) (n2c x)) := by
  unfold cReplaceOracle
  unfold cReplaceOracleAux
  lift_lets; extract_lets; expose_names
  have hinput_to_decode {x hist} : evalp O input_to_decode ⟪o, x, hist⟫ = x+1 := by
    simp [input_to_decode]
  have ho {x hist} : evalp O o_1 ⟪o, x, hist⟫ = o := by simp [o_1]
  match x with
  | 0 => simp []; simp only [replaceOracle, replaceOracle, n2c, c2n]
  | 1 => simp [hinput_to_decode, ho]; simp only [replaceOracle, replaceOracle, n2c, c2n]
  | 2 => simp [hinput_to_decode, ho]; simp only [replaceOracle, replaceOracle, n2c, c2n]
  | 3 => simp [hinput_to_decode, ho]; simp only [replaceOracle, replaceOracle, n2c, c2n]
  | 4 => simp [hinput_to_decode, ho]; simp only [replaceOracle, replaceOracle, n2c, c2n_n2c]
  | n+5 => simp at hx

private lemma bounds1 {n} : (n/2/2).left ≤ n+4 :=
  le_add_right_of_le
    (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
private lemma bounds2 {n} : (n/2/2).right ≤ n+4 :=
  le_add_right_of_le
    (Nat.le_trans (unpair_right_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
private lemma bounds3 {n} : (n/2/2) ≤ n+4 :=
  le_add_right_of_le (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))

/-
Structure of proof:
We lift the let-bindings in the theorem statement and within the definition of `cReplaceOracle`.

The let bindings in the theorem statement are named the same as their corresponding let-bindings in
`cReplaceOracle`.

For example we have
`let m := n.div2.div2` in the theorem statement, and
`let m := cDiv2.comp <| cDiv2.comp n` in the definition of `cReplaceOracleAux`.

In the process of lifting, the names bindings from the code are attached with the suffix "_1".

We show that these bindings from the code and from the theorem statement are equivalent:
`have hm : evalp O m_1 ⟪o, n+4, inp⟫ = m := by simp [m_1, hn, m]`

The theorem then follows from using these equivalence results in simplification.
-/
theorem cReplaceOracle_evp_aux_nMod4 {O o n} :
    evalp O (cReplaceOracle) ⟪o, ((n+4)+1)⟫ =
    let m := n.div2.div2
    let ml := evalp O (cReplaceOracle) ⟪o, m.left⟫
    let mr := evalp O (cReplaceOracle) ⟪o, m.right⟫
    let mp := evalp O (cReplaceOracle) ⟪o, m  ⟫
        if n%4=0 then 2*(2*⟪ml, mr⟫  )     + 5
    else if n%4=1 then 2*(2*⟪ml, mr⟫  ) +1  + 5
    else if n%4=2 then 2*(2*⟪ml, mr⟫ +1 )   + 5
    else if n%4=3 then 2*(2*(mp)  +1)+1     + 5
    else 0 := by
  lift_lets; extract_lets; expose_names
  unfold cReplaceOracle;
  unfold cReplaceOracleAux
  lift_lets; extract_lets; expose_names
  let (eq := hinp) inp := evalp O cReplaceOracleAux ⟪o, n+4⟫
  unfold cReplaceOracleAux at hinp; lift_lets at hinp
  -- show that the code let-bindings correspond to our let-bindings
  have hinput_to_decode : evalp O input_to_decode ⟪o, n+4, inp⟫ = n+5 := by simp [input_to_decode]
  have hn : evalp O n_1 ⟪o, n+4, inp⟫ = n := by simp [n_1, hinput_to_decode]
  have hnMod4 : evalp O nMod4 ⟪o, n+4, inp⟫ = n%4 := by simp [nMod4, hn]
  have hm : evalp O m_1 ⟪o, n+4, inp⟫ = m := by simp [m_1, hn, m]
  have hlookup {c'} (hcs'': evalp O c' ⟪o, n+4, inp⟫ ≤ n+4) :
      evalp O (lookup c') ⟪o, n+4, inp⟫ =
      let c'' := evalp O c' ⟪o, n+4, inp⟫
      evalp O (cReplaceOracle) ⟪o, c''⟫ := by
    lift_lets; extract_lets; expose_names
    have aux2 : evalp O c' ⟪o, n+4, inp⟫ = c'' := by simp [c'']
    simp only [lookup, evp_simps]
    simp only [aux2] at hcs'' ⊢
    simp [comp_hist, inp, cReplaceOracle, cReplaceOracleAux, hcs'']
  have hml : evalp O ml_1 ⟪o, n+4, inp⟫ = ml := by
    have := @hlookup (left.comp m_1) (by simp [hm, m, div2_val, bounds1])
    simpa [ml_1, this, hm] using by rfl
  have hmr : evalp O mr_1 ⟪o, n+4, inp⟫ = mr := by
    have := @hlookup (right.comp m_1) (by simp [hm, m, div2_val, bounds2])
    simpa [mr_1, this, hm] using by rfl
  have hmp : evalp O mp_1 ⟪o, n+4, inp⟫ = mp := by
    have := @hlookup m_1 (by simp [hm, m, div2_val, bounds3])
    simpa [mp_1, this, hm] using by rfl
  have hpair_code   : evalp O pair_code   ⟪o, n+4, inp⟫ = 2*(2*⟪ml, mr⟫  )  +5 := by
    simp [pair_code, hml, hmr, mul_comm]
  have hcomp_code   : evalp O comp_code   ⟪o, n+4, inp⟫ = 2*(2*⟪ml, mr⟫  )+1+5 := by
    simp [comp_code, hml, hmr, mul_comm]
  have hprec_code   : evalp O prec_code   ⟪o, n+4, inp⟫ = 2*(2*⟪ml, mr⟫+1)  +5 := by
    simp [prec_code, hml, hmr, mul_comm]
  have hrfind'_code : evalp O rfind'_code ⟪o, n+4, inp⟫ = 2*(2*(mp)    +1)+1+5 := by
    simp [rfind'_code, hmp, mul_comm]
  -- simplify unfolding covrec, rewrite with hinp then simplify
  -- with the correspondence theorems above
  simp only [evp_simps, ← hinp, hinput_to_decode, hnMod4]
  match h : n%4 with
  | 0 => simp [hpair_code]
  | 1 => simp [hcomp_code]
  | 2 => simp [hprec_code]
  | 3 => simp [hrfind'_code]
  | x+4 =>
    have contrad : n%4<4 := by
      apply Nat.mod_lt
      decide
    rw [h] at contrad
    rw [show x.succ.succ.succ.succ=x+4 from rfl] at contrad
    simp at contrad

lemma codes_aux_aux_0 {n} (hno : n.bodd = false) :  2 * n.div2 = n := by
  have h0 := bodd_add_div2 n
  simpa [hno] using h0
lemma codes_aux_aux_1 {n} (hno : n.bodd = true) :  2 * n.div2 +1 = n := by
  have h0 := bodd_add_div2 n
  simp only [hno, Bool.toNat_true] at h0
  rw (config := {occs := .pos [2]}) [←h0]
  exact Nat.add_comm (2 * n.div2) 1
lemma codes_aux_0 {n} (hno : n.bodd = false) (hn2o : n.div2.bodd = false) :
    2 * (2 * n.div2.div2) = n := by
  rw [codes_aux_aux_0 hn2o]
  rw [codes_aux_aux_0 hno]
lemma codes_aux_1 {n} (hno : n.bodd = true) (hn2o : n.div2.bodd = false) :
    2 * (2 * n.div2.div2 ) + 1 = n := by
  rw [codes_aux_aux_0 hn2o]
  rw [codes_aux_aux_1 hno]
lemma codes_aux_2 {n} (hno : n.bodd = false) (hn2o : n.div2.bodd = true) :
    2 * (2 * n.div2.div2 + 1) = n := by
  rw [codes_aux_aux_1 hn2o]
  rw [codes_aux_aux_0 hno]
lemma codes_aux_3 {n} (hno : n.bodd = true) (hn2o : n.div2.bodd = true) :
    2 * (2 * n.div2.div2 + 1) + 1 = n := by
  rw [codes_aux_aux_1 hn2o]
  rw [codes_aux_aux_1 hno]

theorem nMod4_eq_0 {n} (hno : n.bodd = false) (hn2o : n.div2.bodd = false) : n%4=0 := by
  rw [←codes_aux_0 hno hn2o]; omega
theorem nMod4_eq_1 {n} (hno : n.bodd = true) (hn2o : n.div2.bodd = false) : n%4=1 := by
  rw [←codes_aux_1 hno hn2o]; omega
theorem nMod4_eq_2 {n} (hno : n.bodd = false) (hn2o : n.div2.bodd = true) : n%4=2 := by
  rw [←codes_aux_2 hno hn2o]; omega
theorem nMod4_eq_3 {n} (hno : n.bodd = true) (hn2o : n.div2.bodd = true) : n%4=3 := by
  rw [←codes_aux_3 hno hn2o]; omega

@[simp, evp_simps] theorem cReplaceOracle_evp {O : ℕ → ℕ} :
    evalp O (cReplaceOracle) = fun x ↦c2n (replaceOracle (n2c x.left) (n2c x.right)) := by
  funext oc
  let o := oc.left
  let c := oc.right
  have oc_eq : oc = Nat.pair o c := Eq.symm (pair_unpair oc)
  rw [oc_eq]
  simp only [pair_l, pair_r] -- simplify the rhs
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    match c with
    | 0 => apply cReplaceOracle_evp_aux; decide
    | 1 => apply cReplaceOracle_evp_aux; decide
    | 2 => apply cReplaceOracle_evp_aux; decide
    | 3 => apply cReplaceOracle_evp_aux; decide
    | 4 => apply cReplaceOracle_evp_aux; decide
    | n + 5 =>
      let m := n.div2.div2
      have hm : m < n + 5 := by
        simp only [m, Nat.div2_val]
        exact lt_of_le_of_lt
          (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
      have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
      have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
      rw [show n+5=(n+4)+1 from rfl]
      cases hno : n.bodd with
      | false => cases hn2o : n.div2.bodd with
        -- pair
        | false =>
          have h0: n%4=0 := nMod4_eq_0 hno hn2o
          simp only [replaceOracle, replaceOracle, n2c, c2n, hno, hn2o] -- simplify the rhs
          -- rw [cReplaceOracle_evp_aux_nMod4_0 h0]
          rw [cReplaceOracle_evp_aux_nMod4]
          simp? [h0] says
            simp only [h0, ↓reduceIte, unpair1_to_l, unpair2_to_r, Nat.add_right_cancel_iff,
              mul_eq_mul_left_iff, pair_eq_pair, OfNat.ofNat_ne_zero, or_false]
          constructor
          · rw [ih m.left _m1];
          · rw [ih m.right _m2];
        -- prec
        | true =>
          have h0: n%4=2 := nMod4_eq_2 hno hn2o
          simp only [replaceOracle, replaceOracle, n2c, c2n, hno, hn2o] -- simplify the rhs
          rw [cReplaceOracle_evp_aux_nMod4]
          simp? [h0] says
            simp only [h0, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, unpair1_to_l,
              unpair2_to_r, Nat.add_right_cancel_iff, mul_eq_mul_left_iff, pair_eq_pair, or_false]
          constructor
          · rw [ih m.left _m1];
          · rw [ih m.right _m2];
      | true => cases hn2o : n.div2.bodd with
        -- comp
        | false =>
          have h0: n%4=1 := nMod4_eq_1 hno hn2o
          simp only [replaceOracle, replaceOracle, n2c, c2n, hno, hn2o] -- simplify the rhs
          rw [cReplaceOracle_evp_aux_nMod4]
          simp? [h0] says
            simp only [h0, one_ne_zero, ↓reduceIte, unpair1_to_l, unpair2_to_r,
              Nat.add_right_cancel_iff, mul_eq_mul_left_iff, pair_eq_pair, OfNat.ofNat_ne_zero,
              or_false]
          constructor
          · rw [ih m.left _m1];
          · rw [ih m.right _m2];
        -- rfind
        | true =>
          have h0: n%4=3 := nMod4_eq_3 hno hn2o
          simp only [replaceOracle, replaceOracle, n2c, c2n, hno, hn2o] -- simplify the rhs
          rw [cReplaceOracle_evp_aux_nMod4]
          simp? [h0] says
            simp only [h0, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.succ_ne_self,
              Nat.add_right_cancel_iff, mul_eq_mul_left_iff, or_false]
          rw [ih m hm];

@[simp, ev_simps] theorem cReplaceOracle_ev {O : ℕ → ℕ} :
    eval O (cReplaceOracle) = fun x : ℕ ↦ c2n (replaceOracle (n2c x.left) (n2c x.right)) := by
  rw [← evalp_eq_eval cReplaceOracle_prim]; simp only [cReplaceOracle_evp];

@[simp] theorem plift_eq {O o} (ho : IsTotal O o) :
    (@PFun.lift ℕ ℕ fun x ↦ (eval O o x).get (ho x)) = eval O o := by
  ext a b : 1
  simp_all only [PFun.coe_val, Part.some_get]

set_option backward.isDefEq.respectTransparency false in
theorem eval_replace_oracle_prop {O o c} (ho : IsTotal O o) :
    eval O (replaceOracle o c) = eval (fun x ↦ (eval O o x).get (ho x)) c := by
  unfold replaceOracle
  induction c <;> (simp only [eval]; try (unfold replaceOracle; simp_all))
  exact Eq.symm (plift_eq ho)
end Oracle.Single.Code
end replaceOracle
