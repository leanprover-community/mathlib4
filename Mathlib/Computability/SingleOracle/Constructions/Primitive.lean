/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
module

public import Mathlib.Computability.SingleOracle.Basic
public import Mathlib.Data.Nat.Dist

/-!
# Construction of basic primitive recursive functions

This file defines basic primitive recursive codes for basic functions, such as if-else, or
arithmetic functions.

## Structure
Each construction is roughly structured as follows.

Suppose we want to construct a primitive recursive function `f : ℕ → ℕ`.

`def c_f := ...`
  · the code which will implement `f`

`@[cp] theorem c_f_prim : IsPrim c_f := by unfold c_f; apply_cp`
  · theorem which asserts that the code `c_f` is constructed without rfind'.
    the macro `apply_cp` aggressively applies rules tagged with `cp`.
    sometimes for large constructions, one needs to supply an argument to `apply_cp`
    to increase the search depth (e.g. `apply_cp 60`.)

`@[simp, evp_simps] theorem c_f_evp {O : ℕ → ℕ} : evalp O c_f = f := by ...`
  · theorem which asserts that the code `c_f` implements `f` upon evaluation with `evalp`.

`@[simp, ev_simps] theorem c_f_ev {O : ℕ → ℕ} : eval O c_f = f := by`
  `rw [← evalp_eq_eval c_f_prim]; simp only [c_f_evp]`
  · theorem which asserts that the code `c_f` implements `f` upon evaluation with `eval`.
    This follows "for free" once you have `c_f_evp `.

`theorem PrimrecIn.f : PrimrecIn O f := by rw [←c_f_evp]; exact isPrim_prop`
  · theorem asserting that the function `f` is primitive recursive. This again follows
    immediately from `c_f_evp`.

-/

@[expose] public section

open Oracle.Single
open Oracle.Single.Code
open Nat

section comp₂
namespace Oracle.Single.Code
def comp₂ := fun c1 c2 c3 : Code => c1.comp (pair c2 c3)
@[cp] theorem comp₂_prim {c1 c2 c3} (hc1 : IsPrim c1) (hc2 : IsPrim c2) (hc3 : IsPrim c3) :
  IsPrim (comp₂ c1 c2 c3) := by unfold comp₂; apply_cp
@[simp, evp_simps] theorem comp₂_evp {O c1 c2 c3} :
    evalp O (comp₂ c1 c2 c3) = fun x => evalp O c1 ⟪evalp O c2 x, evalp O c3 x⟫ := by
  simp only [comp₂, evp_simps];
set_option backward.isDefEq.respectTransparency false in
@[simp, ev_simps] theorem comp₂_ev {O c1 c2 c3} :
    eval O (comp₂ c1 c2 c3) = fun x => ⟪eval O c2 x, eval O c3 x⟫ >>= (eval O c1) := by
  simp [eval, comp₂, Seq.seq]
end Oracle.Single.Code
end comp₂

section comp₄
namespace Oracle.Single.Code
def comp₄ := fun c1 c2 c3 c4 c5 : Code => c1.comp₂ (pair c2 c3) (pair c4 c5)
@[cp] theorem comp₄_prim {c1 c2 c3 c4 c5}
  (hc1 : IsPrim c1) (hc2 : IsPrim c2)
  (hc3 : IsPrim c3) (hc4 : IsPrim c4) (hc5 : IsPrim c5) :
  IsPrim (comp₄ c1 c2 c3 c4 c5) := by unfold comp₄; apply_cp
@[simp, evp_simps] theorem comp₄_evp {O c1 c2 c3 c4 c5} : evalp O (comp₄ c1 c2 c3 c4 c5) = fun x ↦
  evalp O c1 ⟪evalp O c2 x, evalp O c3 x, evalp O c4 x, evalp O c5 x⟫ := by
  simp only [comp₄, evp_simps]
set_option backward.isDefEq.respectTransparency false in
@[simp, ev_simps] theorem comp₄_ev {O c1 c2 c3 c4 c5} : eval O (comp₄ c1 c2 c3 c4 c5) =
  fun x => ⟪eval O c2 x, eval O c3 x, eval O c4 x, eval O c5 x⟫
   >>= (eval O c1) := by
    simp [comp₄, eval, comp₂, Seq.seq]
end Oracle.Single.Code
end comp₄

section comp₃
namespace Oracle.Single.Code
def comp₃ := fun c1 c2 c3 c4 : Code => c1.comp₂ c2 (pair c3 c4)
@[cp] theorem comp₃_prim {c1 c2 c3 c4}
  (hc1 : IsPrim c1) (hc2 : IsPrim c2) (hc3 : IsPrim c3) (hc4 : IsPrim c4) :
  IsPrim (comp₃ c1 c2 c3 c4) := by unfold comp₃; apply_cp
@[simp, evp_simps] theorem comp₃_evp {c1 c2 c3 c4} {O : ℕ → ℕ} :
    evalp O (comp₃ c1 c2 c3 c4) = fun x ↦
    evalp O c1 ⟪evalp O c2 x, evalp O c3 x, evalp O c4 x⟫ := by
  simp only [comp₃, evp_simps]
set_option backward.isDefEq.respectTransparency false in
@[simp, ev_simps] theorem comp₃_ev {c1 c2 c3 c4} {O : ℕ → ℕ} : eval O (comp₃ c1 c2 c3 c4) = fun x ↦
  ⟪eval O c2 x, eval O c3 x, eval O c4 x⟫ >>= (eval O c1) := by
    simp [comp₃, eval, comp₂, Seq.seq]
end Oracle.Single.Code
end comp₃

section id
namespace Oracle.Single.Code
def cId := left.pair right
@[cp] theorem cId_prim : IsPrim cId := by unfold cId; apply_cp
@[simp, evp_simps] theorem cId_evp {O : ℕ → ℕ} {n} : evalp O cId n = n := by simp [cId, evalp]
theorem cId_evp' {O : ℕ → ℕ} : evalp O cId = id := by funext x; simp [evp_simps]
@[simp, ev_simps] theorem cId_ev {O : ℕ → ℕ} {n} : eval O cId n = n := by simp [cId,eval,Seq.seq]
end Oracle.Single.Code
theorem PrimrecIn.id {O : ℕ → ℕ} : PrimrecIn O id := by
  rw [← cId_evp']; exact isPrim_prop
end id

section const
namespace Oracle.Single.Code
def cConst : ℕ → Code
| 0 => zero
| n+1 => comp succ (cConst n)
@[cp] theorem cConst_prim {n} : IsPrim (cConst n) := by
  induction n
  · unfold cConst; exact IsPrim.zero
  · unfold cConst
    expose_names
    exact IsPrim.comp IsPrim.succ h
@[simp, evp_simps] theorem cConst_evp {O : ℕ → ℕ} : ∀ n m, evalp O (cConst n) m = n
| 0, _ => rfl
| n+1, m => by simp! [cConst_evp n m]
@[simp, ev_simps] theorem cConst_ev {O : ℕ → ℕ} : ∀ n m, eval O (cConst n) m = n
| 0, _ => rfl
| n+1, m => by simp! [cConst_ev n m]
end Oracle.Single.Code
end const


section curry
namespace Oracle.Single.Code
def cCurry (c : Code) (n : ℕ) : Code := comp c (pair (cConst n) cId)
theorem _id_eq_c_id : cId = Code.id := by simp [cId,Code.id]
theorem _const_eq_c_const : cConst = Code.const := by
  funext n;
  unfold cConst
  unfold Code.const
  induction n
  · exact rfl
  · simp only [comp.injEq, true_and]
    unfold cConst
    unfold Code.const
    expose_names
    exact h
theorem _curry_eq_c_curry : cCurry = curry := by
  unfold cCurry
  unfold curry
  rw [_id_eq_c_id]
  rw [_const_eq_c_const]
-- @[simp] theorem cCurry_prim : IsPrim (cCurry c n) := by
@[simp, evp_simps] theorem cCurry_evp {O : ℕ → ℕ} {c n x} :
    evalp O (cCurry c n) x = evalp O c ⟪n, x⟫ := by simp [cCurry, evp_simps]
@[simp, ev_simps] theorem cCurry_ev {O : ℕ → ℕ} {c n x} :
    eval O (cCurry c n) x = eval O c ⟪n, x⟫ := by
  rw [_curry_eq_c_curry]; exact eval_curry c n x
end Oracle.Single.Code
end curry

section sgsg'
/-- The signum function on naturals. -/
@[simp] def Nat.sg := fun x => if x=0 then 0 else 1
/-- Maps zero to 1 and non-zero natural numbers to 0. This is the inverse of `Nat.sg` for
boolean-like computations. -/
@[simp] def Nat.sg' := fun x => if x=0 then 1 else 0
namespace Oracle.Single.Code
def cSg := comp (prec zero (((cConst 1).comp left).comp left)) (pair zero cId)
@[cp] theorem cSg_prim : IsPrim cSg := by unfold cSg; apply_cp
@[simp, evp_simps] theorem cSg_evp {O : ℕ → ℕ} : evalp O cSg = Nat.sg := by
  simp only [cSg, evp_simps]
  funext n; induction n with
  | zero => exact rfl
  | succ n _ => simp
@[simp, ev_simps] theorem cSg_ev {O : ℕ → ℕ} : eval O cSg = Nat.sg := by
  rw [← evalp_eq_eval cSg_prim]; simp only [cSg_evp]
def cSg' := comp (prec (cConst 1) (((zero).comp left).comp left)) (pair zero cId)
@[cp] theorem cSg'_prim : IsPrim cSg' := by unfold cSg'; apply_cp
@[simp, evp_simps] theorem cSg'_evp {O : ℕ → ℕ} : evalp O cSg' = Nat.sg' := by
  simp only [cSg', evp_simps]
  funext n; induction n with
  | zero => exact rfl
  | succ n _ => simp
@[simp, ev_simps] theorem cSg'_ev {O : ℕ → ℕ} : eval O cSg' = Nat.sg' := by
  rw [← evalp_eq_eval cSg'_prim]; simp only [cSg'_evp]
end Oracle.Single.Code
theorem PrimrecIn.sg {O : ℕ → ℕ} : PrimrecIn O Nat.sg := by
  rw [← cSg_evp]; exact isPrim_prop
theorem PrimrecIn.sg' {O : ℕ → ℕ} : PrimrecIn O Nat.sg' := by
  rw [← cSg'_evp]; exact isPrim_prop
@[simp] abbrev cNot := cSg'
end sgsg'

section n2b
namespace Oracle.Single.Code
def cN2b := cSg
@[cp] theorem cN2b_prim : IsPrim cN2b := by unfold cN2b; apply_cp 10
@[simp, evp_simps] theorem cN2b_evp {O : ℕ → ℕ} :
    evalp O cN2b = fun x => if n2b x = true then 1 else 0 := by
  simp only [cN2b, evp_simps]
  unfold Nat.sg; unfold n2b
  aesop
@[simp, ev_simps] theorem cN2b_ev {O : ℕ → ℕ} :
    eval O cN2b = fun x => if n2b x = true then 1 else 0 := by
  rw [← evalp_eq_eval cN2b_prim]; simp only [cN2b_evp]; funext x; aesop
end Oracle.Single.Code
end n2b

section add
namespace Oracle.Single.Code
def cAdd := (prec cId ((succ.comp right).comp right))
@[cp] theorem cAdd_prim : IsPrim cAdd := by unfold cAdd; apply_cp
@[simp, evp_simps] theorem cAdd_evp {O : ℕ → ℕ} : evalp O cAdd = unpaired2 Nat.add := by
  simp only [cAdd, evp_simps]
  funext n;
  simp only [unpaired, unpair1_to_l, succ_eq_add_one, unpair2_to_r, unpaired2, add_eq]
  induction n.right with
  | zero => exact rfl
  | succ n h => exact Nat.add_left_inj.mpr h
@[simp, ev_simps] theorem cAdd_ev {O : ℕ → ℕ} : eval O cAdd = unpaired2 Nat.add := by
  rw [← evalp_eq_eval cAdd_prim]; simp only [cAdd_evp]
end Oracle.Single.Code
end add
section mul
namespace Oracle.Single.Code
def cMul := prec zero (cAdd.comp (pair left (right.comp right)))
@[cp] theorem cMul_prim : IsPrim cMul := by unfold cMul; apply_cp
@[simp, evp_simps] theorem cMul_evp {O : ℕ → ℕ} : evalp O cMul = unpaired2 Nat.mul := by
  simp only [cMul, evp_simps]
  funext n;
  simp only [unpaired, unpaired2, unpair1_to_l, pair_l, pair_r, add_eq, unpair2_to_r, mul_eq]
  induction n.right with
  | zero => exact rfl
  | succ n h =>
    simp only [*, mul_succ];
    (expose_names; exact Nat.add_comm (unpair n_1).1 ((unpair n_1).1 * n))
@[simp, ev_simps] theorem cMul_ev {O : ℕ → ℕ} : eval O cMul = unpaired2 Nat.mul := by
  rw [← evalp_eq_eval cMul_prim]; simp only [cMul_evp]
end Oracle.Single.Code
end mul
section pow
namespace Oracle.Single.Code
def cPow := prec (cConst 1) (cMul.comp (pair (right.comp right) left))
@[cp] theorem cPow_prim : IsPrim cPow := by unfold cPow; apply_cp
@[simp, evp_simps] theorem cPow_evp {O : ℕ → ℕ} : evalp O cPow = unpaired2 Nat.pow := by
  simp only [cPow, evp_simps]
  funext n;
  simp only [unpaired, unpaired2, unpair1_to_l, pair_l, pair_r, unpair2_to_r, mul_eq]
  induction n.right with
  | zero => exact rfl
  | succ n h => simp [*, pow_succ];
@[simp, ev_simps] theorem cPow_ev {O : ℕ → ℕ} : eval O cPow = unpaired2 Nat.pow := by
  rw [← evalp_eq_eval cPow_prim]; simp only [cPow_evp]
end Oracle.Single.Code
end pow

section prec1
namespace Oracle.Single.Code
def cPrec1 (m) (cf : Code) := ((prec (cConst m) (cf.comp right)).comp (zero.pair cId))
@[cp] theorem cPrec1_prim {cf m} (hcf : IsPrim cf) : IsPrim (@cPrec1 m cf) := by
  unfold cPrec1; apply_cp
@[simp, evp_simps] theorem cPrec1_evp {cf m} {O : ℕ → ℕ} :
    evalp O (cPrec1 m cf) = (fun n => n.rec m fun y IH => evalp O cf <| Nat.pair y IH) := by
  simp [cPrec1, evp_simps]
end Oracle.Single.Code
theorem PrimrecIn.prec1 {cf m} {O : ℕ → ℕ} :
    PrimrecIn O (fun n => n.rec m fun y IH => evalp O cf <| Nat.pair y IH) := by
  rw [← cPrec1_evp]; exact isPrim_prop
end prec1
section casesOn1
namespace Oracle.Single.Code
def cCasesOn1 (m) (cf : Code) := @cPrec1 m (cf.comp left)
@[cp] theorem cCasesOn1_prim {cf m} (hcf : IsPrim cf) :
  IsPrim (cCasesOn1 m cf) := by unfold cCasesOn1; apply_cp
@[simp, evp_simps] theorem cCasesOn1_evp {cf m} {O : ℕ → ℕ} :
  evalp O (@cCasesOn1 m cf) = (Nat.casesOn · m (evalp O cf)) := by simp [cCasesOn1, evp_simps]
end Oracle.Single.Code
end casesOn1

section pred
namespace Oracle.Single.Code
def cPred := (cCasesOn1 0 cId)
@[cp] theorem cPred_prim : IsPrim cPred := by unfold cPred; apply_cp
@[simp, evp_simps] theorem cPred_evp {O : ℕ → ℕ} : evalp O cPred = Nat.pred := by
  simp only [cPred]
  funext n;
  cases n <;> simp [*, evp_simps]
@[simp, ev_simps] theorem cPred_ev {O : ℕ → ℕ} : eval O cPred = Nat.pred := by
  rw [← evalp_eq_eval cPred_prim]; simp only [cPred_evp]
end Oracle.Single.Code
end pred
section sub
namespace Oracle.Single.Code
def cSub := prec cId ((cPred.comp right).comp right)
@[cp] theorem cSub_prim : IsPrim cSub := by unfold cSub; apply_cp
@[simp, evp_simps] theorem cSub_evp {O : ℕ → ℕ} : evalp O cSub = unpaired2 Nat.sub := by
  simp only [cSub, evp_simps]
  funext n;
  simp? [unpaired2] says
    simp only [unpaired, unpair1_to_l, pred_eq_sub_one, unpair2_to_r, unpaired2, sub_eq]
  induction n.right with
  | zero => exact rfl
  | succ n h =>
    simp [*, Nat.sub_add_eq];
@[simp, ev_simps] theorem cSub_ev {O : ℕ → ℕ} : eval O cSub = unpaired2 Nat.sub := by
  rw [← evalp_eq_eval cSub_prim]; simp only [cSub_evp]
end Oracle.Single.Code
end sub
section dist
namespace Oracle.Single.Code
def cDist := cAdd.comp (pair cSub (cSub.comp (pair right left)))
@[cp] theorem cDist_prim : IsPrim cDist := by unfold cDist; apply_cp
@[simp, evp_simps] theorem cDist_evp {O : ℕ → ℕ} : evalp O cDist = unpaired2 Nat.dist := by
  simpa [cDist, evp_simps] using by rfl
@[simp, ev_simps] theorem cDist_ev {O : ℕ → ℕ} : eval O cDist = unpaired2 Nat.dist := by
  rw [← evalp_eq_eval cDist_prim]; simp only [cDist_evp]
end Oracle.Single.Code
end dist
@[simp] theorem eq_zero_iff_dist_zero {a b : ℕ} : a.dist b = 0 ↔ a=b :=
  ⟨fun x ↦ Nat.eq_of_dist_eq_zero x, fun x ↦ Nat.dist_eq_zero x⟩
theorem sgdist_eq_ifeq {a b : ℕ} : (if a.dist b = 0 then 0 else 1) = (if a=b then 0 else 1) := by
  simp only [eq_zero_iff_dist_zero]

section if_eq'
namespace Oracle.Single.Code
/-- eval cIfEq' (x,y) = [x=y] -/
def cIfEq' := cSg.comp cDist
@[cp] theorem cIfEq'_prim : IsPrim cIfEq' := by unfold cIfEq'; apply_cp
@[simp, evp_simps] theorem cIfEq'_evp {O : ℕ → ℕ} :
    evalp O cIfEq' = fun ab => if ab.left=ab.right then 0 else 1 := by
  simp [cIfEq', evp_simps];
@[simp, ev_simps] theorem cIfEq'_ev {O : ℕ → ℕ} :
    eval O cIfEq' = fun ab => if ab.left=ab.right then Part.some 0 else Part.some 1 := by
  rw [← evalp_eq_eval cIfEq'_prim]; simp only [cIfEq'_evp]; funext xs;
  exact apply_ite Part.some (xs.left = xs.right) 0 1
end Oracle.Single.Code
end if_eq'

section if_eq_te
namespace Oracle.Single.Code
/-- eval cIfEqTe (x,y) = [x=y] -/
def cIfEqTe :=
  let eq := cIfEq'.comp₂ (left.comp left) (right.comp left);
  cAdd.comp₂
  (cMul.comp₂ eq (right.comp right))
  (cMul.comp₂ (cNot.comp eq) (left.comp right))
@[cp] theorem cIfEqTe_prim : IsPrim cIfEqTe := by
  unfold cIfEqTe
  extract_lets; expose_names
  have cp_eq : IsPrim eq := by apply_cp;
  apply_cp

@[simp, evp_simps] theorem cIfEqTe_evp {O : ℕ → ℕ} {a b c d} :
    evalp O cIfEqTe ⟪a,b,c,d⟫ = if a=b then c else d := by
  simp only [cIfEqTe];
  cases Classical.em (a=b) with
  | inl h => simp [h, evp_simps]
  | inr h => simp [h, evp_simps]
@[simp, ev_simps] theorem cIfEqTe_ev {O : ℕ → ℕ} {a b c d} :
    eval O cIfEqTe ⟪a,b,c,d⟫ = if a=b then c else d := by
  rw [← evalp_eq_eval cIfEqTe_prim];
  simp [evp_simps]
theorem cIfEqTe_evp' {O : ℕ → ℕ} :
    evalp O cIfEqTe = fun x =>
      if x.left.left = x.left.right then
        x.right.left
      else x.right.right := by
  simp only [cIfEqTe, evp_simps];
  funext xs
  cases Classical.em (xs.left.left=xs.left.right) with
  | inl h => simp [h]
  | inr h => simp [h]
theorem cIfEqTe_ev' {O : ℕ → ℕ} :
    eval O cIfEqTe = fun x =>
      if x.left.left = x.left.right then
        x.right.left
      else x.right.right := by
  rw [← evalp_eq_eval cIfEqTe_prim]; simp only [cIfEqTe_evp']; funext xs;
  cases Classical.em (xs.left.left=xs.left.right) with
  | inl h => simp [h]
  | inr h => simp [h]

end Oracle.Single.Code
end if_eq_te
section if_lt_te
namespace Oracle.Single.Code
/-- eval cIfLtTe (x,y) = [x<y] -/
def cIfLtTe :=
  let lt := cSg.comp <| cSub.comp₂ (succ.comp <| left.comp left) (right.comp left);
  cAdd.comp₂
  (cMul.comp₂ lt (right.comp right))
  (cMul.comp₂ (cNot.comp lt) (left.comp right))
@[cp] theorem cIfLtTe_prim : IsPrim cIfLtTe := by unfold cIfLtTe; apply_cp 60
@[simp, evp_simps] theorem cIfLtTe_evp {O : ℕ → ℕ} {a b c d} :
    evalp O cIfLtTe ⟪a,b,c,d⟫ = if a<b then c else d := by
  simp only [cIfLtTe, evp_simps];
  cases Classical.em (a<b) with
  | inl h => simp [h, Nat.sub_eq_zero_of_le h]
  | inr h =>
    have h1: a+1-b>0 := by exact tsub_pos_iff_not_le.mpr h
    have h0: ¬(a+1-b=0) := by exact Nat.ne_zero_of_lt h1
    simp [h, h0]
@[simp, ev_simps] theorem cIfLtTe_ev {O : ℕ → ℕ} {a b c d} :
    eval O cIfLtTe ⟪a,b,c,d⟫ = if a<b then c else d := by
  rw [← evalp_eq_eval cIfLtTe_prim]; simp [evp_simps]
end Oracle.Single.Code
end if_lt_te

section if_le_te
namespace Oracle.Single.Code
-- we use the fact that `a<b+1 ↔ a ≤ b`.
/-- eval cIfLeTe (x,y) = [x ≤ y] -/
def cIfLeTe :=
  cIfLtTe.comp (pair (pair (left.comp left) (succ.comp <| right.comp left)) right)
@[cp] theorem cIfLeTe_prim : IsPrim cIfLeTe := by unfold cIfLeTe; apply_cp
@[simp, evp_simps] theorem cIfLeTe_evp {O : ℕ → ℕ} {a b c d} :
    evalp O cIfLeTe ⟪a,b,c,d⟫ = if a ≤ b then c else d := by
  simp only [cIfLeTe, evp_simps];
  cases Classical.em (a<b+1) with
  | inl h => simp [h, Nat.lt_add_one_iff.mp h, evp_simps]
  | inr h => simp [h, Nat.lt_add_one_iff.not.mp h, evp_simps]
@[simp, ev_simps] theorem cIfLeTe_ev {O : ℕ → ℕ} {a b c d} :
    eval O cIfLeTe ⟪a,b,c,d⟫ = if a ≤ b then c else d := by
  rw [← evalp_eq_eval cIfLeTe_prim]; simp [evp_simps]
end Oracle.Single.Code
end if_le_te

section flip
namespace Oracle.Single.Code
/-- eval cFlip (x,y) = (y,x) -/
def cFlip := pair right left
@[cp] theorem cFlip_prim : IsPrim cFlip := by unfold cFlip; apply_cp
@[simp, evp_simps] theorem cFlip_evp {O : ℕ → ℕ} {a b} : evalp O cFlip ⟪a, b⟫ = ⟪b, a⟫ := by
  simp [cFlip, evp_simps];
@[simp, ev_simps] theorem cFlip_ev {O : ℕ → ℕ} {a b} : eval O cFlip ⟪a, b⟫ = ⟪b, a⟫ := by
  rw [← evalp_eq_eval cFlip_prim]; simp [evp_simps]
end Oracle.Single.Code
end flip

section if_gt_te
namespace Oracle.Single.Code
/-- eval cIfGtTe (x,y) = [x>y] -/
def cIfGtTe := cIfLtTe.comp (pair (cFlip.comp left) right)
@[cp] theorem cIfGtTe_prim : IsPrim cIfGtTe := by unfold cIfGtTe; apply_cp
@[simp, evp_simps] theorem cIfGtTe_evp {O : ℕ → ℕ} {a b c d} :
    evalp O cIfGtTe ⟪a,b,c,d⟫ = if a>b then c else d := by simp [cIfGtTe, evp_simps];
@[simp, ev_simps] theorem cIfGtTe_ev {O : ℕ → ℕ} {a b c d} :
    eval O cIfGtTe ⟪a,b,c,d⟫ = if a>b then c else d := by
  rw [← evalp_eq_eval cIfGtTe_prim]; simp [evp_simps]
end Oracle.Single.Code
end if_gt_te
section if_ge_te
namespace Oracle.Single.Code
/-- eval cIfGeTe (x,y) = [x>y] -/
def cIfGeTe := cIfLeTe.comp (pair (cFlip.comp left) right)
@[cp] theorem cIfGeTe_prim : IsPrim cIfGeTe := by unfold cIfGeTe; apply_cp
@[simp, evp_simps] theorem cIfGeTe_evp {O : ℕ → ℕ} {a b c d} :
  evalp O cIfGeTe ⟪a,b,c,d⟫ = if a≥b then c else d := by simp [cIfGeTe, evp_simps];
@[simp, ev_simps] theorem cIfGeTe_ev {O : ℕ → ℕ} {a b c d} :
    eval O cIfGeTe ⟪a,b,c,d⟫ = if a≥b then c else d := by
  rw [← evalp_eq_eval cIfGeTe_prim]; simp [evp_simps]
end Oracle.Single.Code
end if_ge_te

section ifz
namespace Oracle.Single.Code
def cIfz := cAdd.comp <| pair
  (cMul.comp <| pair (cSg'.comp left) (left.comp right))
  (cMul.comp <| pair (cSg.comp left)  (right.comp right))
@[cp] theorem cIfz_prim : IsPrim cIfz := by unfold cIfz; apply_cp
@[simp, evp_simps] theorem cIfz_evp {O : ℕ → ℕ} :
    evalp O cIfz = fun (cab : ℕ) => if cab.left=0 then cab.right.left else cab.right.right := by
  simp only [cIfz, evp_simps];
  funext xs
  have hsplit : xs.left = 0 ∨ ¬ (xs.left = 0) := by exact Or.symm (ne_or_eq xs.left 0)
  cases hsplit with
  | inl h => simp [h]
  | inr h => simp [h]
theorem cIfz_ev' {O : ℕ → ℕ} :
    eval O cIfz = fun (cab : ℕ) => if cab.left=0 then cab.right.left else cab.right.right := by
  rw [← evalp_eq_eval cIfz_prim]; simp only [cIfz_evp];
@[simp, ev_simps] theorem cIfz_ev {O : ℕ → ℕ} {cab} :
    eval O cIfz cab = if cab.left=0 then cab.right.left else cab.right.right := by
  simp [cIfz_ev']
end Oracle.Single.Code
end ifz

section ift
namespace Oracle.Single.Code
def cIft := cIfz.comp₂ (cSg'.comp <| left) right
@[cp] theorem cIft_prim : IsPrim cIft := by unfold cIft; apply_cp
@[simp, evp_simps] theorem cIft_evp {O : ℕ → ℕ} :
    evalp O cIft = fun (cab : ℕ) =>
      if (n2b cab.left) then
        cab.right.left else
      cab.right.right := by
  simp only [cIft, evp_simps];
  funext xs
  have hsplit : xs.left = 0 ∨ ¬ (xs.left = 0) := by exact Or.symm (ne_or_eq xs.left 0)
  cases hsplit with
  | inl h => simp [h, n2b]
  | inr h => simp [h, n2b]
theorem cIft_ev' {O : ℕ → ℕ} :
    eval O cIft = fun (cab : ℕ) => if (n2b cab.left) then cab.right.left else cab.right.right := by
  rw [← evalp_eq_eval cIft_prim]; simp only [cIft_evp];
@[simp, ev_simps] theorem cIft_ev {O : ℕ → ℕ} {cab} :
    eval O cIft cab = if (n2b cab.left) then cab.right.left else cab.right.right := by
  simp [cIft_ev']
end Oracle.Single.Code
end ift

section nat_iterate
namespace Oracle.Single.Code
def cNatIterate (cf : Code) :=
  prec
    cId
    (cf.comp (right.comp right))

@[cp] theorem cNatIterate_prim {cf} (hcf : IsPrim cf) : IsPrim (cNatIterate cf) := by
  unfold cNatIterate; apply_cp
@[simp, evp_simps] theorem cNatIterate_evp {O : ℕ → ℕ} {cf input i} :
    evalp O (cNatIterate cf) ⟪input, i⟫ = (evalp O cf)^[i] (input) := by
  simp only [cNatIterate, evp_simps]
  simp only [unpaired, unpair_pair]
  induction i with
  | zero => simp
  | succ n ih =>
    simp only [ih, Function.iterate_succ, Function.comp_apply]
    exact Eq.symm (Function.iterate_succ_apply' (evalp O cf) n input)
end Oracle.Single.Code
end nat_iterate

section mul2
namespace Oracle.Single.Code
def cMul2 := cMul.comp₂ cId (cConst 2)
@[cp] theorem cMul2_prim : IsPrim cMul2 := by unfold cMul2; apply_cp
@[simp, evp_simps] theorem cMul2_evp {O : ℕ → ℕ} : evalp O cMul2 = fun x => x*2 := by
  simp [cMul2, evp_simps]
@[simp, ev_simps] theorem cMul2_ev {O : ℕ → ℕ} : eval O cMul2 = (fun x => x*(2 : ℕ)) := by
  rw [← evalp_eq_eval cMul2_prim]; simp only [cMul2_evp];
end Oracle.Single.Code
end mul2

section max
namespace Oracle.Single.Code
def cMax := cIfLeTe.comp₄ left right right left
@[cp] theorem cMax_prim : IsPrim cMax := by unfold cMax; apply_cp
@[simp, evp_simps] theorem cMax_evp {O : ℕ → ℕ} : evalp O cMax = unpaired2 Nat.max := by
  simpa only [cMax, evp_simps] using by rfl
@[simp, ev_simps] theorem cMax_ev {O : ℕ → ℕ} : eval O cMax = unpaired2 Nat.max := by
  rw [← evalp_eq_eval cMax_prim]; simp only [cMax_evp]
end Oracle.Single.Code
end max
