/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Mathlib.Computability.SingleOracle.Basic

/-!
# Construction of basic primitive recursive functions

This file defines basic primitive recursive codes for basic functions, such as if-else, or
arithmetic functions.

## Structure
Each construction is roughly structured as follows.

Suppose we want to construct a primitive recursive function `f : ℕ → ℕ`.

`def c_f := ...`
  · the code which will implement `f`

`@[cp] theorem c_f_prim : code_prim c_f := by unfold c_f; apply_cp`
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

`theorem PrimrecIn.f : PrimrecIn O f := by rw [←c_f_evp]; exact code_prim_prop`
  · theorem asserting that the function `f` is primitive recursive. This again follows
    immediately from `c_f_evp`.

-/

open Oracle.Single
open Oracle.Single.Code
open Nat

section comp₂
namespace Oracle.Single.Code
def comp₂ := fun c1 c2 c3 : Code => c1.comp (pair c2 c3)
@[cp] theorem comp₂_prim {c1 c2 c3} (hc1 : code_prim c1) (hc2 : code_prim c2) (hc3 : code_prim c3) :
  code_prim (comp₂ c1 c2 c3) := by unfold comp₂; apply_cp
@[simp, evp_simps] theorem comp₂_evp {O c1 c2 c3} :
    evalp O (comp₂ c1 c2 c3) = fun x => evalp O c1 ⟪evalp O c2 x, evalp O c3 x⟫ := by
  simp only [comp₂, evp_simps];
@[simp, ev_simps] theorem comp₂_ev {O c1 c2 c3} :
    eval O (comp₂ c1 c2 c3) = fun x => ⟪eval O c2 x, eval O c3 x⟫ >>= (eval O c1) := by
  simp [eval, comp₂, Seq.seq]
end Oracle.Single.Code
end comp₂

section comp₄
namespace Oracle.Single.Code
def comp₄ := fun c1 c2 c3 c4 c5 : Code => c1.comp₂ (pair c2 c3) (pair c4 c5)
@[cp] theorem comp₄_prim {c1 c2 c3 c4 c5}
  (hc1 : code_prim c1) (hc2 : code_prim c2)
  (hc3 : code_prim c3) (hc4 : code_prim c4) (hc5 : code_prim c5) :
  code_prim (comp₄ c1 c2 c3 c4 c5) := by unfold comp₄; apply_cp
@[simp, evp_simps] theorem comp₄_evp {O c1 c2 c3 c4 c5} : evalp O (comp₄ c1 c2 c3 c4 c5) = fun x ↦
  evalp O c1 ⟪evalp O c2 x, evalp O c3 x, evalp O c4 x, evalp O c5 x⟫ := by
  simp only [comp₄, evp_simps]
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
  (hc1 : code_prim c1) (hc2 : code_prim c2) (hc3 : code_prim c3) (hc4 : code_prim c4) :
  code_prim (comp₃ c1 c2 c3 c4) := by unfold comp₃; apply_cp
@[simp, evp_simps] theorem comp₃_evp {c1 c2 c3 c4} {O : ℕ → ℕ} :
    evalp O (comp₃ c1 c2 c3 c4) = fun x ↦
    evalp O c1 ⟪evalp O c2 x, evalp O c3 x, evalp O c4 x⟫ := by
  simp only [comp₃, evp_simps]
@[simp, ev_simps] theorem comp₃_ev {c1 c2 c3 c4} {O : ℕ → ℕ} : eval O (comp₃ c1 c2 c3 c4) = fun x ↦
  ⟪eval O c2 x, eval O c3 x, eval O c4 x⟫ >>= (eval O c1) := by
    simp [comp₃, eval, comp₂, Seq.seq]
end Oracle.Single.Code
end comp₃

section id
namespace Oracle.Single.Code
def c_id := left.pair right
@[cp] theorem c_id_prim : code_prim c_id := by unfold c_id; apply_cp
@[simp, evp_simps] theorem c_id_evp {O : ℕ → ℕ} {n} : evalp O c_id n = n := by simp [c_id, evalp]
theorem c_id_evp' {O : ℕ → ℕ} : evalp O c_id = id := by funext x; simp [evp_simps]
@[simp, ev_simps] theorem c_id_ev {O : ℕ → ℕ} {n} : eval O c_id n = n := by simp [c_id,eval,Seq.seq]
end Oracle.Single.Code
theorem PrimrecIn.id {O : ℕ → ℕ} : PrimrecIn O id := by
  rw [← c_id_evp']; exact code_prim_prop
end id

section const
namespace Oracle.Single.Code
def c_const : ℕ → Code
| 0 => zero
| n+1 => comp succ (c_const n)
@[cp] theorem c_const_prim {n} : code_prim (c_const n) := by
  induction n
  · unfold c_const; exact code_prim.zero
  · unfold c_const
    expose_names
    exact code_prim.comp code_prim.succ h
@[simp, evp_simps] theorem c_const_evp {O : ℕ → ℕ} : ∀ n m, evalp O (c_const n) m = n
| 0, _ => rfl
| n+1, m => by simp! [c_const_evp n m]
@[simp, ev_simps] theorem c_const_ev {O : ℕ → ℕ} : ∀ n m, eval O (c_const n) m = n
| 0, _ => rfl
| n+1, m => by simp! [c_const_ev n m]
end Oracle.Single.Code
end const


section curry
namespace Oracle.Single.Code
def c_curry (c : Code) (n : ℕ) : Code := comp c (pair (c_const n) c_id)
theorem _id_eq_c_id : c_id = Code.id := by simp [c_id,Code.id]
theorem _const_eq_c_const : c_const = Code.const := by
  funext n;
  unfold c_const
  unfold Code.const
  induction n
  · exact rfl
  · simp only [comp.injEq, true_and]
    unfold c_const
    unfold Code.const
    expose_names
    exact h
theorem _curry_eq_c_curry : c_curry = curry := by
  unfold c_curry
  unfold curry
  rw [_id_eq_c_id]
  rw [_const_eq_c_const]
-- @[simp] theorem c_curry_prim : code_prim (c_curry c n) := by
@[simp, evp_simps] theorem c_curry_evp {O : ℕ → ℕ} {c n x} :
    evalp O (c_curry c n) x = evalp O c ⟪n, x⟫ := by simp [c_curry, evp_simps]
@[simp, ev_simps] theorem c_curry_ev {O : ℕ → ℕ} {c n x} :
    eval O (c_curry c n) x = eval O c ⟪n, x⟫ := by
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
def c_sg := comp (prec zero (((c_const 1).comp left).comp left)) (pair zero c_id)
@[cp] theorem c_sg_prim : code_prim c_sg := by unfold c_sg; apply_cp
@[simp, evp_simps] theorem c_sg_evp {O : ℕ → ℕ} : evalp O c_sg = Nat.sg := by
  simp only [c_sg, evp_simps]
  funext n; induction n with
  | zero => exact rfl
  | succ n _ => simp
@[simp, ev_simps] theorem c_sg_ev {O : ℕ → ℕ} : eval O c_sg = Nat.sg := by
  rw [← evalp_eq_eval c_sg_prim]; simp only [c_sg_evp]
def c_sg' := comp (prec (c_const 1) (((zero).comp left).comp left)) (pair zero c_id)
@[cp] theorem c_sg'_prim : code_prim c_sg' := by unfold c_sg'; apply_cp
@[simp, evp_simps] theorem c_sg'_evp {O : ℕ → ℕ} : evalp O c_sg' = Nat.sg' := by
  simp only [c_sg', evp_simps]
  funext n; induction n with
  | zero => exact rfl
  | succ n _ => simp
@[simp, ev_simps] theorem c_sg'_ev {O : ℕ → ℕ} : eval O c_sg' = Nat.sg' := by
  rw [← evalp_eq_eval c_sg'_prim]; simp only [c_sg'_evp]
end Oracle.Single.Code
theorem PrimrecIn.sg {O : ℕ → ℕ} : PrimrecIn O Nat.sg := by
  rw [← c_sg_evp]; exact code_prim_prop
theorem PrimrecIn.sg' {O : ℕ → ℕ} : PrimrecIn O Nat.sg' := by
  rw [← c_sg'_evp]; exact code_prim_prop
@[simp] abbrev c_not := c_sg'
end sgsg'

section n2b
namespace Oracle.Single.Code
def c_n2b := c_sg
@[cp] theorem c_n2b_prim : code_prim c_n2b := by unfold c_n2b; apply_cp 10
@[simp, evp_simps] theorem c_n2b_evp {O : ℕ → ℕ} :
    evalp O c_n2b = fun x => if n2b x = true then 1 else 0 := by
  simp only [c_n2b, evp_simps]
  unfold Nat.sg; unfold n2b
  aesop
@[simp, ev_simps] theorem c_n2b_ev {O : ℕ → ℕ} :
    eval O c_n2b = fun x => if n2b x = true then 1 else 0 := by
  rw [← evalp_eq_eval c_n2b_prim]; simp only [c_n2b_evp]; funext x; aesop
end Oracle.Single.Code
end n2b

section add
namespace Oracle.Single.Code
def c_add := (prec c_id ((succ.comp right).comp right))
@[cp] theorem c_add_prim : code_prim c_add := by unfold c_add; apply_cp
@[simp, evp_simps] theorem c_add_evp {O : ℕ → ℕ} : evalp O c_add = unpaired2 Nat.add := by
  simp only [c_add, evp_simps]
  funext n;
  simp only [unpaired, unpair1_to_l, succ_eq_add_one, unpair2_to_r, unpaired2, add_eq]
  induction n.right with
  | zero => exact rfl
  | succ n h => exact Nat.add_left_inj.mpr h
@[simp, ev_simps] theorem c_add_ev {O : ℕ → ℕ} : eval O c_add = unpaired2 Nat.add := by
  rw [← evalp_eq_eval c_add_prim]; simp only [c_add_evp]
end Oracle.Single.Code
end add
section mul
namespace Oracle.Single.Code
def c_mul := prec zero (c_add.comp (pair left (right.comp right)))
@[cp] theorem c_mul_prim : code_prim c_mul := by unfold c_mul; apply_cp
@[simp, evp_simps] theorem c_mul_evp {O : ℕ → ℕ} : evalp O c_mul = unpaired2 Nat.mul := by
  simp only [c_mul, evp_simps]
  funext n;
  simp only [unpaired, unpaired2, unpair1_to_l, pair_l, pair_r, add_eq, unpair2_to_r, mul_eq]
  induction n.right with
  | zero => exact rfl
  | succ n h =>
    simp only [*, mul_succ];
    (expose_names; exact Nat.add_comm (unpair n_1).1 ((unpair n_1).1 * n))
@[simp, ev_simps] theorem c_mul_ev {O : ℕ → ℕ} : eval O c_mul = unpaired2 Nat.mul := by
  rw [← evalp_eq_eval c_mul_prim]; simp only [c_mul_evp]
end Oracle.Single.Code
end mul
section pow
namespace Oracle.Single.Code
def c_pow := prec (c_const 1) (c_mul.comp (pair (right.comp right) left))
@[cp] theorem c_pow_prim : code_prim c_pow := by unfold c_pow; apply_cp
@[simp, evp_simps] theorem c_pow_evp {O : ℕ → ℕ} : evalp O c_pow = unpaired2 Nat.pow := by
  simp only [c_pow, evp_simps]
  funext n;
  simp only [unpaired, unpaired2, unpair1_to_l, pair_l, pair_r, unpair2_to_r, mul_eq]
  induction n.right with
  | zero => exact rfl
  | succ n h => simp [*, pow_succ];
@[simp, ev_simps] theorem c_pow_ev {O : ℕ → ℕ} : eval O c_pow = unpaired2 Nat.pow := by
  rw [← evalp_eq_eval c_pow_prim]; simp only [c_pow_evp]
end Oracle.Single.Code
end pow

section prec1
namespace Oracle.Single.Code
def c_prec1 (m) (cf : Code) := ((prec (c_const m) (cf.comp right)).comp (zero.pair c_id))
@[cp] theorem c_prec1_prim {cf m} (hcf : code_prim cf) : code_prim (@c_prec1 m cf) := by
  unfold c_prec1; apply_cp
@[simp, evp_simps] theorem c_prec1_evp {cf m} {O : ℕ → ℕ} :
    evalp O (c_prec1 m cf) = (fun n => n.rec m fun y IH => evalp O cf <| Nat.pair y IH) := by
  simp [c_prec1, evp_simps]
end Oracle.Single.Code
theorem PrimrecIn.prec1 {cf m} {O : ℕ → ℕ} :
    PrimrecIn O (fun n => n.rec m fun y IH => evalp O cf <| Nat.pair y IH) := by
  rw [← c_prec1_evp]; exact code_prim_prop
end prec1
section casesOn1
namespace Oracle.Single.Code
def c_casesOn1 (m) (cf : Code) := @c_prec1 m (cf.comp left)
@[cp] theorem c_casesOn1_prim {cf m} (hcf : code_prim cf) :
  code_prim (c_casesOn1 m cf) := by unfold c_casesOn1; apply_cp
@[simp, evp_simps] theorem c_casesOn1_evp {cf m} {O : ℕ → ℕ} :
  evalp O (@c_casesOn1 m cf) = (Nat.casesOn · m (evalp O cf)) := by simp [c_casesOn1, evp_simps]
end Oracle.Single.Code
end casesOn1

section pred
namespace Oracle.Single.Code
def c_pred := (c_casesOn1 0 c_id)
@[cp] theorem c_pred_prim : code_prim c_pred := by unfold c_pred; apply_cp
@[simp, evp_simps] theorem c_pred_evp {O : ℕ → ℕ} : evalp O c_pred = Nat.pred := by
  simp only [c_pred]
  funext n;
  cases n <;> simp [*, evp_simps]
@[simp, ev_simps] theorem c_pred_ev {O : ℕ → ℕ} : eval O c_pred = Nat.pred := by
  rw [← evalp_eq_eval c_pred_prim]; simp only [c_pred_evp]
end Oracle.Single.Code
end pred
section sub
namespace Oracle.Single.Code
def c_sub := prec c_id ((c_pred.comp right).comp right)
@[cp] theorem c_sub_prim : code_prim c_sub := by unfold c_sub; apply_cp
@[simp, evp_simps] theorem c_sub_evp {O : ℕ → ℕ} : evalp O c_sub = unpaired2 Nat.sub := by
  simp only [c_sub, evp_simps]
  funext n;
  simp? [unpaired2] says
    simp only [unpaired, unpair1_to_l, pred_eq_sub_one, unpair2_to_r, unpaired2, sub_eq]
  induction n.right with
  | zero => exact rfl
  | succ n h =>
    simp [*, Nat.sub_add_eq];
@[simp, ev_simps] theorem c_sub_ev {O : ℕ → ℕ} : eval O c_sub = unpaired2 Nat.sub := by
  rw [← evalp_eq_eval c_sub_prim]; simp only [c_sub_evp]
end Oracle.Single.Code
end sub
section dist
namespace Oracle.Single.Code
def c_dist := c_add.comp (pair c_sub (c_sub.comp (pair right left)))
@[cp] theorem c_dist_prim : code_prim c_dist := by unfold c_dist; apply_cp
@[simp, evp_simps] theorem c_dist_evp {O : ℕ → ℕ} : evalp O c_dist = unpaired2 Nat.dist := by
  simpa [c_dist, evp_simps] using by rfl
@[simp, ev_simps] theorem c_dist_ev {O : ℕ → ℕ} : eval O c_dist = unpaired2 Nat.dist := by
  rw [← evalp_eq_eval c_dist_prim]; simp only [c_dist_evp]
end Oracle.Single.Code
end dist
@[simp] theorem eq_zero_iff_dist_zero {a b : ℕ} : a.dist b = 0 ↔ a=b :=
  ⟨fun x ↦ Nat.eq_of_dist_eq_zero x, fun x ↦ Nat.dist_eq_zero x⟩
theorem sgdist_eq_ifeq {a b : ℕ} : (if a.dist b = 0 then 0 else 1) = (if a=b then 0 else 1) := by
  simp only [eq_zero_iff_dist_zero]

section if_eq'
namespace Oracle.Single.Code
/-- eval c_if_eq' (x,y) = [x=y] -/
def c_if_eq' := c_sg.comp c_dist
@[cp] theorem c_if_eq'_prim : code_prim c_if_eq' := by unfold c_if_eq'; apply_cp
@[simp, evp_simps] theorem c_if_eq'_evp {O : ℕ → ℕ} :
    evalp O c_if_eq' = fun ab => if ab.left=ab.right then 0 else 1 := by
  simp [c_if_eq', evp_simps];
@[simp, ev_simps] theorem c_if_eq'_ev {O : ℕ → ℕ} :
    eval O c_if_eq' = fun ab => if ab.left=ab.right then Part.some 0 else Part.some 1 := by
  rw [← evalp_eq_eval c_if_eq'_prim]; simp only [c_if_eq'_evp]; funext xs;
  exact apply_ite Part.some (xs.left = xs.right) 0 1
end Oracle.Single.Code
end if_eq'

section if_eq_te
namespace Oracle.Single.Code
/-- eval c_if_eq_te (x,y) = [x=y] -/
def c_if_eq_te :=
  let eq := c_if_eq'.comp₂ (left.comp left) (right.comp left);
  c_add.comp₂
  (c_mul.comp₂ eq (right.comp right))
  (c_mul.comp₂ (c_not.comp eq) (left.comp right))
@[cp] theorem c_if_eq_te_prim : code_prim c_if_eq_te := by
  unfold c_if_eq_te
  extract_lets; expose_names
  have cp_eq : code_prim eq := by apply_cp;
  apply_cp

@[simp, evp_simps] theorem c_if_eq_te_evp {O : ℕ → ℕ} {a b c d} :
    evalp O c_if_eq_te ⟪a,b,c,d⟫ = if a=b then c else d := by
  simp only [c_if_eq_te];
  cases Classical.em (a=b) with
  | inl h => simp [h, evp_simps]
  | inr h => simp [h, evp_simps]
@[simp, ev_simps] theorem c_if_eq_te_ev {O : ℕ → ℕ} {a b c d} :
    eval O c_if_eq_te ⟪a,b,c,d⟫ = if a=b then c else d := by
  rw [← evalp_eq_eval c_if_eq_te_prim];
  simp [evp_simps]
theorem c_if_eq_te_evp' {O : ℕ → ℕ} :
    evalp O c_if_eq_te = fun x =>
      if x.left.left = x.left.right then
        x.right.left
      else x.right.right := by
  simp only [c_if_eq_te, evp_simps];
  funext xs
  cases Classical.em (xs.left.left=xs.left.right) with
  | inl h => simp [h]
  | inr h => simp [h]
theorem c_if_eq_te_ev' {O : ℕ → ℕ} :
    eval O c_if_eq_te = fun x =>
      if x.left.left = x.left.right then
        x.right.left
      else x.right.right := by
  rw [← evalp_eq_eval c_if_eq_te_prim]; simp only [c_if_eq_te_evp']; funext xs;
  cases Classical.em (xs.left.left=xs.left.right) with
  | inl h => simp [h]
  | inr h => simp [h]

end Oracle.Single.Code
end if_eq_te
section if_lt_te
namespace Oracle.Single.Code
/-- eval c_if_lt_te (x,y) = [x<y] -/
def c_if_lt_te :=
  let lt := c_sg.comp <| c_sub.comp₂ (succ.comp <| left.comp left) (right.comp left);
  c_add.comp₂
  (c_mul.comp₂ lt (right.comp right))
  (c_mul.comp₂ (c_not.comp lt) (left.comp right))
@[cp] theorem c_if_lt_te_prim : code_prim c_if_lt_te := by
  repeat (first|assumption|apply_rules using cp|simp|constructor)
@[simp, evp_simps] theorem c_if_lt_te_evp {O : ℕ → ℕ} {a b c d} :
    evalp O c_if_lt_te ⟪a,b,c,d⟫ = if a<b then c else d := by
  simp only [c_if_lt_te, evp_simps];
  cases Classical.em (a<b) with
  | inl h => simp [h, Nat.sub_eq_zero_of_le h]
  | inr h =>
    have h1: a+1-b>0 := by exact tsub_pos_iff_not_le.mpr h
    have h0: ¬(a+1-b=0) := by exact Nat.ne_zero_of_lt h1
    simp [h, h0]
@[simp, ev_simps] theorem c_if_lt_te_ev {O : ℕ → ℕ} {a b c d} :
    eval O c_if_lt_te ⟪a,b,c,d⟫ = if a<b then c else d := by
  rw [← evalp_eq_eval c_if_lt_te_prim]; simp [evp_simps]
end Oracle.Single.Code
end if_lt_te

section if_le_te
namespace Oracle.Single.Code
-- we use the fact that `a<b+1 ↔ a ≤ b`.
/-- eval c_if_le_te (x,y) = [x ≤ y] -/
def c_if_le_te :=
  c_if_lt_te.comp (pair (pair (left.comp left) (succ.comp <| right.comp left)) right)
@[cp] theorem c_if_le_te_prim : code_prim c_if_le_te := by unfold c_if_le_te; apply_cp
@[simp, evp_simps] theorem c_if_le_te_evp {O : ℕ → ℕ} {a b c d} :
    evalp O c_if_le_te ⟪a,b,c,d⟫ = if a ≤ b then c else d := by
  simp only [c_if_le_te, evp_simps];
  cases Classical.em (a<b+1) with
  | inl h => simp [h, Nat.lt_add_one_iff.mp h, evp_simps]
  | inr h => simp [h, Nat.lt_add_one_iff.not.mp h, evp_simps]
@[simp, ev_simps] theorem c_if_le_te_ev {O : ℕ → ℕ} {a b c d} :
    eval O c_if_le_te ⟪a,b,c,d⟫ = if a ≤ b then c else d := by
  rw [← evalp_eq_eval c_if_le_te_prim]; simp [evp_simps]
end Oracle.Single.Code
end if_le_te

section flip
namespace Oracle.Single.Code
/-- eval c_flip (x,y) = (y,x) -/
def c_flip := pair right left
@[cp] theorem c_flip_prim : code_prim c_flip := by unfold c_flip; apply_cp
@[simp, evp_simps] theorem c_flip_evp {O : ℕ → ℕ} {a b} : evalp O c_flip ⟪a, b⟫ = ⟪b, a⟫ := by
  simp [c_flip, evp_simps];
@[simp, ev_simps] theorem c_flip_ev {O : ℕ → ℕ} {a b} : eval O c_flip ⟪a, b⟫ = ⟪b, a⟫ := by
  rw [← evalp_eq_eval c_flip_prim]; simp [evp_simps]
end Oracle.Single.Code
end flip

section if_gt_te
namespace Oracle.Single.Code
/-- eval c_if_gt_te (x,y) = [x>y] -/
def c_if_gt_te := c_if_lt_te.comp (pair (c_flip.comp left) right)
@[cp] theorem c_if_gt_te_prim : code_prim c_if_gt_te := by unfold c_if_gt_te; apply_cp
@[simp, evp_simps] theorem c_if_gt_te_evp {O : ℕ → ℕ} {a b c d} :
    evalp O c_if_gt_te ⟪a,b,c,d⟫ = if a>b then c else d := by simp [c_if_gt_te, evp_simps];
@[simp, ev_simps] theorem c_if_gt_te_ev {O : ℕ → ℕ} {a b c d} :
    eval O c_if_gt_te ⟪a,b,c,d⟫ = if a>b then c else d := by
  rw [← evalp_eq_eval c_if_gt_te_prim]; simp [evp_simps]
end Oracle.Single.Code
end if_gt_te
section if_ge_te
namespace Oracle.Single.Code
/-- eval c_if_ge_te (x,y) = [x>y] -/
def c_if_ge_te := c_if_le_te.comp (pair (c_flip.comp left) right)
@[cp] theorem c_if_ge_te_prim : code_prim c_if_ge_te := by unfold c_if_ge_te; apply_cp
@[simp, evp_simps] theorem c_if_ge_te_evp {O : ℕ → ℕ} {a b c d} :
  evalp O c_if_ge_te ⟪a,b,c,d⟫ = if a≥b then c else d := by simp [c_if_ge_te, evp_simps];
@[simp, ev_simps] theorem c_if_ge_te_ev {O : ℕ → ℕ} {a b c d} :
    eval O c_if_ge_te ⟪a,b,c,d⟫ = if a≥b then c else d := by
  rw [← evalp_eq_eval c_if_ge_te_prim]; simp [evp_simps]
end Oracle.Single.Code
end if_ge_te

section ifz
namespace Oracle.Single.Code
def c_ifz := c_add.comp <| pair
  (c_mul.comp <| pair (c_sg'.comp left) (left.comp right))
  (c_mul.comp <| pair (c_sg.comp left)  (right.comp right))
@[cp] theorem c_ifz_prim : code_prim c_ifz := by unfold c_ifz; apply_cp
@[simp, evp_simps] theorem c_ifz_evp {O : ℕ → ℕ} :
    evalp O c_ifz = fun (cab : ℕ) => if cab.left=0 then cab.right.left else cab.right.right := by
  simp only [c_ifz, evp_simps];
  funext xs
  have hsplit : xs.left = 0 ∨ ¬ (xs.left = 0) := by exact Or.symm (ne_or_eq xs.left 0)
  cases hsplit with
  | inl h => simp [h]
  | inr h => simp [h]
theorem c_ifz_ev' {O : ℕ → ℕ} :
    eval O c_ifz = fun (cab : ℕ) => if cab.left=0 then cab.right.left else cab.right.right := by
  rw [← evalp_eq_eval c_ifz_prim]; simp only [c_ifz_evp];
@[simp, ev_simps] theorem c_ifz_ev {O : ℕ → ℕ} {cab} :
    eval O c_ifz cab = if cab.left=0 then cab.right.left else cab.right.right := by
  simp [c_ifz_ev']
end Oracle.Single.Code
end ifz

section ift
namespace Oracle.Single.Code
def c_ift := c_ifz.comp₂ (c_sg'.comp <| left) right
@[cp] theorem c_ift_prim : code_prim c_ift := by unfold c_ift; apply_cp
@[simp, evp_simps] theorem c_ift_evp {O : ℕ → ℕ} :
    evalp O c_ift = fun (cab : ℕ) =>
      if (n2b cab.left) then
        cab.right.left else
      cab.right.right := by
  simp only [c_ift, evp_simps];
  funext xs
  have hsplit : xs.left = 0 ∨ ¬ (xs.left = 0) := by exact Or.symm (ne_or_eq xs.left 0)
  cases hsplit with
  | inl h => simp [h, n2b]
  | inr h => simp [h, n2b]
theorem c_ift_ev' {O : ℕ → ℕ} :
    eval O c_ift = fun (cab : ℕ) => if (n2b cab.left) then cab.right.left else cab.right.right := by
  rw [← evalp_eq_eval c_ift_prim]; simp only [c_ift_evp];
@[simp, ev_simps] theorem c_ift_ev {O : ℕ → ℕ} {cab} :
    eval O c_ift cab = if (n2b cab.left) then cab.right.left else cab.right.right := by
  simp [c_ift_ev']
end Oracle.Single.Code
end ift

section nat_iterate
namespace Oracle.Single.Code
def c_nat_iterate (cf : Code) :=
  prec
    c_id
    (cf.comp (right.comp right))

@[cp] theorem c_nat_iterate_prim {cf} (hcf : code_prim cf) : code_prim (c_nat_iterate cf) := by
  unfold c_nat_iterate; apply_cp
@[simp, evp_simps] theorem c_nat_iterate_evp {O : ℕ → ℕ} {cf input i} :
    evalp O (c_nat_iterate cf) ⟪input, i⟫ = (evalp O cf)^[i] (input) := by
  simp only [c_nat_iterate, evp_simps]
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
def c_mul2 := c_mul.comp₂ c_id (c_const 2)
@[cp] theorem c_mul2_prim : code_prim c_mul2 := by unfold c_mul2; apply_cp
@[simp, evp_simps] theorem c_mul2_evp {O : ℕ → ℕ} : evalp O c_mul2 = fun x => x*2 := by
  simp [c_mul2, evp_simps]
@[simp, ev_simps] theorem c_mul2_ev {O : ℕ → ℕ} : eval O c_mul2 = (fun x => x*(2 : ℕ)) := by
  rw [← evalp_eq_eval c_mul2_prim]; simp only [c_mul2_evp];
end Oracle.Single.Code
end mul2

section max
namespace Oracle.Single.Code
def c_max := c_if_le_te.comp₄ left right right left
@[cp] theorem c_max_prim : code_prim c_max := by unfold c_max; apply_cp
@[simp, evp_simps] theorem c_max_evp {O : ℕ → ℕ} : evalp O c_max = unpaired2 Nat.max := by
  simpa only [c_max, evp_simps] using by rfl
@[simp, ev_simps] theorem c_max_ev {O : ℕ → ℕ} : eval O c_max = unpaired2 Nat.max := by
  rw [← evalp_eq_eval c_max_prim]; simp only [c_max_evp]
end Oracle.Single.Code
end max
