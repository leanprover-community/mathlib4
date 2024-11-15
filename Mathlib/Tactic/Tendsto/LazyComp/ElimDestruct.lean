import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tendsto.Main
import Qq

set_option linter.style.header false
set_option linter.all false
set_option linter.style.longLine false


open Filter Asymptotics TendstoTactic Stream' Seq

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}


def PreMS.nil : PreMS (basis_hd :: basis_tl) := .nil
def PreMS.cons (hd : (ℝ × PreMS basis_tl)) (tl : PreMS (basis_hd :: basis_tl)) :
    PreMS (basis_hd :: basis_tl) := .cons hd tl

theorem one_const : PreMS.one [] = 1 := by rfl
theorem neg_const (x : PreMS []) : (x.neg) = -x := by simp [PreMS.neg, PreMS.mulConst]
theorem add_const (x y : PreMS []) : (PreMS.add x y) = x + y := by rfl
theorem mul_const (x y : PreMS []) : (PreMS.mul x y) = x * y := by simp [PreMS.mul]

theorem monomial_zero_destruct : destruct (PreMS.monomial (basis_hd :: basis_tl) 0) =
    .some ((1, PreMS.one _), @PreMS.nil basis_hd basis_tl) := by
  rfl

theorem monomial_succ_destruct (m : ℕ) : destruct (PreMS.monomial (basis_hd :: basis_tl) (m + 1)) =
    .some ((0, PreMS.monomial basis_tl m), @PreMS.nil basis_hd basis_tl) := by
  rfl

theorem neg_destruct (ms : PreMS (basis_hd :: basis_tl)) : destruct ms.neg =
    match destruct ms with
    | none => none
    | some ((exp, coef), tl) => .some ((exp, coef.neg), PreMS.neg (basis := basis_hd :: basis_tl) tl) := by
  cases ms <;> simp

theorem add_destruct (x y : PreMS (basis_hd :: basis_tl)) : destruct (x.add y) =
    match destruct x, destruct y with
    | none, none => none
    | none, some r => some r
    | some r, none => some r
    | some ((x_exp, x_coef), x_tl), some ((y_exp, y_coef), y_tl) =>
      if y_exp < x_exp then
        .some ((x_exp, x_coef), (PreMS.add x_tl y))
      else if x_exp < y_exp then
        .some ((y_exp, y_coef), (PreMS.add x y_tl))
      else
        .some ((x_exp, x_coef.add y_coef), (@PreMS.add (basis_hd :: basis_tl) x_tl y_tl)) := by
  cases x <;> cases y <;> simp [PreMS.add_nil]
  all_goals sorry -- we need translate `+` back to `.add`

theorem mul_destruct (x y : PreMS (basis_hd :: basis_tl)) : destruct (x.mul y) =
    match destruct x, destruct y with
    | none, _ => none
    | _, none => none
    | some ((x_exp, x_coef), x_tl), some ((y_exp, y_coef), y_tl) =>
      .some ((x_exp + y_exp, x_coef.mul y_coef), ((PreMS.mulMonomial y_tl x_coef x_exp).add
      (PreMS.mul x_tl y))) := by
  cases' x with x_exp x_coef x_tl <;> cases' y with y_exp y_coef y_tl <;> simp
  rfl

open Lean Elab Meta Tactic Qq

simproc elimDestruct (Stream'.Seq.destruct _) := fun e => do
  match e.getAppFnArgs with
  | (``Stream'.Seq.destruct, #[_, ms]) =>
    match (← inferType ms).getAppFnArgs with
    | (``PreMS, #[basis]) =>
      match basis.getAppFnArgs with
      | (``List.nil, _) =>
        return .continue
      | (``List.cons, #[_, basis_hd, basis_tl]) =>
        let basis_tl : Q(Basis) := basis_tl
        match ms.getAppFnArgs with
        | (``PreMS.nil, _) =>
          return .done {
            expr := ← mkAppOptM ``Option.none #[q(Seq1 (ℝ × PreMS $basis_tl))],
            proof? := ← mkAppOptM ``Stream'.Seq.destruct_nil #[q(ℝ × (PreMS $basis_tl))]
          }
        | (``PreMS.cons, #[_, _, hd, tl]) =>
          return .done {
            expr := ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[hd, tl]],
            proof? := ← mkAppM ``Stream'.Seq.destruct_cons #[hd, tl]
          }
        | (``PreMS.monomial, #[basis, n]) =>
          match (← getNatValue? n).get! with
          | 0 =>
            let pf ← mkAppOptM ``monomial_zero_destruct #[basis_hd, basis_tl]
            let some (_, _, rhs) := (← inferType pf).eq? | return .continue
            return .visit {expr := rhs, proof? := pf}
          | m + 1 =>
            let pf ← mkAppOptM ``monomial_succ_destruct #[basis_hd, basis_tl, mkNatLit m]
            let some (_, _, rhs) := (← inferType pf).eq? | return .continue
            return .visit {expr := rhs, proof? := pf}
        | (``PreMS.neg, #[_, arg]) =>
          let pf ← mkAppOptM ``neg_destruct #[none, none, arg]
          let some (_, _, rhs) := (← inferType pf).eq? | return .continue
          return .visit {expr := rhs, proof? := pf}
        | (``PreMS.add, #[_, arg1, arg2]) =>
          let pf ← mkAppOptM ``add_destruct #[none, none, arg1, arg2]
          let some (_, _, rhs) := (← inferType pf).eq? | return .continue
          return .visit {expr := rhs, proof? := pf}
        | (``PreMS.mul, #[_, arg1, arg2]) =>
          let pf ← mkAppOptM ``mul_destruct #[none, none, arg1, arg2]
          let some (_, _, rhs) := (← inferType pf).eq? | return .continue
          return .visit {expr := rhs, proof? := pf}
        | _ => return .continue
      | _ => return .continue
    | _ => return .continue
  | _ => return .continue

syntax "elim_destruct" : tactic
macro_rules
| `(tactic| elim_destruct) =>
    `(tactic|
      repeat (
        simp only [elimDestruct, one_const, neg_const, add_const, mul_const];
        try norm_num1;
        try simp only [↓reduceIte, one_const, neg_const, add_const, mul_const]
      )
    )


namespace Test

def basis : List (ℝ → ℝ) := [fun (x : ℝ) ↦ x]
theorem basis_wo : MS.WellOrderedBasis basis := by sorry
theorem zero_aux : 0 < basis.length := by simp [basis]


def ms_monom : PreMS [id] := PreMS.monomial [id] 0

def ms_nil : PreMS [id] := PreMS.nil

def ms_cons : PreMS [id] := PreMS.cons (1, 1) .nil -- x monomial

def ms_cons2 : PreMS [id] := PreMS.cons (2, 1) ms_cons -- x^2 + x

example : destruct ms_nil = .none := by
  unfold ms_nil
  elim_destruct

example : destruct ms_cons = .some ((1, 1), .nil) := by
  unfold ms_cons
  elim_destruct

example : destruct (ms_nil.neg) = .none := by
  unfold ms_nil
  elim_destruct

example : destruct (ms_nil.add ms_nil) = .none := by
  unfold ms_nil
  elim_destruct

example : destruct (ms_nil.add ms_cons) = .some ((1, 1), .nil) := by
  unfold ms_nil ms_cons
  elim_destruct

example : destruct (ms_cons.add ms_nil) = .some ((1, 1), .nil) := by
  unfold ms_nil ms_cons
  elim_destruct

example : destruct (ms_cons.add ms_cons) = .some ((1, 2), .nil) := by
  unfold ms_cons
  elim_destruct
  sorry -- it's ok we don't need tail

example : destruct (ms_cons.add ms_cons2) = .some ((2, 1), .nil) := by
  unfold ms_cons ms_cons2
  elim_destruct
  sorry -- it's ok we don't need tail

example : destruct (ms_nil.mul ms_nil) = .none := by
  unfold ms_nil
  elim_destruct

example : destruct (ms_nil.mul ms_cons) = .none := by
  unfold ms_nil ms_cons
  elim_destruct

example : destruct (ms_cons.mul ms_nil) = .none := by
  unfold ms_nil ms_cons
  elim_destruct

example : destruct (ms_cons.mul ms_cons) = .some ((2, 1), .nil) := by
  unfold ms_cons
  elim_destruct
  sorry -- it's ok we don't need tail


example : destruct ms_monom = .some ((1, 1), @PreMS.nil id []) := by
  unfold ms_monom
  elim_destruct
  -- elim_destruct

example :
    let ms_monom2 : PreMS [id, id] := PreMS.monomial [id, id] 1;
    destruct ms_monom2 = .some ((0, PreMS.monomial [id] 0), @PreMS.nil id [id]) := by
  intro ms_monom2
  unfold ms_monom2
  elim_destruct

example : (if (1 : ℝ) < (3/2 : ℝ) then 1 else 0) = 1 := by
  norm_num1
  simp only [↓reduceIte]

end Test
