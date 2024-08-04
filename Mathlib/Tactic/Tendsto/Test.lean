import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real


import Qq
----------------------------------------------------------------
open Lean Qq

inductive MyException where
| SignOracleException

abbrev MyM := Except MyException

inductive SignOracleResult (x : Q(ℝ)) where
| neg (proof : Expr)
| pos (proof : Expr)
| zero (proof : Expr)

def SignOracle : Type := (x : Q(ℝ)) → MyM (SignOracleResult x)
-------------------------------------------------------------------


inductive MS : ℕ → Type where
| const (c : ℝ) : MS 0
| nil {n : ℕ} : MS n
| cons {n : ℕ} : MS n → ℝ → MS (n + 1) → MS (n + 1)

-- MS 0 = ℝ
-- MS n + 1 = List (MS n × ℝ)

noncomputable def MS.eval {n : ℕ} (basis : Mathlib.Vector (ℝ → ℝ) n) (x : ℝ) (F : MS n) : ℝ :=
  match F with
  | .const c => c
  | .nil => 0
  | .cons coef deg tail => (basis.head x)^deg * (coef.eval basis.tail x) + (tail.eval basis x)

def ex_1 : MS 0 := .const 1
def ex_x : MS 1 := .cons ex_1 1 .nil
def ex_x_1 : MS 1 := .cons ex_1 0 ex_x -- x + 1
def ex : MS 2 := .cons ex_x_1 1 .nil -- (x + 1) * e^x

example : ex_x_1.eval ⟨[id], rfl⟩ 3 = 4 := by
  simp [ex_x_1, MS.eval, Mathlib.Vector.head]
  ring_nf

example : ex.eval ⟨[Real.exp, id], rfl⟩ 3 = 4 * Real.exp 3 := by
  simp [ex_x_1, MS.eval, Mathlib.Vector.head, Mathlib.Vector.tail]
  ring_nf

noncomputable def MS.add {n : ℕ} (F G : MS n) : MS n :=
  match F, G with
  | .nil, G => G
  | F, .nil => F
  | .const c₁, .const c₂ => .const (c₁ + c₂)
  | .cons F_coef F_deg F_tail, .cons G_coef G_deg G_tail =>
    if F_deg < G_deg then
      .cons F_coef F_deg (MS.add F_tail (.cons G_coef G_deg G_tail))
    else if G_deg < F_deg then
      .cons G_coef G_deg (MS.add (.cons F_coef F_deg F_tail) G_tail)
    else
      .cons (MS.add F_coef G_coef) F_deg (MS.add F_tail G_tail)

example : (MS.add ex_x ex_x_1).eval ⟨[id], rfl⟩ 3 = 7 := by
  simp [ex_x, ex_x_1, MS.eval, MS.add]
  norm_num
  simp [ex_1, ex_x, ex_x_1, MS.eval, MS.add, Mathlib.Vector.head, Mathlib.Vector.tail]
  norm_num

noncomputable instance {n : ℕ} : Add (MS n) where
  add := MS.add

def MS.neg {n : ℕ} (F : MS n) : MS n :=
  match F with
  | .const c => .const (-c)
  | .nil => .nil
  | .cons coef deg tail => .cons coef.neg deg tail.neg

instance {n : ℕ} : Neg (MS n) where
  neg := MS.neg

def MS.ofReal {n : ℕ} (c : ℝ) : MS n :=
  match n with
  | 0 => .const c
  | _ + 1 => .cons (MS.ofReal c) 0 .nil

example : (MS.ofReal 4 : MS 5).eval ⟨[id, id, id, id, id], rfl⟩ 111 = 4 := by
  simp [MS.ofReal, MS.eval]

instance {n : ℕ} : Coe ℝ (MS n) where
  coe c := MS.ofReal c
