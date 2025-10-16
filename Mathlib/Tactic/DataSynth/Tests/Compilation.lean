import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.DataSynth
import Mathlib.Tactic.NormNum

inductive Expr
  | var (n : ℕ)
  | const (n : ℤ)
  | add (x y : Expr)
  | mul (x y : Expr)
  | zmul (n : ℤ) (x : Expr)


variable {R : Type*} [Ring R]

def Expr.eval (vars : List R) (e : Expr) : R :=
  match e with
  | var n => vars.getD n 0
  | add x y => x.eval vars + y.eval vars
  | mul x y => x.eval vars * y.eval vars
  | zmul n x => n • x.eval vars
  | const n => n

/-- Is `x` one of the `vars`? Return the index `n`. -/
@[data_synth out n]
def IsVar (vars : List R) (x : R) (n : Nat) : Prop :=
  x = vars.getD n 0

@[data_synth]
theorem isVar_head (vars : List R) (x : R) : IsVar (x :: vars) x 0 := by
  simp[IsVar]

@[data_synth]
theorem isVar_tail (vars : List R) (y x : R) {n} (hx : IsVar vars x n) :
    IsVar (y :: vars) x (n+1) := by
  simp_all [IsVar]


/-- Turns expression in `R` into `Expr` -/
@[data_synth out e]
def CompileExpr (vars : List R) (x : R) (e : Expr) : Prop :=
  x = e.eval vars

variable (vars : List R)

@[data_synth]
theorem compileExpr_var (x : R) {n} (hx : IsVar vars x n) :
    CompileExpr vars x (.var n) := by
  simp_all [IsVar,CompileExpr,Expr.eval]

@[data_synth]
theorem compileExpr_const_int (n : ℤ) :
    CompileExpr vars (n : R) (.const n) := by
  simp_all [CompileExpr,Expr.eval]

@[data_synth]
theorem compileExpr_const_nat (n : ℕ) :
    CompileExpr vars (n : R) (.const n) := by
  simp_all [CompileExpr,Expr.eval]

@[data_synth]
theorem compileExpr_const_ofNat (n : ℕ) :
    CompileExpr vars (OfNat.ofNat (α:=R) n) (.const n) := by
  simp_all [CompileExpr,Expr.eval]
  sorry

@[data_synth]
theorem compileExpr_add (x y : R) {e e'}
    (hx : CompileExpr vars x e) (hy : CompileExpr vars y e') :
    CompileExpr vars (x + y) (.add e e') := by
  simp_all [CompileExpr,Expr.eval]

@[data_synth]
theorem compileExpr_mul (x y : R) {e e'}
    (hx : CompileExpr vars x e) (hy : CompileExpr vars y e') :
    CompileExpr vars (x * y) (.mul e e') := by
  simp_all [CompileExpr,Expr.eval]

@[data_synth]
theorem compileExpr_zmul_int (n : ℤ) (x : R) {e} (hx : CompileExpr vars x e) :
    CompileExpr vars (n • x) (.zmul n e) := by
  simp_all [CompileExpr,Expr.eval]

@[data_synth]
theorem compileExpr_zmul_nat (n : ℕ) (x : R) {e} (hx : CompileExpr vars x e) :
    CompileExpr vars (n • x) (.zmul n e) := by
  simp_all [CompileExpr,Expr.eval]


set_option pp.proofs false

variable (x y : R)

#check (by data_synth : CompileExpr [x,y] x _)
#check (by data_synth : CompileExpr [x,y] y _)
#check (by data_synth : CompileExpr [x,y] ((-3:ℤ) : R) _)
#check (by data_synth : CompileExpr [x,y] (x*y*x+5•x) _)
