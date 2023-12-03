/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

/-! # `norm_num` extensions for factorials

Extensions for `norm_num` that compute `Nat.factorial`, `Nat.ascFactorial` and `Nat.descFactorial`.

This is done by reducing each of these to `ascFactorial`, which is computed using a divide and
conquer strategy that improves performance and avoids exceeding the recursion depth.

-/

namespace Mathlib.Meta.NormNum

open Nat Qq Lean Elab.Tactic Qq Meta

lemma ascFactorial_mul_ascFactorial (n l k : ℕ) :
    n.ascFactorial l * (n + l).ascFactorial k = n.ascFactorial (l + k) := by
  apply mul_left_cancel₀ (factorial_pos n).ne.symm
  simp [factorial_mul_ascFactorial, ← mul_assoc, add_assoc]

lemma asc_factorial_aux (n l m a b : ℕ) (h₁ : n.ascFactorial l = a)
    (h₂ : (n + l).ascFactorial m = b) : n.ascFactorial (l + m) = a * b := by
  rw [← h₁, ← h₂]
  symm
  apply ascFactorial_mul_ascFactorial

/-- Calculate `n.ascFactorial l` and return this value along with a proof of the result. -/
partial def proveAscFactorial (n l : ℕ) : (result : Q(ℕ)) × Q(($n).ascFactorial $l = $result) :=
  if l ≤ 50 then
    let res : Q(ℕ) := mkRawNatLit (n.ascFactorial l)
    ⟨res, (q(Eq.refl $res) : Expr)⟩
  else
    let m : ℕ := l / 2
    let r : ℕ := l - m
    let ⟨a, a_prf⟩ := proveAscFactorial n m
    let ⟨b, b_prf⟩ := proveAscFactorial (n + m) r
    let prf : Expr := q(asc_factorial_aux $n $m $r $a $b $a_prf $b_prf)
    ⟨mkRawNatLit (a.natLit! * b.natLit!), prf⟩

lemma isNat_factorial {n x : ℕ} (h₁ : IsNat n x) (a : ℕ) (h₂ : (0).ascFactorial x = a) :
    IsNat (n !) a := by
  constructor
  simp [zero_ascFactorial, h₁.out, ← h₂]

/-- Evaluates the `Nat.factorial` function. -/
@[norm_num Nat.factorial _]
def evalNatFactorial : NormNumExt where eval {u α} e := do
  let .app _ (x : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨val, ascPrf⟩ := proveAscFactorial 0 ex.natLit!
  let ascPrf' : Q(ascFactorial 0 $ex = $val) := ascPrf
  let prf := q(isNat_factorial $p $val $ascPrf')
  return .isNat sℕ q($val) prf

lemma isNat_ascFactorial {n x l y : ℕ} (h₁ : IsNat n x) (h₂ : IsNat l y) (a : ℕ)
    (p : (x).ascFactorial y = a) : IsNat (n.ascFactorial l) a := by
  constructor
  simp [h₁.out, h₂.out, ← p]

/-- Evaluates the Nat.ascFactorial function. -/
@[norm_num Nat.ascFactorial _ _]
def evalNatAscFactorial : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨ex₁, p₁⟩ ← deriveNat x sℕ
  let ⟨ex₂, p₂⟩ ← deriveNat y sℕ
  let ⟨val, ascPrf⟩ := proveAscFactorial (ex₁.natLit!) (ex₂.natLit!)
  let ascPrf' : Q(ascFactorial $ex₁ $ex₂ = $val) := ascPrf
  let prf := q(isNat_ascFactorial $p₁ $p₂ $val $ascPrf')
  return .isNat sℕ q($val) prf

lemma isNat_descFactorial {n x l y : ℕ} (z : ℕ) (h₁ : IsNat n x) (h₂ : IsNat l y)
    (h₃ : x = z + y) (a : ℕ) (p : z.ascFactorial y = a) : IsNat (n.descFactorial l) a := by
  constructor
  simp [h₁.out, h₂.out, ← p, h₃]
  apply Nat.add_descFactorial_eq_ascFactorial

lemma isNat_descFactorial_zero {n x l y : ℕ} (z : ℕ) (h₁ : IsNat n x) (h₂ : IsNat l y)
    (h₃ : y = z + x + 1) : IsNat (n.descFactorial l) 0 := by
  constructor
  simp [h₁.out, h₂.out, h₃]

private partial def evalNatDescFactorialNotZero {x' y' : Q(ℕ)} (x y z : Q(ℕ)) (px : Q(IsNat $x' $x))
    (py : Q(IsNat $y' $y)) : Expr × Expr :=
  let eq_prf : Q($x = $z + $y) := (q(Eq.refl $x) : Expr)
  let ⟨val, ascPrf⟩ := proveAscFactorial (z.natLit!) (y.natLit!)
  let ascPrf : Q(ascFactorial $z $y = $val) := ascPrf
  let prf : Q(IsNat (descFactorial $x' $y') $val) :=
    q(isNat_descFactorial $z $px $py $eq_prf $val $ascPrf)
  (val, prf)

private partial def evalNatDescFactorialZero {x' y' : Q(ℕ)} (x y z : Q(ℕ)) (px : Q(IsNat $x' $x))
    (py : Q(IsNat $y' $y)) : Expr × Expr :=
  let eq_prf : Q($y = $z + $x + 1) := (q(Eq.refl $y) : Expr)
  let prf : Q(IsNat (descFactorial $x' $y') 0) :=
    q(isNat_descFactorial_zero $z $px $py $eq_prf)
  (mkRawNatLit 0, prf)

/-- Evaluates the Nat.ascFactorial function. -/
@[norm_num Nat.descFactorial _ _]
def evalNatDescFactorial : NormNumExt where eval {u α} e := do
  let .app (.app _ (x' : Q(ℕ))) (y' : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨x, p₁⟩ ← deriveNat x' sℕ
  let ⟨y, p₂⟩ ← deriveNat y' sℕ
  if x.natLit! ≥ y.natLit! then
    let z : ℕ := x.natLit! - y.natLit!
    let (val, prf) := evalNatDescFactorialNotZero (x' := x') (y' := y') x y (mkRawNatLit z) p₁ p₂
    return .isNat sℕ val prf
  else
    let z : ℕ := y.natLit! - x.natLit! - 1
    let (val, prf) := evalNatDescFactorialZero (x' := x') (y' := y') x y (mkRawNatLit z) p₁ p₂
    return .isNat sℕ val prf
