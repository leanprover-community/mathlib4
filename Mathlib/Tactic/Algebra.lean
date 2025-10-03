/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Tactic.Module

set_option linter.all false

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List Mathlib.Tactic.Module

namespace Mathlib.Tactic.Algebra

open Mathlib.Meta AtomM

attribute [local instance] monadLiftOptionMetaM

/-
TODOs:
* Handle division, inversion, algebraMap.
* `match_coefficients` tactic that normalizes polynomials and matches corresponding coefficients.
* Handle `algebraMap` in some way. Either with a preprocessing step or as a special case in `eval`
* Handle expressions specific to `Polynomial`: Simplify Polynomial.map (note it sends X ↦ X),
  and handle the Algebra (Polynomial _) (Polynomial _) instance gracefully.
* The new normal form puts the coefficients an the end as `x * y * 1 • r` and `X^n * C a`. We really
  ought to put it in front.
-/

section ExSum

set_option linter.style.longLine false


section lemmas

open NormNum
variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem add_overlap_nonzero {a₁ a₂ b₁ b₂ c₁ c₂ : R}
    (h₁ : a₁ + b₁ = c₁) (h₂ : a₂ + b₂ = c₂) :
    a₁ + a₂ + (b₁ + b₂) = c₁ + c₂ := by
  rw [← h₁, ← h₂, add_assoc, add_assoc, add_left_comm a₂]

theorem add_overlap_zero {a₁ a₂ b₁ b₂ c₂ : R}
    (h₁ : IsNat (a₁ + b₁) 0) (h₂ : a₂ + b₂ = c₂) :
    a₁ + a₂ + (b₁ + b₂) = c₂ := by
  sorry

section Nat
variable {n d : ℕ}
theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm
theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm
theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp
theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm
theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
theorem int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp
theorem nnrat_rawCast {R} [DivisionSemiring R] :
    (NNRat.rawCast n d : R) = Nat.rawCast n / Nat.rawCast d := by simp
theorem rat_rawCast_neg {R} [DivisionRing R] :
    (Rat.rawCast (.negOfNat n) d : R) = Int.rawCast (.negOfNat n) / Nat.rawCast d := by simp
end Nat

theorem mul_pow_add_overlap_zero {b₁ b₂ x : A} {e : ℕ}
    (h : IsNat (b₁ + b₂) 0) :
    IsNat (x ^ e * b₁ + x ^ e * b₂) 0 := by
  sorry

theorem smul_add_left_zero {r s : R} {a b : A} (h : r + s = 0) :
    IsNat (r • a + s • b) 0 := by
  sorry

theorem smul_add_smul_same {r s t : R} {a b : A} (ha : a = b) (ht : r + s = t) :
    r • a + s • b = t • a := by
  rw [ha, ← add_smul, ht]

theorem smul_congr {r r' : R} {a a' : A} {ef : A} (hr : r = r') (ha : a = a') (hf : r' • a' = ef) :
    r • a = ef := by
  rw [hr, ha, hf]

theorem eval_smul_eq {e : A} {r : R} {a : A} {ef : A}
    (he : e = r • a) (hf : r • a = ef) :
    e = ef := by
  rw [he, hf]

theorem mul_pow_add_overlap_nonzero {x : A} {e : ℕ} {b₁ b₂ c : A}
    (h : b₁ + b₂ = c) :
    x ^ e * b₁ + x ^ e * b₂ = x ^ e * c := by
  rw [← mul_add, h]

theorem add_add_add_comm {a₁ a₂ b₁ b₂ c : A}
    (h : a₂ + (b₁ + b₂) = c) :
    a₁ + a₂ + (b₁ + b₂) = a₁ + c := by
  rw [add_assoc, h]

theorem add_add_add_comm' {a₁ a₂ b₁ b₂ c : A}
    (h : (a₁ + a₂) + b₂ = c) :
    a₁ + a₂ + (b₁ + b₂) = b₁ + c := by
  sorry

theorem neg_smul_one {r s : R} [Ring R] [Ring A]
    (h : -r = s) :
    -(r • (1 : A)) = s • 1 := by
  sorry

theorem neg_pow_mul (x : A) (e : ℕ) {b c : A} [Ring R] [Ring A]
    (h : -b = c) :
    -(x ^ e * b) = x ^ e * c := by
  sorry

theorem neg_add {a b c d : A} [Ring R] [Ring A]
    (ha : -a = c) (hb : -b = d) :
    -(a + b) = c + d := by
  sorry

theorem sub_eq_add_neg' {a b c d : A} [Ring R] [Ring A]
    (hc : -b = c) (hd : a + c = d) :
    a - b = d := by
  sorry

theorem isNat_zero_eq {a : A} [AddMonoidWithOne A]
    (h : IsNat a 0) :
    a = 0 := by
  sorry

theorem isInt_negOfNat_eq {a : A} {lit : ℕ} [Ring R] [Ring A]
    (h : IsInt a (Int.negOfNat lit)) :
    a = (Int.rawCast (Int.negOfNat lit) + 0 : R) • (1 : A) + 0 := by
  sorry

theorem pow_eq_pow_mul_smul_one {a : A} {b : ℕ} :
    a ^ b = (a + 0) ^ b * (Nat.rawCast 1 + 0 : R) • (1 : A) := by
  sorry

theorem pow_eq_pow_mul_smul_one_add_zero {a : A} {b : ℕ} :
    a ^ b = a ^ b * (Nat.rawCast 1 + 0 : R) • (1 : A) + 0 := by
  sorry

theorem smul_one_pow {r r' : R} {b : ℕ}
    (h : r ^ (b + 0) = r') :
    (r • (1 : A)) ^ b = r' • 1 := by
  sorry

theorem pow_mul_pow {x : A} {e e' : ℕ} {b c : A} {n : ℕ}
    (he : e * n = e') (hb : b ^ n = c) :
    (x ^ e * b) ^ n = x ^ e' * c := by
  sorry

theorem pow_even {a b c : A} {m : ℕ}
    (hb : a ^ m = b) (hc : b * b = c) :
    a ^ (m+m) = c := by
  sorry

theorem pow_odd {a b c d : A} {m : ℕ}
    (hb : a ^ m = b) (hc : b * b = c) (hd : c * a = d) :
    a ^ (m+m+1) = d := by
  sorry

theorem pow_rawCast_one {a : A} :
    a ^ Nat.rawCast (nat_lit 1) = a := by
  sorry

theorem zero_pow_pos {b : ℕ} (h : 0 < b) :
    (0 : A) ^ b = 0 := by
  sorry

theorem pow_add_zero {a c : A} {b : ℕ}
    (h : a ^ b = c) :
    (a + 0) ^ b = c + 0 := by
  sorry

theorem pow_factored {a d e : A} {b e' k : ℕ}
    (hb : b = e' * k) (hd : a ^ e' = d) (he : d ^ k = e) :
    a ^ b = e := by
  sorry

theorem pow_zero_eq {a : A} :
    a ^ 0 = (Nat.rawCast 1 + 0 : R) • (1 : A) + 0 := by
  sorry

theorem pow_add {a c₁ c₂ d : A} {b₁ b₂ : ℕ}
    (hc₁ : a ^ b₁ = c₁) (hc₂ : a ^ b₂ = c₂) (hd : c₁ * c₂ = d) :
    a ^ (b₁ + b₂) = d := by
  sorry

theorem atom_eq_pow_one_mul_smul_one_add_zero {a : A} :
    a = a ^ Nat.rawCast 1 * (Nat.rawCast 1 + 0 : R) • (1 : A) + 0 := by
  sorry

theorem atom_eq_pow_one_mul_smul_one_add_zero' {a e : A}
    (h : a = e) :
    a = e ^ Nat.rawCast 1 * (Nat.rawCast 1 + 0 : R) • (1 : A) + 0 := by
  sorry

theorem eval_add {a b a' b' c : A}
    (ha : a = a') (hb : b = b') (hc : a' + b' = c) :
    a + b = c := by
  sorry

theorem eval_neg {a a' b : A} [Ring A]
    (ha : a = a') (hb : -a' = b) :
    -a = b := by
  sorry

theorem eval_sub {a b a' b' c : A} [Ring A]
    (ha : a = a') (hb : b = b') (hc : a' - b' = c) :
    a - b = c := by
  sorry

theorem eval_mul {a b a' b' c : A}
    (ha : a = a') (hb : b = b') (hc : a' * b' = c) :
    a * b = c := by
  sorry

theorem eval_pow {a a' c : A} {b b' : ℕ}
    (ha : a = a') (hb : b = b') (hc : a' ^ b' = c) :
    a ^ b = c := by
  sorry

theorem smul_smul_one {r s t : R}
    (h : r * s = t) :
    r • s • (1 : A) = t • 1 := by
  rw [smul_smul, h]

theorem smul_mul_assoc {r : R} {x : A} {e : ℕ} {b c : A}
    (h : r • b = c) :
    r • (x ^ e * b) = x ^ e * c := by
  sorry

theorem smul_add {r : R} {a b c d : A}
    (ha : r • a = c) (hb : r • b = d) :
    r • (a + b) = c + d := by
  sorry

theorem smul_one_mul_smul_one {r s t : R}
    (h : r * s = t) :
    r • (1 : A) * s • 1 = t • 1 := by
  sorry

theorem pow_mul_mul_smul_one {x : A} {e : ℕ} {b d : A} {r : R}
    (h : b * (r • 1) = d) :
    x ^ e * b * r • 1 = x ^ e * d := by
  sorry

theorem smul_one_mul_pow_mul {r : R} {x : A} {e : ℕ} {b c : A}
    (h : r • 1 * b = c) :
    r • 1 * (x ^ e * b) = x ^ e * c := by
  sorry

theorem pow_mul_mul_pow_mul {x : A} {ea eb e : ℕ} {b₁ b₂ c : A}
    (pe : ea + eb = e) (pc : b₁ * b₂ = c) :
    x ^ ea * b₁ * (x ^ eb * b₂) = x ^ e * c := by
  sorry

theorem pow_mul_mul_assoc {x xb : A} {ea eb : ℕ} {b₁ b c : A}
    (pc : b₁ * (xb ^ eb * b) = c) :
    x ^ ea * b₁ * (xb ^ eb * b) = x ^ ea * c := by
  sorry

theorem mul_pow_mul_assoc {xa xb : A} {ea eb : ℕ} {b₁ b c : A}
    (pc : xa ^ ea * b₁ * b = c) :
    xa ^ ea * b₁ * (xb ^ eb * b) = xb ^ eb * c := by
  sorry

theorem mul_add_of_add {a a₁ b c₁ c₂ c : A}
    (pb₁' : a * a₁ = c₁) (pt : a * b = c₂) (pd : c₁ + 0 + c₂ = c) :
    a * (a₁ + b) = c := by
  sorry

theorem add_mul_of_add {a₁ a₂ b c₁ c₂ c : A}
    (pc₁ : a₁ * b = c₁) (pc₂ : a₂ * b = c₂) (pd : c₁ + c₂ = c) :
    (a₁ + a₂) * b = c := by
  sorry

end lemmas

open Ring in
mutual

/-- The base `e` of a normalized exponent expression in an algebra context. -/
inductive ExBase : ∀ {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {_ : Q(CommSemiring $R)}
  {_ : Q(CommSemiring $A)} (_ : Q(Algebra $R $A)), (e : Q($A)) → Type
  /-- An atomic expression `e` with id `id`. -/
  | atom {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
      {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
      {sAlg : Q(Algebra $R $A)} {e : Q($A)} (id : ℕ) : ExBase q($sAlg) e
  /-- A sum of monomials. -/
  | sum {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
      {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
      {sAlg : Q(Algebra $R $A)} {e : Q($A)} (_ : ExSum q($sAlg) e) : ExBase q($sAlg) e

/-- A monomial in an algebra context, which is a product of powers of `ExBase` expressions,
terminated by a scalar multiplication. -/
inductive ExProd : ∀ {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {_ : Q(CommSemiring $R)}
  {_ : Q(CommSemiring $A)} (_ : Q(Algebra $R $A)), (e : Q($A)) → Type
  /-- A scalar multiplication `r • a` where `r` is a coefficient from the base ring. -/
  | smul {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
      {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
      {sAlg : Q(Algebra $R $A)} {r : Q($R)} (vr : Ring.ExSum q($sR) r)
      : ExProd q($sAlg) q($r • 1 : $A)
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is an `ExBase`
  and `e` is an `Ring.ExProd` representing a monomial expression in `ℕ`. -/
  | mul {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
      {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
      {sAlg : Q(Algebra $R $A)} {x : Q($A)} {e : Q(ℕ)} {b : Q($A)} :
    ExBase q($sAlg) x → Ring.ExProd Ring.sℕ e → ExProd q($sAlg) b →
    ExProd q($sAlg) q($x ^ $e * $b)

/-- A polynomial expression, which is a sum of monomials. -/
inductive ExSum : ∀ {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {_ : Q(CommSemiring $R)}
  {_ : Q(CommSemiring $A)} (_ : Q(Algebra $R $A)), (a : Q($A)) → Type
  | zero {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
      {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)}
      {sAlg : Q(Algebra $R $A)} : ExSum q($sAlg) q(0:$A)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
    {a b : Q($A)} {sAlg : Q(Algebra $R $A)} :
    ExProd q($sAlg) a → ExSum q($sAlg) b →
      ExSum q($sAlg) q($a + $b)

end

mutual -- partial only to speed up compilation

/-- Equality test for expressions. This is not a `BEq` instance because it is heterogeneous. -/
partial def ExBase.eq
    {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} {sAlg : Q(Algebra $R $A)} {a b : Q($A)} :
    ExBase sAlg a → ExBase sAlg b → Bool
  | .atom i, .atom j => i == j
  | .sum a, .sum b => a.eq b
  | _, _ => false

@[inherit_doc ExBase.eq]
partial def ExProd.eq
    {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} {sAlg : Q(Algebra $R $A)} {a b : Q($A)} :
    ExProd sAlg a → ExProd sAlg b → Bool
  | .smul vr₁, .smul vr₂ => vr₁.eq vr₂
  | .mul vx₁ ve₁ vb₁, .mul vx₂ ve₂ vb₂ => vx₁.eq vx₂ && ve₁.eq ve₂ && vb₁.eq vb₂
  | _, _ => false

@[inherit_doc ExBase.eq]
partial def ExSum.eq
    {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} {sAlg : Q(Algebra $R $A)} {a b : Q($A)} :
    ExSum sAlg a → ExSum sAlg b → Bool
  | .zero, .zero => true
  | .add a₁ a₂, .add b₁ b₂ => a₁.eq b₁ && a₂.eq b₂
  | _, _ => false

end

mutual -- partial only to speed up compilation
/--
A total order on normalized expressions.
This is not an `Ord` instance because it is heterogeneous.
-/
partial def ExBase.cmp
    {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} {sAlg : Q(Algebra $R $A)} {a b : Q($A)} :
    ExBase sAlg a → ExBase sAlg b → Ordering
  | .atom i, .atom j => compare i j
  | .sum a, .sum b => a.cmp b
  | .atom .., .sum .. => .lt
  | .sum .., .atom .. => .gt

@[inherit_doc ExBase.cmp]
partial def ExProd.cmp
    {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} {sAlg : Q(Algebra $R $A)} {a b : Q($A)} :
    ExProd sAlg a → ExProd sAlg b → Ordering
  | .smul vr₁, .smul vr₂ => vr₁.cmp vr₂
  | .mul vx₁ ve₁ vb₁, .mul vx₂ ve₂ vb₂ => (vx₁.cmp vx₂).then (ve₁.cmp ve₂) |>.then (vb₁.cmp vb₂)
  | .smul .., .mul .. => .lt
  | .mul .., .smul .. => .gt

@[inherit_doc ExBase.cmp]
partial def ExSum.cmp
    {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} {sAlg : Q(Algebra $R $A)} {a b : Q($A)} :
    ExSum sAlg a → ExSum sAlg b → Ordering
  | .zero, .zero => .eq
  | .add a₁ a₂, .add b₁ b₂ => (a₁.cmp b₁).then (a₂.cmp b₂)
  | .zero, .add .. => .lt
  | .add .., .zero => .gt

end

mutual -- partial only to speed up compilation

/-- Compare the structure of two `ExProd` values, ignoring scalar coefficients.
This is used by `equateScalarsSum` to determine if two monomials have the same structure. -/
partial def ExProd.cmpShape
    {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} {sAlg : Q(Algebra $R $A)} {a b : Q($A)} :
    ExProd sAlg a → ExProd sAlg b → Ordering
  | .smul _, .smul _ => .eq
  | .mul vx₁ ve₁ vb₁, .mul vx₂ ve₂ vb₂ => (vx₁.cmp vx₂).then (ve₁.cmp ve₂) |>.then (vb₁.cmpShape vb₂)
  | .smul .., .mul .. => .lt
  | .mul .., .smul .. => .gt

end

variable
    {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} {sAlg : Q(Algebra $R $A)} {a b : Q($A)}

instance : Inhabited (Σ e, (ExBase sAlg) e) := ⟨default, .atom 0⟩
instance : Inhabited (Σ e, (ExSum sAlg) e) := ⟨_, .zero⟩
instance : Inhabited (Σ e, (ExProd sAlg) e) := ⟨_, .smul .zero⟩

mutual

/-- Converts `ExBase sAlg` to `ExBase sAlg'`, assuming the algebras are defeq. -/
partial def ExBase.cast
    {u v w x : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {R' : Q(Type w)} {A' : Q(Type x)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
    {sR' : Q(CommSemiring $R')} {sA' : Q(CommSemiring $A')}
    {sAlg : Q(Algebra $R $A)} {sAlg' : Q(Algebra $R' $A')} {a : Q($A)} :
    ExBase sAlg a → Σ a, ExBase sAlg' a
  | .atom i => ⟨a, .atom i⟩
  | .sum a => let ⟨_, vb⟩ := a.cast; ⟨_, .sum vb⟩

/-- Converts `ExProd sAlg` to `ExProd sAlg'`, assuming the algebras are defeq. -/
partial def ExProd.cast
    {u v w x : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {R' : Q(Type w)} {A' : Q(Type x)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
    {sR' : Q(CommSemiring $R')} {sA' : Q(CommSemiring $A')}
    {sAlg : Q(Algebra $R $A)} {sAlg' : Q(Algebra $R' $A')} {a : Q($A)} :
    ExProd sAlg a → Σ a, ExProd sAlg' a
  | .smul vr => ⟨_, .smul vr.cast.2⟩
  | .mul vx ve vb => ⟨_, .mul vx.cast.2 ve vb.cast.2⟩

/-- Converts `ExSum sAlg` to `ExSum sAlg'`, assuming the algebras are defeq. -/
partial def ExSum.cast
    {u v w x : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {R' : Q(Type w)} {A' : Q(Type x)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
    {sR' : Q(CommSemiring $R')} {sA' : Q(CommSemiring $A')}
    {sAlg : Q(Algebra $R $A)} {sAlg' : Q(Algebra $R' $A')} {a : Q($A)} :
    ExSum sAlg a → Σ a, ExSum sAlg' a
  | .zero => ⟨_, .zero⟩
  | .add a₁ a₂ => ⟨_, .add a₁.cast.2 a₂.cast.2⟩

end

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A))

def _root_.Mathlib.Tactic.Ring.ExSum.one : Ring.ExSum q($sA) q(Nat.rawCast (nat_lit 1) + 0 : $A) :=
  .add (.const (e := q(Nat.rawCast (nat_lit 1) : $A)) 1 none) .zero

/-- WARNING : n should be a natural literal. -/
def mkNat (n : Q(ℕ)) : Ring.ExSum q($sA) q(Nat.rawCast $n + 0 : $A) :=
  .add (.const (e := q(Nat.rawCast ($n) : $A)) n.natLit! none) .zero

-- omit sA in
-- def mkInt (rA : Q(Ring $A)) (n : Q(ℤ)) (n' : ℤ) : Ring.ExSum q(inferInstance) q(Int.rawCast $n + 0 : $A) :=
--   .add (α := q($A)) (sα := q(inferInstance)) (.const (e := q(Int.rawCast $n)) n' none) .zero

-- def _root_.Mathlib.Tactic.Ring.ExProd.one : Ring.ExProd q($sA) q((nat_lit 1).rawCast : $A) :=
--   .const 1 none

-- def ExSMul.ofExProd (va : Ring.ExProd q($sA) q($a)) : ExSMul q($sAlg) q(((Nat.rawCast (nat_lit 1)) + 0:$R) • $a) :=
--   .smul one va

-- def ExSMul.toExSum (va : ExSMul q($sAlg) q($a)) : ExSum q($sAlg) q($a + 0) :=
--   .add va .zero

section
/-- Embed an exponent (an `ExBase, ExProd` pair) as an `ExProd` by multiplying by 1. -/
def ExBase.toProd {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
    {sAlg : Q(Algebra $R $A)} {a : Q($A)} {b : Q(ℕ)}
    (va : ExBase sAlg a) (vb : Ring.ExProd Ring.sℕ b) :
    ExProd sAlg q($a ^ $b * ((nat_lit 1).rawCast + 0: $R) • (1: $A)) :=
  .mul va vb (.smul (.one (sA := sR) ) (sAlg := sAlg))

/-- Embed `ExProd` in `ExSum` by adding 0. -/
def ExProd.toSum {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
    {sAlg : Q(Algebra $R $A)} {a : Q($A)} (va : ExProd sAlg a) : ExSum sAlg q($a + 0) :=
  .add va .zero
end

namespace ExSum

end ExSum
end ExSum

/- Copied from `Ring` -/
structure Result {u : Lean.Level} {A : Q(Type u)} (E : Q($A) → Type) (e : Q($A)) where
  /-- The normalized result. -/
  expr : Q($A)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A)) (b : Q($A))

open NormNum

/--
Two monomials are said to "overlap" if they differ by a constant factor, in which case the
constants just add. When this happens, the constant may be either zero (if the monomials cancel)
or nonzero (if they add up); the zero case is handled specially.
-/
inductive Overlap (a : Q($A)) where
  /-- The expression `e` (the sum of monomials) is equal to `0`. -/
  | zero (_ : Q(IsNat $a (nat_lit 0)))
  /-- The expression `e` (the sum of monomials) is equal to another monomial
  (with nonzero leading coefficient). -/
  | nonzero (_ : Result (ExProd q($sAlg)) a)

/--
Given monomials `va, vb`, attempts to add them together to get another monomial.
If the monomials are not compatible, returns `none`.
For example, `xy + 2xy = 3xy` is a `.nonzero` overlap, while `xy + xz` returns `none`
and `xy + -xy = 0` is a `.zero` overlap.
-/
def evalAddOverlap {a b : Q($A)} (va : ExProd sAlg a) (vb : ExProd sAlg b) :
    OptionT MetaM (Overlap q($sAlg) q($a + $b)) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .smul vr, .smul vs => do
    let ⟨t, vt, pt⟩ ← Ring.evalAdd q($sR) vr vs
    match vt with
    | .zero .. =>
      return .zero q(smul_add_left_zero $pt)
    | vt =>
      return .nonzero ⟨_, .smul vt, q(smul_add_smul_same rfl $pt)⟩
  | .mul (x := xa) (e := ea) vxa vea va₂, .mul (x := xb) (e := eb) vxb veb vb₂ => do
    guard (vxa.eq vxb && vea.eq veb)
    have : $xa =Q $xb := ⟨⟩
    have : $ea =Q $eb := ⟨⟩
    match ← evalAddOverlap va₂ vb₂ with
    | .zero p => return .zero q(mul_pow_add_overlap_zero $p)
    | .nonzero ⟨_, vc, p⟩ =>
      return .nonzero ⟨_, .mul vxa vea vc, q(mul_pow_add_overlap_nonzero $p)⟩
  | _, _ => OptionT.fail


/-- Adds two polynomials `va, vb` together to get a normalized result polynomial.

* `0 + b = b`
* `a + 0 = a`
* `a * x + a * y = a * (x + y)` (for `x`, `y` coefficients; uses `evalAddOverlap`)
* `(a₁ + a₂) + (b₁ + b₂) = a₁ + (a₂ + (b₁ + b₂))` (if `a₁.lt b₁`)
* `(a₁ + a₂) + (b₁ + b₂) = b₁ + ((a₁ + a₂) + b₂)` (if not `a₁.lt b₁`)
-/
partial def evalAdd {a b : Q($A)} (va : ExSum sAlg a) (vb : ExSum sAlg b) :
    MetaM <| Result (ExSum sAlg) q($a + $b) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .zero .., vb => return ⟨b, vb, q(zero_add $b)⟩
  | va, .zero .. => return ⟨a, va, q(add_zero _)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ =>
    match ← (evalAddOverlap sAlg va₁ vb₁).run with
    | some (.nonzero ⟨_, vc₁, pc₁⟩) =>
      let ⟨_, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨_, .add vc₁ vc₂, q(add_overlap_nonzero $pc₁ $pc₂)⟩
    | some (.zero pc₁) =>
      let ⟨c₂, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨c₂, vc₂, q(add_overlap_zero $pc₁ $pc₂)⟩
    | none =>
      if let .lt := va₁.cmp vb₁ then
        have : $b =Q $b₁ + $_b₂ := ⟨⟩
        let ⟨_c, vc, pc⟩ ← evalAdd va₂ vb
        return ⟨_, .add va₁ vc, q(add_add_add_comm $pc)⟩
      else
        have : $a =Q $a₁ + $_a₂ := ⟨⟩
        let ⟨_c, vc, pc⟩ ← evalAdd va vb₂
        return ⟨_, .add vb₁ vc, q(add_add_add_comm' $pc)⟩

partial def evalSMulExProd {r : Q($R)} {a : Q($A)} (vr : Ring.ExSum sR r) :
  ExProd sAlg a →
  MetaM (Result (ExProd q($sAlg)) q($r • $a))
  | .smul vs => do
    let ⟨t, vt, pt⟩ ← Ring.evalMul sR vr vs
    return ⟨_, .smul vt, q(smul_smul_one $pt)⟩
  | .mul (x := x) (e := e) (b := b) vx ve vb => do
    let ⟨_, vc, pc⟩ ← evalSMulExProd vr vb
    return ⟨_, .mul vx ve vc, q(smul_mul_assoc $pc)⟩


partial def evalSMul {r : Q($R)} {a : Q($A)} (vr : Ring.ExSum sR r) :
  ExSum sAlg a →
  MetaM (Result (ExSum q($sAlg)) q($r • $a))
  | .zero .. =>
    pure ⟨_, .zero, q(smul_zero $r)⟩
  | .add vsmul vt => do
    let ⟨a, va, pa⟩ ← evalSMulExProd q($sAlg) vr vsmul
    let ⟨t, vt, pt⟩ ← evalSMul vr vt
    return ⟨_, .add va vt, q(smul_add $pa $pt)⟩

partial def evalMul₂ {a b : Q($A)} (va : ExProd sAlg a) (vb : ExProd sAlg b) :
    MetaM <| Result (ExProd sAlg) q($a * $b) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .smul vr, .smul vs => do
    let ⟨_, vt, pt⟩ ← Ring.evalMul sR vr vs
    return ⟨_, .smul vt, q(smul_one_mul_smul_one $pt)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .smul vr =>
    let ⟨_, vc, pc⟩ ← evalMul₂ va₃ (.smul vr)
    return ⟨_, .mul va₁ va₂ vc, q(pow_mul_mul_smul_one $pc)⟩
  | .smul vr, .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ =>
    let ⟨_, vc, pc⟩ ← evalMul₂ (.smul vr) vb₃
    return ⟨_, .mul vb₁ vb₂ vc, q(smul_one_mul_pow_mul $pc)⟩
  | .mul (x := xa) (e := ea) vxa vea va₂, .mul (x := xb) (e := eb) vxb veb vb₂ => do
    if vxa.eq vxb then
      have : $xa =Q $xb := ⟨⟩
      if let some (.nonzero ⟨_, ve, pe⟩) ← (Ring.evalAddOverlap Ring.sℕ vea veb).run then
        let ⟨_, vc, pc⟩ ← evalMul₂ va₂ vb₂
        return ⟨_, .mul vxa ve vc, q(pow_mul_mul_pow_mul $pe $pc)⟩
    if let .lt := (vxa.cmp vxb).then (vea.cmp veb) then
      let ⟨_, vc, pc⟩ ← evalMul₂ va₂ (.mul vxb veb vb₂)
      return ⟨_, .mul vxa vea vc, q(pow_mul_mul_assoc $pc)⟩
    else
      let ⟨_, vc, pc⟩ ← evalMul₂ (.mul vxa vea va₂) vb₂
      return ⟨_, .mul vxb veb vc, q(mul_pow_mul_assoc $pc)⟩

/-- Multiplies a monomial `va` to a polynomial `vb` to get a normalized result polynomial.

* `a * 0 = 0`
* `a * (b₁ + b₂) = (a * b₁) + (a * b₂)`
-/
def evalMul₁ {a b : Q($A)} (va : ExProd sAlg a) (vb : ExSum sAlg b) :
    MetaM <| Result (ExSum sAlg) q($a * $b) := do
  match vb with
  | .zero => return ⟨_, .zero, q(mul_zero $a)⟩
  | .add vb₁ vb₂ =>
    let ⟨_, vb₁', pb₁'⟩ ← evalMul₂ sAlg va vb₁
    let ⟨_, vt, pt⟩ ← evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ ← evalAdd sAlg vb₁'.toSum vt
    return ⟨_, vd, q(mul_add_of_add $pb₁' $pt $pd)⟩

/-- Multiplies two polynomials `va, vb` together to get a normalized result polynomial.

* `0 * b = 0`
* `(a₁ + a₂) * b = (a₁ * b) + (a₂ * b)`
-/
def evalMul {a b : Q($A)} (va : ExSum sAlg a) (vb : ExSum sAlg b) :
    MetaM <| Result (ExSum sAlg) q($a * $b) := do
  match va with
  | .zero => return ⟨_, .zero, q(zero_mul $b)⟩
  | .add va₁ va₂ =>
    let ⟨c₁, vc₁, pc₁⟩ ← evalMul₁ sAlg va₁ vb
    let ⟨c₂, vc₂, pc₂⟩ ← evalMul va₂ vb
    let ⟨_, vd, pd⟩ ← evalAdd sAlg vc₁ vc₂
    return ⟨_, vd, q(add_mul_of_add $pc₁ $pc₂ $pd)⟩

def evalNegProd {a : Q($A)} (rR : Q(Ring $R)) (rA : Q(Ring $A)) (va : ExProd sAlg a) :
    MetaM <| Result (ExProd sAlg) q(-$a) := do
  match va with
  | .smul vr =>
    let ⟨s, vs, pb⟩ ← Ring.evalNeg sR rR vr
    return ⟨_, .smul vs, (q(neg_smul_one (R := $R) (A := $A) $pb):)⟩
  | .mul (x := x) (e := e) vx ve vb =>
    let ⟨_, vc, pc⟩ ← evalNegProd rR rA vb
    return ⟨_, .mul vx ve vc,
      (q(neg_pow_mul $x $e (R := $R) (A := $A) $pc):)⟩

def evalNeg {a : Q($A)} (rR : Q(Ring $R)) (rA : Q(Ring $A)) (va : ExSum sAlg a) :
    MetaM <| Result (ExSum sAlg) q(-$a) := do
  match va with
  | .zero =>
    assumeInstancesCommute
    return ⟨_, .zero, (q(Ring.neg_zero (R := $A)):)⟩
  | .add va₁ va₂ =>
    let ⟨_, vb₁, pb₁⟩ ← evalNegProd sAlg rR rA va₁
    let ⟨_, vb₂, pb₂⟩ ← evalNeg rR rA va₂
    return ⟨_, .add vb₁ vb₂, (q(neg_add (R := $R) (A := $A) $pb₁ $pb₂):)⟩

def evalSub {a b : Q($A)} (rR : Q(Ring $R)) (rA : Q(Ring $A))
    (va : ExSum sAlg a) (vb : ExSum sAlg b) :
    MetaM <| Result (ExSum sAlg) q($a - $b) := do
  let ⟨_c, vc, pc⟩ ← evalNeg sAlg rR rA vb
  let ⟨d, vd, (pd : Q($a + $_c = $d))⟩ ← evalAdd sAlg va vc
  assumeInstancesCommute
  return ⟨_, vd, (q(Ring.sub_pf $pc $pd) : Expr)⟩

def _root_.Mathlib.Tactic.Ring.Cache.cast (c : Ring.Cache sR) :
  Ring.Cache sA where
    rα := c.rα
    dsα := c.dsα
    czα := c.czα

variable {a} in
def evalCast (c : Ring.Cache q($sR)) :
    NormNum.Result a → Option (Result (ExSum sAlg) a)
  | .isNat _ (.lit (.natVal 0)) p => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(isNat_zero_eq $p)⟩
  | .isNat _ lit p => do
    assumeInstancesCommute
    -- Lift the literal to the base ring as a scalar multiple of 1
    pure ⟨_, (ExProd.smul (mkNat lit)).toSum,
      (q(by simp [← Algebra.algebraMap_eq_smul_one]; exact ($p).out))⟩
  | .isNegNat rA lit p => do
    let some rR := c.rα | none
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNat sR rR lit.natLit!
    have : $r =Q Int.rawCast (Int.negOfNat $lit) := ⟨⟩
    assumeInstancesCommute
    pure ⟨_, (ExProd.smul vr.toSum).toSum, (q(isInt_negOfNat_eq (R := $R) $p):)⟩
  -- We don't handle rational expressions in A.
  | _ => none

/--
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to just build an
exponent expression. (This has a slightly different normalization than `evalPowAtom` because
the input types are different.)

* `x ^ e = (x + 0) ^ e * 1`
-/
def evalPowProdAtom {a : Q($A)} {b : Q(ℕ)} (va : ExProd sAlg a) (vb : Ring.ExProd Ring.sℕ b) :
    Result (ExProd sAlg) q($a ^ $b) :=
  ⟨_, (ExBase.sum va.toSum).toProd vb, q(pow_eq_pow_mul_smul_one)⟩

/--
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to just build an
exponent expression.

* `x ^ e = x ^ e * 1 + 0`
-/
def evalPowAtom {a : Q($A)} {b : Q(ℕ)} (va : ExBase sAlg a) (vb : Ring.ExProd Ring.sℕ b) :
    Result (ExSum sAlg) q($a ^ $b) :=
  ⟨_, (va.toProd vb).toSum, q(pow_eq_pow_mul_smul_one_add_zero)⟩

/-- There are several special cases when exponentiating monomials:

* `(r • 1) ^ b = r ^ b • 1 ^ b`
* `(a * b) ^ e = a ^ e * b ^ e`

In all other cases we use `evalPowProdAtom`.
-/
def evalPowProd {a : Q($A)} {b : Q(ℕ)} (va : ExProd sAlg a) (vb : Ring.ExProd Ring.sℕ b) :
    MetaM <| Result (ExProd sAlg) q($a ^ $b) := do
  Lean.Core.checkSystem decl_name%.toString
  let res : OptionT MetaM (Result (ExProd sAlg) q($a ^ $b)) := do
    match va, vb with
    | .smul (r := r) vr, vb =>
      let ⟨r', vr', pr'⟩ ← Ring.evalPow q($sR) vr (Ring.ExSum.add vb .zero)
      return ⟨_, .smul vr', q(smul_one_pow $pr')⟩
    | .mul vxa₁ vea₁ va₂, vb =>
      let ⟨_, vc₁, pc₁⟩ ← Ring.evalMulProd Ring.sℕ vea₁ vb
      let ⟨_, vc₂, pc₂⟩ ← evalPowProd va₂ vb
      return ⟨_, .mul vxa₁ vc₁ vc₂, q(pow_mul_pow $pc₁ $pc₂)⟩
  return (← res.run).getD (evalPowProdAtom sAlg va vb)

/--
The main case of exponentiation of ring expressions is when `va` is a polynomial and `n` is a
nonzero literal expression, like `(x + y)^5`. In this case we work out the polynomial completely
into a sum of monomials.

* `x ^ 1 = x`
* `x ^ (2*n) = x ^ n * x ^ n`
* `x ^ (2*n+1) = x ^ n * x ^ n * x`
-/
partial def evalPowNat {a : Q($A)} (va : ExSum sAlg a) (n : Q(ℕ)) :
    MetaM <| Result (ExSum sAlg) q($a ^ $n) := do
  let nn := n.natLit!
  if nn = 1 then
    return ⟨_, va, (q(Ring.pow_one (R := $A) $a):)⟩
  else
    let nm := nn >>> 1
    have m : Q(ℕ) := mkRawNatLit nm
    if nn &&& 1 = 0 then
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul sAlg vb vb
      have : $n =Q $m + $m := ⟨⟩
      return ⟨_, vc, q(pow_even $pb $pc)⟩
    else
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul sAlg vb vb
      let ⟨_, vd, pd⟩ ← evalMul sAlg vc va
      have : $n =Q $m + $m + 1 := ⟨⟩
      return ⟨_, vd, q(pow_odd $pb $pc $pd)⟩

/-- Exponentiates a polynomial `va` by a monomial `vb`, including several special cases.

* `a ^ 1 = a`
* `0 ^ e = 0` if `0 < e`
* `(a + 0) ^ b = a ^ b` computed using `evalPowProd`
* `a ^ b = (a ^ b') ^ k` if `b = b' * k` and `k > 1`

Otherwise `a ^ b` is just encoded as `a ^ b * 1 + 0` using `evalPowAtom`.
-/
partial def evalPow₁ {a : Q($A)} {b : Q(ℕ)} (va : ExSum sAlg a) (vb : Ring.ExProd Ring.sℕ b) :
    MetaM <| Result (ExSum sAlg) q($a ^ $b) := do
  match va, vb with
  | va, .const 1 =>
    haveI : $b =Q Nat.rawCast (nat_lit 1) := ⟨⟩
    return ⟨_, va, q(pow_rawCast_one)⟩
  | .zero, vb => match vb.evalPos with
    | some p => return ⟨_, .zero, q(zero_pow_pos $p)⟩
    | none => return evalPowAtom sAlg (.sum .zero) vb
  | ExSum.add va .zero, vb =>
    let ⟨_, vc, pc⟩ ← evalPowProd sAlg va vb
    return ⟨_, vc.toSum, q(pow_add_zero $pc)⟩
  | va, vb =>
    if vb.coeff > 1 then
      let ⟨k, _, vc, pc⟩ := Ring.extractCoeff vb
      let ⟨_, vd, pd⟩ ← evalPow₁ va vc
      let ⟨_, ve, pe⟩ ← evalPowNat sAlg vd k
      return ⟨_, ve, q(pow_factored $pc $pd $pe)⟩
    else
      return evalPowAtom sAlg (.sum va) vb

/-- Exponentiates two polynomials `va, vb`.

* `a ^ 0 = 1`
* `a ^ (b₁ + b₂) = a ^ b₁ * a ^ b₂`
-/
def evalPow {a : Q($A)} {b : Q(ℕ)} (va : ExSum sAlg a) (vb : Ring.ExSum Ring.sℕ b) :
    MetaM <| Result (ExSum sAlg) q($a ^ $b) := do
  match vb with
  | .zero => return ⟨_, (ExProd.smul (.one (sA := sR))).toSum, q(pow_zero_eq)⟩
  | .add vb₁ vb₂ =>
    let ⟨_, vc₁, pc₁⟩ ← evalPow₁ sAlg va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalPow va vb₂
    let ⟨_, vd, pd⟩ ← evalMul sAlg vc₁ vc₂
    return ⟨_, vd, q(pow_add $pc₁ $pc₂ $pd)⟩

def evalAtom :
    AtomM (Result (ExSum q($sAlg)) q($a)) := do
  let r ← (← read).evalAtom a
  have e' : Q($A) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ve' : ExSum _ _ :=
    ((ExBase.atom i (e := a')).toProd (Ring.ExProd.mkNat Ring.sℕ 1).2).toSum
  pure ⟨_, ve',
  match r.proof? with
  | none =>
      have : $a =Q $a' := ⟨⟩
      (q(atom_eq_pow_one_mul_smul_one_add_zero))
  | some (p : Q($a = $e')) => (q(atom_eq_pow_one_mul_smul_one_add_zero' $p))
  ⟩

partial def eval {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (cacheR : Ring.Cache q($sR))
    (cacheA : Ring.Cache q($sA)) (e : Q($A)) :
    AtomM (Result (ExSum sAlg) e) := Lean.withIncRecDepth do
  let els := do
    try evalCast sAlg cacheR (← derive e)
    catch _ => evalAtom sAlg e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, cacheA.rα, cacheA.dsα with
  | ``HSMul.hSMul, _, _ | ``SMul.smul, _, _ => match e with
    | ~q(@HSMul.hSMul $R' $A' _ $inst $r' $a') =>
      if ! (← isDefEq R R') then
        -- TODO: Handle case if R extends R'
        return ← els
      if ! (← isDefEq A A') then
        throwError "algebra: HSmul not implemented"
      have r : Q($R) := r'
      have a : Q($A) := a'
      let ⟨r'', vr, pr⟩ ← Ring.eval q($sR) cacheR q($r)
      let ⟨a'', va, pa⟩ ← eval q($sAlg) cacheR cacheA q($a)
      let ⟨ef, vf, pf⟩ ← evalSMul sAlg vr va
      have : v =QL u_2 := ⟨⟩
      have : $A =Q $A' := ⟨⟩
      have : u =QL u_1 := ⟨⟩
      have : $R =Q $R' := ⟨⟩
      have : $r =Q $r' := ⟨⟩
      have : $a =Q $a' := ⟨⟩
      assumeInstancesCommute
      return ⟨ef, vf, q(eval_smul_eq rfl (smul_congr $pr $pa $pf))⟩
    | _ => els
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval q($sAlg) cacheR cacheA q($a)
      let ⟨_, vb, pb⟩ ← eval q($sAlg) cacheR cacheA q($b)
      let ⟨_, vab, pab⟩ ← evalAdd q($sAlg) va vb
      return ⟨_, vab, q(eval_add $pa $pb $pab)⟩
    | _ => els
  | ``Neg.neg, some rA, _ => match e with
    | ~q(-$a) =>
      let some rR := cacheR.rα | els
      let ⟨_, va, pa⟩ ← eval sAlg cacheR cacheA a
      let ⟨b, vb, p⟩ ← evalNeg sAlg rR rA va
      pure ⟨b, vb, q(eval_neg $pa $p)⟩
  | ``HSub.hSub, some rA, _ | ``Sub.sub, some rA, _ => match e with
    | ~q($a - $b) =>
      let some rR := cacheR.rα | els
      let ⟨_, va, pa⟩ ← eval sAlg cacheR cacheA a
      let ⟨_, vb, pb⟩ ← eval sAlg cacheR cacheA b
      let ⟨c, vc, p⟩ ← evalSub sAlg rR rA va vb
      pure ⟨c, vc, q(eval_sub $pa $pb $p)⟩
    | _ => els
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _ => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval sAlg cacheR cacheA a
      let ⟨_, vb, pb⟩ ← eval sAlg cacheR cacheA b
      let ⟨_, vab, pab⟩ ← evalMul sAlg va vb
      return ⟨_, vab, q(eval_mul $pa $pb $pab)⟩
    | _ =>
      els
  | ``HPow.hPow, _, _ | ``Pow.pow, _, _ => match e with
    | ~q($a ^ ($eb : ℕ)) =>
      let ⟨_, va, pa⟩ ← eval sAlg cacheR cacheA a
      let ⟨_, vb, pb⟩ ← Ring.eval Ring.sℕ .nat eb
      let ⟨c, vc, p⟩ ← evalPow sAlg va vb
      return ⟨c, vc, q(eval_pow $pa $pb $p)⟩
    | _ => els
  | _, _, _ =>
    els

open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq

/-- If `e` has type `Type u` for some level `u`, return `u` and `e : Q(Type u)` -/
def inferLevelQ (e : Expr) : MetaM (Σ u : Lean.Level, Q(Type u)) := do
  let .sort u ← whnf (← inferType e) | throwError "not a type{indentExpr e}"
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr e}"
  return ⟨v, e⟩

section cleanup
variable {R : Type*} [Semiring R]
end cleanup
/-- A cleanup routine, which simplifies normalized expressions to a more human-friendly format. -/
def cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let thms : SimpTheorems := {}
    let thms ← [``add_zero, ``add_assoc_rev, ``_root_.mul_one, ``mul_assoc_rev,
      ``_root_.pow_one, ``mul_neg, ``add_neg, ``one_smul,
      ``Nat.ofNat_nsmul_eq_mul].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
       ``nnrat_rawCast, ``rat_rawCast_neg].foldlM (·.addConst · (post := false)) thms
    let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
      (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)

    pure <| ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

theorem eq_congr {R : Type*} {a b a' b' : R} (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  subst ha hb
  exact h

def normalize (goal : MVarId) {u v : Lean.Level} (R : Q(Type u)) (A : Q(Type v)) :
    AtomM MVarId := do
  let some (A', e₁, e₂) :=
    (← whnfR <|← instantiateMVars <|← goal.getType).eq?
    | throwError "algebra failed: not an equality"
  guard (←isDefEq A A')
  have sA : Q(CommSemiring $A) := ← synthInstanceQ q(CommSemiring $A)
  have sR : Q(CommSemiring $R) := ← synthInstanceQ q(CommSemiring $R)
  have sAlg : Q(Algebra $R $A) := ← synthInstanceQ q(Algebra $R $A)

  have e₁ : Q($A) := e₁
  have e₂ : Q($A) := e₂
  let cr ← Ring.mkCache sR
  let ca ← Ring.mkCache sA
  let (⟨a, exa, pa⟩ : Result (ExSum sAlg) e₁) ← eval sAlg cr ca e₁
  let (⟨b, exb, pb⟩ : Result (ExSum sAlg) e₂) ← eval sAlg cr ca e₂

  let g' ← mkFreshExprMVarQ q($a = $b)
  goal.assign q(eq_congr $pa $pb $g' : $e₁ = $e₂)
  -- if ← isDefEq a b then
    -- have : $a =Q $b := ⟨⟩
    -- g'.mvarId!.assign (q(rfl : $a = $b) : Expr)
  return g'.mvarId!
  -- else throwError "algebra failed to normalize expression."
  -- let l ← ExSum.eq_exSum g'.mvarId! a b exa exb
  -- Tactic.pushGoals l
  -- for g in l do
  --   let l ← evalTacticAt (← `(tactic| norm_num)) g
  --   Tactic.pushGoals l
    -- NormNum.normNumAt g (← getSimpContext)

/-- Infer from the expression what base ring the normalization should use.
 TODO: Find a better way to do this. -/
partial def inferBaseAux (e : Expr) :
    OptionT MetaM <|  Σ u : Lean.Level, Q(Type u) := do
  let .const n _ := (← withReducible <| whnf e).getAppFn | failure
  match_expr e with
  | SMul.smul R _ _ _ _ =>
    return ←inferLevelQ R
  | HSMul.hSMul R _ _ _ _ _ =>
    return ←inferLevelQ R
  | Eq _ a b => (inferBaseAux a) <|> (inferBaseAux b)
  | HAdd.hAdd _ _ _ _ a b => inferBaseAux a <|> inferBaseAux b
  | Add.add _ _ _ a b => inferBaseAux a <|> inferBaseAux b
  | HMul.hMul _ _ _ _ a b => inferBaseAux a <|> inferBaseAux b
  | Mul.mul _ _ _ a b => inferBaseAux a <|> inferBaseAux b
  | HSub.hSub _ _ _ _ a b => inferBaseAux a <|> inferBaseAux b
  | Sub.sub _ _ _ a b => inferBaseAux a <|> inferBaseAux b
  | HPow.hPow _ _ _ _ a _ => inferBaseAux a
  /- Should it try to be clever here and return q(ℤ)
    instead of q(ℕ) if there's negation or subtraction and no other ring?
    Maybe not... what if there's natural number subtraction. And if the desired ring doesn't
    appear in an smul / algebraMap the user shouldn't be too surprised that the tactic failed. -/
  | Neg.neg _ _ a => inferBaseAux a
  | _ =>
    failure

def inferBase (e : Expr) :
    MetaM <| Σ u : Lean.Level, Q(Type u) := do
  return (← (inferBaseAux e).run).getD ⟨0, q(ℕ)⟩

def isAtomOrDerivable (c : Ring.Cache sR) (e : Q($A)) : AtomM (Option (Option (Result (ExSum sAlg) e))) := do
  let els := try
      pure <| some (evalCast sAlg c (← derive e))
    catch _ => pure (some none)
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _
  | ``HSMul.hSMul, _, _
  | ``HPow.hPow, _, _ | ``Pow.pow, _, _
  | ``Neg.neg, some _, _
  | ``HSub.hSub, some _, _ | ``Sub.sub, some _, _
  | ``Inv.inv, _, some _
  | ``HDiv.hDiv, _, some _ | ``Div.div, _, some _ => pure none
  | _, _, _ => els

def evalExpr {u : Lean.Level} (R : Q(Type u)) (e : Expr) : AtomM Simp.Result := do
  let e ← withReducible <| whnf e
  guard e.isApp -- all interesting ring expressions are applications
  let ⟨v, A, e⟩ ← inferTypeQ' e
  let sA ← synthInstanceQ q(CommSemiring $A)
  let sR ← synthInstanceQ q(CommSemiring $R)
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  let cr ← Ring.mkCache sR
  let ca ← Ring.mkCache sA
  assumeInstancesCommute
  let ⟨a, _, pa⟩ ← match ← isAtomOrDerivable q($sAlg) cr q($e) with
  | none => eval sAlg cr ca e -- `none` indicates that `eval` will find something algebraic.
  | some none => failure -- No point rewriting atoms
  | some (some r) => pure r -- Nothing algebraic for `eval` to use, but `norm_num` simplifies.
  pure { expr := a, proof? := pa }

def evalExprInfer (e : Expr) : AtomM Simp.Result := do
  let ⟨_, R⟩ ← inferBase e
  evalExpr R e

/-- Attempt -/
elab (name := algebraNF) "algebra_nf" tk:"!"? loc:(location)?  : tactic => do
  -- let mut cfg ← elabConfig cfg
  let mut cfg := {}
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (evalExprInfer) (cleanup cfg)
  transformAtLocation (m ·) "ring_nf" loc cfg.failIfUnchanged false

elab (name := algebraNFWith) "algebra_nf" tk:"!"? " with " R:term loc:(location)?  : tactic => do
  -- let mut cfg ← elabConfig cfg
  let mut cfg := {}
  let ⟨u, R⟩ ← inferLevelQ (← elabTerm R none)
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (evalExpr R) (cleanup cfg)
  transformAtLocation (m ·) "ring_nf" loc cfg.failIfUnchanged false

/-- Frontend of `algebra`: attempt to close a goal `g`, assuming it is an equation of semirings. -/
def proveEq (base : Option (Σ u : Lean.Level, Q(Type u))) (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "algebra failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  let ⟨u, R⟩ ←
    match base with
      | .some p => do pure p
      | none => do
        pure (← inferBase (← g.getType))
  have A : Q(Type v) := α
  let sA ← synthInstanceQ q(CommSemiring $A)
  let sR ← synthInstanceQ q(CommSemiring $R)
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  have e₁ : Q($A) := e₁; have e₂ : Q($A) := e₂
  let eq ← algCore q($sAlg) e₁ e₂
  g.assign eq
where
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  algCore {u v : Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (e₁ e₂ : Q($A)) : AtomM Q($e₁ = $e₂) := do
    let cr ← Ring.mkCache sR
    let ca ← Ring.mkCache sA
    profileitM Exception "algebra" (← getOptions) do
      let ⟨a, va, pa⟩ ← eval sAlg cr ca e₁
      let ⟨b, vb, pb⟩ ← eval sAlg cr ca e₂
      unless va.eq vb do
        let g ← mkFreshExprMVar (← (← Ring.ringCleanupRef.get) q($a = $b))
        throwError "algebra failed, algebra expressions not equal\n{g.mvarId!}"
      let pb : Q($e₂ = $a) := pb
      /- TODO: extract lemma -/
      return q(by simp_all)

elab (name := algebra) "algebra":tactic =>
  withMainContext do
    let g ← getMainGoal
    AtomM.run .default (proveEq none g)

elab (name := algebra_over) "algebra" " with " R:term : tactic =>
  withMainContext do
    let ⟨u, R⟩ ← inferLevelQ (← elabTerm R none)
    let g ← getMainGoal
    AtomM.run .default (proveEq (some ⟨u, R⟩) g)

def ExProd.equateZero {a : Q($A)}
(va : ExProd q($sAlg) a) : MetaM <| Q($a = 0) × MVarId :=
  match va with
  | .smul (r := r) vr => do
    let pf ← mkFreshExprMVarQ q($r = 0)
    return ⟨q(sorry), pf.mvarId!⟩
  | .mul (x := x) (e := e) vx ve vb => do
    -- For x^e * b = 0, we need b = 0 (assuming x^e ≠ 0)
    vb.equateZero

def equateZero {a : Q($A)} (va : ExSum q($sAlg) a) :
    MetaM <| Q($a = 0) × List MVarId :=
  match va with
  | .zero => do
    return ⟨q(rfl), []⟩
  | .add va₁ va₂ => do
    let ⟨pf, id⟩ ← va₁.equateZero
    let ⟨pf', mvars⟩ ← equateZero va₂
    return ⟨q(sorry), id :: mvars⟩

def ExProd.equateScalarsProd {a b : Q($A)} (va : ExProd q($sAlg) a) (vb : ExProd q($sAlg) b) :
    MetaM <| Q($a = $b) × Option MVarId := do
  match va, vb with
  | .smul (r := r) vr, .smul (r := s) vs =>
    -- For r • 1 = s • 1, we need r = s
    if vr.eq vs then
      have : $r =Q $s := ⟨⟩
      return ⟨q(sorry), none⟩
    else
      let pab ← mkFreshExprMVarQ q($r = $s)
      return ⟨q(sorry), some pab.mvarId!⟩
  | .mul (x := xa) (e := ea) vxa vea va', .mul (x := xb) (e := eb) vxb veb vb' =>
    -- For x^e * a' = x^e * b', we need a' = b' (bases and exponents already match)
    va'.equateScalarsProd vb'
  | _, _ =>
    -- This shouldn't happen - the caller should ensure structural equality
    throwError "equateScalarsProd: structure mismatch"


def equateScalarsSum {a b : Q($A)} (va : ExSum q($sAlg) a) (vb : ExSum q($sAlg) b) :
    MetaM <| Q($a = $b) × List MVarId := do
  match va, vb with
  | .zero, .zero => do
    return ⟨q(rfl), []⟩
  | va, .zero => do
    equateZero _ va
  | .zero, vb => do
    let ⟨pf, mvars⟩ ← equateZero _ vb
    return ⟨q(Eq.symm $pf), mvars⟩
  | .add (a := a₁) (b := a₂) va₁ va₂, .add (a := b₁) (b := b₂) vb₁ vb₂ =>
    -- Compare the leading terms by shape (ignoring scalar coefficients)
    match va₁.cmpShape vb₁ with
    | .lt =>
      -- va₁ < vb₁ in shape, so va₁ must be 0
      let ⟨pr, id⟩ ← va₁.equateZero
      let ⟨pf, ids⟩ ← equateScalarsSum va₂ (.add vb₁ vb₂)
      return ⟨q(sorry), id :: ids⟩
    | .gt =>
      -- vb₁ < va₁ in shape, so vb₁ must be 0
      let ⟨ps, id⟩ ← vb₁.equateZero
      let ⟨pf, ids⟩ ← equateScalarsSum (.add va₁ va₂) vb₂
      return ⟨q(sorry), id :: ids⟩
    | .eq =>
      -- The leading terms have the same structure, need to equate coefficients
      let ⟨pf, ids⟩ ← equateScalarsSum va₂ vb₂
      let ⟨pab, idOpt⟩ ← va₁.equateScalarsProd sAlg vb₁
      match idOpt with
      | none => return ⟨q(sorry), ids⟩
      | some id => return ⟨q(sorry), id :: ids⟩

#check simpTarget

#check Simp.Simproc

def runSimp (f : Simp.Result → MetaM Simp.Result) (g : MVarId) : MetaM MVarId := do
  let mut cfg := {}
  let e ← g.getType
  let r ← RingNF.cleanup cfg {expr := e, proof? := none}
  applySimpResultToTarget g e r

def matchScalarsAux (base : Option (Σ u : Lean.Level, Q(Type u))) (g : MVarId) : MetaM (List MVarId) :=
  do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "algebra failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  let ⟨u, R⟩ ←
    match base with
      | .some p => do pure p
      | none => do
        pure (← inferBase (← g.getType))
  have A : Q(Type v) := α
  let sA ← synthInstanceQ q(CommSemiring $A)
  let sR ← synthInstanceQ q(CommSemiring $R)
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  have e₁ : Q($A) := e₁; have e₂ : Q($A) := e₂
  let ⟨eq, mids⟩ ← AtomM.run .instances <| algCore q($sAlg) e₁ e₂
  -- surely there's a better way to apply the cleanup routine to each goal.
  let res ← mids.mapM (runSimp (RingNF.cleanup {}))
  g.assign eq
  return res
where
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  algCore {u v : Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (e₁ e₂ : Q($A)) :
      AtomM (Q($e₁ = $e₂) × List MVarId) := do
    let cr ← Ring.mkCache sR
    let ca ← Ring.mkCache sA
    profileitM Exception "algebra" (← getOptions) do
      let ⟨a, va, pa⟩ ← eval sAlg cr ca e₁
      let ⟨b, vb, pb⟩ ← eval sAlg cr ca e₂
      let ⟨pab, mvars⟩ ← equateScalarsSum sAlg va vb
      return ⟨q(sorry), mvars⟩

elab (name := matchScalarsAlgWith) "match_scalars_alg" " with " R:term :tactic => withMainContext do
  let ⟨u, R⟩ ← inferLevelQ (← elabTerm R none)
  Tactic.liftMetaTactic (matchScalarsAux <| .some ⟨u, R⟩)

elab (name := matchScalarsAlg) "match_scalars_alg" :tactic =>
  Tactic.liftMetaTactic (matchScalarsAux .none)


example {x : ℚ} {y : ℤ} : y • x + (1:ℤ) • x = (1 + y) • x := by
  algebra

end Mathlib.Tactic.Algebra


-- why doesn't match_expr match on the HSMul.hSmul expression?????
example (x : ℚ) :  x + x = (2 : ℤ) • x := by
  algebra
  -- match_scalars <;> simp

example (x : ℚ) : x = 1 := by
  algebra_nf with ℕ
  sorry

example (x y : ℚ) : x + y  = y + x := by
  algebra

example (x y : ℚ) : x + y*x + x + y  = (x + x) + (x*y + y) := by
  algebra

-- BUG: ExProd.one doesn't match with the empty product in sums.
example (x : ℚ) : x + x + x  = 3 * x := by
  algebra

example (x : ℚ) : (x + x) + (x + x)  = x + x + x + x := by
  algebra

example (x y : ℚ) : x + (y)*(x+y) = 0 := by
  algebra_nf
  sorry

example (x y : ℚ) : x + (x)*(x + -y) = 0 := by
  -- NOTE: it can only handle negation if the base ring can.
  algebra_nf with ℤ
  sorry


example (x y : ℚ) : (x * x + x * y) + (x * y + y * y) = 0 := by
  algebra_nf
  sorry

example (x y : ℚ) : (x + y)*(x+y) = x*x + 2 * x * y + y * y := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra

-- Handle negative integer constants
example (x y : ℚ) : (x + (-3) * y)*(x+y) = x*x + (-2) * x * y + (-3) * y^2 := by
  algebra with ℤ

example (x y : ℚ) : (x+y)*x = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra_nf
  sorry

example (x y : ℚ) : (x+y)*y  = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra_nf with ℕ
  sorry


example (x : ℚ) : (x + 1)^3 = x^3 + 3*x^2 + 3*x + 1 := by
  algebra

example (x : ℚ) (hx : x = 0) : (x+1)^10 = 1 := by
  algebra_nf
  simp [hx]

-- TODO: Find out what's triggering this linter.
set_option linter.style.commandStart false

example {a b : ℤ} (x y : ℚ) : (a + b) • (x + y) = b • x + a • (x + y) + b • y := by
  -- ring does nothing
  ring_nf
  algebra

example {a b : ℤ} (x y : ℚ) : (a - b) • (x + y) = - b • x + a • (x + y) - b • y := by
  -- ring does nothing
  ring_nf
  algebra


example {a b : ℤ} (x y : ℚ) (ha : a = 2) : (a + b) • (x + y) = b • x + (2:ℤ) • (x + y) + b • y := by
  -- ring does nothing
  match_scalars_alg with ℤ
  sorry
  sorry




example (x y : ℚ) (a : ℤ) (h : 2 * a = 3) : (x + a • y)^2 = x^2 + 3 * x*y + a^2 • y^2 := by
  grind


example : 2 = 1 := by
  match_scalars_alg with ℕ
  sorry



-- #lint

example (x y : ℚ) (m n : ℕ) : (x + 2) ^ (2 * n+1) = ((x+2)^n)^2 * (x+2) := by
  algebra

example (x y : ℚ) (m n : ℕ) : (x^n +  1)^2 = 0 := by
  algebra_nf
  sorry
