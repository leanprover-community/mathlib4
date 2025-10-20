/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.Algebra.Lemmas
import Mathlib.Tactic.Ring.RingNF

/-!
# The `algebra` tactic
A suite of three tactics for solving equations in commutative algebras over commutative (semi)rings,
where the exponents can also contain variables.

Based largely on the implementation of `ring`. The `algebra` normal form mirrors that of `ring`
except that the constants are expressions in the base ring that are kept in ring normal form.

## Organization
The structure of this file closely matches that of `Ring.Basic`.

* Normalized expressions are stored as an `ExSum`, a type which is part of the inductive family of
types `ExSum`, `ExProd` and `ExBase`.
* We implement evaluation functions (`evalAdd`, `evalMul`, etc.) for all of the operations we
support, which take normalized expressions and return a new normalized expression together with
a proof that the new expression equals the operation applied to the input expressions.

This tactic is used internally to implement the `polynomial` tactic.
-/

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic Mathlib.Meta AtomM

namespace Mathlib.Tactic.Algebra


attribute [local instance] monadLiftOptionMetaM

section ExSum

open NormNum

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
  /-- An empty sum. -/
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
  | .mul vx₁ ve₁ vb₁, .mul vx₂ ve₂ vb₂ =>
    (vx₁.cmp vx₂).then (ve₁.cmp ve₂) |>.then (vb₁.cmpShape vb₂)
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

/-- The number one in normal form. -/
def _root_.Mathlib.Tactic.Ring.ExSum.one : Ring.ExSum q($sA) q(Nat.rawCast (nat_lit 1) + 0 : $A) :=
  .add (.const (e := q(Nat.rawCast (nat_lit 1) : $A)) 1 none) .zero

/--
Constructs the expression for a natural number literal `n` in the algebra `A`.
-/
def mkNat (n : Q(ℕ)) : Ring.ExSum q($sA) q(Nat.rawCast $n + 0 : $A) :=
  .add (.const (e := q(Nat.rawCast ($n) : $A)) n.natLit! none) .zero
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

end ExSum

/-- This cache contains typeclasses required during `algebra`'s execution. These assumptions
  are stronger than `ring` because `algebra` occasionally requires commutativity to move between
  the base ring and the algebra. -/
structure Cache {u : Level} {A : Q(Type u)} (sA : Q(CommSemiring $A)) extends Ring.Cache sA where
  /-- A CommRing instance on `A`, if available. -/
  commRing : Option Q(CommRing $A)
  /-- A DivisionRing instance on `A`, if available. -/
  divisionRing : Option Q(DivisionRing $A)
  /-- A Semifield instance on `A`, if available. -/
  semifield : Option Q(Semifield $A)
  /-- A Field instance on `A`, if available. -/
  field : Option Q(Field $A)

/-- Create a new cache for `A` by doing the necessary instance searches. -/
def mkCache {u : Level} {A : Q(Type u)} (sA : Q(CommSemiring $A)) : MetaM (Cache sA) := do return {
  commRing := (← trySynthInstanceQ q(CommRing $A)).toOption
  divisionRing := (← trySynthInstanceQ q(DivisionRing $A)).toOption
  semifield := (← trySynthInstanceQ q(Semifield $A)).toOption
  field := (← trySynthInstanceQ q(Field $A)).toOption
  toCache := ← Ring.mkCache sA
}

open Mathlib.Tactic.Ring (Result)
open NormNum hiding Result

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A)) (b : Q($A))

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

/-- Evaluates scalar multiplication `r • a` where `r` is a polynomial from the base ring
and `a` is a monomial.

* `r • (s • 1) = (r * s) • 1`
* `r • (x ^ e * b) = x ^ e * (r • b)`
-/
partial def evalSMulExProd {r : Q($R)} {a : Q($A)} (vr : Ring.ExSum sR r) :
  ExProd sAlg a →
  MetaM (Result (ExProd q($sAlg)) q($r • $a))
  | .smul vs => do
    let ⟨_, vt, pt⟩ ← Ring.evalMul sR vr vs
    return ⟨_, .smul vt, q(smul_smul_one $pt)⟩
  | .mul (x := x) (e := e) (b := b) vx ve vb => do
    let ⟨_, vc, pc⟩ ← evalSMulExProd vr vb
    return ⟨_, .mul vx ve vc, q(smul_mul_assoc $pc)⟩


/-- Evaluates scalar multiplication `r • a` where `r` is a polynomial from the base ring
and `a` is a polynomial.

* `r • 0 = 0`
* `r • (a + b) = (r • a) + (r • b)`
-/
partial def evalSMul {r : Q($R)} {a : Q($A)} (vr : Ring.ExSum sR r) :
  ExSum sAlg a →
  MetaM (Result (ExSum q($sAlg)) q($r • $a))
  | .zero .. =>
    pure ⟨_, .zero, q(smul_zero $r)⟩
  | .add vsmul vt => do
    let ⟨_, va, pa⟩ ← evalSMulExProd q($sAlg) vr vsmul
    let ⟨_, vt, pt⟩ ← evalSMul vr vt
    return ⟨_, .add va vt, q(smul_add $pa $pt)⟩

/-- Multiplies two monomials `va, vb` together to get a normalized result monomial.

* `(r • 1) * (s • 1) = (r * s) • 1`
* `(x ^ e * a) * (s • 1) = x ^ e * (a * (s • 1))`
* `(r • 1) * (x ^ e * b) = x ^ e * ((r • 1) * b)`
* `(x ^ ea * a₂) * (x ^ eb * b₂) = x ^ (ea + eb) * (a₂ * b₂)` (if bases match)
* `(x ^ ea * a₂) * (y ^ eb * b₂) = x ^ ea * (a₂ * (y ^ eb * b₂))` (if `x.lt y`)
* `(x ^ ea * a₂) * (y ^ eb * b₂) = y ^ eb * ((x ^ ea * a₂) * b₂)` (if not `x.lt y`)
-/
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
    let ⟨_, vc₁, pc₁⟩ ← evalMul₁ sAlg va₁ vb
    let ⟨_, vc₂, pc₂⟩ ← evalMul va₂ vb
    let ⟨_, vd, pd⟩ ← evalAdd sAlg vc₁ vc₂
    return ⟨_, vd, q(add_mul_of_add $pc₁ $pc₂ $pd)⟩

/-- Negates a monomial `va` to get a normalized monomial.

* `-(r • 1) = (-r) • 1`
* `-(a * b) = a * (-b)`
-/
def evalNegProd {a : Q($A)} (rR : Q(CommRing $R)) (rA : Q(CommRing $A)) (va : ExProd sAlg a) :
    MetaM <| Result (ExProd sAlg) q(-$a) := do
  match va with
  | .smul (r := r) vr =>
    assumeInstancesCommute
    let ⟨_s, vs, (pb : Q(-$r = $_s))⟩ ← Ring.evalNeg sR (q(inferInstance)) vr
    return ⟨_, .smul vs, (q(neg_smul_one (R := $R) (A := $A) $pb))⟩
  | .mul (x := x) (e := e) vx ve vb =>
    assumeInstancesCommute
    let ⟨_, vc, pc⟩ ← evalNegProd rR rA vb
    return ⟨_, .mul vx ve vc,
      (q(neg_pow_mul $x $e $pc))⟩

/-- Negates a polynomial `va` to get a normalized polynomial.

* `-0 = 0`
* `-(a + b) = -a + (-b)`
-/
def evalNeg {a : Q($A)} (rR : Q(CommRing $R)) (rA : Q(CommRing $A)) (va : ExSum sAlg a) :
    MetaM <| Result (ExSum sAlg) q(-$a) := do
  match va with
  | .zero =>
    assumeInstancesCommute
    return ⟨_, .zero, (q(Ring.neg_zero (R := $A)):)⟩
  | .add va₁ va₂ =>
    let ⟨_, vb₁, pb₁⟩ ← evalNegProd sAlg rR rA va₁
    let ⟨_, vb₂, pb₂⟩ ← evalNeg rR rA va₂
    return ⟨_, .add vb₁ vb₂, (q(neg_add (A := $A) $pb₁ $pb₂):)⟩

/-- Subtracts two polynomials `va` and `vb` to get a normalized polynomial.

* `a - b = a + (-b)`
-/
def evalSub {a b : Q($A)} (rR : Q(CommRing $R)) (rA : Q(CommRing $A))
    (va : ExSum sAlg a) (vb : ExSum sAlg b) :
    MetaM <| Result (ExSum sAlg) q($a - $b) := do
  let ⟨_c, vc, pc⟩ ← evalNeg sAlg rR rA vb
  let ⟨_d, vd, (pd : Q($a + $_c = $_d))⟩ ← evalAdd sAlg va vc
  assumeInstancesCommute
  return ⟨_, vd, (q(Ring.sub_pf $pc $pd) : Expr)⟩

variable {a} in
/-- Evaluates a numeric literal in the algebra `A` by lifting it through the base ring `R`. -/
def evalCast (cR : Algebra.Cache q($sR)) (cA : Algebra.Cache q($sA)):
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
    let some crR := cR.commRing | none
    let some crA := cA.commRing | none
    let some rR := cR.rα | none
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNat q($sR) q($rR) lit.natLit!
    have : $r =Q Int.rawCast (Int.negOfNat $lit) := ⟨⟩
    assumeInstancesCommute
    pure ⟨_, (ExProd.smul vr.toSum).toSum, (q(isInt_negOfNat_eq $p))⟩
  | .isNNRat rA q n d p => do
    -- TODO: use semifields here.
    let some dsR := cR.semifield | none
    let some dsA := cA.semifield | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNNRat q($sR) q(inferInstance) q n d q(IsNNRat.den_nz (α := $A) $p)
    have : $r =Q (NNRat.rawCast $n $d : $R) := ⟨⟩
    pure ⟨_, (ExProd.smul vr.toSum).toSum, q(isNNRat_eq_rawCast (a := $a) $p)⟩
  | .isNegNNRat dA q n d p => do
    let some fR := cR.field | none
    let some fA := cA.field | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNNRat q($sR) q(inferInstance) q n d q(IsRat.den_nz $p)
    have : $r =Q (Rat.rawCast (.negOfNat $n) $d : $R) := ⟨⟩
    pure ⟨_, (ExProd.smul vr.toSum).toSum, (q(isRat_eq_rawCast (a := $a) $p))⟩
  | _ => none

/--
The fallback case for exponentiating monomials is to use `ExBase.toProd` to just build an
exponent expression. (This has a slightly different normalization than `evalPowAtom` because
the input types are different.)

* `a ^ e = (a + 0) ^ e * 1 • 1`
-/
def evalPowProdAtom {a : Q($A)} {b : Q(ℕ)} (va : ExProd sAlg a) (vb : Ring.ExProd Ring.sℕ b) :
    Result (ExProd sAlg) q($a ^ $b) :=
  ⟨_, (ExBase.sum va.toSum).toProd vb, q(pow_eq_pow_mul_smul_one)⟩

/--
The fallback case for exponentiating base expressions is to use `ExBase.toProd` to just build an
exponent expression.

* `x ^ e = x ^ e * 1 • 1 + 0`
-/
def evalPowAtom {a : Q($A)} {b : Q(ℕ)} (va : ExBase sAlg a) (vb : Ring.ExProd Ring.sℕ b) :
    Result (ExSum sAlg) q($a ^ $b) :=
  ⟨_, (va.toProd vb).toSum, q(pow_eq_pow_mul_smul_one_add_zero)⟩

/-- Exponentiates a monomial `a` by an exponent `b`, with special cases:

* `(r • 1) ^ b = r ^ b • 1`
* `(x ^ e * a) ^ b = x ^ (e * b) * (a ^ b)`

In all other cases we use `evalPowProdAtom`.
-/
def evalPowProd {a : Q($A)} {b : Q(ℕ)} (va : ExProd sAlg a) (vb : Ring.ExProd Ring.sℕ b) :
    MetaM <| Result (ExProd sAlg) q($a ^ $b) := do
  Lean.Core.checkSystem decl_name%.toString
  let res : OptionT MetaM (Result (ExProd sAlg) q($a ^ $b)) := do
    match va, vb with
    | .smul (r := r) vr, vb =>
      let ⟨_r', vr', pr'⟩ ← Ring.evalPow q($sR) vr (Ring.ExSum.add vb .zero)
      return ⟨_, .smul vr', q(smul_one_pow $pr')⟩
    | .mul vxa₁ vea₁ va₂, vb =>
      let ⟨_, vc₁, pc₁⟩ ← Ring.evalMulProd Ring.sℕ vea₁ vb
      let ⟨_, vc₂, pc₂⟩ ← evalPowProd va₂ vb
      return ⟨_, .mul vxa₁ vc₁ vc₂, q(pow_mul_pow $pc₁ $pc₂)⟩
  return (← res.run).getD (evalPowProdAtom sAlg va vb)

/--
The main case of exponentiation of algebra expressions is when `va` is a polynomial and `n` is a
nonzero literal expression, like `(x + y)^5`. In this case we work out the polynomial completely
into a sum of monomials.

* `a ^ 1 = a`
* `a ^ (2*n) = (a ^ n) * (a ^ n)`
* `a ^ (2*n+1) = (a ^ n) * (a ^ n) * a`
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

/-- Exponentiates a polynomial `va` by a monomial exponent `vb`, including several special cases.

* `a ^ 1 = a`
* `0 ^ e = 0` if `0 < e`
* `(a + 0) ^ b = a ^ b` computed using `evalPowProd`
* `a ^ b = (a ^ b') ^ k` if `b = b' * k` and `k > 1`

Otherwise `a ^ b` is just encoded as `a ^ b * 1 • 1 + 0` using `evalPowAtom`.
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

* `a ^ 0 = 1 • 1 + 0`
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

/--
Evaluates an atom, an expression where `algebra` can find no additional structure.

* `a = a ^ 1 * (1 • 1) + 0`
-/
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

/-- Push `algebraMap`s into sums and products and convert `algebraMap`s from `ℕ`, `ℤ` and `ℚ`
into casts. -/
def pushCast (e : Expr) : MetaM Simp.Result := do
  -- collect the available `push_cast` lemmas
  let mut thms : SimpTheorems := ← NormCast.pushCastExt.getTheorems
  let simps : Array Name := #[``eq_natCast, ``eq_intCast, ``eq_ratCast]
  for thm in simps do
    let ⟨levelParams, _, proof⟩ ← abstractMVars (mkConst thm)
    thms ← thms.add (.stx (← mkFreshId) Syntax.missing) levelParams proof
  -- now run `simp` with these lemmas, and (importantly) *no* simprocs
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  let (r, _) ← simp e ctx (simprocs := #[])
  return r

/-- Handle scalar multiplication when the scalar ring `R'` doesn't match the base ring `R`.
Assumes `R` is an `R'`-algebra (i.e., `R'` is smaller), and casts the scalar using `algebraMap`. -/
def evalSMulCast {u u' v : Lean.Level} {R : Q(Type u)} {R' : Q(Type u')} {A : Q(Type v)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A))
    (smul : Q(HSMul $R' $A $A)) (r' : Q($R')) (a : Q($A)) :
    MetaM <| Σ r : Q($R), Q($r • $a = $r' • $a) := do
  if (← isDefEq R R') then
    have : u =QL u' := ⟨⟩
    have : $R =Q $R' := ⟨⟩
    assumeInstancesCommute
    return ⟨q($r'), q(rfl)⟩
  let _sR' ← synthInstanceQ q(CommSemiring $R')
  -- Synthesize the algebra instance showing R is an R'-algebra
  let _algR'R ← synthInstanceQ q(Algebra $R' $R)
  -- TODO: Determine if I should be synthing this instance.
  let _mod ← synthInstanceQ q(Module $R' $A)
  let _ist ← synthInstanceQ q(IsScalarTower $R' $R $A)
  assumeInstancesCommute
  let r_cast : Q($R) := q(algebraMap $R' $R $r')
  let res ← pushCast r_cast
  have r₀ : Q($R) := res.expr
  let pf : Q($r₀ = $r_cast) ← res.getProof
  return ⟨r₀, q($pf ▸ algebraMap_smul $R $r' $a)⟩

/--
Evaluates expression `e` of type `A` into a normalized representation as a polynomial over
algebra `A` with base ring `R`. This is the main driver of `algebra`, which calls out to
`evalAdd`, `evalMul`, `evalSMul`, `evalPow` etc.
-/
partial def eval {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (cacheR : Algebra.Cache q($sR))
    (cacheA : Algebra.Cache q($sA)) (e : Q($A)) :
    AtomM (Result (ExSum sAlg) e) := Lean.withIncRecDepth do
  let els := do
    try evalCast sAlg cacheR cacheA (← derive e)
    catch _ => evalAtom sAlg e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, cacheA.rα, cacheA.dsα with
  | ``HSMul.hSMul, _, _ | ``SMul.smul, _, _ => match e with
    | ~q(@HSMul.hSMul $R' $A' _ $inst $r' $a') =>
      if ! (← isDefEq A A') then
        throwError "algebra: HSmul not implemented"
      have : u_2 =QL v := ⟨⟩
      have : $A =Q $A' := ⟨⟩
      have a : Q($A) := a'
      have : $a =Q $a' := ⟨⟩
      try
        let ⟨r, (pf_smul : Q(($r : $R) • $a = $r' • $a))⟩ ←
          evalSMulCast q($sAlg) q(inferInstance) r' a
        let ⟨_r'', vr, pr⟩ ← Ring.eval q($sR) cacheR.toCache q($r)
        let ⟨_a'', va, pa⟩ ← eval q($sAlg) cacheR cacheA q($a)
        let ⟨ef, vf, pf⟩ ← evalSMul sAlg vr va
        assumeInstancesCommute
        have pe : Q($e = $r' • $a) := q(rfl)
        have : Q($r' • $a = $r • $a) := q(Eq.symm ($pf_smul))
        return ⟨ef, vf, q(eval_smul_eq (($pe).trans $this) (smul_congr $pr $pa $pf))⟩
      catch | _ => els
    | _ => els
  | ``DFunLike.coe, _, _ => match e with
    | ~q(DFunLike.coe (@algebraMap $R' _ $inst₁ $inst₂ $inst₃) $r') =>
      -- try
        let ⟨r, pf_smul⟩ ←
          evalSMulCast q($sAlg) q(inferInstance) q($r') q(1)
        let ⟨_r'', vr, pr⟩ ← Ring.eval q($sR) cacheR.toCache q($r)
        let ⟨_a'', va, pa⟩ ← eval q($sAlg) cacheR cacheA q(1)
        let ⟨ef, vf, pf⟩ ← evalSMul sAlg vr va
        have pe : Q($e = $r' • 1) := q(Algebra.algebraMap_eq_smul_one $r')
        assumeInstancesCommute
        return ⟨ef, vf, q(eval_smul_eq (($pe).trans ($pf_smul).symm) (smul_congr $pr $pa $pf))⟩
      -- catch | _ => els
    | _ => els
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval q($sAlg) cacheR cacheA q($a)
      let ⟨_, vb, pb⟩ ← eval q($sAlg) cacheR cacheA q($b)
      let ⟨_, vab, pab⟩ ← evalAdd q($sAlg) va vb
      return ⟨_, vab, q(eval_add $pa $pb $pab)⟩
    | _ => els
  | ``Neg.neg, some _, _ => match e with
    | ~q(-$a) =>
      let some crR := cacheR.commRing | els
      let some crA := cacheA.commRing | els
      let ⟨_, va, pa⟩ ← eval sAlg cacheR cacheA a
      let ⟨b, vb, p⟩ ← evalNeg sAlg crR crA va
      assumeInstancesCommute
      pure ⟨b, vb, q(eval_neg $pa $p)⟩
  | ``HSub.hSub, some _, _ | ``Sub.sub, some _, _ => match e with
    | ~q($a - $b) =>
      let some crR := cacheR.commRing | els
      let some crA := cacheA.commRing | els
      let ⟨_, va, pa⟩ ← eval sAlg cacheR cacheA a
      let ⟨_, vb, pb⟩ ← eval sAlg cacheR cacheA b
      let ⟨c, vc, p⟩ ← evalSub sAlg crR crA va vb
      assumeInstancesCommute
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

/-- If `e` has type `Type u` for some level `u`, return `u` and `e : Q(Type u)`. -/
def inferLevelQ (e : Expr) : MetaM (Σ u : Lean.Level, Q(Type u)) := do
  let .sort u ← whnf (← inferType e) | throwError "not a type{indentExpr e}"
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr e}"
  return ⟨v, e⟩

/-- A cleanup routine for `algebra_nf`, which simplifies normalized expressions
to a more human-friendly format. -/
def cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let thms : SimpTheorems := {}
    let thms ← [``add_zero, ``add_assoc_rev, ``_root_.mul_one, ``mul_assoc_rev, ``_root_.pow_one,
      ``mul_neg, ``add_neg, ``one_smul, ``mul_smul_comm].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
       ``nnrat_rawCast, ``rat_rawCast_neg].foldlM (·.addConst · (post := false)) thms
    let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
      (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    pure <| ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

/-- Normalizes both sides of an equality goal in an algebra. Used by the `algebra` tactic. -/
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
  let cr ← Algebra.mkCache sR
  let ca ← Algebra.mkCache sA
  let (⟨a, _exa, pa⟩ : Result (ExSum sAlg) e₁) ← eval sAlg cr ca e₁
  let (⟨b, _exb, pb⟩ : Result (ExSum sAlg) e₂) ← eval sAlg cr ca e₂

  let g' ← mkFreshExprMVarQ q($a = $b)
  goal.assign q(($pa ▸ $pb ▸ $g') : $e₁ = $e₂)
  return g'.mvarId!

/-- Collect all scalar rings from scalar multiplications and `algebraMap` applications in the
expression. -/
partial def collectScalarRings (e : Expr) : MetaM (List (Σ u : Lean.Level, Q(Type u))) := do
  match_expr e with
  | SMul.smul R _ _ _ a =>
    return [←inferLevelQ R] ++ (← collectScalarRings a)
  | DFunLike.coe _ _R _A _inst φ _ =>
      match_expr φ with
      | algebraMap R _ _ _ _ => return [← inferLevelQ R]
      | _ => return []
  | HSMul.hSMul R _ _ _ _ a => return [←inferLevelQ R] ++ (← collectScalarRings a)
  | Eq _ a b => return (← collectScalarRings a) ++ (← collectScalarRings b)
  | HAdd.hAdd _ _ _ _ a b => return (← collectScalarRings a) ++ (← collectScalarRings b)
  | Add.add _ _ _ a b => return (← collectScalarRings a) ++ (← collectScalarRings b)
  | HMul.hMul _ _ _ _ a b => return (← collectScalarRings a) ++ (← collectScalarRings b)
  | Mul.mul _ _ _ a b => return (← collectScalarRings a) ++ (← collectScalarRings b)
  | HSub.hSub _ _ _ _ a b => return (← collectScalarRings a) ++ (← collectScalarRings b)
  | Sub.sub _ _ _ a b => return (← collectScalarRings a) ++ (← collectScalarRings b)
  | HPow.hPow _ _ _ _ a _ => collectScalarRings a
  | Neg.neg _ _ a => collectScalarRings a
  | _ => return []

/-- Given two rings, determine which is 'larger' in the sense that the larger is an algebra
over the smaller. Returns the first ring if they're the same or incompatible. -/
def pickLargerRing (r1 r2 : Σ u : Lean.Level, Q(Type u)) :
    MetaM (Σ u : Lean.Level, Q(Type u)) := do
  let ⟨u1, R1⟩ := r1
  let ⟨u2, R2⟩ := r2
  -- If they're definitionally equal, return the first one
  if ← withReducible <| isDefEq R1 R2 then
    return r1
  -- Try to show R2 is an R1-algebra (meaning R1 is smaller, so return R2)
  try
    let _i1 ← synthInstanceQ q(CommSemiring $R1)
    let _i2 ← synthInstanceQ q(Semiring $R2)
    let _i3 ← synthInstanceQ q(Algebra $R1 $R2)
    return r2
  catch _ => try
    -- Try to show R1 is an R2-algebra (meaning R2 is smaller, so return R1)
    let _i1 ← synthInstanceQ q(CommSemiring $R2)
    let _i2 ← synthInstanceQ q(Semiring $R1)
    let _i3 ← synthInstanceQ q(Algebra $R2 $R1)
    return r1
  catch _ =>
    -- If neither works, return the first ring
    return r1

/-- Infer from the expression what base ring the normalization should use.
 Finds all scalar rings in the expression and picks the 'larger' one in the sense that
 it is an algebra over the smaller rings. -/
def inferBase (ca : Cache q($sA)) (e : Expr) : MetaM <| Σ u : Lean.Level, Q(Type u) := do
  let rings ← collectScalarRings e
  let res ← match rings with
  | [] =>
    match ca.field, ca.czα, ca.commRing with
    | some _, some _, _ =>
      -- A is a Field
      return ⟨0, q(ℚ)⟩
    | _, _, some _ =>
      -- A is a CommRing
      return ⟨0, q(ℤ)⟩
    | _, _, _ =>
      return ⟨0, q(ℕ)⟩
  | r :: rs => rs.foldlM pickLargerRing r
  return res

/-- Check if an expression is an atom or can be simplified by `norm_num`, versus being an algebraic
operation that should be normalized by `eval`. Used by `algebra_nf`. -/
def isAtomOrDerivable (cr : Algebra.Cache sR) (ca : Algebra.Cache sA) (e : Q($A)) :
    AtomM (Option (Option (Result (ExSum sAlg) e))) := do
  let els := try
      pure <| some (evalCast sAlg cr ca (← derive e))
    catch _ => pure (some none)
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, ca.commRing, cr.commRing, ca.dsα with
  | ``HAdd.hAdd, _, _, _ | ``Add.add, _, _, _
  | ``HMul.hMul, _, _, _ | ``Mul.mul, _, _, _
  | ``HSMul.hSMul, _, _, _| ``SMul.smul, _, _, _
  | ``HPow.hPow, _, _, _ | ``Pow.pow, _, _, _
  | ``Neg.neg, some _, some _, _
  | ``HSub.hSub, some _, some _, _ | ``Sub.sub, some _, some _, _ => pure none
  -- for algebraMap, should possibly match more closely.
  | ``DFunLike.coe, _, _, _ => pure none
  | _, _, _, _ => els

/-- The core of `algebra_nf with R` - normalize the expression `e` over the base ring `R` -/
def evalExpr {u : Lean.Level} (R : Q(Type u)) (e : Expr) : AtomM Simp.Result := do
  let e ← withReducible <| whnf e
  guard e.isApp -- all interesting ring expressions are applications
  let ⟨v, A, e⟩ ← inferTypeQ' e
  let sA ← synthInstanceQ q(CommSemiring $A)
  let sR ← synthInstanceQ q(CommSemiring $R)
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  let cr ← Algebra.mkCache sR
  let ca ← Algebra.mkCache sA
  assumeInstancesCommute
  let ⟨a, _, pa⟩ ← match ← isAtomOrDerivable q($sAlg) cr ca q($e) with
  | none => eval sAlg cr ca e -- `none` indicates that `eval` will find something algebraic.
  | some none => failure -- No point rewriting atoms
  | some (some r) => pure r -- Nothing algebraic for `eval` to use, but `norm_num` simplifies.
  pure { expr := a, proof? := pa }

/-- The core of `algebra_nf` - normalize an expression while first inferring the base ring `R`.

This is somewhat unstable as the normal form will depend on `R` and the inferred ring depends
strongly on the form of the initial expression. For example: ⊢ P ((n : ℕ) • x) ∧ P ((n : ℤ) • x)
is unchanged by `algebra_nf` -/
def evalExprInfer (e : Expr) : AtomM Simp.Result := do
  let ⟨_, A, e⟩ ← inferTypeQ' e
  let sA ← synthInstanceQ q(CommSemiring $A)
  let cA ← mkCache q($sA)
  let ⟨_, R⟩ ← inferBase cA e
  evalExpr R e


/-- Attempt to normalize all expressions in an algebra over some fixed base ring. -/
elab (name := algebraNFWith) "algebra_nf" tk:"!"? " with " R:term loc:(location)?  : tactic => do
  let mut cfg := {}
  let ⟨_u, R⟩ ← inferLevelQ (← elabTerm R none)
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (evalExpr R) (cleanup cfg)
  transformAtLocation (m ·) "algebra_nf" loc cfg.failIfUnchanged false

/-- Attempt to normalize all expressions in algebras over commutative rings.

The tactic attempts to infer the base ring from the expression being normalized, and may infer
different rings on different subexpressions. This makes the normal form unpredictable.

Use `algebra_nf with` instead. -/
elab (name := algebraNF) "algebra_nf" tk:"!"? loc:(location)?  : tactic => do
  let suggestion : Tactic.TryThis.Suggestion := {
    suggestion := ← `(tactic| algebra_nf with _)
    postInfo? := "\n\n 'algebra_nf' without specifying the base ring is unstable. \
    Use `algebra_nf with` instead." }
  Meta.Tactic.TryThis.addSuggestion (← getRef) suggestion (origSpan? := ← getRef)
  let mut cfg := {}
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (evalExprInfer) (cleanup cfg)
  transformAtLocation (m ·) "algebra_nf" loc cfg.failIfUnchanged false

/-- Frontend of `algebra`: attempt to close a goal `g`, assuming it is an equation of semirings. -/
def proveEq (base : Option (Σ u : Lean.Level, Q(Type u))) (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "algebra failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have A : Q(Type v) := α
  let sA ← synthInstanceQ q(CommSemiring $A)
  let cA ← Algebra.mkCache sA
  let ⟨u, R⟩ ←
    match base with
      | .some p => do pure p
      | none => do
        pure (← inferBase cA (← g.getType))
  let sR ← synthInstanceQ q(CommSemiring $R)
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  let cR ← Algebra.mkCache sR
  have e₁ : Q($A) := e₁; have e₂ : Q($A) := e₂
  let eq ← algCore q($sAlg) cR cA e₁ e₂
  g.assign eq
where
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  algCore {u v : Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A))
      (cR : Cache q($sR)) (cA : Cache q($sA)) (e₁ e₂ : Q($A)) : AtomM Q($e₁ = $e₂) := do
    profileitM Exception "algebra" (← getOptions) do
      let ⟨a, va, pa⟩ ← eval sAlg cR cA e₁
      let ⟨b, vb, pb⟩ ← eval sAlg cR cA e₂
      unless va.eq vb do
        let g ← mkFreshExprMVar (← (← Ring.ringCleanupRef.get) q($a = $b))
        throwError "algebra failed, algebra expressions not equal\n{g.mvarId!}"
      let pb : Q($e₂ = $a) := pb
      return q(by simp_all)

/-- Given a goal which is an equality in a commutative R-algebra A, parse the LHS and RHS of the
goal as linear combinations of A-atoms over some semiring R, and close the goal if the two
expressions are the same. The R-coefficients are put into ring normal form.

The scalar ring R is inferred automatically by looking for scalar multiplications and algebraMaps
present in the expressions.
 -/
elab (name := algebra) "algebra":tactic =>
  withMainContext do
    let g ← getMainGoal
    AtomM.run .default (proveEq none g)

/-- Given a goal which is an equality in a commutative R-algebra A, parse the LHS and RHS of the
goal as linear combinations of A-atoms over some semiring R, and close the goal if the two
expressions are the same. The R-coefficients are put into ring normal form. -/
elab (name := algebraWith) "algebra" " with " R:term : tactic =>
  withMainContext do
    let ⟨u, R⟩ ← inferLevelQ (← elabTerm R none)
    let g ← getMainGoal
    AtomM.run .default (proveEq (some ⟨u, R⟩) g)

/-- Prove a monomial equals zero by setting its scalar equal to zero in a side goal.

Used by `match_scalars_alg`
-/
def ExProd.equateZero {a : Q($A)}
(va : ExProd q($sAlg) a) : MetaM <| Q($a = 0) × MVarId :=
  match va with
  | .smul (r := r) vr => do
    let pf ← mkFreshExprMVarQ q($r = 0)
    return ⟨q(smul_one_eq_zero (R := $R) $pf), pf.mvarId!⟩
  | .mul (x := x) (e := e) vx ve vb => do
    let ⟨pf, ids⟩ ← vb.equateZero
    -- TODO: extract lemma
    return ⟨q(by subst_vars; simp), ids⟩

/-- Prove a polynomial equals zero by setting its scalars equal to zero as side goals.

Used by `match_scalars_alg`
-/
def equateZero {a : Q($A)} (va : ExSum q($sAlg) a) :
    MetaM <| Q($a = 0) × List MVarId :=
  match va with
  | .zero => do
    return ⟨q(rfl), []⟩
  | .add va₁ va₂ => do
    let ⟨pf, id⟩ ← va₁.equateZero
    let ⟨pf', mvars⟩ ← equateZero va₂
    return ⟨q(add_eq_zero $pf $pf'), id :: mvars⟩

/-- Prove two monomials are equal by equating their scalars in the base ring. Assumes the monomials
consist of the same factors.

Used by `match_scalars_alg`.
-/
def ExProd.equateScalarsProd {a b : Q($A)} (va : ExProd q($sAlg) a) (vb : ExProd q($sAlg) b) :
    MetaM <| Q($a = $b) × Option MVarId := do
  match va, vb with
  | .smul (r := r) vr, .smul (r := s) vs =>
    -- For r • 1 = s • 1, we need r = s
    if vr.eq vs then
      have : $r =Q $s := ⟨⟩
      return ⟨q(rfl), none⟩
    else
      let pab ← mkFreshExprMVarQ q($r = $s)
      return ⟨q(smul_one_eq_smul_one' $pab), some pab.mvarId!⟩
  | .mul (x := xa) (e := ea) _vxa _vea va', .mul (x := xb) (e := eb) _vxb veb vb' =>
    -- For x^e * a' = x^e * b', we need a' = b' (bases and exponents already match)
    let ⟨pf, mvOpt⟩ ← va'.equateScalarsProd vb'
    have : $xa =Q $xb := ⟨⟩
    have : $ea =Q $eb := ⟨⟩
    return ⟨q(mul_eq_mul_of_eq $pf), mvOpt⟩
  | _, _ =>
    -- This shouldn't happen - the caller should ensure structural equality
    throwError "equateScalarsProd: structure mismatch"


/-- Prove two polylnomials are equal by equating their scalars in the base ring as side goals.

Used by `match_scalars_alg`. -/
def equateScalarsSum {a b : Q($A)} (va : ExSum q($sAlg) a) (vb : ExSum q($sAlg) b) :
    MetaM <| Q($a = $b) × List MVarId := do
  match va, vb with
  | .zero, .zero => do
    return ⟨q(rfl), []⟩
  | va, .zero => do
    let ⟨pf, mvars⟩ ← equateZero _ va
    return ⟨q($pf), mvars⟩
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
      return ⟨q(add_eq_of_zero_add $pr $pf), id :: ids⟩
    | .gt =>
      -- vb₁ < va₁ in shape, so vb₁ must be 0
      let ⟨ps, id⟩ ← vb₁.equateZero
      let ⟨pf, ids⟩ ← equateScalarsSum (.add va₁ va₂) vb₂
      return ⟨q(add_eq_of_add_zero $ps $pf), id :: ids⟩
    | .eq =>
      -- The leading terms have the same structure, need to equate coefficients
      let ⟨pf, ids⟩ ← equateScalarsSum va₂ vb₂
      let ⟨pab, idOpt⟩ ← va₁.equateScalarsProd sAlg vb₁
      return ⟨q(add_eq_of_eq_eq $pab $pf),
        match idOpt with
        | none => ids
        | some id => id :: ids
      ⟩

/-- Use `f` to simplify the type of a metavariable `g`. Does not recurse. -/
def applySimp (f : Simp.Result → MetaM Simp.Result) (g : MVarId) : MetaM MVarId := do
  let e ← g.getType
  let r ← f {expr := e, proof? := none}
  applySimpResultToTarget g e r

/-- The core of `match_scalars_alg`. Normalizes both sides of an equation and proves their equality
by creating side goals equating matching coefficients in the base ring. -/
def matchScalarsAux (base : Option (Σ u : Lean.Level, Q(Type u))) (g : MVarId) :
    MetaM (List MVarId) :=
  do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "algebra failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have A : Q(Type v) := α
  let sA ← synthInstanceQ q(CommSemiring $A)
  let cA ← Algebra.mkCache sA
  let ⟨u, R⟩ ←
    match base with
      | .some p => do pure p
      | none => do
        pure (← inferBase cA (← g.getType))
  let sR ← synthInstanceQ q(CommSemiring $R)
  let cR ← Algebra.mkCache sR
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  have e₁ : Q($A) := e₁; have e₂ : Q($A) := e₂
  let ⟨eq, mids⟩ ← AtomM.run .instances <| algCore q($sAlg) cR cA q($e₁) q($e₂)
  let res ← mids.mapM (applySimp (RingNF.cleanup {}))
  g.assign eq
  return res
where
  /-- The core of `matchScalarsAux` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  algCore {u v : Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A))
      (cR : Cache q($sR)) (cA : Cache q($sA)) (e₁ e₂ : Q($A)) :
      AtomM (Q($e₁ = $e₂) × List MVarId) := do
    profileitM Exception "algebra" (← getOptions) do
      let ⟨_a, va, pa⟩ ← eval sAlg cR cA e₁
      let ⟨_b, vb, pb⟩ ← eval sAlg cR cA e₂
      let ⟨pab, mvars⟩ ← equateScalarsSum sAlg va vb
      return ⟨q(eq_trans_trans $pa $pb $pab), mvars⟩

/-- Given a goal which is an equality in a commutative R-algebra A, parse the LHS and RHS of the
goal as linear combinations of A-atoms over some semiring R, and reduce the goal to the respective
equalities of the R-coefficients of each atom. The R-coefficients are put into ring normal form. -/
elab (name := matchScalarsAlgWith) "match_scalars_alg" " with " R:term :tactic => withMainContext do
  let ⟨u, R⟩ ← inferLevelQ (← elabTerm R none)
  Tactic.liftMetaTactic (matchScalarsAux <| .some ⟨u, R⟩)

/-- Given a goal which is an equality in a commutative R-algebra A, parse the LHS and RHS of the
goal as linear combinations of A-atoms over some semiring R, and reduce the goal to the respective
equalities of the R-coefficients of each atom. The R-coefficients are put into ring normal form.

The scalar ring R is inferred automatically by looking for scalar multiplications and algebraMaps
present in the expressions.
-/
elab (name := matchScalarsAlg) "match_scalars_alg" :tactic =>
  Tactic.liftMetaTactic (matchScalarsAux .none)

end Mathlib.Tactic.Algebra
