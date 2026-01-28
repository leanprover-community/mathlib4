/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Anne Baanen
-/
module

public meta import Mathlib.Util.AtomM
public meta import Mathlib.Tactic.Ring.Common
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public meta import Mathlib.Tactic.NormNum.Result

/-!
# `ring` tactic

A tactic for solving equations in commutative (semi)rings,
where the exponents can also contain variables.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .

More precisely, expressions of the following form are supported:
- constants (non-negative integers)
- variables
- coefficients (any rational number, embedded into the (semi)ring)
- addition of expressions
- multiplication of expressions (`a * b`)
- scalar multiplication of expressions (`n • a`; the multiplier must have type `ℕ`)
- exponentiation of expressions (the exponent must have type `ℕ`)
- subtraction and negation of expressions (if the base is a full ring)

The extension to exponents means that something like `2 * 2^n * b = b * 2^(n+1)` can be proved,
even though it is not strictly speaking an equation in the language of commutative rings.

## Implementation notes

The basic approach to prove equalities is to normalise both sides and check for equality.
The normalisation is guided by building a value in the type `ExSum` at the meta level,
together with a proof (at the base level) that the original value is equal to
the normalised version.

The outline of the file:
- Define a mutual inductive family of types `ExSum`, `ExProd`, `ExBase`,
  which can represent expressions with `+`, `*`, `^` and rational numerals.
  The mutual induction ensures that associativity and distributivity are applied,
  by restricting which kinds of subexpressions appear as arguments to the various operators.
- Represent addition, multiplication and exponentiation in the `ExSum` type,
  thus allowing us to map expressions to `ExSum` (the `eval` function drives this).
  We apply associativity and distributivity of the operators here (helped by `Ex*` types)
  and commutativity as well (by sorting the subterms; unfortunately not helped by anything).
  Any expression not of the above formats is treated as an atom (the same as a variable).

There are some details we glossed over which make the plan more complicated:
- The order on atoms is not initially obvious.
  We construct a list containing them in order of initial appearance in the expression,
  then use the index into the list as a key to order on.
- For `pow`, the exponent must be a natural number, while the base can be any semiring `α`.
  We swap out operations for the base ring `α` with those for the exponent ring `ℕ`
  as soon as we deal with exponents.

## Caveats and future work

The normalized form of an expression is the one that is useful for the tactic,
but not as nice to read. To remedy this, the user-facing normalization calls `ringNFCore`.

Subtraction cancels out identical terms, but division does not.
That is: `a - a = 0 := by ring` solves the goal,
but `a / a := 1 by ring` doesn't.
Note that `0 / 0` is generally defined to be `0`,
so division cancelling out is not true in general.

Multiplication of powers can be simplified a little bit further:
`2 ^ n * 2 ^ n = 4 ^ n := by ring` could be implemented
in a similar way that `2 * a + 2 * a = 4 * a := by ring` already works.
This feature wasn't needed yet, so it's not implemented yet.

## Tags

ring, semiring, exponent, power
-/

@[expose] public meta section

assert_not_exists IsOrderedMonoid

namespace Mathlib.Tactic

namespace Ring

open Mathlib.Meta Qq Lean.Meta AtomM
open NormNum hiding Result
open Common (Result)

attribute [local instance] monadLiftOptionMetaM

open Lean (MetaM Expr mkRawNatLit)

/-- A shortcut instance for `CommSemiring ℕ` used by ring. -/
def instCommSemiringNat : CommSemiring ℕ := inferInstance

/-- A shortcut instance for `CommSemiring ℤ` used by ring. -/
def instCommSemiringInt : CommSemiring ℤ := inferInstance

/--
A typed expression of type `CommSemiring ℕ` used when we are working on
ring subexpressions of type `ℕ`.
-/
def sℕ : Q(CommSemiring ℕ) := q(instCommSemiringNat)

/--
A typed expression of type `CommSemiring ℤ` used when we are working on
ring subexpressions of type `ℤ`.
-/
def sℤ : Q(CommSemiring ℤ) := q(instCommSemiringInt)


variable {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))

@[reducible]
def ExBase := Common.ExBase (BaseType sα) sα
@[reducible]
def ExProd := Common.ExProd (BaseType sα) sα
@[reducible]
def ExSum := Common.ExSum (BaseType sα) sα

section
variable {R : Type*} [CommSemiring R] {a : R}

theorem cast_pos {n : ℕ} : IsNat (a : R) n → a = n.rawCast + 0
  | ⟨e⟩ => by simp [e]

theorem cast_zero : IsNat (a : R) (nat_lit 0) → a = 0
  | ⟨e⟩ => by simp [e]

theorem cast_neg {n : ℕ} {R} [Ring R] {a : R} :
    IsInt a (.negOfNat n) → a = (Int.negOfNat n).rawCast + 0
  | ⟨e⟩ => by simp [e]

theorem cast_nnrat {n : ℕ} {d : ℕ} {R} [DivisionSemiring R] {a : R} :
    IsNNRat a n d → a = NNRat.rawCast n d + 0
  | ⟨_, e⟩ => by simp [e, div_eq_mul_inv]

theorem cast_rat {n : ℤ} {d : ℕ} {R} [DivisionRing R] {a : R} :
    IsRat a n d → a = Rat.rawCast n d + 0
  | ⟨_, e⟩ => by simp [e, div_eq_mul_inv]

end

section
/--
Constructs the expression corresponding to `.const n`.
(The `.const` constructor does not check that the expression is correct.)
-/
def ExProd.mkNat (n : ℕ) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(ℕ) := .lit (.natVal n)
  ⟨q(($lit).rawCast : $α), .const ⟨n, none⟩⟩

/--
Constructs the expression corresponding to `.const (-n)`.
(The `.const` constructor does not check that the expression is correct.)
-/
def ExProd.mkNegNat (_ : Q(Ring $α)) (n : ℕ) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(ℕ) := mkRawNatLit n
  ⟨q((Int.negOfNat $lit).rawCast : $α), .const ⟨(-n), none⟩⟩

/--
Constructs the expression corresponding to `.const q h` for `q = n / d`
and `h` a proof that `(d : α) ≠ 0`.
(The `.const` constructor does not check that the expression is correct.)
-/
def ExProd.mkNNRat (_ : Q(DivisionSemiring $α)) (q : ℚ) (n : Q(ℕ)) (d : Q(ℕ)) (h : Expr) :
    (e : Q($α)) × ExProd sα e :=
  ⟨q(NNRat.rawCast $n $d : $α), .const ⟨q, h⟩⟩

/--
Constructs the expression corresponding to `.const q h` for `q = -(n / d)`
and `h` a proof that `(d : α) ≠ 0`.
(The `.const` constructor does not check that the expression is correct.)
-/
def ExProd.mkNegNNRat (_ : Q(DivisionRing $α)) (q : ℚ) (n : Q(ℕ)) (d : Q(ℕ)) (h : Expr) :
    (e : Q($α)) × ExProd sα e :=
  ⟨q(Rat.rawCast (.negOfNat $n) $d : $α), .const ⟨q, h⟩⟩
end


def evalCast {α : Q(Type u)} (sα : Q(CommSemiring $α)) {e : Q($α)} :
    NormNum.Result e → Option (Result (ExSum sα) e)
  | .isNat _ (.lit (.natVal 0)) p => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(cast_zero $p)⟩
  | .isNat _ lit p => do
    assumeInstancesCommute
    have ⟨e', s⟩ := ExProd.mkNat sα lit.natLit!
    have : $e' =Q ($lit).rawCast := ⟨⟩
    pure ⟨_, s.toSum, q(cast_pos $p)⟩
  /- In the following cases, Qq needs help identifying the `0` in the produced type with the `0`
  in the expected type, which arise from different instances. -/
  | .isNegNat rα lit p =>
    pure ⟨_, (ExProd.mkNegNat sα rα lit.natLit!).2.toSum, (q(cast_neg $p) : Expr)⟩
  | .isNNRat dsα q n d p =>
    pure ⟨_, (ExProd.mkNNRat sα dsα q n d q(IsNNRat.den_nz $p)).2.toSum, (q(cast_nnrat $p) : Expr)⟩
  | .isNegNNRat dα q n d p =>
    pure ⟨_, (ExProd.mkNegNNRat sα dα q n d q(IsRat.den_nz $p)).2.toSum, (q(cast_rat $p) : Expr)⟩
  | _ => none


section

variable {R : Type*} [CommSemiring R] {n : ℕ} {a₁ a₂ a₃ : ℕ} {b₁ b₂ b₃ : R}

/-! ### Scalar multiplication by `ℕ` -/

theorem natCast_nat (n) : ((Nat.rawCast n : ℕ) : R) = Nat.rawCast n := by simp

theorem natCast_mul {a₁ a₃ : ℕ} (a₂) (_ : ((a₁ : ℕ) : R) = b₁)
    (_ : ((a₃ : ℕ) : R) = b₃) : ((a₁ ^ a₂ * a₃ : ℕ) : R) = b₁ ^ a₂ * b₃ := by
  subst_vars; simp

theorem natCast_zero : ((0 : ℕ) : R) = 0 := Nat.cast_zero

theorem natCast_add {a₁ a₂ : ℕ}
    (_ : ((a₁ : ℕ) : R) = b₁) (_ : ((a₂ : ℕ) : R) = b₂) : ((a₁ + a₂ : ℕ) : R) = b₁ + b₂ := by
  subst_vars; simp

mutual -- partial only to speed up compilation

variable {v : Lean.Level} {β : Q(Type v)} (sβ : Q(CommSemiring $β))
  (_ : v =QL 0) (_ : $β =Q ℕ) (_ : $sβ =Q inferInstance)

/-- Applies `Nat.cast` to a nat polynomial to produce a polynomial in `α`.

* An atom `e` causes `↑e` to be allocated as a new atom.
* A sum delegates to `ExSum.evalNatCast`.
-/
partial def ExBase.evalNatCast {a : Q(ℕ)} (va : ExBase sβ a) : AtomM (Result (ExBase sα) q($a)) :=
  match va with
  | .atom _ => do
    let (i, ⟨b', _⟩) ← addAtomQ q($a)
    pure ⟨b', .atom i, q(Eq.refl $b')⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← ExSum.evalNatCast va
    pure ⟨_, .sum vc, p⟩

/-- Applies `Nat.cast` to a nat monomial to produce a monomial in `α`.

* `↑c = c` if `c` is a numeric literal
* `↑(a ^ n * b) = ↑a ^ n * ↑b`
-/
partial def ExProd.evalNatCast {a : Q(ℕ)} (va : ExProd sβ a) : AtomM (Result (ExProd sα) q($a)) :=
  match va with
  | .const ⟨c, hc⟩ =>
    have n : Q(ℕ) := a.appArg!
    have : $a =Q Nat.rawCast $n := ⟨⟩
    -- WARNING: I don't think the hc here is correct.
    pure ⟨q(Nat.rawCast $n), .const ⟨c, hc⟩, q(natCast_nat (R := $α) $n)⟩
  | .mul (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb₁, pb₁⟩ ← ExBase.evalNatCast va₁
    let ⟨_, vb₃, pb₃⟩ ← ExProd.evalNatCast va₃
    assumeInstancesCommute
    pure ⟨_, .mul vb₁ va₂ vb₃, q(natCast_mul $a₂ $pb₁ $pb₃)⟩

/-- Applies `Nat.cast` to a nat polynomial to produce a polynomial in `α`.

* `↑0 = 0`
* `↑(a + b) = ↑a + ↑b`
-/
partial def ExSum.evalNatCast {a : Q(ℕ)} (va : ExSum sβ a) : AtomM (Result (ExSum sα) q($a)) := do
  assumeInstancesCommute
  match va with
  | .zero => pure ⟨_, .zero, q(natCast_zero (R := $α))⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← ExProd.evalNatCast va₁
    let ⟨_, vb₂, pb₂⟩ ← ExSum.evalNatCast va₂
    pure ⟨_, .add vb₁ vb₂, q(natCast_add $pb₁ $pb₂)⟩

end

/-! ### Scalar multiplication by `ℤ` -/

theorem natCast_int {R} [CommRing R] (n) : ((Nat.rawCast n : ℤ) : R) = Nat.rawCast n := by simp

theorem intCast_negOfNat_Int {R} [CommRing R] (n) :
    ((Int.rawCast (Int.negOfNat n) : ℤ) : R) = Int.rawCast (Int.negOfNat n) := by simp

theorem intCast_mul {R} [CommRing R] {b₁ b₃ : R} {a₁ a₃ : ℤ} (a₂) (_ : ((a₁ : ℤ) : R) = b₁)
    (_ : ((a₃ : ℤ) : R) = b₃) : ((a₁ ^ a₂ * a₃ : ℤ) : R) = b₁ ^ a₂ * b₃ := by
  subst_vars; simp

theorem intCast_zero {R} [CommRing R] : ((0 : ℤ) : R) = 0 := Int.cast_zero

theorem intCast_add {R} [CommRing R] {b₁ b₂ : R} {a₁ a₂ : ℤ}
    (_ : ((a₁ : ℤ) : R) = b₁) (_ : ((a₂ : ℤ) : R) = b₂) : ((a₁ + a₂ : ℤ) : R) = b₁ + b₂ := by
  subst_vars; simp


mutual -- partial only to speed up compilation

variable {v : Lean.Level} {β : Q(Type v)} (sβ : Q(CommSemiring $β))
  (_ : v =QL 0) (_ : $β =Q ℤ) (_ : $sβ =Q inferInstance)

/-- Applies `Int.cast` to an int polynomial to produce a polynomial in `α`.

* An atom `e` causes `↑e` to be allocated as a new atom.
* A sum delegates to `ExSum.evalIntCast`.
-/
def ExBase.evalIntCast {a : Q(ℤ)} (rα : Q(CommRing $α)) (va : ExBase sβ a) :
    AtomM (Result (ExBase sα) q($a)) :=
  match va with
  | .atom _ => do
    assumeInstancesCommute
    let (i, ⟨b', _⟩) ← addAtomQ q($a)
    pure ⟨b', .atom i, q(Eq.refl $b')⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← ExSum.evalIntCast rα va
    pure ⟨_, .sum vc, p⟩


/-- Applies `Int.cast` to an int monomial to produce a monomial in `α`.

* `↑c = c` if `c` is a numeric literal
* `↑(a ^ n * b) = ↑a ^ n * ↑b`
-/
def ExProd.evalIntCast {a : Q(ℤ)} (rα : Q(CommRing $α)) (va : ExProd sβ a) :
    AtomM (Result (ExProd sα) q($a)) :=
  match va with
  | .const ⟨c, hc⟩ => do
    match a with
    | ~q(Nat.rawCast $m) =>
      pure ⟨q(Nat.rawCast $m), .const ⟨c, hc⟩, q(natCast_int (R := $α) $m)⟩
    | ~q(Int.rawCast (Int.negOfNat $m)) =>
      pure ⟨q(Int.rawCast (Int.negOfNat $m)), .const ⟨c, hc⟩, q(intCast_negOfNat_Int (R := $α) $m)⟩
  | .mul (e := a₂) (x := x) (b := b) va₁ va₂ va₃ => do
    have : $a =Q $x ^ $a₂ * $b := ⟨⟩
    let ⟨_, vb₁, pb₁⟩ ← ExBase.evalIntCast rα va₁
    let ⟨_, vb₃, pb₃⟩ ← ExProd.evalIntCast rα va₃
    assumeInstancesCommute
    pure ⟨_, .mul vb₁ va₂ vb₃, (q(intCast_mul $a₂ $pb₁ $pb₃))⟩

/-- Applies `Int.cast` to an int polynomial to produce a polynomial in `α`.

* `↑0 = 0`
* `↑(a + b) = ↑a + ↑b`
-/
def ExSum.evalIntCast {a : Q(ℤ)} (rα : Q(CommRing $α))
    (va : ExSum sβ a) :
    AtomM (Result (ExSum sα) q($a)) :=
  match va with
  | .zero => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(intCast_zero)⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← ExProd.evalIntCast rα va₁
    let ⟨_, vb₂, pb₂⟩ ← ExSum.evalIntCast rα va₂
    assumeInstancesCommute
    pure ⟨_, .add vb₁ vb₂, (q(intCast_add $pb₁ $pb₂))⟩

end


mutual

/-- Converts `ExBase sα` to `ExBase sβ`, assuming `sα` and `sβ` are defeq. -/
def ExBase.cast
    {v : Lean.Level} {β : Q(Type v)} {sβ : Q(CommSemiring $β)} {a : Q($α)} :
    ExBase sα a → Σ a, ExBase sβ a
  | .atom i => ⟨a, .atom i⟩
  | .sum a => let ⟨_, vb⟩ := ExSum.cast a; ⟨_, .sum vb⟩

/-- Converts `ExProd sα` to `ExProd sβ`, assuming `sα` and `sβ` are defeq. -/
def ExProd.cast
    {v : Lean.Level} {β : Q(Type v)} {sβ : Q(CommSemiring $β)} {a : Q($α)} :
    ExProd sα a → Σ a, ExProd sβ a
  | .const ⟨i, h⟩ => ⟨a, .const ⟨i, h⟩⟩
  | .mul a₁ a₂ a₃ => ⟨_, .mul (ExBase.cast a₁).2 a₂ (ExProd.cast a₃).2⟩

/-- Converts `ExSum sα` to `ExSum sβ`, assuming `sα` and `sβ` are defeq. -/
def ExSum.cast
    {v : Lean.Level} {β : Q(Type v)} {sβ : Q(CommSemiring $β)} {a : Q($α)} :
    ExSum sα a → Σ a, ExSum sβ a
  | .zero => ⟨_, .zero⟩
  | .add a₁ a₂ => ⟨_, .add (ExProd.cast a₁).2 (ExSum.cast a₂).2⟩

end

lemma smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b := rfl

theorem Nat.smul_eq_mul {n : ℕ} {r : R} (hr : n = r) {a : R} : n • a = r * a := by
  subst_vars
  simp only [nsmul_eq_mul]

omit [CommSemiring R] in
theorem Int.smul_eq_mul {n : ℤ} {r : R} [CommRing R] (hr : n = r) {a : R} :
    n • a = r * a := by
  subst_vars
  simp only [zsmul_eq_mul]

def BaseType.toResult {a : Q($α)} : BaseType sα a → NormNum.Result a
| ⟨q, h⟩ => Result.ofRawRat q a h

def BaseType.ofResult {a : Q($α)} (res : NormNum.Result a) : Option <| Result (BaseType sα) a := do
  let ⟨qc, hc⟩ ← res.toRatNZ
  let ⟨c, pc⟩ := res.toRawEq
  return ⟨q($c), ⟨qc, hc⟩, q($pc)⟩

namespace RingCompute

def add (a b : Q($α)) (za : BaseType sα a) (zb : BaseType sα b) :
    MetaM (Result (BaseType sα) q($a + $b) × Option Q(IsNat ($a + $b) 0)) := do
  let res ← za.toResult.add zb.toResult
  let isZero : Option Q(IsNat ($a + $b) 0) := match res with
  | Result.isNat inst lit pf =>
    if lit.natLit! == 0 then
      -- WARNING: unsafe Qq, issues with assumeInstancesCommute, even in MetaM.
      some pf
    else
      none
  | _ => none
  let r ← BaseType.ofResult sα res
  return ⟨r, isZero⟩

def mul (a b : Q($α)) (za : BaseType sα a) (zb : BaseType sα b) :
    MetaM (Result (BaseType sα) q($a * $b)) := do
  let res ← za.toResult.mul zb.toResult
  return ← BaseType.ofResult sα res

def cast (v : Lean.Level) (β : Q(Type v)) (sβ : Q(CommSemiring $β))
    (_smul : Q(HSMul $β $α $α)) (_x : Q($β))
    (rx : AtomM (Result (Common.ExSum (BaseType sβ) q($sβ)) q($_x))) :
    AtomM ((y : Q($α)) × Common.ExSum (BaseType sα) sα q($y) ×
      Q(∀ (a : $α), $_x • a = $y * a)) := do
  let ⟨x', vx, px⟩ ← rx
  if (← isDefEq sα sβ) then
    have : u =QL v := ⟨⟩
    have : $α =Q $β := ⟨⟩
    have : $sα =Q $sβ := ⟨⟩
    let ⟨b, vb⟩ := (ExSum.cast (u := v) (v := u) (sα := sβ) (sβ := sα) vx)
    have : $b =Q $x' := ⟨⟩
    assumeInstancesCommute
    return ⟨_, vb, q(fun a => $px ▸ smul_eq_mul $x' a)⟩
  match v, β, sβ with
  | 0, ~q(ℕ), ~q(inferInstance) =>
    let ⟨y, vy, py⟩ ← ExSum.evalNatCast sα sβ vx
    assumeInstancesCommute
    return ⟨y, vy, q(fun _ => $px ▸ Nat.smul_eq_mul $py)⟩
  | 0, ~q(ℤ), ~q(inferInstance) =>
    -- TODO: use the cache instead.
    let rα : Q(CommRing $α) ← synthInstanceQ q(CommRing $α)
    let ⟨y, vy, py⟩ ← ExSum.evalIntCast sα sβ rα vx
    assumeInstancesCommute
    return ⟨y, vy, q(fun _ => $px ▸ Int.smul_eq_mul $py)⟩
  | _ => failure

def neg (a : Q($α)) (_crα : Q(CommRing $α)) (za : BaseType sα a) :
    MetaM (Result (BaseType sα) q(-$a)) := do
  let res ← za.toResult.neg q(inferInstance)
  -- We have to unpack this result due to instance issues.
  let ⟨_, vc, pc⟩ ← BaseType.ofResult sα res
  return ⟨_, vc, q($pc)⟩

def pow (a : Q($α)) (za : BaseType sα a) (b : Q(ℕ))
    (vb : Common.ExProd Common.btℕ Common.sℕ q($b)) :
    OptionT MetaM (Result (BaseType sα) q($a ^ $b)) := do
  match vb with
  | .const _ =>
    -- TODO: Decide if this is the best way to extract the exponent as a Nat.
    have lit : Q(ℕ) := b.appArg!
    let res ← (NormNum.evalPow.core q($a ^ $lit) q(HPow.hPow) q($a) lit lit
      q(IsNat.raw_refl $lit) q(inferInstance) za.toResult).run
    match res with
    | none => OptionT.fail
    | some res =>
      have : $b =Q $lit := ⟨⟩
      let ⟨_, vc, pc⟩ ← BaseType.ofResult sα res
      return ⟨_, vc, q($pc)⟩
  | _ => OptionT.fail

def inv {a : Q($α)} (czα : Option Q(CharZero $α)) (_sfα : Q(Semifield $α))
    (za : BaseType sα a) : AtomM (Option (Result (BaseType sα) q($a⁻¹))) := do
  match (← (Lean.observing? <| za.toResult.inv _ czα :)) with
  | some res =>
    let ⟨_, vc, pc⟩ ← BaseType.ofResult sα res
    return some ⟨_, vc, q($pc)⟩
  | none => return none

def derive (x : Q($α)) : MetaM (Result (Common.ExSum (BaseType sα) sα) q($x)) := do
  let res ← NormNum.derive x
  let ⟨_, va, pa⟩ ← evalCast sα res
  return ⟨_, va, q($pa)⟩

def isOne {x : Q($α)} (zx : BaseType sα x) : Option Q(IsNat $x 1) := do
  let ⟨qx, _hx⟩ := zx
  if qx == 1 then
    have : $x =Q Nat.rawCast 1 := ⟨⟩
    assumeInstancesCommute
    return q(⟨rfl⟩)
  else
    failure

end RingCompute

open RingCompute in
def ringCompute : Common.RingCompute (BaseType sα) sα where
  add := add sα
  mul := mul sα
  cast := cast sα
  neg := neg sα
  pow := pow sα
  inv := inv sα
  derive := derive sα
  eq zx zy := zx.value == zy.value
  compare zx zy := compare zx.value zy.value
  isOne := isOne sα
  one := ⟨q((nat_lit 1).rawCast), ⟨1, none⟩, q(rfl)⟩
  toString {_} (zx) := s!"{zx.value}"


def rcℕ : Common.RingCompute (u := 0) Common.btℕ Common.sℕ := Ring.ringCompute Common.sℕ

universe u

/-- `CSLift α β` is a typeclass used by `ring` for lifting operations from `α`
(which is not a commutative semiring) into a commutative semiring `β` by using an injective map
`lift : α → β`. -/
class CSLift (α : Type u) (β : outParam (Type u)) where
  /-- `lift` is the "canonical injection" from `α` to `β` -/
  lift : α → β
  /-- `lift` is an injective function -/
  inj : Function.Injective lift

/-- `CSLiftVal a b` means that `b = lift a`. This is used by `ring` to construct an expression `b`
from the input expression `a`, and then run the usual ring algorithm on `b`. -/
class CSLiftVal {α} {β : outParam (Type u)} [CSLift α β] (a : α) (b : outParam β) : Prop where
  /-- The output value `b` is equal to the lift of `a`. This can be supplied by the default
  instance which sets `b := lift a`, but `ring` will treat this as an atom so it is more useful
  when there are other instances which distribute addition or multiplication. -/
  eq : b = CSLift.lift a

instance (priority := low) {α β} [CSLift α β] (a : α) : CSLiftVal a (CSLift.lift a) := ⟨rfl⟩

theorem of_lift {α β} [inst : CSLift α β] {a b : α} {a' b' : β}
    [h1 : CSLiftVal a a'] [h2 : CSLiftVal b b'] (h : a' = b') : a = b :=
  inst.2 <| by rwa [← h1.1, ← h2.1]

open Lean Parser.Tactic Elab Command Elab.Tactic

theorem of_eq {α} {a b c : α} (_ : (a : α) = c) (_ : b = c) : a = b := by subst_vars; rfl

/--
This is a routine which is used to clean up the unsolved subgoal
of a failed `ring1` application. It is overridden in `Mathlib/Tactic/Ring/RingNF.lean`
to apply the `ring_nf` simp set to the goal.
-/
initialize ringCleanupRef : IO.Ref (Expr → MetaM Expr) ← IO.mkRef pure

/-- Frontend of `ring1`: attempt to close a goal `g`, assuming it is an equation of semirings. -/
def proveEq (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "ring failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ←
    try Except.ok <$> synthInstanceQ q(CommSemiring $α)
    catch e => pure (.error e)
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let eq ← match sα with
  | .ok sα => ringCore sα e₁ e₂
  | .error e =>
    let β ← mkFreshExprMVarQ q(Type v)
    let e₁' ← mkFreshExprMVarQ q($β)
    let e₂' ← mkFreshExprMVarQ q($β)
    let (sβ, (pf : Q($e₁' = $e₂' → $e₁ = $e₂))) ← try
      let _l ← synthInstanceQ q(CSLift $α $β)
      let sβ ← synthInstanceQ q(CommSemiring $β)
      let _ ← synthInstanceQ q(CSLiftVal $e₁ $e₁')
      let _ ← synthInstanceQ q(CSLiftVal $e₂ $e₂')
      pure (sβ, q(of_lift (a := $e₁) (b := $e₂)))
    catch _ => throw e
    pure q($pf $(← ringCore sβ e₁' e₂'))
  g.assign eq
where
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  ringCore {v : Level} {α : Q(Type v)} (sα : Q(CommSemiring $α))
      (e₁ e₂ : Q($α)) : AtomM Q($e₁ = $e₂) := do
    let c ← Common.mkCache sα
    profileitM Exception "ring" (← getOptions) do
      let ⟨a, va, pa⟩ ← Common.eval ringCompute rcℕ (ringCompute sα) c e₁
      let ⟨b, vb, pb⟩ ← Common.eval ringCompute rcℕ (ringCompute sα) c e₂
      unless va.eq rcℕ (ringCompute sα) vb do
        let g ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a = $b))
        throwError "ring failed, ring expressions not equal\n{g.mvarId!}"
      have : $a =Q $b := ⟨⟩
      return q(of_eq $pa $pb)

/--
`ring1` solves the goal when it is an equality in *commutative* (semi)rings,
allowing variables in the exponent.

This version of `ring` fails if the target is not an equality.

* `ring1!` uses a more aggressive reducibility setting to determine equality of atoms.
-/
elab (name := ring1) "ring1" tk:"!"? : tactic => liftMetaMAtMain fun g ↦ do
  AtomM.run (if tk.isSome then .default else .reducible) (proveEq g)

@[tactic_alt ring1] macro "ring1!" : tactic => `(tactic| ring1 !)

end
end Ring
end Tactic
end Mathlib
