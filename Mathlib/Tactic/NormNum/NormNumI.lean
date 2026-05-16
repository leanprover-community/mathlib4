/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yunzhou Xie, Sidharth Hariharan
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
## `norm_num` extension for complex numbers

This file provides a `norm_num` extension for complex numbers, allowing the computation of
additions, multiplications, inversions, conjugates, and powers of complex numbers.

-/

public meta section

open Lean Meta Elab Qq Tactic Complex Mathlib.Tactic
open ComplexConjugate

namespace Mathlib.Meta.NormNumI

/-- The result of `norm_num` running on an expression `a : ℂ`. -/
structure ResultI (a : Q(ℂ)) where
  /-- The result of `norm_num` running on the real part of `a`. -/
  re : NormNum.Result q(RCLike.re $a)
  /-- The result of `norm_num` running on the imaginary part of `a`. -/
  im : NormNum.Result q(RCLike.im $a)

-- TODO : get rid of cast in `$a = $x + Complex.I * $y`.
-- also try replace `getD` with `get!`
/-- when obtained a result `a` in `ResultI`, one could get `x y : ℝ` such that `a = x + yi`. -/
def ResultI.eqeq {a : Q(ℂ)} (r : ResultI a) :
    MetaM (Σ x y : Q(ℝ), Q($a = $x + Complex.I * $y)) := do
  let ⟨(x : Q(ℝ)), pf1, _⟩ ← r.re.toSimpResult
  let ⟨(y : Q(ℝ)), pf2, _⟩ ← r.im.toSimpResult
  let pf1' : Q(Complex.re $a = $x) := pf1.getD q(rfl : $x = _)
  let pf2' : Q(Complex.im $a = $y) := pf2.getD q(rfl : $y = _)
  return ⟨x, y, q(Complex.ext (by simpa using $pf1') (by simpa using $pf2'))⟩

/-- ResultI made from two Results on real and imaginary parts. -/
def ResultI.mk' {z : Q(ℂ)} {p1 p2 : Q(ℝ)} (h1 : NormNum.Result q($p1))
    (h2 : NormNum.Result q($p2)) (pf₁ : Q(RCLike.re $z = $p1)) (pf₂ : Q(RCLike.im $z = $p2)) :
    ResultI z where
  re := h1.eqTrans pf₁
  im := h2.eqTrans pf₂

/-- ResultI induced by equality -/
def ResultI.eqTrans {a b : Q(ℂ)} (eq : Q($a = $b)) (r : ResultI b) : ResultI a :=
  .mk' r.re r.im q(congr_arg RCLike.re $eq) q(congr_arg RCLike.im $eq)

/-- ResultI induced by addition -/
def ResultI.add {a b : Q(ℂ)} (ha : ResultI q($a)) (hb : ResultI q($b)) :
    MetaM (ResultI q($a + $b)) := do
  return .mk' (← ha.re.add hb.re q(inferInstance)) (← ha.im.add hb.im q(inferInstance))
    q(map_add RCLike.re $a $b) q(map_add RCLike.im $a $b)

/-- ResultI induced by negation -/
def ResultI.neg {z : Q(ℂ)} (ha : ResultI q($z)) :
    MetaM (ResultI q(-$z)) := do
  return .mk' (← ha.re.neg q(inferInstance)) (← ha.im.neg q(inferInstance))
    q(map_neg RCLike.re $z) q(map_neg RCLike.im $z)

/-- ResultI induced by subtraction -/
def ResultI.sub {a b : Q(ℂ)} (ha : ResultI q($a)) (hb : ResultI q($b)) :
    MetaM (ResultI q($a - $b)) := do
  return .mk' (← ha.re.sub hb.re q(inferInstance)) (← ha.im.sub hb.im q(inferInstance))
    q(map_sub RCLike.re $a $b) q(map_sub RCLike.im $a $b)

/-- ResultI induced by multiplication -/
def ResultI.mul {a b : Q(ℂ)} (ha : ResultI q($a)) (hb : ResultI q($b)) :
    MetaM (ResultI q($a * $b)) := do
  return .mk'
    (← (← ha.re.mul hb.re q(inferInstance)).sub (← ha.im.mul hb.im q(inferInstance))
      q(inferInstance))
    (← (← ha.re.mul hb.im q(inferInstance)).add (← ha.im.mul hb.re q(inferInstance))
      q(inferInstance))
    q(RCLike.mul_re $a $b) q(RCLike.mul_im $a $b)

/-- ResultI induced by conjugation -/
def ResultI.conj {z : Q(ℂ)} (hz : ResultI q($z)) :
    MetaM (ResultI q(conj $z)) := do
  return .mk' hz.re (← hz.im.neg q(inferInstance))
    q(RCLike.conj_re $z) q(RCLike.conj_im $z)

/-- ResultI induced by taking inverse -/
def ResultI.inv {z : Q(ℂ)} (hz : ResultI q($z)) :
    MetaM (ResultI q($z⁻¹)) := do
  return .mk'
    (← (← (← (← hz.re.mul hz.re q(inferInstance)).add (← hz.im.mul hz.im q(inferInstance))
      q(inferInstance)).inv q(inferInstance) (Option.some q(inferInstance))).mul hz.re
      q(inferInstance))
    (← ((← (← (← (← hz.re.mul hz.re q(inferInstance)).add (← hz.im.mul hz.im q(inferInstance))
      q(inferInstance)).inv q(inferInstance) (Option.some q(inferInstance))).mul hz.im
      q(inferInstance))).neg q(inferInstance))
    q(by rw [RCLike.inv_re, div_eq_mul_inv, mul_comm, RCLike.normSq_apply])
    q(by rw [RCLike.inv_im, div_eq_mul_inv, mul_comm, RCLike.normSq_apply, mul_neg])

theorem eq_of_eq_of_eq_of_eq {z w : ℂ}
    (ha : (RCLike.re z = RCLike.re w) = True)
    (hb : (RCLike.im z = RCLike.im w) = True) : z = w := by
  apply RCLike.ext <;> simp_all

theorem ne_of_re_ne {z w : ℂ} (h : (RCLike.re z = RCLike.re w) = False) :
    z ≠ w := by
  rintro rfl
  simp_all

theorem ne_of_im_ne {z w : ℂ} (h : (RCLike.im z = RCLike.im w) = False) :
    z ≠ w := by
  rintro rfl
  simp_all

theorem of_pow_negSucc (w : ℂ) {n : ℕ} {k' : ℤ} (hk : NormNum.IsInt k' (Int.negSucc n)) :
    (w ^ (k' : ℤ)) = (w ^ (n + 1))⁻¹ := by
  rw [hk.out, Int.cast_id, zpow_negSucc]

theorem of_pow_ofNat (w : ℂ) {k : ℤ} {n : ℕ} (hkk' : NormNum.IsInt k n) :
    w ^ k = w ^ n := by
  simp [hkk'.out]

theorem re_pow_zero (z : ℂ) : NormNum.IsNat (re (z ^ 0)) 1 := ⟨by simp⟩
theorem im_pow_zero (z : ℂ) : NormNum.IsNat (im (z ^ 0)) 0 := ⟨by simp⟩

theorem pow_bit_false (z : ℂ) (m : ℕ) : z ^ Nat.bit false m = z ^ m * z ^ m := by
  rw [Nat.bit, cond, pow_mul', sq]

theorem pow_bit_true (z : ℂ) (m : ℕ) : z ^ Nat.bit true m = z ^ m * z ^ m * z := by
  rw [Nat.bit, cond, pow_add, pow_mul', pow_one, sq]

/-- Using fast exponentiation to handle nat powers of complexes. -/
partial def ResultI.pow (n' : ℕ) :
    (z : Q(ℂ)) → (n : Q(ℕ)) → Q(NormNum.IsNat $n $n') → (r : ResultI z) →
    MetaM (ResultI q($z ^ $n)) :=
  n'.binaryRec'
    (fun z n _ _ => do
      have : $n =Q 0 := ⟨⟩
      return ⟨.isNat q(inferInstance) q(1) q(re_pow_zero $z),
        .isNat q(inferInstance) q(0) q(im_pow_zero $z)⟩)
    (fun bit (m : ℕ) _ rec z n _ hz => do
      let rm ← rec q($z) q($m) q(⟨rfl⟩) hz
      let rm2 ← rm.mul rm
      match bit with
      | true =>
        have : $n =Q Nat.bit true $m := ⟨⟩
        return (← rm2.mul hz).eqTrans q(pow_bit_true $z $m)
      | false =>
        have : $n =Q Nat.bit false $m := ⟨⟩
        return rm2.eqTrans q(pow_bit_false $z $m))

/-- Result of `norm_num` running on lift of natural numbers in real -/
def NormNum.Resultn (n0 : ℕ) : MetaM (NormNum.Result q(OfNat.ofNat (α := ℝ) $n0)) := do
  have n : Q(ℕ) := .lit (.natVal n0)
  let ⟨_, (pa)⟩ ← NormNum.mkOfNat q(ℝ) q(inferInstance) n
  return NormNum.Result.isNat (α := q(ℝ)) q(inferInstance) n q(NormNum.isNat_ofNat ℝ $pa)

/-- Result of `norm_num` on scientific expressions in real -/
def NormNum.ResultOfScientific (mantissa : ℕ) (exponentSign : Bool) (decimalExponent : ℕ) :
    MetaM (NormNum.Result q(OfScientific.ofScientific (α := ℝ) $mantissa
    $exponentSign $decimalExponent )) := do
  let x : Q(ℝ) := q(OfScientific.ofScientific (α := ℝ) $mantissa
    $exponentSign $decimalExponent )
  match exponentSign with
  | true =>
    let rme ← NormNum.derive (q(mkRat $mantissa (10 ^ $decimalExponent)) : Q(ℝ))
    let some ⟨q, n, d, p⟩ := rme.toNNRat' q(inferInstance) | failure
    assumeInstancesCommute
    return .isNNRat (x := x) q(inferInstance) q n d (q(NormNum.isNNRat_ofScientific_of_true $p):)
  | false =>
  let n' := Nat.mul mantissa (Nat.pow (10 : ℕ) decimalExponent)
  have n : Q(ℕ) := mkRawNatLit n'
  have pm : Q(NormNum.IsNat $mantissa $mantissa) := q(.mk rfl)
  have pe : Q(NormNum.IsNat $decimalExponent $decimalExponent) := q(.mk rfl)
  haveI : $n =Q Nat.mul $mantissa (Nat.pow (10 : ℕ) $decimalExponent) := ⟨⟩
  return .isNat (x := x) q(inferInstance) n
    (q(NormNum.isNat_ofScientific_of_false (α := ℝ) $pm $pe (.refl $n)):)

/-- Parsing all the basic calculation in complex. -/
partial def parse (z : Q(ℂ)) : MetaM (ResultI q($z)) := do
  trace[debug] "NormNumI.parse: parsing {z}"
  match z with
  | ~q($z₁ + $z₂) =>
    let r1 ← parse z₁
    let r2 ← parse z₂
    return ((← r1.add r2).eqTrans q(rfl))
  | ~q($z₁ * $z₂) =>
    let r1 ← parse z₁
    let r2 ← parse z₂
    return ((← r1.mul r2).eqTrans q(rfl))
  | ~q($z⁻¹) =>
    let r ← parse z
    return ((← r.inv).eqTrans q(rfl))
  | ~q($z₁ / $z₂) => do
    let r ← parse q($z₁ * $z₂⁻¹)
    return r.eqTrans q(rfl)
  | ~q(-$w) => do
    let r ← parse w
    return ((← r.neg).eqTrans q(rfl))
  | ~q($z₁ - $z₂) =>
    let r1 ← parse z₁
    let r2 ← parse z₂
    return ((← r1.sub r2).eqTrans q(rfl))
  | ~q(conj $w) =>
    let r ← parse w
    return ((← r.conj).eqTrans q(rfl))
  | ~q($w ^ ($n' : ℕ)) =>
    let rw ← parse w
    let ⟨n, hn⟩ ← NormNum.deriveNat q($n') q(inferInstance)
    return (← rw.pow n.natLit! _ _ hn).eqTrans q(rfl)
  | ~q($w ^ ($k : ℤ)) =>
    let ⟨k', hm⟩ ← NormNum.deriveInt q($k) q(inferInstance)
    match k'.intLit! with
    | Int.ofNat n =>
      let r ← parse q($w ^ $n)
      let _i : $k' =Q $n := ⟨⟩
      return r.eqTrans q(of_pow_ofNat $w $hm)
    | Int.negSucc n =>
      let r ← parse q(($w ^ ($n + 1))⁻¹)
      let _i : $k' =Q Int.negSucc $n := ⟨⟩
      return r.eqTrans q(of_pow_negSucc $w $hm)
  | ~q(Complex.I) =>
  return ResultI.mk (← NormNum.Resultn 0) (← NormNum.Resultn 1)
  | ~q(0) =>
  return ResultI.mk (← NormNum.Resultn 0) (← NormNum.Resultn 0)
  | ~q(1) =>
  return ResultI.mk (← NormNum.Resultn 1) (← NormNum.Resultn 0)
  | ~q(OfNat.ofNat $en (self := @instOfNatAtLeastTwo ℂ _ _ $inst)) =>
  let some n := en.rawNatLit? | failure
  return ResultI.mk (← NormNum.Resultn n) (← NormNum.Resultn 0)
  | ~q(OfScientific.ofScientific $em $ex $eexp) =>
  let some m := em.rawNatLit? | failure
  let x : Bool := ex.isConstOf ``true
  let some exp := eexp.rawNatLit? | failure
  return ResultI.mk (← NormNum.ResultOfScientific m x exp) (← NormNum.Resultn 0)
  | _ => throwError "found the atom {z} which is not a numeral"

/-- Create the `NormNumI` tactic in `conv` mode. -/
elab "norm_numI" : conv => do
  let z ← Conv.getLhs
  let ⟨1, ~q(ℂ), z⟩ ← inferTypeQ z | throwError "{z} is not a complex number"
  let r1 ← parse z
  let ⟨_, _, pf⟩ ← r1.eqeq
  let r : Simp.ResultQ q($z) := .mk _ <| .some q(($pf))
  Conv.applySimpResult r

end NormNumI

namespace NormNum

/-- The `norm_num` extension which identifies expressions of the form `(z : ℂ) = (w : ℂ)`,
such that `norm_num` successfully recognises both the real and imaginary parts of both `z` and `w`.
-/
@[norm_num (_ : ℂ) = _] def evalComplexEq : NormNumExt where eval {v β} e := do
  trace[debug] "trigger norm_num instance for {e}"
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let ~q(($z : ℂ) = $w) := e | failure
  haveI' : $e =Q ($z = $w) := ⟨⟩
  let ⟨z1, z2⟩ ← NormNumI.parse z
  let ⟨w1, w2⟩ ← NormNumI.parse w
  let ⟨e, some pf, _⟩ := ← (← Result.eq z1 w1).toSimpResult | failure
  if ← isDefEq e q(True) then
    let ⟨e', some pf', _⟩ := ← (← Result.eq z2 w2).toSimpResult | failure
    if ← isDefEq e' q(True) then
      let pfn ← mkAppM ``NormNumI.eq_of_eq_of_eq_of_eq #[pf, pf']
      return Result'.isBool true pfn
    else
      let pfn ← mkAppM ``NormNumI.ne_of_im_ne #[pf']
      return Result'.isBool false pfn
  else
    let pfn ← mkAppM ``NormNumI.ne_of_re_ne #[pf]
    return Result'.isBool false pfn

/-- The `norm_num` extension which identifies expressions of the form `Complex.re (z : ℂ)`,
such that `norm_num` successfully recognises the real part of `z`.
-/
@[norm_num Complex.re _] def evalRe : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℝ := ⟨⟩
  let ~q(Complex.re $z) := e | failure
  return (← NormNumI.parse z).re

/-- The `norm_num` extension which identifies expressions of the form `Complex.im (z : ℂ)`,
such that `norm_num` successfully recognises the imaginary part of `z`.
-/
@[norm_num Complex.im _] def evalIm : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℝ := ⟨⟩
  let ~q(Complex.im $z) := e | failure
  return (← NormNumI.parse z).im

end NormNum

end Mathlib.Meta
