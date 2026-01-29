/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yunzhou Xie, Sidharth Hariharan
-/
-- import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic

/-!
## `norm_num` extension for complex numbers

This file provides a `norm_num` extension for complex numbers, allowing the computation of
additions, multiplications, inversions, conjugates, and powers of complex numbers.

-/

open Lean Meta Elab Qq Tactic Complex Mathlib.Tactic
open ComplexConjugate

namespace Mathlib.Meta
namespace NormNumI

structure ResultI (a : Q(ℂ)) where
  re : NormNum.Result q(RCLike.re $a)
  im : NormNum.Result q(RCLike.im $a)

-- TODO : get rid of cast in `$a = $x + Complex.I * $y`.
-- also try replace `getD` with `get!`
def ResultI.eqeq {a : Q(ℂ)} (r : ResultI a) :
    MetaM (Σ x y : Q(ℝ), Q($a = $x + Complex.I * $y)) := do
  let ⟨(x : Q(ℝ)), pf1, _⟩ ← r.re.toSimpResult
  let ⟨(y : Q(ℝ)), pf2, _⟩ ← r.im.toSimpResult
  let pf1' : Q(Complex.re $a = $x) := pf1.getD q(rfl : $x = _)
  let pf2' : Q(Complex.im $a = $y) := pf2.getD q(rfl : $y = _)
  return ⟨x, y, q(Complex.ext (by simpa using $pf1') (by simpa using $pf2'))⟩


-- def ResultI.cast {a b : Q(ℂ)} (r : ResultI a) (h : Q($a = $b)): ResultI b :=
--   { re := { r.re with expr := q(Complex.re $b) }
--     im := r.im.cast q(Complex.im $b) }
  -- have : a = b := (q(rfl (a := $a)) :)
  -- $h ▸ r

def ResultI.mk' {z : Q(ℂ)} {p1 p2 : Q(ℝ)} (h1 : NormNum.Result q($p1))
    (h2 : NormNum.Result q($p2)) (pf₁ : Q(RCLike.re $z = $p1)) (pf₂ : Q(RCLike.im $z = $p2)) :
    ResultI z where
  re := h1.eqTrans pf₁
  im := h2.eqTrans pf₂

def ResultI.eqTrans {a b : Q(ℂ)} (eq : Q($a = $b)) (r : ResultI b) : ResultI a :=
  .mk' r.re r.im q(congr_arg RCLike.re $eq) q(congr_arg RCLike.im $eq)

def ResultI.add {a b : Q(ℂ)} (ha : ResultI q($a)) (hb : ResultI q($b)) :
    MetaM (ResultI q($a + $b)) := do
  return .mk' (← ha.re.add hb.re q(inferInstance)) (← ha.im.add hb.im q(inferInstance))
    q(map_add RCLike.re $a $b) q(map_add RCLike.im $a $b)

def ResultI.neg {z : Q(ℂ)} (ha : ResultI q($z)) :
    MetaM (ResultI q(-$z)) := do
  return .mk' (← ha.re.neg q(inferInstance)) (← ha.im.neg q(inferInstance))
    q(map_neg RCLike.re $z) q(map_neg RCLike.im $z)

def ResultI.sub {a b : Q(ℂ)} (ha : ResultI q($a)) (hb : ResultI q($b)) :
    MetaM (ResultI q($a - $b)) := do
  return .mk' (← ha.re.sub hb.re q(inferInstance)) (← ha.im.sub hb.im q(inferInstance))
    q(map_sub RCLike.re $a $b) q(map_sub RCLike.im $a $b)

def ResultI.mul {a b : Q(ℂ)} (ha : ResultI q($a)) (hb : ResultI q($b)) :
    MetaM (ResultI q($a * $b)) := do
  return .mk'
    (← (← ha.re.mul hb.re q(inferInstance)).sub (← ha.im.mul hb.im q(inferInstance))
      q(inferInstance))
    (← (← ha.re.mul hb.im q(inferInstance)).add (← ha.im.mul hb.re q(inferInstance))
      q(inferInstance))
    q(RCLike.mul_re $a $b) q(RCLike.mul_im $a $b)

def ResultI.conj {z : Q(ℂ)} (hz : ResultI q($z)) :
    MetaM (ResultI q(conj $z)) := do
  return .mk' hz.re (← hz.im.neg q(inferInstance))
    q(RCLike.conj_re $z) q(RCLike.conj_im $z)

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

-- theorem IsComplex.scientific (m exp : ℕ) (x : Bool) :
--     ResultI (OfScientific.ofScientific m x exp : ℂ)
--     (OfScientific.ofScientific m x exp : ℝ) 0 :=
--   ⟨RCLike.nnratCast_re _, RCLike.nnratCast_im _⟩

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

-- theorem IsComplex.of_pow_negSucc {w : ℂ} {a b : ℝ} {n : ℕ} {k' : ℤ}
--     (hk : NormNum.IsInt k' (Int.negSucc n)) (hz : IsComplex (w ^ (n + 1))⁻¹ a b) :
--     IsComplex (w ^ (k' : ℤ)) a b := by
--   rwa [hk.out, Int.cast_id, zpow_negSucc]

-- theorem IsComplex.of_pow_ofNat {w : ℂ} {k : ℤ} {n : ℕ} {a b : ℝ}
--     (hkk' : NormNum.IsInt k n) (hw : IsComplex (w ^ n) a b) :
--     IsComplex (w ^ k) a b := by
--   obtain rfl : k = n := by simpa using hkk'.out
--   simpa only [zpow_natCast] using hw

-- theorem pow_bit_false (z : ℂ) (m : ℕ) : z ^ Nat.bit false m = z ^ m * z ^ m := by
--   rw [Nat.bit, cond, pow_mul', sq]

-- theorem pow_bit_true (z : ℂ) (m : ℕ) : z ^ Nat.bit true m = z ^ m * z ^ m * z := by
--   rw [Nat.bit, cond, pow_add, pow_mul', pow_one, sq]

-- /-- Using fast exponentiation to handle nat powers of complexes. -/
-- partial def parsePow (n' : ℕ) :
--     ⦃a b : Q(ℝ)⦄ → (z : Q(ℂ)) → (n : Q(ℕ)) → Q(NormNum.IsNat $n $n') →  Q(IsComplex $z $a $b) →
--     MetaM (Σ a b : Q(ℝ), Q(IsComplex ($z ^ $n) $a $b)) :=
--   n'.binaryRec'
--     (fun {_ _} z n _ _ => do
--       have : $n =Q 0 := ⟨⟩
--       return ⟨q(1), q(0), q(pow_zero $z ▸ .one)⟩)
--     (fun bit (m : ℕ) _ rec {_ _} z n _ hz => do
--       match bit with
--       | true =>
--         have : $n =Q Nat.bit true $m := ⟨⟩
--         let ⟨_, _, hzm⟩ ← rec q($z) q($m) q(⟨rfl⟩) hz
--         return ⟨_, _, q(have hzm' := $hzm; pow_bit_true $z $m ▸
--          (IsComplex.mul hzm' hzm').mul $hz)⟩
--       | false =>
--         have : $n =Q Nat.bit false $m := ⟨⟩
--         let ⟨_, _, hzm⟩ ← rec q($z) q($m) q(⟨rfl⟩) hz
--         return ⟨_, _, q(have hzm' := $hzm; pow_bit_false $z $m ▸ IsComplex.mul hzm' hzm')⟩)
def NormNum.Resultn (n0 : ℕ) : MetaM (NormNum.Result q(OfNat.ofNat (α := ℝ) $n0)) := do
  have n : Q(ℕ) := .lit (.natVal n0)
  let e : Q(ℝ) := q(OfNat.ofNat (α := ℝ) $n)
  let ⟨_, (pa : Q($n = $e))⟩ ← NormNum.mkOfNat q(ℝ) q(inferInstance) n
  return NormNum.Result.isNat (α := q(ℝ)) q(inferInstance) n q(NormNum.isNat_ofNat ℝ $pa)

-- def NormNum.OfScientific

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
  -- | ~q($w ^ ($n' : ℕ)) =>
  --   let ⟨_, _, pf⟩ ← parse w
  --   let ⟨_, _, pfp⟩ ← parsePow n.natLit! q($w) q($n') hn q($pf)
  --   return ⟨_, _, q($pfp)⟩
  -- | ~q($w ^ ($k : ℤ)) =>
  --   let ⟨k', hm⟩ ← NormNum.deriveInt q($k) q(inferInstance)
  --   match k'.intLit! with
  --   | Int.ofNat n =>
  --     let ⟨a, b, pf⟩ ← parse q($w ^ $n)
  --     let _i : $k' =Q $n := ⟨⟩
  --     return ⟨a, b, q(.of_pow_ofNat $hm $pf)⟩
  --   | Int.negSucc n =>
  --     let ⟨a, b, pf⟩ ← parse q(($w ^ ($n + 1))⁻¹)
  --     let _i : $k' =Q Int.negSucc $n := ⟨⟩
  --     return ⟨a, b, q(.of_pow_negSucc $hm $pf)⟩
  | ~q(Complex.I) =>
      -- a bit tricky because `I.im` could be either `1` or `0`
  return ResultI.mk (← NormNum.Resultn 0) (← NormNum.Resultn 1)
  | ~q(0) =>
  return ResultI.mk (← NormNum.Resultn 0) (← NormNum.Resultn 0)
  | ~q(1) =>
  return ResultI.mk (← NormNum.Resultn 1) (← NormNum.Resultn 0)
  | ~q(OfNat.ofNat $en (self := @instOfNatAtLeastTwo ℂ _ _ $inst)) =>
  let some n := en.rawNatLit? | failure
  return ResultI.mk (← NormNum.Resultn n) (← NormNum.Resultn 0) --q(sorry) q(rfl)
  | ~q(OfScientific.ofScientific $m $x $exp) =>
  return sorry
  --   return ⟨_, _, q(.scientific _ _ _)⟩
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
