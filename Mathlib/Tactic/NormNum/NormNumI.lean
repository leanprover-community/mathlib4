/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yunzhou Xie, Sidharth Hariharan
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Complex.Basic

/-!
## `norm_num` extension for complex numbers

This file provides a `norm_num` extension for complex numbers, allowing the computation of
additions, multiplications, inversions, conjugates, and powers of complex numbers.

-/

open Lean Meta Elab Qq Tactic Complex Mathlib.Tactic
open ComplexConjugate

namespace Mathlib.Meta
namespace NormNumI

/-- Assert that a complex number is equal to `re + im * I`. -/
structure IsComplex (z : ℂ) (re im : ℝ) : Prop where
  out : z = ⟨re, im⟩

theorem IsComplex.I : IsComplex I 0 1 := ⟨rfl⟩

theorem IsComplex.zero : IsComplex (0 : ℂ) 0 0 := ⟨rfl⟩

theorem IsComplex.one : IsComplex (1 : ℂ) 1 0 := ⟨rfl⟩

theorem IsComplex.add : ∀ {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ},
    IsComplex z₁ a₁ b₁ → IsComplex z₂ a₂ b₂ → IsComplex (z₁ + z₂) (a₁ + a₂) (b₁ + b₂)
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩ => ⟨rfl⟩

theorem IsComplex.mul : ∀ {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ},
    IsComplex z₁ a₁ b₁ → IsComplex z₂ a₂ b₂ →
      IsComplex (z₁ * z₂) (a₁ * a₂ - b₁ * b₂) (a₁ * b₂ + b₁ * a₂)
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩ => ⟨rfl⟩

theorem IsComplex.inv {z : ℂ} {x y : ℝ} (h : IsComplex z x y) :
    IsComplex z⁻¹ (x / (x * x + y * y)) (- y / (x * x + y * y)) := by
  constructor
  obtain ⟨rfl⟩ := h
  rw [inv_def]
  exact Complex.ext (by simp [normSq_apply]; rfl) (by simp [normSq_apply, neg_div]; rfl)

theorem IsComplex.neg : ∀ {z : ℂ} {a b : ℝ}, IsComplex z a b → IsComplex (-z) (-a) (-b)
  | _, _, _, ⟨rfl⟩ => ⟨rfl⟩

theorem IsComplex.sub : ∀ {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ},
    IsComplex z₁ a₁ b₁ → IsComplex z₂ a₂ b₂ → IsComplex (z₁ - z₂) (a₁ - a₂) (b₁ - b₂)
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩ => ⟨rfl⟩

theorem IsComplex.conj : ∀ {z : ℂ} {a b : ℝ}, IsComplex z a b → IsComplex (conj z) a (-b)
  | _, _, _, ⟨rfl⟩ => ⟨rfl⟩

theorem IsComplex.ofNat (n : ℕ) [n.AtLeastTwo] :
    IsComplex (OfNat.ofNat (α := ℂ) n) (OfNat.ofNat n) 0 := ⟨rfl⟩

theorem IsComplex.scientific (m exp : ℕ) (x : Bool) :
    IsComplex (OfScientific.ofScientific m x exp : ℂ) (OfScientific.ofScientific m x exp : ℝ) 0 :=
  ⟨rfl⟩

theorem eq_eq {z : ℂ} {a b a' b' : ℝ} (pf : IsComplex z a b) (pf_a : a = a') (pf_b : b = b') :
  IsComplex z a' b' := by simp_all

theorem eq_of_eq_of_eq_of_eq {z w : ℂ} {az bz aw bw : ℝ}
    (hz : IsComplex z az bz) (hw : IsComplex w aw bw)
    (ha : az = aw) (hb : bz = bw) : z = w := by
  simp [hz.out, hw.out, ha, hb]

theorem ne_of_re_ne {z w : ℂ} {az bz aw bw : ℝ} (hz : IsComplex z az bz) (hw : IsComplex w aw bw)
    (ha : az ≠ aw) : z ≠ w := by
  simp [hz.out, hw.out, ha]

theorem ne_of_im_ne {z w : ℂ} {az bz aw bw : ℝ} (hz : IsComplex z az bz) (hw : IsComplex w aw bw)
    (hb : bz ≠ bw) : z ≠ w := by
  simp [hz.out, hw.out, hb]

theorem IsComplex.re_eq {z : ℂ} {a b : ℝ} (hz : IsComplex z a b) : Complex.re z = a := by
  simp [hz.out]

theorem IsComplex.im_eq {z : ℂ} {a b : ℝ} (hz : IsComplex z a b) : Complex.im z = b := by
  simp [hz.out]

theorem IsComplex.of_pow_negSucc {w : ℂ} {a b : ℝ} {n : ℕ} {k' : ℤ}
    (hk : NormNum.IsInt k' (Int.negSucc n)) (hz : IsComplex (w ^ (n + 1))⁻¹ a b) :
    IsComplex (w ^ (k' : ℤ)) a b := by
  constructor
  rw [hk.out, Int.cast_id, zpow_negSucc, hz.out]

theorem IsComplex.of_pow_ofNat {w : ℂ} {k : ℤ} {n : ℕ} {a b : ℝ}
    (hkk' : NormNum.IsInt k n) (hw : IsComplex (w ^ n) a b) :
    IsComplex (w ^ k) a b := by
  obtain rfl : k = n := by simpa using hkk'.out
  constructor
  simpa using hw.out

theorem pow_bit_false (z : ℂ) (m : ℕ) : z ^ Nat.bit false m = z ^ m * z ^ m := by
  rw [Nat.bit, cond, pow_mul', sq]

theorem pow_bit_true (z : ℂ) (m : ℕ) : z ^ Nat.bit true m = z ^ m * z ^ m * z := by
  rw [Nat.bit, cond, pow_add, pow_mul', pow_one, sq]

/-- Using fast exponentiation to handle nat powers of complexes. -/
partial def parsePow (n' : ℕ) :
    ⦃a b : Q(ℝ)⦄ → (z : Q(ℂ)) → (n : Q(ℕ)) → Q(NormNum.IsNat $n $n') →  Q(IsComplex $z $a $b) →
    MetaM (Σ a b : Q(ℝ), Q(IsComplex ($z ^ $n) $a $b)) :=
  n'.binaryRec'
    (fun {_ _} z n _ _ => do
      have : $n =Q 0 := ⟨⟩
      return ⟨q(1), q(0), q(pow_zero $z ▸ .one)⟩)
    (fun bit (m : ℕ) _ rec {_ _} z n _ hz => do
      match bit with
      | true =>
        have : $n =Q Nat.bit true $m := ⟨⟩
        let ⟨_, _, hzm⟩ ← rec q($z) q($m) q(⟨rfl⟩) hz
        return ⟨_, _, q(have hzm' := $hzm; pow_bit_true $z $m ▸ (IsComplex.mul hzm' hzm').mul $hz)⟩
      | false =>
        have : $n =Q Nat.bit false $m := ⟨⟩
        let ⟨_, _, hzm⟩ ← rec q($z) q($m) q(⟨rfl⟩) hz
        return ⟨_, _, q(have hzm' := $hzm; pow_bit_false $z $m ▸ IsComplex.mul hzm' hzm')⟩)

/-- Parsing all the basic calculation in complex. -/
partial def parse (z : Q(ℂ)) : MetaM (Σ a b : Q(ℝ), Q(IsComplex $z $a $b)) := do
  match z with
  | ~q($z₁ + $z₂) =>
    let ⟨_a₁, _b₁, pf₁⟩ ← parse z₁
    let ⟨_a₂, _b₂, pf₂⟩ ← parse z₂
    pure ⟨_, _, q(.add $pf₁ $pf₂)⟩
  | ~q($z₁ * $z₂) =>
    let ⟨_a₁, _b₁, pf₁⟩ ← parse z₁
    let ⟨_a₂, _b₂, pf₂⟩ ← parse z₂
    pure ⟨_, _, q(.mul $pf₁ $pf₂)⟩
  | ~q($z⁻¹) =>
    let ⟨_x, _y, pf⟩ ← parse z
    pure ⟨_, _, q(.inv $pf)⟩
  | ~q($z₁ / $z₂) => do
    let ⟨_a, _b, pf⟩ ← parse q($z₁ * $z₂⁻¹)
    return ⟨_, _, q($pf)⟩
  | ~q(-$w) => do
    let ⟨_a, _b, pf⟩ ← parse w
    return ⟨_, _, q(.neg $pf)⟩
  | ~q($z₁ - $z₂) =>
    let ⟨_a₁, _b₁, pf₁⟩ ← parse z₁
    let ⟨_a₂, _b₂, pf₂⟩ ← parse z₂
    pure ⟨_, _, q(.sub $pf₁ $pf₂)⟩
  | ~q(conj $w) =>
    let ⟨_a, _b, pf⟩ ← parse w
    return ⟨_, _, q(.conj $pf)⟩
  | ~q($w ^ ($n' : ℕ)) =>
    let ⟨n, hn⟩ ← NormNum.deriveNat q($n') q(inferInstance)
    let ⟨_, _, pf⟩ ← parse w
    let ⟨_, _, pfp⟩ ← parsePow n.natLit! q($w) q($n') hn q($pf)
    return ⟨_, _, q($pfp)⟩
  | ~q($w ^ ($k : ℤ)) =>
    let ⟨k', hm⟩ ← NormNum.deriveInt q($k) q(inferInstance)
    match k'.intLit! with
    | Int.ofNat n =>
      let ⟨a, b, pf⟩ ← parse q($w ^ $n)
      let _i : $k' =Q $n := ⟨⟩
      return ⟨a, b, q(.of_pow_ofNat $hm $pf)⟩
    | Int.negSucc n =>
      let ⟨a, b, pf⟩ ← parse q(($w ^ ($n + 1))⁻¹)
      let _i : $k' =Q Int.negSucc $n := ⟨⟩
      return ⟨a, b, q(.of_pow_negSucc $hm $pf)⟩
  | ~q(Complex.I) =>
    pure ⟨_, _, q(.I)⟩
  | ~q(0) =>
    pure ⟨_, _, q(.zero)⟩
  | ~q(1) =>
    pure ⟨_, _, q(.one)⟩
  | ~q(OfNat.ofNat $en (self := @instOfNatAtLeastTwo ℂ _ _ $inst)) =>
    return ⟨_, _, q(.ofNat $en)⟩
  | ~q(OfScientific.ofScientific $m $x $exp) =>
    return ⟨_, _, q(.scientific _ _ _)⟩
  | _ => throwError "found the atom {z} which is not a numeral"

/-- Using `norm_num` to normalise expressions -/
def normalize (z : Q(ℂ)) : MetaM (Σ a b : Q(ℝ), Q(IsComplex $z $a $b)) := do
  let ⟨a, b, pf⟩ ← parse z
  let ra ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) a
  let rb ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) b
  let { expr := (a' : Q(ℝ)), proof? := (pf_a : Q($a = $a')) } ← ra.toSimpResult | unreachable!
  let { expr := (b' : Q(ℝ)), proof? := (pf_b : Q($b = $b')) } ← rb.toSimpResult | unreachable!
  return ⟨a', b', q(eq_eq $pf $pf_a $pf_b)⟩

/-- Create the `NormNumI` tactic in `conv` mode. -/
elab "norm_numI" : conv => do
  let z ← Conv.getLhs
  let ⟨1, ~q(ℂ), z⟩ ← inferTypeQ z | throwError "{z} is not a complex number"
  let ⟨_, _, pf⟩ ← normalize z
  let r : Simp.ResultQ q($z) := .mk _ <| .some q(($pf).out)
  Conv.applySimpResult r

end NormNumI
namespace NormNum

/-- The `norm_num` extension which identifies expressions of the form `(z : ℂ) = (w : ℂ)`,
such that `norm_num` successfully recognises both the real and imaginary parts of both `z` and `w`.
-/
@[norm_num (_ : ℂ) = _] def evalComplexEq : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let ~q(($z : ℂ) = $w) := e | failure
  haveI' : $e =Q ($z = $w) := ⟨⟩
  let ⟨az, bz, pfz⟩ ← NormNumI.parse z
  let ⟨aw, bw, pfw⟩ ← NormNumI.parse w
  let ⟨ba, ra⟩ ← deriveBool q($az = $aw)
  match ba with
  | true =>
    let ⟨bb, rb⟩ ← deriveBool q($bz = $bw)
    match bb with
    | true => return Result'.isBool true q(NormNumI.eq_of_eq_of_eq_of_eq $pfz $pfw $ra $rb)
    | false => return Result'.isBool false q(NormNumI.ne_of_im_ne $pfz $pfw $rb)
  | false => return Result'.isBool false q(NormNumI.ne_of_re_ne $pfz $pfw $ra)

/-- The `norm_num` extension which identifies expressions of the form `Complex.re (z : ℂ)`,
such that `norm_num` successfully recognises the real part of `z`.
-/
@[norm_num Complex.re _] def evalRe : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℝ := ⟨⟩
  let ~q(Complex.re $z) := e | failure
  let ⟨a, _, pf⟩ ← NormNumI.parse z
  let r ← derive q($a)
  return r.eqTrans q(($pf).re_eq)

/-- The `norm_num` extension which identifies expressions of the form `Complex.im (z : ℂ)`,
such that `norm_num` successfully recognises the imaginary part of `z`.
-/
@[norm_num Complex.im _] def evalIm : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℝ := ⟨⟩
  let ~q(Complex.im $z) := e | failure
  let ⟨_, b, pf⟩ ← NormNumI.parse z
  let r ← derive q($b)
  return r.eqTrans q(($pf).im_eq)

end NormNum

end Mathlib.Meta
