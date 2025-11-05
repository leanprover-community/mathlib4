/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yunzhou Xie, Sidharth Hariharan
-/
import Mathlib.Analysis.Normed.Ring.Basic
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


-- def ResultI.cast {a b : Q(ℂ)} (r : ResultI a) (h : Q($a = $b)): ResultI b :=
--   { re := { r.re with expr := q(Complex.re $b) }
--     im := r.im.cast q(Complex.im $b) }
  -- have : a = b := (q(rfl (a := $a)) :)
  -- $h ▸ r
#check NormNum.Result

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

def ResultI.mul {a b : Q(ℂ)} (ha : ResultI q($a)) (hb : ResultI q($b)) :
    MetaM (ResultI q($a * $b)) := do
  return .mk'
    (← (← ha.re.mul hb.re q(inferInstance)).sub (← ha.im.mul hb.im q(inferInstance))
      q(inferInstance))
    (← (← ha.re.mul hb.im q(inferInstance)).add (← ha.im.mul hb.re q(inferInstance))
      q(inferInstance))
    q(RCLike.mul_re $a $b) q(RCLike.mul_im $a $b)

-- /-- Assert that a complex number is equal to `re + im * I`. -/
-- structure IsComplex [RCLike ℂ] (z : ℂ) (re im : ℝ) : Prop where
--   re_eq : RCLike.re z = re
--   im_eq : RCLike.im z = im

-- theorem IsComplex.I : IsComplex (RCLike.I : ℂ) 0 1 := ⟨rfl, rfl⟩

-- theorem IsComplex.zero : IsComplex (0 : ℂ) 0 0 := ⟨RCLike.zero_re, RCLike.zero_im⟩

-- theorem IsComplex.one : IsComplex (1 : ℂ) 1 0 := ⟨RCLike.one_re, RCLike.one_im⟩

-- theorem IsComplex.add : ∀ {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ},
--     IsComplex z₁ a₁ b₁ → IsComplex z₂ a₂ b₂ → IsComplex (z₁ + z₂) (a₁ + a₂) (b₁ + b₂)
--   | _, _, _, _, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩ => ⟨map_add _ _ _, map_add _ _ _⟩

-- theorem IsComplex.mul : ∀ {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ},
--     IsComplex z₁ a₁ b₁ → IsComplex z₂ a₂ b₂ →
--       IsComplex (z₁ * z₂) (a₁ * a₂ - b₁ * b₂) (a₁ * b₂ + b₁ * a₂)
--   | z₁, z₂, _, _, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩ => ⟨RCLike.mul_re z₁ z₂, RCLike.mul_im z₁ z₂⟩

-- theorem IsComplex.inv {z : ℂ} {x y : ℝ} (h : IsComplex z x y) :
--     IsComplex z⁻¹ (x / (x * x + y * y)) (- y / (x * x + y * y)) := by
--   obtain ⟨rfl, rfl⟩ := h
--   constructor <;> simp [RCLike.normSq]

-- theorem IsComplex.neg : ∀ {z : ℂ} {a b : ℝ}, IsComplex z a b → IsComplex (-z) (-a) (-b)
--   | _, _, _, ⟨rfl, rfl⟩ => ⟨map_neg _ _, map_neg _ _⟩

-- theorem IsComplex.sub : ∀ {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ},
--     IsComplex z₁ a₁ b₁ → IsComplex z₂ a₂ b₂ → IsComplex (z₁ - z₂) (a₁ - a₂) (b₁ - b₂)
--   | _, _, _, _, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩ => ⟨map_sub _ _ _, map_sub _ _ _⟩

-- theorem IsComplex.conj : ∀ {z : ℂ} {a b : ℝ}, IsComplex z a b → IsComplex (conj z) a (-b)
--   | _, _, _, ⟨rfl, rfl⟩ => ⟨RCLike.conj_re _, RCLike.conj_im _⟩

-- theorem IsComplex.ofNat (n : ℕ) [n.AtLeastTwo] :
--     IsComplex (OfNat.ofNat (α := ℂ) n) (OfNat.ofNat n) 0 := ⟨RCLike.ofNat_re _, RCLike.ofNat_im _⟩

-- theorem IsComplex.scientific (m exp : ℕ) (x : Bool) :
--     IsComplex (OfScientific.ofScientific m x exp : ℂ) (OfScientific.ofScientific m x exp : ℝ) 0 :=
--   ⟨RCLike.nnratCast_re _, RCLike.nnratCast_im _⟩

-- theorem eq_eq {z : ℂ} {a b a' b' : ℝ} (pf : IsComplex z a b) (pf_a : a = a') (pf_b : b = b') :
--   IsComplex z a' b' := by simp_all

-- theorem eq_of_eq_of_eq_of_eq {z w : ℂ} {az bz aw bw : ℝ}
--     (hz : IsComplex z az bz) (hw : IsComplex w aw bw)
--     (ha : az = aw) (hb : bz = bw) : z = w := by
--   obtain ⟨rfl, rfl⟩ := hz
--   obtain ⟨rfl, rfl⟩ := hw
--   apply RCLike.ext <;> assumption

-- theorem ne_of_re_ne {z w : ℂ} {az bz aw bw : ℝ} (hz : IsComplex z az bz) (hw : IsComplex w aw bw) :
--     az ≠ aw → z ≠ w := (mt · ·) <| by
--   rintro rfl
--   obtain ⟨rfl, rfl⟩ := hz
--   obtain ⟨rfl, rfl⟩ := hw
--   rfl

-- theorem ne_of_im_ne {z w : ℂ} {az bz aw bw : ℝ} (hz : IsComplex z az bz) (hw : IsComplex w aw bw) :
--     bz ≠ bw → z ≠ w := (mt · ·) <| by
--   rintro rfl
--   obtain ⟨rfl, rfl⟩ := hz
--   obtain ⟨rfl, rfl⟩ := hw
--   rfl

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
--         return ⟨_, _, q(have hzm' := $hzm; pow_bit_true $z $m ▸ (IsComplex.mul hzm' hzm').mul $hz)⟩
--       | false =>
--         have : $n =Q Nat.bit false $m := ⟨⟩
--         let ⟨_, _, hzm⟩ ← rec q($z) q($m) q(⟨rfl⟩) hz
--         return ⟨_, _, q(have hzm' := $hzm; pow_bit_false $z $m ▸ IsComplex.mul hzm' hzm')⟩)

/-- Parsing all the basic calculation in complex. -/
partial def parse (z : Q(ℂ)) : MetaM (ResultI q($z)) := do
  match z with
  | ~q($z₁ + $z₂) =>
    let r1 ← parse z₁
    let r2 ← parse z₂
    return ((← r1.add r2).eqTrans q(rfl))
  | ~q($z₁ * $z₂) =>
    let r1 ← parse z₁
    let r2 ← parse z₂
    return ((← r1.mul r2).eqTrans q(rfl))
  -- | ~q($z⁻¹) =>
  --   let ⟨_x, _y, pf⟩ ← parse z
  --   pure ⟨_, _, q(.inv $pf)⟩
  -- | ~q($z₁ / $z₂) => do
  --   let ⟨_a, _b, pf⟩ ← parse q($z₁ * $z₂⁻¹)
  --   return ⟨_, _, q($pf)⟩
  -- | ~q(-$w) => do
  --   let ⟨_a, _b, pf⟩ ← parse w
  --   return ⟨_, _, q(.neg $pf)⟩
  -- | ~q($z₁ - $z₂) =>
  --   let ⟨_a₁, _b₁, pf₁⟩ ← parse z₁
  --   let ⟨_a₂, _b₂, pf₂⟩ ← parse z₂
  --   pure ⟨_, _, q(.sub $pf₁ $pf₂)⟩
  -- | ~q(conj $w) =>
  --   let ⟨_a, _b, pf⟩ ← parse w
  --   return ⟨_, _, q(.conj $pf)⟩
  -- | ~q($w ^ ($n' : ℕ)) =>
  --   let ⟨n, hn⟩ ← NormNum.deriveNat q($n') q(inferInstance)
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
  -- | ~q(Complex.I) =>
  --   pure ⟨_, _, q(.I)⟩
  | ~q(0) =>
    ResultI.mk' (z := q(0)) (NormNum.Result.isNat q(inferInstance) q(0) q(⟨rfl⟩))
      ((NormNum.Result.isNat q(inferInstance) q(0) q(⟨rfl⟩)))
      q(Nat.cast_zero (R := ℝ) ▸ RCLike.zero_re) q(Nat.cast_zero (R := ℝ) ▸ RCLike.zero_im)
  | ~q(1) =>
    ResultI.mk' (z := q(1)) (NormNum.Result.isNat q(inferInstance) q(1) q(⟨rfl⟩))
      (NormNum.Result.isNat q(inferInstance) q(0) q(⟨rfl⟩))
      q(Nat.cast_one (R := ℝ) ▸ RCLike.one_re) q(Nat.cast_zero (R := ℝ) ▸ RCLike.one_im)
  | ~q(OfNat.ofNat $en (self := @instOfNatAtLeastTwo ℂ _ _ $inst)) =>
    ResultI.mk' (z := z) (NormNum.Result.isNat q(inferInstance) q($en) q(⟨rfl⟩))
      (NormNum.Result.isNat q(inferInstance) q(0) q(⟨rfl⟩))
      q(@Nat.cast_ofNat ℝ $en _ $inst ▸ RCLike.ofNat_re $en)
      q(Nat.cast_zero (R := ℝ) ▸ RCLike.ofNat_im $en)
  -- | ~q(OfScientific.ofScientific $m $x $exp) =>
  --   return ⟨_, _, q(.scientific _ _ _)⟩
  | _ => throwError "found the atom {z} which is not a numeral"

/-- Using `norm_num` to normalise expressions -/
noncomputable def normalize (z : Q(ℂ)) : MetaM (ResultI q($z)) := do
  -- let r ← parse z
  let ra ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) q(RCLike.re $z)
  let rb ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) q(RCLike.im $z)
  -- let { expr := (a' : Q(ℝ)), proof? := (pf_a ) } ← ra.toSimpResult | unreachable!
  -- let { expr := (b' : Q(ℝ)), proof? := (pf_b ) } ← rb.toSimpResult | unreachable!
  -- -- return ⟨a', b', q(eq_eq $pf $pf_a $pf_b)⟩
  -- return ResultI.mk' ra rb q(rfl) q(rfl)
  sorry

#exit
-- TODO: change to use `x + y*I` so that it's fine for `ℝ` too.
theorem IsComplex.out {z : ℂ} {re im : ℝ} (h : IsComplex z re im) : z = ⟨re, im⟩ := by
  obtain ⟨rfl, rfl⟩ := h
  rfl


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
