/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/

import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Tactic.NormNum.Basic

/-!
# `norm_num` extensions for Ordinals

The default `norm_num` extensions for many operators requires a semiring,
which without a right distributive law, ordinals do not have.

We must therefore define new extensions for them.
-/

namespace Mathlib.Meta.NormNum
open Lean Lean.Meta Qq Ordinal

/- The `guard_msgs` in this file are for checking whether the current default extensions have been
updated and the extensions in this file are no longer needed. -/

/-- info: 12 * 5 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) * (5 : Ordinal.{0})

lemma isNat_ordinalMul.{u} : ∀ {a b : Ordinal.{u}} {an bn rn : ℕ},
    IsNat a an → IsNat b bn → an * bn = rn → IsNat (a * b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_mul ..⟩

/-- The `norm_num` extension for multiplication on ordinals. -/
@[norm_num (_ : Ordinal) * (_ : Ordinal)]
def evalOrdinalMul : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) * ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! * bn.natLit!)
      have : ($an * $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalMul $pa $pb (.refl $rn)))
    | _, _ => throwError "not multiplication on ordinals"

/-- info: 5 ≤ 12 -/
#guard_msgs in
#norm_num (5 : Ordinal.{0}) ≤ 12

/-- info: 5 < 12 -/
#guard_msgs in
#norm_num (5 : Ordinal.{0}) < 12

lemma isNat_ordinalLE_true.{u} : ∀ {a b : Ordinal.{u}} {an bn : ℕ},
    IsNat a an → IsNat b bn → decide (an ≤ bn) = true → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.cast_le.mpr <| of_decide_eq_true h

lemma isNat_ordinalLE_false.{u} : ∀ {a b : Ordinal.{u}} {an bn : ℕ},
    IsNat a an → IsNat b bn → decide (an ≤ bn) = false → ¬a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => not_iff_not.mpr Nat.cast_le |>.mpr <| of_decide_eq_false h

lemma isNat_ordinalLT_true.{u} : ∀ {a b : Ordinal.{u}} {an bn : ℕ},
    IsNat a an → IsNat b bn → decide (an < bn) = true → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.cast_lt.mpr <| of_decide_eq_true h

lemma isNat_ordinalLT_false.{u} : ∀ {a b : Ordinal.{u}} {an bn : ℕ},
    IsNat a an → IsNat b bn → decide (an < bn) = false → ¬a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => not_iff_not.mpr Nat.cast_lt |>.mpr <| of_decide_eq_false h

/-- The `norm_num` extension for inequality on ordinals. -/
@[norm_num (_ : Ordinal) ≤ (_ : Ordinal)]
def evalOrdinalLE : NormNumExt where
  eval {u α} e := do
    let ⟨_⟩ ← assertLevelDefEqQ u ql(0)
    match α, e with
    | ~q(Prop), ~q(($a : Ordinal) ≤ ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u_1}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      if an.natLit! ≤ bn.natLit! then
        have this : decide ($an ≤ $bn) =Q true := ⟨⟩
        pure (.isTrue q(isNat_ordinalLE_true $pa $pb $this))
      else
        have this : decide ($an ≤ $bn) =Q false := ⟨⟩
        pure (.isFalse q(isNat_ordinalLE_false $pa $pb $this))
    | _, _ => throwError "not inequality on ordinals"

/-- The `norm_num` extension for strict inequality on ordinals. -/
@[norm_num (_ : Ordinal) < (_ : Ordinal)]
def evalOrdinalLT : NormNumExt where
  eval {u α} e := do
    let ⟨_⟩ ← assertLevelDefEqQ u ql(0)
    match α, e with
    | ~q(Prop), ~q(($a : Ordinal) < ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u_1}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      if an.natLit! < bn.natLit! then
        have this : decide ($an < $bn) =Q true := ⟨⟩
        pure (.isTrue q(isNat_ordinalLT_true $pa $pb $this))
      else
        have this : decide ($an < $bn) =Q false := ⟨⟩
        pure (.isFalse q(isNat_ordinalLT_false $pa $pb $this))
    | _, _ => throwError "not strict inequality on ordinals"

/-- info: 12 - 5 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) - 5

lemma isNat_ordinalSub.{u} : ∀ {a b : Ordinal.{u}} {an bn rn : ℕ},
    IsNat a an → IsNat b bn → an - bn = rn → IsNat (a - b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_sub ..⟩

/-- The `norm_num` extension for subtration on ordinals. -/
@[norm_num (_ : Ordinal) - (_ : Ordinal)]
def evalOrdinalSub : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) - ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! - bn.natLit!)
      have : ($an - $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalSub $pa $pb (.refl $rn)))
    | _, _ => throwError "not subtration on ordinals"

/-- info: 12 / 5 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) / 5

lemma isNat_ordinalDiv.{u} : ∀ {a b : Ordinal.{u}} {an bn rn : ℕ},
    IsNat a an → IsNat b bn → an / bn = rn → IsNat (a / b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_div ..⟩

/-- The `norm_num` extension for division on ordinals. -/
@[norm_num (_ : Ordinal) / (_ : Ordinal)]
def evalOrdinalDiv : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) / ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! / bn.natLit!)
      have : ($an / $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalDiv $pa $pb (.refl $rn)))
    | _, _ => throwError "not division on ordinals"

/-- info: 12 % 5 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) % 5

lemma isNat_ordinalMod.{u} : ∀ {a b : Ordinal.{u}} {an bn rn : ℕ},
    IsNat a an → IsNat b bn → an % bn = rn → IsNat (a % b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_mod ..⟩

/-- The `norm_num` extension for modulo on ordinals. -/
@[norm_num (_ : Ordinal) % (_ : Ordinal)]
def evalOrdinalMod : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) % ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! % bn.natLit!)
      have : ($an % $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalMod $pa $pb (.refl $rn)))
    | _, _ => throwError "not modulo on ordinals"

lemma isNat_ordinalOPow.{u} : ∀ {a b : Ordinal.{u}} {an bn rn : ℕ},
    IsNat a an → IsNat b bn → an ^ bn = rn → IsNat (a ^ b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_opow ..⟩

/-- The `norm_num` extension for homogenous power on ordinals. -/
@[norm_num (_ : Ordinal) ^ (_ : Ordinal)]
def evalOrdinalOPow : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) ^ ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! ^ bn.natLit!)
      have : ($an ^ $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalOPow $pa $pb (.refl $rn)))
    | _, _ => throwError "not homogenous power on ordinals"

/-- info: 12 ^ 2 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) ^ (2 : ℕ)

lemma isNat_ordinalNPow.{u} : ∀ {a : Ordinal.{u}} {b an bn rn : ℕ},
    IsNat a an → IsNat b bn → an ^ bn = rn → IsNat (a ^ b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_opow .. |>.trans <| opow_natCast ..⟩

/-- The `norm_num` extension for natural power on ordinals. -/
@[norm_num (_ : Ordinal) ^ (_ : ℕ)]
def evalOrdinalNPow : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) ^ ($b : ℕ)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b q(inferInstance)
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! ^ bn.natLit!)
      have : ($an ^ $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalNPow $pa $pb (.refl $rn)))
    | _, _ => throwError "not natural power on ordinals"

end Mathlib.Meta.NormNum
