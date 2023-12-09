/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq

/-!
# `norm_num` extension for modulo operator

This file adds support for the `· % ·` operator to the `norm_num` tactic.
-/

set_option autoImplicit true

namespace Mathlib
open Lean hiding Rat mkRat
open Meta

namespace Meta.NormNum
open Qq

lemma isInt_emod {a b q r m : ℤ} (hm : q * b = m) (h : r + m = a) (h₁ : 0 ≤ r) (h₂ : r < b) :
    IsInt (a % b) r :=
  ⟨by rw [← h, ← hm, Int.add_mul_emod_self, Int.emod_eq_of_lt h₁ h₂, Int.cast_id]⟩

lemma isInt_emod_neg {a b c : ℤ} (h : IsInt (a % -b) c) : IsInt (a % b) c :=
  ⟨(Int.emod_neg _ _).symm.trans h.out⟩

lemma isInt_refl (a : ℤ) : IsInt a a :=
  ⟨rfl⟩

lemma isNat_neg_of_isNegNat {a : ℤ} {b : ℕ} (h : IsInt a (- b)) :
    IsNat (-a) b :=
  ⟨by simp [h.out]⟩

/-- Given expressions `a b` in `ℤ`, evaluate `a % b`.

`a` and `b` should be numeric expressions recognized by `norm_num`.
-/
partial def evalIntMod.go (a b : Q(ℤ)) : MetaM (NormNum.Result q($a % $b)) := do
  let ra ← derive (u := Level.zero) a
  let rb ← derive (u := Level.zero) b
  let rec /-- Given a result for evaluating `a b` in `ℤ`, evaluate `a % b`. -/
    core : (b : Q(ℤ)) → Result b → MetaM (Result (u := Level.zero) (α := q(ℤ)) q($a % $b)) :=
  fun b rb => match rb with
    | (.isNegNat inst nb pb) => do
      have : $inst =Q Int.instRingInt := ⟨⟩
      let pf ← core q(- $b)
        (.isNat q(AddGroupWithOne.toAddMonoidWithOne) nb q(isNat_neg_of_isNegNat $pb))
      return pf.eqTrans q((Int.emod_neg _ _).symm)
    | (.isNat inst nb pb) => do
      have : $inst =Q AddGroupWithOne.toAddMonoidWithOne := ⟨⟩
      let ⟨a, na, pa⟩ ← @Result.toInt _ _ _ q(OrderedRing.toRing) ra
      let q := a / nb.natLit!
      have nq := mkRawIntLit q
      let r := a % nb.natLit!
      have nr := mkRawIntLit r
      let m := q * nb.natLit!
      have nm := mkRawIntLit m
      have pf₁ : Q($nq * $nb = $nm) := (q(Eq.refl $nm) :)
      have pf₂ : Q($nr + $nm = $na) := (q(Eq.refl $na) :)
      have pf₃ : Q(decide (0 ≤ $nr) = true) := (q(Eq.refl true) :)
      have pf₄ : Q(decide ($nr < $nb) = true) := (q(Eq.refl true) :)
      return (.isInt q(OrderedRing.toRing) nr r
        q(isInt_emod (($pb).out.symm ▸ (id $pf₁)) (Eq.trans (id $pf₂) ($pa).out.symm)
          (isInt_le_true (isInt_refl 0) (isInt_refl $nr) $pf₃)
          (isInt_lt_true (α := ℤ) (isInt_refl $nr) (IsNat.to_isInt $pb) $pf₄)))
    | _ => failure
  core b rb

/-- The `norm_num` extension which identifies expressions of the form `Int.emod a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℤ) % _, Mod.mod (_ : ℤ) _, Int.emod _ _] partial def evalIntMod :
    NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℤ))) (b : Q(ℤ)) ← whnfR e | failure
  -- We trust that the default instance for `HMod` is `Int.mod` when the first parameter is `ℤ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HMod.hMod (α := ℤ))
  evalIntMod.go a b

end Mathlib.Meta.NormNum
