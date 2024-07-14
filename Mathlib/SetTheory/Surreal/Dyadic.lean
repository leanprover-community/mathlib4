/-
Copyright (c) 2021 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.SetTheory.Game.Birthday
import Mathlib.SetTheory.Surreal.Basic

#align_import set_theory.surreal.dyadic from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# Dyadic numbers
Dyadic numbers are obtained by localizing ℤ away from 2. They are the initial object in the category
of rings with no 2-torsion.

## Dyadic surreal numbers
We construct dyadic surreal numbers using the canonical map from ℤ[2 ^ {-1}] to surreals.
As we currently do not have a ring structure on `Surreal` we construct this map explicitly. Once we
have the ring structure, this map can be constructed directly by sending `2 ^ {-1}` to `half`.

## Embeddings
The above construction gives us an abelian group embedding of ℤ into `Surreal`. The goal is to
extend this to an embedding of dyadic rationals into `Surreal` and use Cauchy sequences of dyadic
rational numbers to construct an ordered field embedding of ℝ into `Surreal`.
-/


universe u

namespace SetTheory

namespace PGame

/-- For a natural number `n`, the pre-game `powHalf (n + 1)` is recursively defined as
`{0 | powHalf n}`. These are the explicit expressions of powers of `1 / 2`. By definition, we have
`powHalf 0 = 1` and `powHalf 1 ≈ 1 / 2` and we prove later on that
`powHalf (n + 1) + powHalf (n + 1) ≈ powHalf n`. -/
def powHalf : ℕ → PGame
  | 0 => 1
  | n + 1 => ⟨PUnit, PUnit, 0, fun _ => powHalf n⟩
#align pgame.pow_half SetTheory.PGame.powHalf

@[simp]
theorem powHalf_zero : powHalf 0 = 1 :=
  rfl
#align pgame.pow_half_zero SetTheory.PGame.powHalf_zero

theorem powHalf_leftMoves (n) : (powHalf n).LeftMoves = PUnit := by cases n <;> rfl
#align pgame.pow_half_left_moves SetTheory.PGame.powHalf_leftMoves

theorem powHalf_zero_rightMoves : (powHalf 0).RightMoves = PEmpty :=
  rfl
#align pgame.pow_half_zero_right_moves SetTheory.PGame.powHalf_zero_rightMoves

theorem powHalf_succ_rightMoves (n) : (powHalf (n + 1)).RightMoves = PUnit :=
  rfl
#align pgame.pow_half_succ_right_moves SetTheory.PGame.powHalf_succ_rightMoves

@[simp]
theorem powHalf_moveLeft (n i) : (powHalf n).moveLeft i = 0 := by cases n <;> cases i <;> rfl
#align pgame.pow_half_move_left SetTheory.PGame.powHalf_moveLeft

@[simp]
theorem powHalf_succ_moveRight (n i) : (powHalf (n + 1)).moveRight i = powHalf n :=
  rfl
#align pgame.pow_half_succ_move_right SetTheory.PGame.powHalf_succ_moveRight

instance uniquePowHalfLeftMoves (n) : Unique (powHalf n).LeftMoves := by
  cases n <;> exact PUnit.unique
#align pgame.unique_pow_half_left_moves SetTheory.PGame.uniquePowHalfLeftMoves

instance isEmpty_powHalf_zero_rightMoves : IsEmpty (powHalf 0).RightMoves :=
  inferInstanceAs (IsEmpty PEmpty)
#align pgame.is_empty_pow_half_zero_right_moves SetTheory.PGame.isEmpty_powHalf_zero_rightMoves

instance uniquePowHalfSuccRightMoves (n) : Unique (powHalf (n + 1)).RightMoves :=
  PUnit.unique
#align pgame.unique_pow_half_succ_right_moves SetTheory.PGame.uniquePowHalfSuccRightMoves

@[simp]
theorem birthday_half : birthday (powHalf 1) = 2 := by
  rw [birthday_def]; simp
#align pgame.birthday_half SetTheory.PGame.birthday_half

/-- For all natural numbers `n`, the pre-games `powHalf n` are numeric. -/
theorem numeric_powHalf (n) : (powHalf n).Numeric := by
  induction' n with n hn
  · exact numeric_one
  · constructor
    · simpa using hn.moveLeft_lt default
    · exact ⟨fun _ => numeric_zero, fun _ => hn⟩
#align pgame.numeric_pow_half SetTheory.PGame.numeric_powHalf

theorem powHalf_succ_lt_powHalf (n : ℕ) : powHalf (n + 1) < powHalf n :=
  (numeric_powHalf (n + 1)).lt_moveRight default
#align pgame.pow_half_succ_lt_pow_half SetTheory.PGame.powHalf_succ_lt_powHalf

theorem powHalf_succ_le_powHalf (n : ℕ) : powHalf (n + 1) ≤ powHalf n :=
  (powHalf_succ_lt_powHalf n).le
#align pgame.pow_half_succ_le_pow_half SetTheory.PGame.powHalf_succ_le_powHalf

theorem powHalf_le_one (n : ℕ) : powHalf n ≤ 1 := by
  induction' n with n hn
  · exact le_rfl
  · exact (powHalf_succ_le_powHalf n).trans hn
#align pgame.pow_half_le_one SetTheory.PGame.powHalf_le_one

theorem powHalf_succ_lt_one (n : ℕ) : powHalf (n + 1) < 1 :=
  (powHalf_succ_lt_powHalf n).trans_le <| powHalf_le_one n
#align pgame.pow_half_succ_lt_one SetTheory.PGame.powHalf_succ_lt_one

theorem powHalf_pos (n : ℕ) : 0 < powHalf n := by
  rw [← lf_iff_lt numeric_zero (numeric_powHalf n), zero_lf_le]; simp
#align pgame.pow_half_pos SetTheory.PGame.powHalf_pos

theorem zero_le_powHalf (n : ℕ) : 0 ≤ powHalf n :=
  (powHalf_pos n).le
#align pgame.zero_le_pow_half SetTheory.PGame.zero_le_powHalf

theorem add_powHalf_succ_self_eq_powHalf (n) : powHalf (n + 1) + powHalf (n + 1) ≈ powHalf n := by
  induction' n using Nat.strong_induction_on with n hn
  constructor <;> rw [le_iff_forall_lf] <;> constructor
  · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> apply lf_of_lt
    · calc
        0 + powHalf n.succ ≈ powHalf n.succ := zero_add_equiv _
        _ < powHalf n := powHalf_succ_lt_powHalf n
    · calc
        powHalf n.succ + 0 ≈ powHalf n.succ := add_zero_equiv _
        _ < powHalf n := powHalf_succ_lt_powHalf n
  · cases' n with n
    · rintro ⟨⟩
    rintro ⟨⟩
    apply lf_of_moveRight_le
    swap
    · exact Sum.inl default
    calc
      powHalf n.succ + powHalf (n.succ + 1) ≤ powHalf n.succ + powHalf n.succ :=
        add_le_add_left (powHalf_succ_le_powHalf _) _
      _ ≈ powHalf n := hn _ (Nat.lt_succ_self n)
  · simp only [powHalf_moveLeft, forall_const]
    apply lf_of_lt
    calc
      0 ≈ 0 + 0 := Equiv.symm (add_zero_equiv 0)
      _ ≤ powHalf n.succ + 0 := add_le_add_right (zero_le_powHalf _) _
      _ < powHalf n.succ + powHalf n.succ := add_lt_add_left (powHalf_pos _) _
  · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> apply lf_of_lt
    · calc
        powHalf n ≈ powHalf n + 0 := Equiv.symm (add_zero_equiv _)
        _ < powHalf n + powHalf n.succ := add_lt_add_left (powHalf_pos _) _
    · calc
        powHalf n ≈ 0 + powHalf n := Equiv.symm (zero_add_equiv _)
        _ < powHalf n.succ + powHalf n := add_lt_add_right (powHalf_pos _) _
#align pgame.add_pow_half_succ_self_eq_pow_half SetTheory.PGame.add_powHalf_succ_self_eq_powHalf

theorem half_add_half_equiv_one : powHalf 1 + powHalf 1 ≈ 1 :=
  add_powHalf_succ_self_eq_powHalf 0
#align pgame.half_add_half_equiv_one SetTheory.PGame.half_add_half_equiv_one

end PGame

end SetTheory

namespace Surreal

open SetTheory PGame

/-- Powers of the surreal number `half`. -/
def powHalf (n : ℕ) : Surreal :=
  ⟦⟨PGame.powHalf n, PGame.numeric_powHalf n⟩⟧
#align surreal.pow_half Surreal.powHalf

@[simp]
theorem powHalf_zero : powHalf 0 = 1 :=
  rfl
#align surreal.pow_half_zero Surreal.powHalf_zero

@[simp]
theorem double_powHalf_succ_eq_powHalf (n : ℕ) : 2 • powHalf n.succ = powHalf n := by
  rw [two_nsmul]; exact Quotient.sound (PGame.add_powHalf_succ_self_eq_powHalf n)
#align surreal.double_pow_half_succ_eq_pow_half Surreal.double_powHalf_succ_eq_powHalf

@[simp]
theorem nsmul_pow_two_powHalf (n : ℕ) : 2 ^ n • powHalf n = 1 := by
  induction' n with n hn
  · simp only [Nat.zero_eq, pow_zero, powHalf_zero, one_smul]
  · rw [← hn, ← double_powHalf_succ_eq_powHalf n, smul_smul (2 ^ n) 2 (powHalf n.succ), mul_comm,
      pow_succ']
#align surreal.nsmul_pow_two_pow_half Surreal.nsmul_pow_two_powHalf

@[simp]
theorem nsmul_pow_two_powHalf' (n k : ℕ) : 2 ^ n • powHalf (n + k) = powHalf k := by
  induction' k with k hk
  · simp only [add_zero, Surreal.nsmul_pow_two_powHalf, Nat.zero_eq, eq_self_iff_true,
      Surreal.powHalf_zero]
  · rw [← double_powHalf_succ_eq_powHalf (n + k), ← double_powHalf_succ_eq_powHalf k,
      smul_algebra_smul_comm] at hk
    rwa [← zsmul_eq_zsmul_iff' two_ne_zero]
#align surreal.nsmul_pow_two_pow_half' Surreal.nsmul_pow_two_powHalf'

theorem zsmul_pow_two_powHalf (m : ℤ) (n k : ℕ) :
    (m * 2 ^ n) • powHalf (n + k) = m • powHalf k := by
  rw [mul_zsmul]
  congr
  norm_cast
  exact nsmul_pow_two_powHalf' n k
#align surreal.zsmul_pow_two_pow_half Surreal.zsmul_pow_two_powHalf

theorem dyadic_aux {m₁ m₂ : ℤ} {y₁ y₂ : ℕ} (h₂ : m₁ * 2 ^ y₁ = m₂ * 2 ^ y₂) :
    m₁ • powHalf y₂ = m₂ • powHalf y₁ := by
  revert m₁ m₂
  wlog h : y₁ ≤ y₂
  · intro m₁ m₂ aux; exact (this (le_of_not_le h) aux.symm).symm
  intro m₁ m₂ h₂
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp h
  rw [add_comm, pow_add, ← mul_assoc, mul_eq_mul_right_iff] at h₂
  cases' h₂ with h₂ h₂
  · rw [h₂, add_comm, zsmul_pow_two_powHalf m₂ c y₁]
  · have := Nat.one_le_pow y₁ 2 Nat.succ_pos'
    norm_cast at h₂; omega
#align surreal.dyadic_aux Surreal.dyadic_aux

/-- The additive monoid morphism `dyadicMap` sends ⟦⟨m, 2^n⟩⟧ to m • half ^ n. -/
def dyadicMap : Localization.Away (2 : ℤ) →+ Surreal where
  toFun x :=
    (Localization.liftOn x fun x y => x • powHalf (Submonoid.log y)) <| by
      intro m₁ m₂ n₁ n₂ h₁
      obtain ⟨⟨n₃, y₃, hn₃⟩, h₂⟩ := Localization.r_iff_exists.mp h₁
      simp only [Subtype.coe_mk, mul_eq_mul_left_iff] at h₂
      cases h₂
      · obtain ⟨a₁, ha₁⟩ := n₁.prop
        obtain ⟨a₂, ha₂⟩ := n₂.prop
        simp only at ha₁ ha₂ ⊢
        have hn₁ : n₁ = Submonoid.pow 2 a₁ := Subtype.ext ha₁.symm
        have hn₂ : n₂ = Submonoid.pow 2 a₂ := Subtype.ext ha₂.symm
        have h₂ : 1 < (2 : ℤ).natAbs := one_lt_two
        rw [hn₁, hn₂, Submonoid.log_pow_int_eq_self h₂, Submonoid.log_pow_int_eq_self h₂]
        apply dyadic_aux
        rwa [ha₁, ha₂, mul_comm, mul_comm m₂]
      · have : (1 : ℤ) ≤ 2 ^ y₃ := mod_cast Nat.one_le_pow y₃ 2 Nat.succ_pos'
        linarith
  map_zero' := Localization.liftOn_zero _ _
  map_add' x y :=
    Localization.induction_on₂ x y <| by
      rintro ⟨a, ⟨b, ⟨b', rfl⟩⟩⟩ ⟨c, ⟨d, ⟨d', rfl⟩⟩⟩
      have h₂ : 1 < (2 : ℤ).natAbs := one_lt_two
      have hpow₂ := Submonoid.log_pow_int_eq_self h₂
      simp_rw [Submonoid.pow_apply] at hpow₂
      simp_rw [Localization.add_mk, Localization.liftOn_mk,
        Submonoid.log_mul (Int.pow_right_injective h₂), hpow₂]
      calc
        (2 ^ b' * c + 2 ^ d' * a) • powHalf (b' + d') =
            (c * 2 ^ b') • powHalf (b' + d') + (a * 2 ^ d') • powHalf (d' + b') := by
          simp only [add_smul, mul_comm, add_comm]
        _ = c • powHalf d' + a • powHalf b' := by simp only [zsmul_pow_two_powHalf]
        _ = a • powHalf b' + c • powHalf d' := add_comm _ _
#align surreal.dyadic_map Surreal.dyadicMap

@[simp]
theorem dyadicMap_apply (m : ℤ) (p : Submonoid.powers (2 : ℤ)) :
    dyadicMap (IsLocalization.mk' (Localization (Submonoid.powers 2)) m p) =
      m • powHalf (Submonoid.log p) := by
  rw [← Localization.mk_eq_mk']; rfl
#align surreal.dyadic_map_apply Surreal.dyadicMap_apply

-- @[simp] -- Porting note: simp normal form is `dyadicMap_apply_pow'`
theorem dyadicMap_apply_pow (m : ℤ) (n : ℕ) :
    dyadicMap (IsLocalization.mk' (Localization (Submonoid.powers 2)) m (Submonoid.pow 2 n)) =
      m • powHalf n := by
  rw [dyadicMap_apply, @Submonoid.log_pow_int_eq_self 2 one_lt_two]
#align surreal.dyadic_map_apply_pow Surreal.dyadicMap_apply_pow

@[simp]
theorem dyadicMap_apply_pow' (m : ℤ) (n : ℕ) :
    m • Surreal.powHalf (Submonoid.log (Submonoid.pow (2 : ℤ) n)) = m • powHalf n := by
  rw [@Submonoid.log_pow_int_eq_self 2 one_lt_two]

/-- We define dyadic surreals as the range of the map `dyadicMap`. -/
def dyadic : Set Surreal :=
  Set.range dyadicMap
#align surreal.dyadic Surreal.dyadic

-- We conclude with some ideas for further work on surreals; these would make fun projects.
-- TODO show that the map from dyadic rationals to surreals is injective
-- TODO map the reals into the surreals, using dyadic Dedekind cuts
-- TODO show this is a group homomorphism, and injective
-- TODO show the maps from the dyadic rationals and from the reals
-- into the surreals are multiplicative
end Surreal
