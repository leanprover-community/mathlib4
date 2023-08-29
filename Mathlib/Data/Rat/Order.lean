/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Int.Cast.Lemmas

#align_import data.rat.order from "leanprover-community/mathlib"@"a59dad53320b73ef180174aae867addd707ef00e"

/-!
# Order for Rational Numbers

## Summary

We define the order on `ℚ`, prove that `ℚ` is a discrete, linearly ordered field, and define
functions such as `abs` and `sqrt` that depend on this order.


## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering, sqrt, abs
-/


namespace Rat

variable (a b c : ℚ)

open Rat

/-- A rational number is called nonnegative if its numerator is nonnegative. -/
protected def Nonneg (r : ℚ) : Prop :=
  0 ≤ r.num
#align rat.nonneg Rat.Nonneg

@[simp]
theorem divInt_nonneg (a : ℤ) {b : ℤ} (h : 0 < b) : (a /. b).Nonneg ↔ 0 ≤ a := by
  generalize ha : a /. b = x; cases' x with n₁ d₁ h₁ c₁; rw [num_den'] at ha
  -- ⊢ Rat.Nonneg x ↔ 0 ≤ a
                              -- ⊢ Rat.Nonneg (mk' n₁ d₁) ↔ 0 ≤ a
                                                         -- ⊢ Rat.Nonneg (mk' n₁ d₁) ↔ 0 ≤ a
  simp [Rat.Nonneg]
  -- ⊢ 0 ≤ n₁ ↔ 0 ≤ a
  have d0 := Int.ofNat_lt.2 (Nat.pos_of_ne_zero h₁)
  -- ⊢ 0 ≤ n₁ ↔ 0 ≤ a
  have := (divInt_eq_iff (ne_of_gt h) (ne_of_gt d0)).1 ha
  -- ⊢ 0 ≤ n₁ ↔ 0 ≤ a
  constructor <;> intro h₂
  -- ⊢ 0 ≤ n₁ → 0 ≤ a
                  -- ⊢ 0 ≤ a
                  -- ⊢ 0 ≤ n₁
  · apply nonneg_of_mul_nonneg_left _ d0
    -- ⊢ 0 ≤ a * ↑d₁
    rw [this]
    -- ⊢ 0 ≤ n₁ * b
    exact mul_nonneg h₂ (le_of_lt h)
    -- 🎉 no goals
  · apply nonneg_of_mul_nonneg_left _ h
    -- ⊢ 0 ≤ n₁ * b
    rw [← this]
    -- ⊢ 0 ≤ a * ↑d₁
    exact mul_nonneg h₂ (Int.ofNat_zero_le _)
    -- 🎉 no goals
#align rat.mk_nonneg Rat.divInt_nonneg

protected theorem nonneg_add {a b} : Rat.Nonneg a → Rat.Nonneg b → Rat.Nonneg (a + b) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ => by
      have d₁0 : 0 < (d₁ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₁)
      -- ⊢ Rat.Nonneg (n₁ /. ↑d₁) → Rat.Nonneg (n₂ /. ↑d₂) → Rat.Nonneg (n₁ /. ↑d₁ + n₂ …
      have d₂0 : 0 < (d₂ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₂)
      -- ⊢ Rat.Nonneg (n₁ /. ↑d₁) → Rat.Nonneg (n₂ /. ↑d₂) → Rat.Nonneg (n₁ /. ↑d₁ + n₂ …
      simp only [d₁0, d₂0, h₁, h₂, mul_pos, divInt_nonneg, add_def'', Ne.def,
        Nat.cast_eq_zero, not_false_iff]
      intro n₁0 n₂0
      -- ⊢ 0 ≤ n₁ * ↑d₂ + n₂ * ↑d₁
      apply add_nonneg <;> apply mul_nonneg <;> · first |assumption|apply Int.ofNat_zero_le
      -- ⊢ 0 ≤ n₁ * ↑d₂
                           -- ⊢ 0 ≤ n₁
                           -- ⊢ 0 ≤ n₂
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align rat.nonneg_add Rat.nonneg_add

protected theorem nonneg_mul {a b} : Rat.Nonneg a → Rat.Nonneg b → Rat.Nonneg (a * b) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ => by
      have d₁0 : 0 < (d₁ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₁)
      -- ⊢ Rat.Nonneg (n₁ /. ↑d₁) → Rat.Nonneg (n₂ /. ↑d₂) → Rat.Nonneg (n₁ /. ↑d₁ * (n …
      have d₂0 : 0 < (d₂ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₂)
      -- ⊢ Rat.Nonneg (n₁ /. ↑d₁) → Rat.Nonneg (n₂ /. ↑d₂) → Rat.Nonneg (n₁ /. ↑d₁ * (n …
      rw [mul_def' d₁0.ne.symm d₂0.ne.symm, divInt_nonneg _ d₁0, divInt_nonneg _ d₂0,
        divInt_nonneg _ (mul_pos d₁0 d₂0)]
      apply mul_nonneg
      -- 🎉 no goals
#align rat.nonneg_mul Rat.nonneg_mul

protected theorem nonneg_antisymm {a} : Rat.Nonneg a → Rat.Nonneg (-a) → a = 0 :=
  numDenCasesOn' a fun n d h => by
    have d0 : 0 < (d : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h)
    -- ⊢ Rat.Nonneg (n /. ↑d) → Rat.Nonneg (-(n /. ↑d)) → n /. ↑d = 0
    rw [divInt_nonneg _ d0, neg_def, divInt_nonneg _ d0, Right.nonneg_neg_iff,
      divInt_eq_zero d0.ne.symm]
    exact fun h₁ h₂ => le_antisymm h₂ h₁
    -- 🎉 no goals
#align rat.nonneg_antisymm Rat.nonneg_antisymm

protected theorem nonneg_total : Rat.Nonneg a ∨ Rat.Nonneg (-a) := by
  cases' a with n; exact Or.imp_right neg_nonneg_of_nonpos (le_total 0 n)
  -- ⊢ Rat.Nonneg (mk' n den✝) ∨ Rat.Nonneg (-mk' n den✝)
                   -- 🎉 no goals
#align rat.nonneg_total Rat.nonneg_total

instance decidableNonneg : Decidable (Rat.Nonneg a) := by
  cases a; unfold Rat.Nonneg; infer_instance
  -- ⊢ Decidable (Rat.Nonneg (mk' num✝ den✝))
           -- ⊢ Decidable (0 ≤ (mk' num✝ den✝).num)
                              -- 🎉 no goals
#align rat.decidable_nonneg Rat.decidableNonneg

-- Porting note: Now `Std` defines `≤` on `Rat`.
-- This is the old mathlib3 definition.
/-- Relation `a ≤ b` on `ℚ` defined as `a ≤ b ↔ Rat.Nonneg (b - a)`. Use `a ≤ b` instead of
`Rat.le a b`. -/
protected def le' (a b : ℚ) := Rat.Nonneg (b - a)
#align rat.le Rat.le'

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `mk' n d` with `d ≠ 0`. -/
-- Porting note: TODO move
@[elab_as_elim]
def numDenCasesOn''.{u} {C : ℚ → Sort u} (a : ℚ)
    (H : ∀ (n : ℤ) (d : ℕ) (nz red), C (mk' n d nz red)) :
    C a :=
  numDenCasesOn a fun n d h h' => by
    rw [←mk_eq_divInt _ _ h.ne' h']
    -- ⊢ C (mk' n d)
    exact H n d h.ne' _
    -- 🎉 no goals

-- Porting note: TODO can this be shortened?
protected theorem le_iff_Nonneg (a b : ℚ) : a ≤ b ↔ Rat.Nonneg (b - a) :=
  numDenCasesOn'' a fun na da ha hared =>
    numDenCasesOn'' b fun nb db hb hbred => by
      change Rat.blt _ _ = false ↔ _
      -- ⊢ Rat.blt (mk' nb db) (mk' na da) = false ↔ Rat.Nonneg (mk' nb db - mk' na da)
      unfold Rat.blt
      -- ⊢ (if (decide ((mk' nb db).num < 0) && decide (0 ≤ (mk' na da).num)) = true th …
      simp [-divInt_ofNat, mkRat_eq]
      -- ⊢ (if nb < 0 ∧ 0 ≤ na then False else if nb = 0 then na ≤ 0 else (0 < nb → 0 < …
      split_ifs with h h'
      · rw [Rat.sub_def]
        -- ⊢ False ↔ Rat.Nonneg (normalize ((mk' nb db).num * ↑(mk' na da).den - (mk' na  …
        simp [Rat.Nonneg]
        -- ⊢ (normalize (nb * ↑da - na * ↑db) (db * da)).num < 0
        simp [normalize_eq]
        -- ⊢ (nb * ↑da - na * ↑db) / ↑(Nat.gcd (Int.natAbs (nb * ↑da - na * ↑db)) (db * d …
        apply Int.ediv_neg'
        -- ⊢ nb * ↑da - na * ↑db < 0
        · rw [sub_neg]
          -- ⊢ nb * ↑da < na * ↑db
          apply lt_of_lt_of_le
          · apply mul_neg_of_neg_of_pos h.1
            -- ⊢ 0 < ↑da
            rwa [Nat.cast_pos, pos_iff_ne_zero]
            -- 🎉 no goals
          · apply mul_nonneg h.2 (Nat.cast_nonneg _)
            -- 🎉 no goals
        · simp only [Nat.cast_pos]
          -- ⊢ 0 < Nat.gcd (Int.natAbs (nb * ↑da - na * ↑db)) (db * da)
          apply Nat.gcd_pos_of_pos_right
          -- ⊢ 0 < db * da
          apply mul_pos <;> rwa [pos_iff_ne_zero]
          -- ⊢ 0 < db
                            -- 🎉 no goals
                            -- 🎉 no goals
      · simp only [divInt_ofNat, ←zero_iff_num_zero, mkRat_eq_zero hb] at h'
        -- ⊢ na ≤ 0 ↔ Rat.Nonneg (mk' nb db - mk' na da)
        simp [h', Rat.Nonneg]
        -- 🎉 no goals
      · simp [Rat.Nonneg, Rat.sub_def, normalize_eq]
        -- ⊢ (0 < nb → 0 < na) → na * ↑db ≤ nb * ↑da ↔ 0 ≤ (nb * ↑da - na * ↑db) / ↑(Nat. …
        refine ⟨fun H => ?_, fun H _ => ?_⟩
        -- ⊢ 0 ≤ (nb * ↑da - na * ↑db) / ↑(Nat.gcd (Int.natAbs (nb * ↑da - na * ↑db)) (db …
        · refine Int.ediv_nonneg ?_ (Nat.cast_nonneg _)
          -- ⊢ 0 ≤ nb * ↑da - na * ↑db
          rw [sub_nonneg]
          -- ⊢ na * ↑db ≤ nb * ↑da
          push_neg at h
          -- ⊢ na * ↑db ≤ nb * ↑da
          obtain hb|hb := Ne.lt_or_lt h'
          -- ⊢ na * ↑db ≤ nb * ↑da
          · apply H
            -- ⊢ 0 < nb → 0 < na
            intro H'
            -- ⊢ 0 < na
            exact (hb.trans H').false.elim
            -- 🎉 no goals
          · obtain ha|ha := le_or_lt na 0
            -- ⊢ na * ↑db ≤ nb * ↑da
            · apply le_trans <| mul_nonpos_of_nonpos_of_nonneg ha (Nat.cast_nonneg _)
              -- ⊢ 0 ≤ nb * ↑da
              exact mul_nonneg hb.le (Nat.cast_nonneg _)
              -- 🎉 no goals
            · exact H (fun _ => ha)
              -- 🎉 no goals
        · rw [←sub_nonneg]
          -- ⊢ 0 ≤ nb * ↑da - na * ↑db
          contrapose! H
          -- ⊢ (nb * ↑da - na * ↑db) / ↑(Nat.gcd (Int.natAbs (nb * ↑da - na * ↑db)) (db * d …
          apply Int.ediv_neg' H
          -- ⊢ 0 < ↑(Nat.gcd (Int.natAbs (nb * ↑da - na * ↑db)) (db * da))
          simp only [Nat.cast_pos]
          -- ⊢ 0 < Nat.gcd (Int.natAbs (nb * ↑da - na * ↑db)) (db * da)
          apply Nat.gcd_pos_of_pos_right
          -- ⊢ 0 < db * da
          apply mul_pos <;> rwa [pos_iff_ne_zero]
          -- ⊢ 0 < db
                            -- 🎉 no goals
                            -- 🎉 no goals

protected theorem le_def {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_Nonneg]
  -- ⊢ Rat.Nonneg (c /. d - a /. b) ↔ a * d ≤ c * b
  show Rat.Nonneg _ ↔ _
  -- ⊢ Rat.Nonneg (c /. d - a /. b) ↔ a * d ≤ c * b
  rw [← sub_nonneg]
  -- ⊢ Rat.Nonneg (c /. d - a /. b) ↔ 0 ≤ c * b - a * d
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, mul_pos d0 b0]
  -- 🎉 no goals
#align rat.le_def Rat.le_def

protected theorem le_refl : a ≤ a := by
  rw [Rat.le_iff_Nonneg]
  -- ⊢ Rat.Nonneg (a - a)
  show Rat.Nonneg (a - a)
  -- ⊢ Rat.Nonneg (a - a)
  rw [sub_self]
  -- ⊢ Rat.Nonneg 0
  exact le_refl (0 : ℤ)
  -- 🎉 no goals
#align rat.le_refl Rat.le_refl

protected theorem le_total : a ≤ b ∨ b ≤ a := by
  have := Rat.nonneg_total (b - a)
  -- ⊢ a ≤ b ∨ b ≤ a
  rw [Rat.le_iff_Nonneg, Rat.le_iff_Nonneg]
  -- ⊢ Rat.Nonneg (b - a) ∨ Rat.Nonneg (a - b)
  rwa [neg_sub] at this
  -- 🎉 no goals
#align rat.le_total Rat.le_total

protected theorem le_antisymm {a b : ℚ} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [Rat.le_iff_Nonneg] at hab hba
  -- ⊢ a = b
  rw [sub_eq_add_neg] at hba
  -- ⊢ a = b
  rw [←neg_sub, sub_eq_add_neg] at hab
  -- ⊢ a = b
  have := eq_neg_of_add_eq_zero_left (Rat.nonneg_antisymm hba hab)
  -- ⊢ a = b
  rwa [neg_neg] at this
  -- 🎉 no goals
#align rat.le_antisymm Rat.le_antisymm

protected theorem le_trans {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [Rat.le_iff_Nonneg] at hab hbc
  -- ⊢ a ≤ c
  have : Rat.Nonneg (b - a + (c - b)) := Rat.nonneg_add hab hbc
  -- ⊢ a ≤ c
  simp_rw [sub_eq_add_neg, add_left_comm (b + -a) c (-b), add_comm (b + -a) (-b),
    add_left_comm (-b) b (-a), add_comm (-b) (-a), add_neg_cancel_comm_assoc,
    ← sub_eq_add_neg] at this
  rw [Rat.le_iff_Nonneg]
  -- ⊢ Rat.Nonneg (c - a)
  exact this
  -- 🎉 no goals
#align rat.le_trans Rat.le_trans

protected theorem not_le {a b : ℚ} : ¬a ≤ b ↔ b < a := (Bool.not_eq_false _).to_iff

instance linearOrder : LinearOrder ℚ where
  le_refl := Rat.le_refl
  le_trans := @Rat.le_trans
  le_antisymm := @Rat.le_antisymm
  le_total := Rat.le_total
  decidableLE _ _ := by infer_instance
                        -- 🎉 no goals
  lt_iff_le_not_le _ _ := by
    -- 🎉 no goals
    rw [← Rat.not_le, and_iff_right_of_imp (Rat.le_total _ _).resolve_left]

-- Extra instances to short-circuit type class resolution
instance : LT ℚ := by infer_instance
                      -- 🎉 no goals

instance : DistribLattice ℚ := by infer_instance
                                  -- 🎉 no goals

instance : Lattice ℚ := by infer_instance
                           -- 🎉 no goals

instance : SemilatticeInf ℚ := by infer_instance
                                  -- 🎉 no goals

instance : SemilatticeSup ℚ := by infer_instance
                                  -- 🎉 no goals

instance : Inf ℚ := by infer_instance
                       -- 🎉 no goals

instance : Sup ℚ := by infer_instance
                       -- 🎉 no goals

instance : PartialOrder ℚ := by infer_instance
                                -- 🎉 no goals

instance : Preorder ℚ := by infer_instance
                            -- 🎉 no goals

protected theorem le_def' {p q : ℚ} : p ≤ q ↔ p.num * q.den ≤ q.num * p.den := by
  rw [← @num_den q, ← @num_den p]
  -- ⊢ p.num /. ↑p.den ≤ q.num /. ↑q.den ↔ (p.num /. ↑p.den).num * ↑(q.num /. ↑q.de …
  conv_rhs => simp only [num_den]
  -- ⊢ p.num /. ↑p.den ≤ q.num /. ↑q.den ↔ p.num * ↑q.den ≤ q.num * ↑p.den
  exact Rat.le_def (by exact_mod_cast p.pos) (by exact_mod_cast q.pos)
  -- 🎉 no goals
#align rat.le_def' Rat.le_def'

protected theorem lt_def {p q : ℚ} : p < q ↔ p.num * q.den < q.num * p.den := by
  rw [lt_iff_le_and_ne, Rat.le_def']
  -- ⊢ p.num * ↑q.den ≤ q.num * ↑p.den ∧ p ≠ q ↔ p.num * ↑q.den < q.num * ↑p.den
  suffices p ≠ q ↔ p.num * q.den ≠ q.num * p.den by
    constructor <;> intro h
    · exact lt_iff_le_and_ne.mpr ⟨h.left, this.mp h.right⟩
    · have tmp := lt_iff_le_and_ne.mp h
      exact ⟨tmp.left, this.mpr tmp.right⟩
  exact not_iff_not.mpr eq_iff_mul_eq_mul
  -- 🎉 no goals
#align rat.lt_def Rat.lt_def

theorem nonneg_iff_zero_le {a} : Rat.Nonneg a ↔ 0 ≤ a := by
  rw [Rat.le_iff_Nonneg]
  -- ⊢ Rat.Nonneg a ↔ Rat.Nonneg (a - 0)
  show Rat.Nonneg a ↔ Rat.Nonneg (a - 0)
  -- ⊢ Rat.Nonneg a ↔ Rat.Nonneg (a - 0)
  simp
  -- 🎉 no goals
#align rat.nonneg_iff_zero_le Rat.nonneg_iff_zero_le

theorem num_nonneg_iff_zero_le : ∀ {a : ℚ}, 0 ≤ a.num ↔ 0 ≤ a
  | ⟨n, d, h, c⟩ => @nonneg_iff_zero_le ⟨n, d, h, c⟩
#align rat.num_nonneg_iff_zero_le Rat.num_nonneg_iff_zero_le

protected theorem add_le_add_left {a b c : ℚ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [Rat.le_iff_Nonneg, add_sub_add_left_eq_sub, Rat.le_iff_Nonneg]
  -- 🎉 no goals
#align rat.add_le_add_left Rat.add_le_add_left

protected theorem mul_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  rw [← nonneg_iff_zero_le] at ha hb ⊢; exact Rat.nonneg_mul ha hb
  -- ⊢ Rat.Nonneg (a * b)
                                        -- 🎉 no goals
#align rat.mul_nonneg Rat.mul_nonneg

instance : LinearOrderedField ℚ :=
  { Rat.field, Rat.linearOrder, Rat.semiring with
    zero_le_one := by decide
                      -- 🎉 no goals
    add_le_add_left := fun a b ab c => Rat.add_le_add_left.2 ab
    mul_pos := fun a b ha hb =>
      lt_of_le_of_ne (Rat.mul_nonneg (le_of_lt ha) (le_of_lt hb))
        (mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm).symm }

-- Extra instances to short-circuit type class resolution
instance : LinearOrderedCommRing ℚ := by infer_instance
                                         -- 🎉 no goals

instance : LinearOrderedRing ℚ := by infer_instance
                                     -- 🎉 no goals

instance : OrderedRing ℚ := by infer_instance
                               -- 🎉 no goals

instance : LinearOrderedSemiring ℚ := by infer_instance
                                         -- 🎉 no goals

instance : OrderedSemiring ℚ := by infer_instance
                                   -- 🎉 no goals

instance : LinearOrderedAddCommGroup ℚ := by infer_instance
                                             -- 🎉 no goals

instance : OrderedAddCommGroup ℚ := by infer_instance
                                       -- 🎉 no goals

instance : OrderedCancelAddCommMonoid ℚ := by infer_instance
                                              -- 🎉 no goals

instance : OrderedAddCommMonoid ℚ := by infer_instance
                                        -- 🎉 no goals

theorem num_pos_iff_pos {a : ℚ} : 0 < a.num ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le <| by
    simpa [(by cases a; rfl : (-a).num = -a.num)] using @num_nonneg_iff_zero_le (-a)
    -- 🎉 no goals
#align rat.num_pos_iff_pos Rat.num_pos_iff_pos

theorem div_lt_div_iff_mul_lt_mul {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) :
    (a : ℚ) / b < c / d ↔ a * d < c * b := by
  simp only [lt_iff_le_not_le]
  -- ⊢ ↑a / ↑b ≤ ↑c / ↑d ∧ ¬↑c / ↑d ≤ ↑a / ↑b ↔ a * d ≤ c * b ∧ ¬c * b ≤ a * d
  apply and_congr
  -- ⊢ ↑a / ↑b ≤ ↑c / ↑d ↔ a * d ≤ c * b
  · simp [div_num_den, Rat.le_def b_pos d_pos]
    -- 🎉 no goals
  · apply not_congr
    -- ⊢ ↑c / ↑d ≤ ↑a / ↑b ↔ c * b ≤ a * d
    simp [div_num_den, Rat.le_def d_pos b_pos]
    -- 🎉 no goals
#align rat.div_lt_div_iff_mul_lt_mul Rat.div_lt_div_iff_mul_lt_mul

theorem lt_one_iff_num_lt_denom {q : ℚ} : q < 1 ↔ q.num < q.den := by simp [Rat.lt_def]
                                                                      -- 🎉 no goals
#align rat.lt_one_iff_num_lt_denom Rat.lt_one_iff_num_lt_denom

theorem abs_def (q : ℚ) : |q| = q.num.natAbs /. q.den := by
  cases' le_total q 0 with hq hq
  -- ⊢ |q| = ↑(Int.natAbs q.num) /. ↑q.den
  · rw [abs_of_nonpos hq]
    -- ⊢ -q = ↑(Int.natAbs q.num) /. ↑q.den
    rw [← @num_den q, ← divInt_zero_one, Rat.le_def (Int.coe_nat_pos.2 q.pos) zero_lt_one, mul_one,
      zero_mul] at hq
    rw [Int.ofNat_natAbs_of_nonpos hq, ← neg_def, num_den]
    -- 🎉 no goals
  · rw [abs_of_nonneg hq]
    -- ⊢ q = ↑(Int.natAbs q.num) /. ↑q.den
    rw [← @num_den q, ← divInt_zero_one, Rat.le_def zero_lt_one (Int.coe_nat_pos.2 q.pos), mul_one,
      zero_mul] at hq
    rw [Int.natAbs_of_nonneg hq, num_den]
    -- 🎉 no goals
#align rat.abs_def Rat.abs_def

end Rat

-- We make some assertions here about declarations that do not need to be in the import dependencies
-- for this file, but have been in the past.
assert_not_exists Fintype

assert_not_exists Set.Icc

assert_not_exists GaloisConnection

-- These are less significant, but should not be relaxed until at least after port to Lean 4.
assert_not_exists LinearOrderedCommGroupWithZero
