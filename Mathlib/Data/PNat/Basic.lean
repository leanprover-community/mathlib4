/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
Ported by: Jon Eugster

! This file was ported from Lean 3 source module data.pnat.basic
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.PNat.Defs
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Positive.Ring

/-!
# The positive natural numbers

This file develops the type `ℕ+` or `pnat`, the subtype of natural numbers that are positive.
It is defined in `data.pnat.defs`, but most of the development is deferred to here so
that `data.pnat.defs` can have very few imports.
-/


deriving instance AddLeftCancelSemigroup, AddRightCancelSemigroup, AddCommSemigroup,
  LinearOrderedCancelCommMonoid, Add, Mul, Distrib for PNat

namespace PNat

@[simp]
theorem one_add_nat_pred (n : ℕ+) : 1 + n.natPred = n := by
  rw [nat_pred, add_tsub_cancel_iff_le.mpr <| show 1 ≤ (n : ℕ) from n.2]
#align pnat.one_add_nat_pred PNat.one_add_nat_pred

@[simp]
theorem nat_pred_add_one (n : ℕ+) : n.natPred + 1 = n :=
  (add_comm _ _).trans n.one_add_nat_pred
#align pnat.nat_pred_add_one PNat.nat_pred_add_one

@[mono]
theorem nat_pred_strict_mono : StrictMono natPred := fun m n h => Nat.pred_lt_pred m.2.ne' h
#align pnat.nat_pred_strict_mono PNat.nat_pred_strict_mono

@[mono]
theorem nat_pred_monotone : Monotone natPred :=
  nat_pred_strict_mono.Monotone
#align pnat.nat_pred_monotone PNat.nat_pred_monotone

theorem nat_pred_injective : Function.Injective natPred :=
  nat_pred_strict_mono.Injective
#align pnat.nat_pred_injective PNat.nat_pred_injective

@[simp]
theorem nat_pred_lt_nat_pred {m n : ℕ+} : m.natPred < n.natPred ↔ m < n :=
  nat_pred_strict_mono.lt_iff_lt
#align pnat.nat_pred_lt_nat_pred PNat.nat_pred_lt_nat_pred

@[simp]
theorem nat_pred_le_nat_pred {m n : ℕ+} : m.natPred ≤ n.natPred ↔ m ≤ n :=
  nat_pred_strict_mono.le_iff_le
#align pnat.nat_pred_le_nat_pred PNat.nat_pred_le_nat_pred

@[simp]
theorem nat_pred_inj {m n : ℕ+} : m.natPred = n.natPred ↔ m = n :=
  nat_pred_injective.eq_iff
#align pnat.nat_pred_inj PNat.nat_pred_inj

end PNat

namespace Nat

@[mono]
theorem succ_pnat_strict_mono : StrictMono succPNat := fun m n => Nat.succ_lt_succ
#align nat.succ_pnat_strict_mono Nat.succ_pnat_strict_mono

@[mono]
theorem succ_pnat_mono : Monotone succPNat :=
  succ_pnat_strict_mono.Monotone
#align nat.succ_pnat_mono Nat.succ_pnat_mono

@[simp]
theorem succ_pnat_lt_succ_pnat {m n : ℕ} : m.succPnat < n.succPnat ↔ m < n :=
  succ_pnat_strict_mono.lt_iff_lt
#align nat.succ_pnat_lt_succ_pnat Nat.succ_pnat_lt_succ_pnat

@[simp]
theorem succ_pnat_le_succ_pnat {m n : ℕ} : m.succPnat ≤ n.succPnat ↔ m ≤ n :=
  succ_pnat_strict_mono.le_iff_le
#align nat.succ_pnat_le_succ_pnat Nat.succ_pnat_le_succ_pnat

theorem succ_pnat_injective : Function.Injective succPNat :=
  succ_pnat_strict_mono.Injective
#align nat.succ_pnat_injective Nat.succ_pnat_injective

@[simp]
theorem succ_pnat_inj {n m : ℕ} : succPNat n = succPNat m ↔ n = m :=
  succ_pnat_injective.eq_iff
#align nat.succ_pnat_inj Nat.succ_pnat_inj

end Nat

namespace PNat

open Nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/
@[simp, norm_cast]
theorem coe_inj {m n : ℕ+} : (m : ℕ) = n ↔ m = n :=
  SetCoe.ext_iff
#align pnat.coe_inj PNat.coe_inj

@[simp, norm_cast]
theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n :=
  rfl
#align pnat.add_coe PNat.add_coe

/-- `pnat.coe` promoted to an `add_hom`, that is, a morphism which preserves addition. -/
def coeAddHom : AddHom ℕ+ ℕ where
  toFun := coe
  map_add' := add_coe
#align pnat.coe_add_hom PNat.coeAddHom

instance : CovariantClass ℕ+ ℕ+ (· + ·) (· ≤ ·) :=
  Positive.covariantClass_add_le

instance : CovariantClass ℕ+ ℕ+ (· + ·) (· < ·) :=
  Positive.covariantClass_add_lt

instance : ContravariantClass ℕ+ ℕ+ (· + ·) (· ≤ ·) :=
  Positive.contravariantClass_add_le

instance : ContravariantClass ℕ+ ℕ+ (· + ·) (· < ·) :=
  Positive.contravariantClass_add_lt

/-- An equivalence between `ℕ+` and `ℕ` given by `pnat.nat_pred` and `nat.succ_pnat`. -/
@[simps (config := { fullyApplied := false })]
def Equiv.pnatEquivNat : ℕ+ ≃ ℕ where
  toFun := PNat.natPred
  invFun := Nat.succPNat
  left_inv := succ_pnat_nat_pred
  right_inv := Nat.natPred_succPNat
#align equiv.pnat_equiv_nat Equiv.pnatEquivNat

/-- The order isomorphism between ℕ and ℕ+ given by `succ`. -/
@[simps (config := { fullyApplied := false }) apply]
def OrderIso.pnatIsoNat : ℕ+ ≃o
      ℕ where
  toEquiv := Equiv.pnatEquivNat
  map_rel_iff' _ _ := nat_pred_le_nat_pred
#align order_iso.pnat_iso_nat OrderIso.pnatIsoNat

@[simp]
theorem OrderIso.pnat_iso_nat_symm_apply : ⇑OrderIso.pnatIsoNat.symm = Nat.succPNat :=
  rfl
#align order_iso.pnat_iso_nat_symm_apply OrderIso.pnat_iso_nat_symm_apply

theorem lt_add_one_iff : ∀ {a b : ℕ+}, a < b + 1 ↔ a ≤ b := fun a b => Nat.lt_add_one_iff
#align pnat.lt_add_one_iff PNat.lt_add_one_iff

theorem add_one_le_iff : ∀ {a b : ℕ+}, a + 1 ≤ b ↔ a < b := fun a b => Nat.add_one_le_iff
#align pnat.add_one_le_iff PNat.add_one_le_iff

instance : OrderBot ℕ+ where
  bot := 1
  bot_le a := a.property

@[simp]
theorem bot_eq_one : (⊥ : ℕ+) = 1 :=
  rfl
#align pnat.bot_eq_one PNat.bot_eq_one

-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp]
theorem mk_bit0 (n) {h} : (⟨bit0 n, h⟩ : ℕ+) = (bit0 ⟨n, pos_of_bit0_pos h⟩ : ℕ+) :=
  rfl
#align pnat.mk_bit0 PNat.mk_bit0

@[simp]
theorem mk_bit1 (n) {h} {k} : (⟨bit1 n, h⟩ : ℕ+) = (bit1 ⟨n, k⟩ : ℕ+) :=
  rfl
#align pnat.mk_bit1 PNat.mk_bit1

-- Some lemmas that rewrite inequalities between explicit numerals in `ℕ+`
-- into the corresponding inequalities in `ℕ`.
-- TODO: perhaps this should not be attempted by `simp`,
-- and instead we should expect `norm_num` to take care of these directly?
-- TODO: these lemmas are perhaps incomplete:
-- * 1 is not represented as a bit0 or bit1
-- * strict inequalities?
@[simp]
theorem bit0_le_bit0 (n m : ℕ+) : bit0 n ≤ bit0 m ↔ bit0 (n : ℕ) ≤ bit0 (m : ℕ) :=
  Iff.rfl
#align pnat.bit0_le_bit0 PNat.bit0_le_bit0

@[simp]
theorem bit0_le_bit1 (n m : ℕ+) : bit0 n ≤ bit1 m ↔ bit0 (n : ℕ) ≤ bit1 (m : ℕ) :=
  Iff.rfl
#align pnat.bit0_le_bit1 PNat.bit0_le_bit1

@[simp]
theorem bit1_le_bit0 (n m : ℕ+) : bit1 n ≤ bit0 m ↔ bit1 (n : ℕ) ≤ bit0 (m : ℕ) :=
  Iff.rfl
#align pnat.bit1_le_bit0 PNat.bit1_le_bit0

@[simp]
theorem bit1_le_bit1 (n m : ℕ+) : bit1 n ≤ bit1 m ↔ bit1 (n : ℕ) ≤ bit1 (m : ℕ) :=
  Iff.rfl
#align pnat.bit1_le_bit1 PNat.bit1_le_bit1

@[simp, norm_cast]
theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n :=
  rfl
#align pnat.mul_coe PNat.mul_coe

/-- `pnat.coe` promoted to a `monoid_hom`. -/
def coeMonoidHom : ℕ+ →* ℕ where
  toFun := coe
  map_one' := one_coe
  map_mul' := mul_coe
#align pnat.coe_monoid_hom PNat.coeMonoidHom

@[simp]
theorem coe_coe_monoid_hom : (coeMonoidHom : ℕ+ → ℕ) = coe :=
  rfl
#align pnat.coe_coe_monoid_hom PNat.coe_coe_monoid_hom

@[simp]
theorem le_one_iff {n : ℕ+} : n ≤ 1 ↔ n = 1 :=
  le_bot_iff
#align pnat.le_one_iff PNat.le_one_iff

theorem lt_add_left (n m : ℕ+) : n < m + n :=
  lt_add_of_pos_left _ m.2
#align pnat.lt_add_left PNat.lt_add_left

theorem lt_add_right (n m : ℕ+) : n < n + m :=
  (lt_add_left n m).trans_eq (add_comm _ _)
#align pnat.lt_add_right PNat.lt_add_right

@[simp, norm_cast]
theorem coe_bit0 (a : ℕ+) : ((bit0 a : ℕ+) : ℕ) = bit0 (a : ℕ) :=
  rfl
#align pnat.coe_bit0 PNat.coe_bit0

@[simp, norm_cast]
theorem coe_bit1 (a : ℕ+) : ((bit1 a : ℕ+) : ℕ) = bit1 (a : ℕ) :=
  rfl
#align pnat.coe_bit1 PNat.coe_bit1

@[simp, norm_cast]
theorem pow_coe (m : ℕ+) (n : ℕ) : ((m ^ n : ℕ+) : ℕ) = (m : ℕ) ^ n :=
  rfl
#align pnat.pow_coe PNat.pow_coe

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance : Sub ℕ+ :=
  ⟨fun a b => toPNat' (a - b : ℕ)⟩

theorem sub_coe (a b : ℕ+) : ((a - b : ℕ+) : ℕ) = ite (b < a) (a - b : ℕ) 1 := by
  change (to_pnat' _ : ℕ) = ite _ _ _
  split_ifs with h
  · exact to_pnat'_coe (tsub_pos_of_lt h)
  · rw [tsub_eq_zero_iff_le.mpr (le_of_not_gt h : (a : ℕ) ≤ b)]
    rfl
#align pnat.sub_coe PNat.sub_coe

theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b := fun h =>
  Eq <| by
    rw [add_coe, sub_coe, if_pos h]
    exact add_tsub_cancel_of_le h.le
#align pnat.add_sub_of_lt PNat.add_sub_of_lt

/-- If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`. -/
theorem exists_eq_succ_of_ne_one : ∀ {n : ℕ+} (h1 : n ≠ 1), ∃ k : ℕ+, n = k + 1
  | ⟨1, _⟩, h1 => False.elim <| h1 rfl
  | ⟨n + 2, _⟩, _ => ⟨⟨n + 1, by simp⟩, rfl⟩
#align pnat.exists_eq_succ_of_ne_one PNat.exists_eq_succ_of_ne_one

/-- Strong induction on `ℕ+`, with `n = 1` treated separately. -/
def caseStrongInductionOn {p : ℕ+ → Sort _} (a : ℕ+) (hz : p 1)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a := by
  apply strong_induction_on a
  rintro ⟨k, kprop⟩ hk
  cases' k with k
  · exact (lt_irrefl 0 kprop).elim
  cases' k with k
  · exact hz
  exact hi ⟨k.succ, Nat.succ_pos _⟩ fun m hm => hk _ (lt_succ_iff.2 hm)
#align pnat.case_strong_induction_on PNat.caseStrongInductionOn

/-- An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_elim]
def recOn (n : ℕ+) {p : ℕ+ → Sort _} (p1 : p 1) (hp : ∀ n, p n → p (n + 1)) : p n := by
  rcases n with ⟨n, h⟩
  induction' n with n IH
  · exact absurd h (by decide)
  · cases' n with n
    · exact p1
    · exact hp _ (IH n.succ_pos)
#align pnat.rec_on PNat.recOn

@[simp]
theorem rec_on_one {p} (p1 hp) : @PNat.recOn 1 p p1 hp = p1 :=
  rfl
#align pnat.rec_on_one PNat.rec_on_one

@[simp]
theorem rec_on_succ (n : ℕ+) {p : ℕ+ → Sort _} (p1 hp) :
    @PNat.recOn (n + 1) p p1 hp = hp n (@PNat.recOn n p p1 hp) := by
  cases' n with n h
  cases n <;> [exact absurd h (by decide), rfl]
#align pnat.rec_on_succ PNat.rec_on_succ

theorem mod_div_aux_spec :
    ∀ (k : ℕ+) (r q : ℕ) (h : ¬(r = 0 ∧ q = 0)),
      ((modDivAux k r q).1 : ℕ) + k * (modDivAux k r q).2 = r + k * q
  | k, 0, 0, h => (h ⟨rfl, rfl⟩).elim
  | k, 0, q + 1, h => by
    change (k : ℕ) + (k : ℕ) * (q + 1).pred = 0 + (k : ℕ) * (q + 1)
    rw [Nat.pred_succ, Nat.mul_succ, zero_add, add_comm]
  | k, r + 1, q, h => rfl
#align pnat.mod_div_aux_spec PNat.mod_div_aux_spec

theorem mod_add_div (m k : ℕ+) : (mod m k + k * div m k : ℕ) = m := by
  let h₀ := Nat.mod_add_div (m : ℕ) (k : ℕ)
  have : ¬((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0) := by
    rintro ⟨hr, hq⟩
    rw [hr, hq, mul_zero, zero_add] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := mod_div_aux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this
  exact this.trans h₀
#align pnat.mod_add_div PNat.mod_add_div

theorem div_add_mod (m k : ℕ+) : (k * div m k + mod m k : ℕ) = m :=
  (add_comm _ _).trans (mod_add_div _ _)
#align pnat.div_add_mod PNat.div_add_mod

theorem mod_add_div' (m k : ℕ+) : (mod m k + div m k * k : ℕ) = m := by
  rw [mul_comm]
  exact mod_add_div _ _
#align pnat.mod_add_div' PNat.mod_add_div'

theorem div_add_mod' (m k : ℕ+) : (div m k * k + mod m k : ℕ) = m := by
  rw [mul_comm]
  exact div_add_mod _ _
#align pnat.div_add_mod' PNat.div_add_mod'

theorem mod_le (m k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k := by
  change (mod m k : ℕ) ≤ (m : ℕ) ∧ (mod m k : ℕ) ≤ (k : ℕ)
  rw [mod_coe]; split_ifs
  · have hm : (m : ℕ) > 0 := m.pos
    rw [← Nat.mod_add_div (m : ℕ) (k : ℕ), h, zero_add] at hm⊢
    by_cases h' : (m : ℕ) / (k : ℕ) = 0
    · rw [h', mul_zero] at hm
      exact (lt_irrefl _ hm).elim
    · let h' := Nat.mul_le_mul_left (k : ℕ) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h'))
      rw [mul_one] at h'
      exact ⟨h', le_refl (k : ℕ)⟩
  · exact ⟨Nat.mod_le (m : ℕ) (k : ℕ), (Nat.mod_lt (m : ℕ) k.pos).le⟩
#align pnat.mod_le PNat.mod_le

theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) := by
  constructor <;> intro h; rcases h with ⟨_, rfl⟩; apply dvd_mul_right
  rcases h with ⟨a, h⟩; cases a;
  · contrapose h
    apply NeZero
  use a.succ; apply Nat.succ_pos; rw [← coe_inj, h, mul_coe, mk_coe]
#align pnat.dvd_iff PNat.dvd_iff

theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k := by
  rw [dvd_iff]
  rw [Nat.dvd_iff_mod_eq_zero]; constructor
  · intro h
    apply Eq
    rw [mod_coe, if_pos h]
  · intro h
    by_cases h' : (m : ℕ) % (k : ℕ) = 0
    · exact h'
    · replace h : (mod m k : ℕ) = (k : ℕ) := congr_arg _ h
      rw [mod_coe, if_neg h'] at h
      exact ((Nat.mod_lt (m : ℕ) k.pos).Ne h).elim
#align pnat.dvd_iff' PNat.dvd_iff'

theorem le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n := by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left
#align pnat.le_of_dvd PNat.le_of_dvd

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * divExact m k = m := by
  apply Eq; rw [mul_coe]
  change (k : ℕ) * (div m k).succ = m
  rw [← div_add_mod m k, dvd_iff'.mp h, Nat.mul_succ]
#align pnat.mul_div_exact PNat.mul_div_exact

theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n := fun hmn hnm =>
  (le_of_dvd hmn).antisymm (le_of_dvd hnm)
#align pnat.dvd_antisymm PNat.dvd_antisymm

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
  ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩
#align pnat.dvd_one_iff PNat.dvd_one_iff

theorem pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ n) : 0 < a := by
  apply pos_iff_ne_zero.2
  intro hzero
  rw [hzero] at h
  exact PNat.ne_zero n (eq_zero_of_zero_dvd h)
#align pnat.pos_of_div_pos PNat.pos_of_div_pos

end PNat
