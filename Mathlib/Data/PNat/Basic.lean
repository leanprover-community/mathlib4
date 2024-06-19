/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Positive.Ring
import Mathlib.Order.Hom.Basic

#align_import data.pnat.basic from "leanprover-community/mathlib"@"172bf2812857f5e56938cc148b7a539f52f84ca9"

/-!
# The positive natural numbers

This file develops the type `ℕ+` or `PNat`, the subtype of natural numbers that are positive.
It is defined in `Data.PNat.Defs`, but most of the development is deferred to here so
that `Data.PNat.Defs` can have very few imports.
-/

deriving instance AddLeftCancelSemigroup, AddRightCancelSemigroup, AddCommSemigroup,
  LinearOrderedCancelCommMonoid, Add, Mul, Distrib for PNat

namespace PNat

-- Porting note: this instance is no longer automatically inferred in Lean 4.
instance instWellFoundedLT : WellFoundedLT ℕ+ := WellFoundedRelation.isWellFounded
instance instIsWellOrder : IsWellOrder ℕ+ (· < ·) where

@[simp]
theorem one_add_natPred (n : ℕ+) : 1 + n.natPred = n := by
  rw [natPred, add_tsub_cancel_iff_le.mpr <| show 1 ≤ (n : ℕ) from n.2]
#align pnat.one_add_nat_pred PNat.one_add_natPred

@[simp]
theorem natPred_add_one (n : ℕ+) : n.natPred + 1 = n :=
  (add_comm _ _).trans n.one_add_natPred
#align pnat.nat_pred_add_one PNat.natPred_add_one

@[mono]
theorem natPred_strictMono : StrictMono natPred := fun m _ h => Nat.pred_lt_pred m.2.ne' h
#align pnat.nat_pred_strict_mono PNat.natPred_strictMono

@[mono]
theorem natPred_monotone : Monotone natPred :=
  natPred_strictMono.monotone
#align pnat.nat_pred_monotone PNat.natPred_monotone

theorem natPred_injective : Function.Injective natPred :=
  natPred_strictMono.injective
#align pnat.nat_pred_injective PNat.natPred_injective

@[simp]
theorem natPred_lt_natPred {m n : ℕ+} : m.natPred < n.natPred ↔ m < n :=
  natPred_strictMono.lt_iff_lt
#align pnat.nat_pred_lt_nat_pred PNat.natPred_lt_natPred

@[simp]
theorem natPred_le_natPred {m n : ℕ+} : m.natPred ≤ n.natPred ↔ m ≤ n :=
  natPred_strictMono.le_iff_le
#align pnat.nat_pred_le_nat_pred PNat.natPred_le_natPred

@[simp]
theorem natPred_inj {m n : ℕ+} : m.natPred = n.natPred ↔ m = n :=
  natPred_injective.eq_iff
#align pnat.nat_pred_inj PNat.natPred_inj

@[simp, norm_cast]
lemma val_ofNat (n : ℕ) [NeZero n] :
    ((no_index (OfNat.ofNat n) : ℕ+) : ℕ) = OfNat.ofNat n :=
  rfl

@[simp]
lemma mk_ofNat (n : ℕ) (h : 0 < n) :
    @Eq ℕ+ (⟨no_index (OfNat.ofNat n), h⟩ : ℕ+) (haveI : NeZero n := ⟨h.ne'⟩; OfNat.ofNat n) :=
  rfl

end PNat

namespace Nat

@[mono]
theorem succPNat_strictMono : StrictMono succPNat := fun _ _ => Nat.succ_lt_succ
#align nat.succ_pnat_strict_mono Nat.succPNat_strictMono

@[mono]
theorem succPNat_mono : Monotone succPNat :=
  succPNat_strictMono.monotone
#align nat.succ_pnat_mono Nat.succPNat_mono

@[simp]
theorem succPNat_lt_succPNat {m n : ℕ} : m.succPNat < n.succPNat ↔ m < n :=
  succPNat_strictMono.lt_iff_lt
#align nat.succ_pnat_lt_succ_pnat Nat.succPNat_lt_succPNat

@[simp]
theorem succPNat_le_succPNat {m n : ℕ} : m.succPNat ≤ n.succPNat ↔ m ≤ n :=
  succPNat_strictMono.le_iff_le
#align nat.succ_pnat_le_succ_pnat Nat.succPNat_le_succPNat

theorem succPNat_injective : Function.Injective succPNat :=
  succPNat_strictMono.injective
#align nat.succ_pnat_injective Nat.succPNat_injective

@[simp]
theorem succPNat_inj {n m : ℕ} : succPNat n = succPNat m ↔ n = m :=
  succPNat_injective.eq_iff
#align nat.succ_pnat_inj Nat.succPNat_inj

end Nat

namespace PNat

open Nat

/-- We now define a long list of structures on `ℕ+` induced by
 similar structures on `ℕ`. Most of these behave in a completely
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

/-- `coe` promoted to an `AddHom`, that is, a morphism which preserves addition. -/
def coeAddHom : AddHom ℕ+ ℕ where
  toFun := Coe.coe
  map_add' := add_coe
#align pnat.coe_add_hom PNat.coeAddHom

instance covariantClass_add_le : CovariantClass ℕ+ ℕ+ (· + ·) (· ≤ ·) :=
  Positive.covariantClass_add_le

instance covariantClass_add_lt : CovariantClass ℕ+ ℕ+ (· + ·) (· < ·) :=
  Positive.covariantClass_add_lt

instance contravariantClass_add_le : ContravariantClass ℕ+ ℕ+ (· + ·) (· ≤ ·) :=
  Positive.contravariantClass_add_le

instance contravariantClass_add_lt : ContravariantClass ℕ+ ℕ+ (· + ·) (· < ·) :=
  Positive.contravariantClass_add_lt

/-- An equivalence between `ℕ+` and `ℕ` given by `PNat.natPred` and `Nat.succPNat`. -/
@[simps (config := .asFn)]
def _root_.Equiv.pnatEquivNat : ℕ+ ≃ ℕ where
  toFun := PNat.natPred
  invFun := Nat.succPNat
  left_inv := succPNat_natPred
  right_inv := Nat.natPred_succPNat
#align equiv.pnat_equiv_nat Equiv.pnatEquivNat
#align equiv.pnat_equiv_nat_symm_apply Equiv.pnatEquivNat_symm_apply
#align equiv.pnat_equiv_nat_apply Equiv.pnatEquivNat_apply

/-- The order isomorphism between ℕ and ℕ+ given by `succ`. -/
@[simps! (config := .asFn) apply]
def _root_.OrderIso.pnatIsoNat : ℕ+ ≃o ℕ where
  toEquiv := Equiv.pnatEquivNat
  map_rel_iff' := natPred_le_natPred
#align order_iso.pnat_iso_nat OrderIso.pnatIsoNat
#align order_iso.pnat_iso_nat_apply OrderIso.pnatIsoNat_apply

@[simp]
theorem _root_.OrderIso.pnatIsoNat_symm_apply : OrderIso.pnatIsoNat.symm = Nat.succPNat :=
  rfl
#align order_iso.pnat_iso_nat_symm_apply OrderIso.pnatIsoNat_symm_apply

theorem lt_add_one_iff : ∀ {a b : ℕ+}, a < b + 1 ↔ a ≤ b := Nat.lt_add_one_iff
#align pnat.lt_add_one_iff PNat.lt_add_one_iff

theorem add_one_le_iff : ∀ {a b : ℕ+}, a + 1 ≤ b ↔ a < b := Nat.add_one_le_iff
#align pnat.add_one_le_iff PNat.add_one_le_iff

instance instOrderBot : OrderBot ℕ+ where
  bot := 1
  bot_le a := a.property

@[simp]
theorem bot_eq_one : (⊥ : ℕ+) = 1 :=
  rfl
#align pnat.bot_eq_one PNat.bot_eq_one

/-- Strong induction on `ℕ+`, with `n = 1` treated separately. -/
def caseStrongInductionOn {p : ℕ+ → Sort*} (a : ℕ+) (hz : p 1)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a := by
  apply strongInductionOn a
  rintro ⟨k, kprop⟩ hk
  cases' k with k
  · exact (lt_irrefl 0 kprop).elim
  cases' k with k
  · exact hz
  exact hi ⟨k.succ, Nat.succ_pos _⟩ fun m hm => hk _ (Nat.lt_succ_iff.2 hm)
#align pnat.case_strong_induction_on PNat.caseStrongInductionOn

/-- An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_elim]
def recOn (n : ℕ+) {p : ℕ+ → Sort*} (p1 : p 1) (hp : ∀ n, p n → p (n + 1)) : p n := by
  rcases n with ⟨n, h⟩
  induction' n with n IH
  · exact absurd h (by decide)
  · cases' n with n
    · exact p1
    · exact hp _ (IH n.succ_pos)
#align pnat.rec_on PNat.recOn

@[simp]
theorem recOn_one {p} (p1 hp) : @PNat.recOn 1 p p1 hp = p1 :=
  rfl
#align pnat.rec_on_one PNat.recOn_one

@[simp]
theorem recOn_succ (n : ℕ+) {p : ℕ+ → Sort*} (p1 hp) :
    @PNat.recOn (n + 1) p p1 hp = hp n (@PNat.recOn n p p1 hp) := by
  cases' n with n h
  cases n <;> [exact absurd h (by decide); rfl]
#align pnat.rec_on_succ PNat.recOn_succ

-- Porting note (#11229): deprecated
section deprecated

set_option linter.deprecated false

-- Some lemmas that rewrite inequalities between explicit numerals in `ℕ+`
-- into the corresponding inequalities in `ℕ`.
-- TODO: perhaps this should not be attempted by `simp`,
-- and instead we should expect `norm_num` to take care of these directly?
-- TODO: these lemmas are perhaps incomplete:
-- * 1 is not represented as a bit0 or bit1
-- * strict inequalities?
@[simp, deprecated]
theorem bit0_le_bit0 (n m : ℕ+) : bit0 n ≤ bit0 m ↔ bit0 (n : ℕ) ≤ bit0 (m : ℕ) :=
  Iff.rfl
#align pnat.bit0_le_bit0 PNat.bit0_le_bit0

@[simp, deprecated]
theorem bit0_le_bit1 (n m : ℕ+) : bit0 n ≤ bit1 m ↔ bit0 (n : ℕ) ≤ bit1 (m : ℕ) :=
  Iff.rfl
#align pnat.bit0_le_bit1 PNat.bit0_le_bit1

@[simp, deprecated]
theorem bit1_le_bit0 (n m : ℕ+) : bit1 n ≤ bit0 m ↔ bit1 (n : ℕ) ≤ bit0 (m : ℕ) :=
  Iff.rfl
#align pnat.bit1_le_bit0 PNat.bit1_le_bit0

@[simp, deprecated]
theorem bit1_le_bit1 (n m : ℕ+) : bit1 n ≤ bit1 m ↔ bit1 (n : ℕ) ≤ bit1 (m : ℕ) :=
  Iff.rfl
#align pnat.bit1_le_bit1 PNat.bit1_le_bit1

end deprecated

@[simp, norm_cast]
theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n :=
  rfl
#align pnat.mul_coe PNat.mul_coe

/-- `PNat.coe` promoted to a `MonoidHom`. -/
def coeMonoidHom : ℕ+ →* ℕ where
  toFun := Coe.coe
  map_one' := one_coe
  map_mul' := mul_coe
#align pnat.coe_monoid_hom PNat.coeMonoidHom

@[simp]
theorem coe_coeMonoidHom : (coeMonoidHom : ℕ+ → ℕ) = Coe.coe :=
  rfl
#align pnat.coe_coe_monoid_hom PNat.coe_coeMonoidHom

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
theorem pow_coe (m : ℕ+) (n : ℕ) : ↑(m ^ n) = (m : ℕ) ^ n :=
  rfl
#align pnat.pow_coe PNat.pow_coe

/-- b is greater one if any a is less than b -/
theorem one_lt_of_lt {a b : ℕ+} (hab : a < b) : 1 < b := bot_le.trans_lt hab

theorem add_one (a : ℕ+) : a + 1 = succPNat a := rfl

theorem lt_succ_self (a : ℕ+) : a < succPNat a := lt.base a

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance instSub : Sub ℕ+ :=
  ⟨fun a b => toPNat' (a - b : ℕ)⟩

theorem sub_coe (a b : ℕ+) : ((a - b : ℕ+) : ℕ) = ite (b < a) (a - b : ℕ) 1 := by
  change (toPNat' _ : ℕ) = ite _ _ _
  split_ifs with h
  · exact toPNat'_coe (tsub_pos_of_lt h)
  · rw [tsub_eq_zero_iff_le.mpr (le_of_not_gt h : (a : ℕ) ≤ b)]
    rfl
#align pnat.sub_coe PNat.sub_coe

theorem sub_le (a b : ℕ+) : a - b ≤ a := by
  rw [← coe_le_coe, sub_coe]
  split_ifs with h
  · exact Nat.sub_le a b
  · exact a.2

theorem le_sub_one_of_lt {a b : ℕ+} (hab: a < b) : a ≤ b - (1 : ℕ+) := by
  rw [← coe_le_coe, sub_coe]
  split_ifs with h
  · exact Nat.le_pred_of_lt hab
  · exact hab.le.trans (le_of_not_lt h)

theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b :=
  fun h =>
    PNat.eq <| by
      rw [add_coe, sub_coe, if_pos h]
      exact add_tsub_cancel_of_le h.le
#align pnat.add_sub_of_lt PNat.add_sub_of_lt

/-- If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`. -/
theorem exists_eq_succ_of_ne_one : ∀ {n : ℕ+} (_ : n ≠ 1), ∃ k : ℕ+, n = k + 1
  | ⟨1, _⟩, h₁ => False.elim <| h₁ rfl
  | ⟨n + 2, _⟩, _ => ⟨⟨n + 1, by simp⟩, rfl⟩
#align pnat.exists_eq_succ_of_ne_one PNat.exists_eq_succ_of_ne_one

/-- Lemmas with div, dvd and mod operations -/
theorem modDivAux_spec :
    ∀ (k : ℕ+) (r q : ℕ) (_ : ¬(r = 0 ∧ q = 0)),
      ((modDivAux k r q).1 : ℕ) + k * (modDivAux k r q).2 = r + k * q
  | k, 0, 0, h => (h ⟨rfl, rfl⟩).elim
  | k, 0, q + 1, _ => by
    change (k : ℕ) + (k : ℕ) * (q + 1).pred = 0 + (k : ℕ) * (q + 1)
    rw [Nat.pred_succ, Nat.mul_succ, zero_add, add_comm]
  | k, r + 1, q, _ => rfl
#align pnat.mod_div_aux_spec PNat.modDivAux_spec

theorem mod_add_div (m k : ℕ+) : (mod m k + k * div m k : ℕ) = m := by
  let h₀ := Nat.mod_add_div (m : ℕ) (k : ℕ)
  have : ¬((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0) := by
    rintro ⟨hr, hq⟩
    rw [hr, hq, mul_zero, zero_add] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := modDivAux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this
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
  rw [mod_coe]
  split_ifs with h
  · have hm : (m : ℕ) > 0 := m.pos
    rw [← Nat.mod_add_div (m : ℕ) (k : ℕ), h, zero_add] at hm ⊢
    by_cases h₁ : (m : ℕ) / (k : ℕ) = 0
    · rw [h₁, mul_zero] at hm
      exact (lt_irrefl _ hm).elim
    · let h₂ : (k : ℕ) * 1 ≤ k * (m / k) :=
        -- Porting note: Specified type of `h₂` explicitly because `rw` could not unify
        -- `succ 0` with `1`.
        Nat.mul_le_mul_left (k : ℕ) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h₁))
      rw [mul_one] at h₂
      exact ⟨h₂, le_refl (k : ℕ)⟩
  · exact ⟨Nat.mod_le (m : ℕ) (k : ℕ), (Nat.mod_lt (m : ℕ) k.pos).le⟩
#align pnat.mod_le PNat.mod_le

theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) := by
  constructor <;> intro h
  · rcases h with ⟨_, rfl⟩
    apply dvd_mul_right
  · rcases h with ⟨a, h⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := a) <| by
      rintro rfl
      simp only [mul_zero, ne_zero] at h
    use ⟨n.succ, n.succ_pos⟩
    rw [← coe_inj, h, mul_coe, mk_coe]
#align pnat.dvd_iff PNat.dvd_iff

theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k := by
  rw [dvd_iff]
  rw [Nat.dvd_iff_mod_eq_zero]; constructor
  · intro h
    apply PNat.eq
    rw [mod_coe, if_pos h]
  · intro h
    by_cases h' : (m : ℕ) % (k : ℕ) = 0
    · exact h'
    · replace h : (mod m k : ℕ) = (k : ℕ) := congr_arg _ h
      rw [mod_coe, if_neg h'] at h
      exact ((Nat.mod_lt (m : ℕ) k.pos).ne h).elim
#align pnat.dvd_iff' PNat.dvd_iff'

theorem le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n := by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left
#align pnat.le_of_dvd PNat.le_of_dvd

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * divExact m k = m := by
  apply PNat.eq; rw [mul_coe]
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
