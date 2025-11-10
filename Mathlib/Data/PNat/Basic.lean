/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Positive.Ring
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.PNat.Equiv

/-!
# The positive natural numbers

This file develops the type `ℕ+` or `PNat`, the subtype of natural numbers that are positive.
It is defined in `Data.PNat.Defs`, but most of the development is deferred to here so
that `Data.PNat.Defs` can have very few imports.
-/

deriving instance AddLeftCancelSemigroup, AddRightCancelSemigroup, AddCommSemigroup,
  Add, Mul, Distrib for PNat

namespace PNat

instance instCommMonoid : CommMonoid ℕ+ := Positive.commMonoid
instance instIsOrderedCancelMonoid : IsOrderedCancelMonoid ℕ+ := Positive.isOrderedCancelMonoid
instance instCancelCommMonoid : CancelCommMonoid ℕ+ where
instance instWellFoundedLT : WellFoundedLT ℕ+ := WellFoundedRelation.isWellFounded

@[simp]
theorem one_add_natPred (n : ℕ+) : 1 + n.natPred = n := by
  rw [natPred, add_tsub_cancel_iff_le.mpr <| show 1 ≤ (n : ℕ) from n.2]

@[simp]
theorem natPred_add_one (n : ℕ+) : n.natPred + 1 = n :=
  (add_comm _ _).trans n.one_add_natPred

@[mono]
theorem natPred_strictMono : StrictMono natPred := fun m _ h => Nat.pred_lt_pred m.2.ne' h

@[mono]
theorem natPred_monotone : Monotone natPred :=
  natPred_strictMono.monotone

theorem natPred_injective : Function.Injective natPred :=
  natPred_strictMono.injective

@[simp]
theorem natPred_lt_natPred {m n : ℕ+} : m.natPred < n.natPred ↔ m < n :=
  natPred_strictMono.lt_iff_lt

@[simp]
theorem natPred_le_natPred {m n : ℕ+} : m.natPred ≤ n.natPred ↔ m ≤ n :=
  natPred_strictMono.le_iff_le

@[simp]
theorem natPred_inj {m n : ℕ+} : m.natPred = n.natPred ↔ m = n :=
  natPred_injective.eq_iff

@[simp, norm_cast]
lemma val_ofNat (n : ℕ) [NeZero n] :
    ((ofNat(n) : ℕ+) : ℕ) = OfNat.ofNat n :=
  rfl

@[simp]
lemma mk_ofNat (n : ℕ) (h : 0 < n) :
    @Eq ℕ+ (⟨ofNat(n), h⟩ : ℕ+) (haveI : NeZero n := ⟨h.ne'⟩; OfNat.ofNat n) :=
  rfl

end PNat

namespace Nat

@[mono]
theorem succPNat_strictMono : StrictMono succPNat := fun _ _ => Nat.succ_lt_succ

@[mono]
theorem succPNat_mono : Monotone succPNat :=
  succPNat_strictMono.monotone

@[simp]
theorem succPNat_lt_succPNat {m n : ℕ} : m.succPNat < n.succPNat ↔ m < n :=
  succPNat_strictMono.lt_iff_lt

@[simp]
theorem succPNat_le_succPNat {m n : ℕ} : m.succPNat ≤ n.succPNat ↔ m ≤ n :=
  succPNat_strictMono.le_iff_le

theorem succPNat_injective : Function.Injective succPNat :=
  succPNat_strictMono.injective

@[simp]
theorem succPNat_inj {n m : ℕ} : succPNat n = succPNat m ↔ n = m :=
  succPNat_injective.eq_iff

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

@[simp, norm_cast]
theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n :=
  rfl

/-- `coe` promoted to an `AddHom`, that is, a morphism which preserves addition. -/
@[simps]
def coeAddHom : AddHom ℕ+ ℕ where
  toFun := (↑)
  map_add' := add_coe

instance addLeftMono : AddLeftMono ℕ+ :=
  Positive.addLeftMono

instance addLeftStrictMono : AddLeftStrictMono ℕ+ :=
  Positive.addLeftStrictMono

instance addLeftReflectLE : AddLeftReflectLE ℕ+ :=
  Positive.addLeftReflectLE

instance addLeftReflectLT : AddLeftReflectLT ℕ+ :=
  Positive.addLeftReflectLT

/-- The order isomorphism between ℕ and ℕ+ given by `succ`. -/
@[simps! -fullyApplied apply]
def _root_.OrderIso.pnatIsoNat : ℕ+ ≃o ℕ where
  toEquiv := Equiv.pnatEquivNat
  map_rel_iff' := natPred_le_natPred

@[simp]
theorem _root_.OrderIso.pnatIsoNat_symm_apply : OrderIso.pnatIsoNat.symm = Nat.succPNat :=
  rfl

theorem lt_add_one_iff : ∀ {a b : ℕ+}, a < b + 1 ↔ a ≤ b := Nat.lt_add_one_iff

theorem add_one_le_iff : ∀ {a b : ℕ+}, a + 1 ≤ b ↔ a < b := Nat.add_one_le_iff

instance instOrderBot : OrderBot ℕ+ where
  bot := 1
  bot_le a := a.property

@[simp]
theorem bot_eq_one : (⊥ : ℕ+) = 1 :=
  rfl

/-- Strong induction on `ℕ+`, with `n = 1` treated separately. -/
def caseStrongInductionOn {p : ℕ+ → Sort*} (a : ℕ+) (hz : p 1)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a := by
  apply strongInductionOn a
  rintro ⟨k, kprop⟩ hk
  rcases k with - | k
  · exact (lt_irrefl 0 kprop).elim
  rcases k with - | k
  · exact hz
  exact hi ⟨k.succ, Nat.succ_pos _⟩ fun m hm => hk _ (Nat.lt_succ_iff.2 hm)

/-- An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_elim, induction_eliminator]
def recOn (n : ℕ+) {p : ℕ+ → Sort*} (one : p 1) (succ : ∀ n, p n → p (n + 1)) : p n := by
  rcases n with ⟨n, h⟩
  induction n with
  | zero => exact absurd h (by decide)
  | succ n IH =>
    rcases n with - | n
    · exact one
    · exact succ _ (IH n.succ_pos)

@[simp]
theorem recOn_one {p} (one succ) : @PNat.recOn 1 p one succ = one :=
  rfl

@[simp]
theorem recOn_succ (n : ℕ+) {p : ℕ+ → Sort*} (one succ) :
    @PNat.recOn (n + 1) p one succ = succ n (@PNat.recOn n p one succ) := by
  obtain ⟨n, h⟩ := n
  cases n <;> [exact absurd h (by decide); rfl]

@[simp]
theorem ofNat_le_ofNat {m n : ℕ} [NeZero m] [NeZero n] :
    (ofNat(m) : ℕ+) ≤ ofNat(n) ↔ OfNat.ofNat m ≤ OfNat.ofNat n :=
  .rfl

@[simp]
theorem ofNat_lt_ofNat {m n : ℕ} [NeZero m] [NeZero n] :
    (ofNat(m) : ℕ+) < ofNat(n) ↔ OfNat.ofNat m < OfNat.ofNat n :=
  .rfl

@[simp]
theorem ofNat_inj {m n : ℕ} [NeZero m] [NeZero n] :
    (ofNat(m) : ℕ+) = ofNat(n) ↔ OfNat.ofNat m = OfNat.ofNat n :=
  Subtype.mk_eq_mk

@[simp, norm_cast]
theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n :=
  rfl

/-- `PNat.coe` promoted to a `MonoidHom`. -/
def coeMonoidHom : ℕ+ →* ℕ where
  toFun := Coe.coe
  map_one' := one_coe
  map_mul' := mul_coe

@[simp]
theorem coe_coeMonoidHom : (coeMonoidHom : ℕ+ → ℕ) = (↑) :=
  rfl

@[simp]
theorem le_one_iff {n : ℕ+} : n ≤ 1 ↔ n = 1 :=
  le_bot_iff

theorem lt_add_left (n m : ℕ+) : n < m + n :=
  lt_add_of_pos_left _ m.2

theorem lt_add_right (n m : ℕ+) : n < n + m :=
  (lt_add_left n m).trans_eq (add_comm _ _)

@[simp, norm_cast]
theorem pow_coe (m : ℕ+) (n : ℕ) : ↑(m ^ n) = (m : ℕ) ^ n :=
  rfl

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

theorem sub_le (a b : ℕ+) : a - b ≤ a := by
  rw [← coe_le_coe, sub_coe]
  split_ifs with h
  · exact Nat.sub_le a b
  · exact a.2

theorem le_sub_one_of_lt {a b : ℕ+} (hab : a < b) : a ≤ b - (1 : ℕ+) := by
  rw [← coe_le_coe, sub_coe]
  split_ifs with h
  · exact Nat.le_pred_of_lt hab
  · exact hab.le.trans (le_of_not_gt h)

theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b :=
  fun h =>
    PNat.eq <| by
      rw [add_coe, sub_coe, if_pos h]
      exact add_tsub_cancel_of_le h.le

theorem sub_add_of_lt {a b : ℕ+} (h : b < a) : a - b + b = a := by
  rw [add_comm, add_sub_of_lt h]

@[simp]
theorem add_sub {a b : ℕ+} : a + b - b = a :=
  add_right_cancel (sub_add_of_lt (lt_add_left _ _))

/-- If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`. -/
theorem exists_eq_succ_of_ne_one : ∀ {n : ℕ+} (_ : n ≠ 1), ∃ k : ℕ+, n = k + 1
  | ⟨1, _⟩, h₁ => False.elim <| h₁ rfl
  | ⟨n + 2, _⟩, _ => ⟨⟨n + 1, by simp⟩, rfl⟩

/-- Lemmas with div, dvd and mod operations -/
theorem modDivAux_spec :
    ∀ (k : ℕ+) (r q : ℕ) (_ : ¬(r = 0 ∧ q = 0)),
      ((modDivAux k r q).1 : ℕ) + k * (modDivAux k r q).2 = r + k * q
  | _, 0, 0, h => (h ⟨rfl, rfl⟩).elim
  | k, 0, q + 1, _ => by
    change (k : ℕ) + (k : ℕ) * (q + 1).pred = 0 + (k : ℕ) * (q + 1)
    rw [Nat.pred_succ, Nat.mul_succ, zero_add, add_comm]
  | _, _ + 1, _, _ => rfl

theorem mod_add_div (m k : ℕ+) : (mod m k + k * div m k : ℕ) = m := by
  let h₀ := Nat.mod_add_div (m : ℕ) (k : ℕ)
  have : ¬((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0) := by
    rintro ⟨hr, hq⟩
    rw [hr, hq, mul_zero, zero_add] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := modDivAux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this
  exact this.trans h₀

theorem div_add_mod (m k : ℕ+) : (k * div m k + mod m k : ℕ) = m :=
  (add_comm _ _).trans (mod_add_div _ _)

theorem mod_add_div' (m k : ℕ+) : (mod m k + div m k * k : ℕ) = m := by
  rw [mul_comm]
  exact mod_add_div _ _

theorem div_add_mod' (m k : ℕ+) : (div m k * k + mod m k : ℕ) = m := by
  rw [mul_comm]
  exact div_add_mod _ _

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
        Nat.mul_le_mul_left (k : ℕ) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h₁))
      rw [mul_one] at h₂
      exact ⟨h₂, le_refl (k : ℕ)⟩
  · exact ⟨Nat.mod_le (m : ℕ) (k : ℕ), (Nat.mod_lt (m : ℕ) k.pos).le⟩

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

theorem le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n := by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * divExact m k = m := by
  apply PNat.eq; rw [mul_coe]
  change (k : ℕ) * (div m k).succ = m
  rw [← div_add_mod m k, dvd_iff'.mp h, Nat.mul_succ]

theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n := fun hmn hnm =>
  (le_of_dvd hmn).antisymm (le_of_dvd hnm)

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
  ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩

theorem pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ n) : 0 < a := by
  apply pos_iff_ne_zero.2
  intro hzero
  rw [hzero] at h
  exact PNat.ne_zero n (eq_zero_of_zero_dvd h)

end PNat
