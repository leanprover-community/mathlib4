/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.PNat.Equiv

/-!
# Basic order and conversion lemmas for positive natural numbers
-/

@[expose] public section

deriving instance AddLeftMono, AddLeftStrictMono,
  AddLeftReflectLE, AddLeftReflectLT, WellFoundedLT for PNat

namespace PNat

@[gcongr, mono]
theorem natPred_strictMono : StrictMono natPred := fun m _ h => Nat.pred_lt_pred m.2.ne' h

@[gcongr, mono]
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
theorem natPred_inj {m n : ℕ+} : natPred m = natPred n ↔ m = n :=
  natPred_injective.eq_iff

end PNat

namespace Nat

@[gcongr, mono]
theorem succPNat_strictMono : StrictMono succPNat := fun _ _ => Nat.succ_lt_succ

@[gcongr, mono]
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

/-- `coe` promoted to an `AddHom`, that is, a morphism which preserves addition. -/
@[simps]
def coeAddHom : AddHom ℕ+ ℕ where
  toFun := (↑)
  map_add' := add_coe

/- The order isomorphism between ℕ and ℕ+ given by `succ`. -/
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

instance : IsBotOneClass ℕ+ where
  isBot_one a := a.2

@[simp]
theorem bot_eq_one : (⊥ : ℕ+) = 1 :=
  rfl

end PNat
