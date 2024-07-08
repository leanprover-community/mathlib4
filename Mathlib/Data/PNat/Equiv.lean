/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
import Mathlib.Data.PNat.Defs
import Mathlib.Logic.Equiv.Defs

/-!
# The equivalence between `ℕ+` and `ℕ`
-/

/-- An equivalence between `ℕ+` and `ℕ` given by `PNat.natPred` and `Nat.succPNat`. -/
@[simps (config := .asFn)]
def _root_.Equiv.pnatEquivNat : ℕ+ ≃ ℕ where
  toFun := PNat.natPred
  invFun := Nat.succPNat
  left_inv := PNat.succPNat_natPred
  right_inv := Nat.natPred_succPNat
#align equiv.pnat_equiv_nat Equiv.pnatEquivNat
#align equiv.pnat_equiv_nat_symm_apply Equiv.pnatEquivNat_symm_apply
#align equiv.pnat_equiv_nat_apply Equiv.pnatEquivNat_apply
