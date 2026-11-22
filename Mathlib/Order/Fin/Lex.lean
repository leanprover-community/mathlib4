/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Lexicographic order isomorphisms for `Fin`

## Main definitions

* `finProdFinOrderIso`: `finProdFinEquiv` as an order isomorphism
  `Fin m ×ₗ Fin n ≃o Fin (m * n)` for the lexicographic order.
* `natProdFinOrderIso`: `natProdFinEquiv` as an order isomorphism `ℕ ×ₗ Fin n ≃o ℕ`
  for the lexicographic order.
-/

/-- `finProdFinEquiv` as an order isomorphism, for the lexicographic order on
`Fin m × Fin n`. -/
@[expose, simps!]
public def finProdFinOrderIso {m n : ℕ} : Fin m ×ₗ Fin n ≃o Fin (m * n) where
  toEquiv := ofLex.trans finProdFinEquiv
  map_rel_iff' := Fin.mkDivMod_le_mkDivMod_iff.trans Prod.Lex.toLex_le_toLex.symm

/-- `natProdFinEquiv` as an order isomorphism, for the lexicographic order on `ℕ × Fin n`. -/
@[expose, simps!]
public def natProdFinOrderIso (n : ℕ) [NeZero n] : ℕ ×ₗ Fin n ≃o ℕ where
  toEquiv := ofLex.trans (natProdFinEquiv n)
  map_rel_iff' := Nat.mkDivMod_le_mkDivMod_iff.trans Prod.Lex.toLex_le_toLex.symm
