/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
module

public import Mathlib.Data.PNat.Dvd
public import Mathlib.Data.PNat.Algebra.Order
import Mathlib.Tactic.Basify.Attr

/-!
# The positive natural numbers

This file develops the type `ℕ+` or `PNat`, the subtype of natural numbers that are positive.
It is defined in `Data.PNat.Notation`, but most of the development is deferred to here so
that `Data.PNat.Notation`, `Data.PNat.Defs`, etc can have very few imports.

## Implementation details

This file imports more than necessary to prove the results below,
so that it can act as a reexport of underlying theory in a single file.
-/

@[expose] public section

namespace PNat

@[simp, norm_cast, basify_op]
lemma val_ofNat (n : ℕ) [NeZero n] :
    ((ofNat(n) : ℕ+) : ℕ) = OfNat.ofNat n :=
  rfl

@[simp]
lemma mk_ofNat (n : ℕ) (h : 0 < n) :
    @Eq ℕ+ (⟨ofNat(n), h⟩ : ℕ+) (haveI : NeZero n := ⟨h.ne'⟩; OfNat.ofNat n) :=
  rfl

end PNat




namespace PNat

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

/-- If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`. -/
theorem exists_eq_succ_of_ne_one : ∀ {n : ℕ+} (_ : n ≠ 1), ∃ k : ℕ+, n = k + 1
  | ⟨1, _⟩, h₁ => False.elim <| h₁ rfl
  | ⟨n + 2, _⟩, _ => ⟨⟨n + 1, by simp⟩, rfl⟩

end PNat
