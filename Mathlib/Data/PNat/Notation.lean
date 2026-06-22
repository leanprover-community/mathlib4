/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.Notation

/-! # Definition and notation for positive natural numbers -/

@[expose] public section

/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def PNat := { n : ℕ // 0 < n } deriving DecidableEq

@[inherit_doc]
notation "ℕ+" => PNat

/-- Helper constructor for `ℕ+`. -/
abbrev PNat.mk (n : ℕ) (h : 0 < n) : ℕ+ := ⟨n, h⟩

/-- The underlying natural number -/
@[coe]
def PNat.val : ℕ+ → ℕ := Subtype.val

instance coePNatNat : Coe ℕ+ ℕ :=
  ⟨PNat.val⟩

instance : Repr ℕ+ :=
  ⟨fun n n' => reprPrec n.1 n'⟩

instance : One ℕ+ :=
  ⟨⟨1, Nat.zero_lt_one⟩⟩

instance (n : ℕ) [NeZero n] : OfNat ℕ+ n :=
  ⟨⟨n, Nat.pos_of_ne_zero <| NeZero.ne n⟩⟩

@[simp]
lemma mk_one : PNat.mk 1 Nat.zero_lt_one = (1 : ℕ+) :=
  rfl

@[simp]
lemma val_one : (1 : ℕ+).val = 1 :=
  rfl

-- Note: similar to Subtype.coe_mk
@[simp]
theorem mk_coe (n h) : (PNat.val (⟨n, h⟩ : ℕ+) : ℕ) = n :=
  rfl
