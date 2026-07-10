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
@[instance_reducible]
def PNat := { n : ℕ // 0 < n } deriving DecidableEq, LE, LT

@[inherit_doc]
notation "ℕ+" => PNat

/-- Helper constructor for `ℕ+`. -/
abbrev PNat.mk (n : ℕ) (h : 0 < n) : ℕ+ := ⟨n, h⟩

-- Assert that eta-rfl works; if `PNat.mk` was a `def`, it would not.
example (n : ℕ+) : n = PNat.mk n.val n.property := by
  with_reducible_and_instances rfl

/-- The underlying natural number -/
@[coe]
abbrev PNat.val : ℕ+ → ℕ := Subtype.val

-- Assert that eta-rfl works; if `PNat.val` was a `def`, it would not.
example (n : ℕ+) : n = PNat.mk (PNat.val n) n.property := by
  with_reducible_and_instances rfl

instance coePNatNat : Coe ℕ+ ℕ :=
  ⟨PNat.val⟩

instance : Repr ℕ+ :=
  ⟨fun n n' => reprPrec n.1 n'⟩

instance : One ℕ+ :=
  ⟨⟨1, Nat.zero_lt_one⟩⟩

instance (n : ℕ) [NeZero n] : OfNat ℕ+ n :=
  ⟨⟨n, Nat.pos_of_ne_zero <| NeZero.ne n⟩⟩

namespace PNat

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

@[simp, norm_cast]
theorem coe_inj {m n : ℕ+} : (m : ℕ) = n ↔ m = n :=
  Subtype.ext_iff.symm

instance : Add ℕ+ where
  add m n := ⟨m.1 + n.1, Nat.add_pos_right m.val n.property⟩

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
  cases n
  · exact absurd h (by decide)
  · rfl

@[simp, norm_cast]
theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n :=
  rfl

/-- Strong induction on `ℕ+`. -/
def strongInductionOn {p : ℕ+ → Sort*} (n : ℕ+) : (∀ k, (∀ m, m < k → p m) → p k) → p n
  | IH => IH _ fun a _ => strongInductionOn a IH
termination_by n.1

/-- We now define a long list of structures on ℕ+ induced by
similar structures on ℕ. Most of these behave in a completely
obvious way, but there are a few things to be said about
subtraction, division and powers.
-/
theorem mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k := Iff.rfl

theorem mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k := Iff.rfl

@[simp, norm_cast]
theorem coe_le_coe (n k : ℕ+) : (n : ℕ) ≤ k ↔ n ≤ k :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_lt_coe (n k : ℕ+) : (n : ℕ) < k ↔ n < k :=
  Iff.rfl

@[simp]
theorem pos (n : ℕ+) : 0 < (n : ℕ) :=
  n.2

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n :=
  Subtype.ext

theorem coe_injective : Function.Injective PNat.val :=
  fun _ _ ↦ eq

@[simp]
theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 :=
  Nat.ne_of_gt n.2

instance _root_.NeZero.pnat {a : ℕ+} : NeZero (a : ℕ) :=
  ⟨a.ne_zero⟩

@[deprecated "use `one_le`" (since := "2026-05-07")]
protected theorem one_le (n : ℕ+) : (1 : ℕ+) ≤ n :=
  n.2

@[deprecated "use `not_lt_one`" (since := "2026-05-07")]
protected theorem not_lt_one (n : ℕ+) : ¬n < 1 :=
  Nat.not_lt_of_ge n.2

instance : Inhabited ℕ+ :=
  ⟨1⟩

-- Some lemmas that rewrite `PNat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[norm_cast]
theorem one_coe : ((1 : ℕ+) : ℕ) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_one_iff {m : ℕ+} : (m : ℕ) = 1 ↔ m = 1 :=
  coe_injective.eq_iff' one_coe

instance : WellFoundedRelation ℕ+ :=
  measure (fun (a : ℕ+) => (a : ℕ))

end PNat
