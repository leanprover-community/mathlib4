import Mathlib.Data.Bitvec.Lemmas

namespace Fin
variable {n : Nat}

@[simp] lemma ofFin_or_ofFin (x y : Nat) (hx : x < (2 ^ n)) (hy : y < (2 ^ n)) :
    (mk x hx) ||| (mk y hy) = ⟨x ||| y, Nat.bitwise_lt hx hy⟩ := by
  simp only [HOr.hOr, OrOp.or, lor, mk.injEq]
  apply Nat.mod_eq_of_lt <| Nat.bitwise_lt hx hy

@[simp] lemma ofFin_and_ofFin (x y : Nat) (hx : x < (2 ^ n)) (hy : y < (2 ^ n)) :
    (mk x hx) &&& (mk y hy) = ⟨x &&& y, Nat.bitwise_lt hx hy⟩ := by
  simp only [HAnd.hAnd, AndOp.and, land, mk.injEq]
  apply Nat.mod_eq_of_lt <| Nat.bitwise_lt hx hy

end Fin

namespace Std.BitVec

variable {w : Nat} (x y z : BitVec w)

def BitVec.ldiff : BitVec w :=
  ⟨Nat.ldiff x.toNat y.toNat⟩

section
variable (x y : Fin (2^w))

@[simp] lemma ofFin_le_ofFin_iff  : ofFin x ≤ ofFin y ↔ x ≤ y       := Iff.rfl
@[simp] lemma ofFin_or_ofFin      : ofFin x ||| ofFin y = ⟨x ||| y⟩ := rfl
@[simp] lemma ofFin_and_ofFin     : ofFin x &&& ofFin y = ⟨x &&& y⟩ := rfl

end

@[simp] lemma toNat_or : BitVec.toNat (x ||| y) = x.toNat ||| y.toNat := by
  rcases x with ⟨⟨x, _⟩⟩
  rcases y with ⟨⟨y, _⟩⟩
  simp only [ofFin_or_ofFin, Fin.ofFin_or_ofFin, toNat_ofFin]

@[simp] lemma toNat_and : BitVec.toNat (x &&& y) = x.toNat &&& y.toNat := by
  rcases x with ⟨⟨x, _⟩⟩
  rcases y with ⟨⟨y, _⟩⟩
  simp only [ofFin_and_ofFin, Fin.ofFin_and_ofFin, toNat_ofFin]

protected theorem or_comm : x ||| y = y ||| x := by
  apply toNat_inj.mp
  simp only [toNat_or, Nat.lor_comm]

protected theorem or_assoc (x y z : BitVec w) : x ||| y ||| z = x ||| (y ||| z) := by
  apply toNat_inj.mp
  simp only [toNat_or, Nat.lor_assoc]

@[simp] protected theorem or_self : x ||| x = x := by
  apply toNat_inj.mp
  simp only [toNat_or]
  sorry

protected theorem and_comm : x &&& y = y &&& x := by
  apply toNat_inj.mp
  simp only [toNat_and, Nat.land_comm]

protected theorem and_assoc (x y z : BitVec w) : x &&& y &&& z = x &&& (y &&& z) := by
  apply toNat_inj.mp
  simp only [toNat_and, Nat.land_assoc]

@[simp] protected theorem and_self : x &&& x = x := by
  apply toNat_inj.mp
  simp only [toNat_and]
  sorry

/-!
## Instances
-/

instance : Top (BitVec w)       := ⟨-1⟩
instance : Bot (BitVec w)       := ⟨0⟩
instance : HasCompl (BitVec w)  := ⟨(~~~·)⟩
instance : SDiff (BitVec w)     := ⟨BitVec.ldiff⟩
instance : Sup (BitVec w)       := ⟨(· ||| ·)⟩
instance : Inf (BitVec w)       := ⟨(· &&& ·)⟩

namespace BitOrder

/-- Define an alternative ordering on bitvectors: `x ≤ y` iff every bit of `x` is also set in `y` -/
scoped instance instLE : LE (BitVec w) where
  le x y := x ||| y = y

scoped instance instLT : LT (BitVec w) where
  lt x y := x ≤ y ∧ x ≠ y

/-- Define an alternative ordering on bitvectors: `x ≤ y` iff every bit of `x` is also set in `y` -/
scoped instance instPartialOrder : PartialOrder (BitVec w) where
  le_refl x       := BitVec.or_self x
  le_trans x y z h1 h2 := by
    simp only [(· ≤ ·)] at h1 h2 ⊢
    conv_lhs => rw [←h2, ←BitVec.or_assoc, h1, h2]
  le_antisymm x y h1 h2 := by
    simp only [(· ≤ ·)] at h1 h2 ⊢
    rw [←h2, BitVec.or_comm, ←BitVec.or_assoc, BitVec.or_self, h2] at h1
    exact h1
  lt_iff_le_not_le x y := by
    simp only [LT.lt, LE.le, ne_eq, and_congr_right_iff]
    intro h
    rw [BitVec.or_comm, h, eq_comm]

scoped instance : BooleanAlgebra (BitVec w) where
  le_sup_left x y := by
    simp only [LE.le, Sup.sup, or_eq, ← BitVec.or_assoc, BitVec.or_self]
  le_sup_right x y := by
    simp only [LE.le, Sup.sup, or_eq, BitVec.or_comm x, ← BitVec.or_assoc, BitVec.or_self]
  sup_le x y z h1 h2 := by
    simp [LE.le, Sup.sup] at h1 h2 ⊢
    rw [BitVec.or_assoc, h2, h1]
  inf_le_left x y := by
    simp only [LE.le, Inf.inf, and_or, BitVec.or_self]
    rw [BitVec.and_comm, BitVec.or_comm]
    simp
    sorry
  inf_le_right x y := by
    simp only [LE.le, Inf.inf, and_eq]
    sorry
  le_inf            := sorry
  le_sup_inf        := sorry
  inf_compl_le_bot  := sorry
  top_le_sup_compl  := sorry
  le_top            := sorry
  bot_le            := sorry
  sdiff_eq          := sorry
  himp_eq           := sorry

end BitOrder

/-!
## Extras
Stuff I proved that turned out not to be essential
-/

theorem le_of_toNat_le_toNat (x y : BitVec w) : x.toNat ≤ y.toNat → x ≤ y := id

instance : LinearOrder (BitVec w) where
  le_refl x             := le_refl x.toFin
  le_trans x y z        := @le_trans _ _ x.toFin y.toFin z.toFin
  lt_iff_le_not_le x y  := @lt_iff_le_not_le _ _ x.toFin y.toFin
  le_antisymm     := by
    intro ⟨x⟩ ⟨y⟩
    simp only [ofFin_le_ofFin_iff, ofFin.injEq]
    exact le_antisymm
  le_total x y    := @le_total _ _ x.toFin y.toFin
  decidableLE     := inferInstance

theorem ule_or_left (x y : BitVec w) : x ≤ x ||| y := by
  apply le_of_toNat_le_toNat
  simp only [toNat_or]
  generalize y.toNat = y
  induction' x.toNat using Nat.binaryRec with x₀ x ih generalizing y
  · simp only [Nat.zero_lor, zero_le]
  · cases' y using Nat.binaryRec with y₀ y
    · simp only [Nat.lor_zero, le_refl]
    · simp only [Nat.lor_bit]
      cases x₀
      · apply Nat.bit0_le_bit _ (ih _)
      · simp only [Nat.bit_true, Bool.true_or, bit1_le_bit1, ih]

theorem ule_or_right (x y : BitVec w) : y ≤ x ||| y := by
  rw [BitVec.or_comm]; exact ule_or_left y x

theorem Nat.le_bit (b : Bool) (x : Nat) : x ≤ Nat.bit b x := by
  cases b <;> simp [Nat.bit_val, two_mul, Nat.add_assoc]
