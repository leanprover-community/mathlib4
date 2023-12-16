/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Invertible.Basic
import Mathlib.GroupTheory.Subsemigroup.Operations
import Mathlib.Data.Int.Cast.Lemmas

#align_import group_theory.subsemigroup.center from "leanprover-community/mathlib"@"1ac8d4304efba9d03fa720d06516fac845aa5353"

/-!
# Centers of magmas and semigroups

## Main definitions

* `Set.center`: the center of a magma
* `Subsemigroup.center`: the center of a semigroup
* `Set.addCenter`: the center of an additive magma
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
-/


variable {M : Type*}

/-- Conditions for an element to be additively central -/
structure IsAddCentral [Add M] (z : M) : Prop where
  /-- addition commutes -/
  comm (a : M) : z + a = a + z
  /-- associative property for left addition -/
  left_assoc (b c : M) : z + (b + c) = (z + b) + c
  /-- middle associative addition property -/
  mid_assoc (a c : M) : (a + z) + c = a + (z + c)
  /-- associative property for right addition -/
  right_assoc (a b : M) : (a + b) + z = a + (b + z)

/-- Conditions for an element to be multiplicatively central -/
@[to_additive]
structure IsMulCentral [Mul M] (z : M) : Prop where
  /-- multiplication commutes -/
  comm (a : M) : z * a = a * z
  /-- associative property for left multiplication -/
  left_assoc (b c : M) : z * (b * c) = (z * b) * c
  /-- middle associative multiplication property -/
  mid_assoc (a c : M) : (a * z) * c = a * (z * c)
  /-- associative property for right multiplication -/
  right_assoc (a b : M) : (a * b) * z = a * (b * z)

namespace IsMulCentral

variable {a b c : M} [Mul M]

-- c.f. Commute.left_comm
@[to_additive]
protected theorem left_comm (h : IsMulCentral a) (b c) : a * (b * c) = b * (a * c) := by
  simp only [h.comm, h.right_assoc]

-- c.f. Commute.right_comm
@[to_additive]
protected theorem right_comm (h : IsMulCentral c) (a b) : a * b * c = a * c * b := by
  simp only [h.right_assoc, h.mid_assoc, h.comm]

end IsMulCentral

namespace Set

section Mul
variable (M) [Mul M]

/-- The center of a magma. -/
@[to_additive addCenter " The center of an additive magma. "]
def center : Set M :=
  { z | IsMulCentral z }
#align set.center Set.center
#align set.add_center Set.addCenter

-- porting note: The `to_additive` version used to be `mem_addCenter` without the iff
@[to_additive mem_addCenter_iff]
theorem mem_center_iff {z : M} : z ∈ center M ↔ IsMulCentral z :=
  Iff.rfl
#align set.mem_center_iff Set.mem_center_iff
#align set.mem_add_center Set.mem_addCenter_iff

variable {M}

@[to_additive (attr := simp) add_mem_addCenter]
theorem mul_mem_center [Mul M] {z₁ z₂ : M} (hz₁ : z₁ ∈ Set.center M) (hz₂ : z₂ ∈ Set.center M) :
    z₁ * z₂ ∈ Set.center M where
  comm a := calc
    z₁ * z₂ * a = z₂ * z₁ * a := by rw [hz₁.comm]
    _ = z₂ * (z₁ * a) := by rw [hz₁.mid_assoc z₂]
    _ = (a * z₁) * z₂ := by rw [hz₁.comm, hz₂.comm]
    _ = a * (z₁ * z₂) := by rw [hz₂.right_assoc a z₁]
  left_assoc (b c : M) := calc
    z₁ * z₂ * (b * c) = z₁ * (z₂ * (b * c)) := by rw [hz₂.mid_assoc]
    _ = z₁ * ((z₂ * b) * c) := by rw [hz₂.left_assoc]
    _ = (z₁ * (z₂ * b)) * c := by rw [hz₁.left_assoc]
    _ = z₁ * z₂ * b * c := by rw [hz₂.mid_assoc]
  mid_assoc (a c : M) := calc
    a * (z₁ * z₂) * c = ((a * z₁) * z₂) * c := by rw [hz₁.mid_assoc]
    _ = (a * z₁) * (z₂ * c) := by rw [hz₂.mid_assoc]
    _ = a * (z₁ * (z₂ * c)) := by rw [hz₁.mid_assoc]
    _ = a * (z₁ * z₂ * c) := by rw [hz₂.mid_assoc]
  right_assoc (a b : M) := calc
    a * b * (z₁ * z₂) = ((a * b) * z₁) * z₂ := by rw [hz₂.right_assoc]
    _ = (a * (b * z₁)) * z₂ := by rw [hz₁.right_assoc]
    _ =  a * ((b * z₁) * z₂) := by rw [hz₂.right_assoc]
    _ = a * (b * (z₁ * z₂)) := by rw [hz₁.mid_assoc]
#align set.mul_mem_center Set.mul_mem_center
#align set.add_mem_add_center Set.add_mem_addCenter

end Mul

section Semigroup
variable [Semigroup M]

@[to_additive]
theorem _root_.Semigroup.mem_center_iff {z : M} :
    z ∈ Set.center M ↔ ∀ g, g * z = z * g := ⟨fun a g ↦ by rw [IsMulCentral.comm a g],
  fun h ↦ ⟨fun _ ↦ (Commute.eq (h _)).symm, fun _ _ ↦ (mul_assoc z _ _).symm,
  fun _ _ ↦ mul_assoc _ z _, fun _ _ ↦ mul_assoc _ _ z⟩ ⟩

variable (M)

-- TODO Add `instance : Decidable (IsMulCentral a)` for `instance decidableMemCenter [Mul M]`
instance decidableMemCenter [∀ a : M, Decidable <| ∀ b : M, b * a = a * b] :
    DecidablePred (· ∈ center M) := fun _ => decidable_of_iff' _ (Semigroup.mem_center_iff)
#align set.decidable_mem_center Set.decidableMemCenter

end Semigroup

section CommSemigroup
variable (M)

@[to_additive (attr := simp) addCenter_eq_univ]
theorem center_eq_univ [CommSemigroup M] : center M = univ :=
  (Subset.antisymm (subset_univ _)) fun _ _ => Semigroup.mem_center_iff.mpr (fun _ => mul_comm _ _)
#align set.center_eq_univ Set.center_eq_univ
#align set.add_center_eq_univ Set.addCenter_eq_univ

end CommSemigroup

variable (M)

@[to_additive (attr := simp) zero_mem_addCenter]
theorem one_mem_center [MulOneClass M] : (1 : M) ∈ Set.center M where
  comm _  := by rw [one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  mid_assoc _ _ := by rw [mul_one, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]
#align set.one_mem_center Set.one_mem_center
#align set.zero_mem_add_center Set.zero_mem_addCenter

@[simp]
theorem zero_mem_center [MulZeroClass M] : (0 : M) ∈ Set.center M where
  comm _ := by rw [zero_mul, mul_zero]
  left_assoc _ _ := by rw [zero_mul, zero_mul, zero_mul]
  mid_assoc _ _ := by rw [mul_zero, zero_mul, mul_zero]
  right_assoc _ _ := by rw [mul_zero, mul_zero, mul_zero]
#align set.zero_mem_center Set.zero_mem_center

@[simp]
theorem natCast_mem_center [NonAssocSemiring M] (n : ℕ) : (n : M) ∈ Set.center M where
  comm _:= by rw [Nat.commute_cast]
  left_assoc _ _ := by
    induction n with
    | zero => rw [Nat.zero_eq, Nat.cast_zero, zero_mul, zero_mul, zero_mul]
    | succ n ihn => rw [Nat.cast_succ, add_mul, one_mul, ihn, add_mul, add_mul, one_mul]
  mid_assoc _ _ := by
    induction n with
    | zero => rw [Nat.zero_eq, Nat.cast_zero, zero_mul, mul_zero, zero_mul]
    | succ n ihn => rw [Nat.cast_succ, add_mul, mul_add, add_mul, ihn, mul_add, one_mul, mul_one]
  right_assoc _ _ := by
    induction n with
    | zero => rw [Nat.zero_eq, Nat.cast_zero, mul_zero, mul_zero, mul_zero]
    | succ n ihn => rw [Nat.cast_succ, mul_add, ihn, mul_add, mul_add, mul_one, mul_one]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_mem_center [NonAssocSemiring M] (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n)) ∈ Set.center M :=
  natCast_mem_center M n

@[simp]
theorem intCast_mem_center [NonAssocRing M] (n : ℤ) : (n : M) ∈ Set.center M where
  comm _ := by rw [Int.commute_cast]
  left_assoc _ _ := match n with
    | (n : ℕ) => by rw [Int.cast_ofNat, (natCast_mem_center _ n).left_assoc _ _]
    | Int.negSucc n => by
      rw [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, add_mul, add_mul, add_mul,
        neg_mul, one_mul, neg_mul 1, one_mul, ← neg_mul, add_right_inj, neg_mul,
        (natCast_mem_center _ n).left_assoc _ _, neg_mul, neg_mul]
  mid_assoc _ _ := match n with
    | (n : ℕ) => by rw [Int.cast_ofNat, (natCast_mem_center _ n).mid_assoc _ _]
    | Int.negSucc n => by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
        rw [add_mul, mul_add, add_mul, mul_add, neg_mul, one_mul]
        rw [neg_mul, mul_neg, mul_one, mul_neg, neg_mul, neg_mul]
        rw [(natCast_mem_center _ n).mid_assoc _ _]
        simp only [mul_neg]
  right_assoc _ _ := match n with
    | (n : ℕ) => by rw [Int.cast_ofNat, (natCast_mem_center _ n).right_assoc _ _]
    | Int.negSucc n => by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
        rw [mul_add, mul_add, mul_add, mul_neg, mul_one, mul_neg, mul_neg, mul_one, mul_neg,
          add_right_inj, (natCast_mem_center _ n).right_assoc _ _, mul_neg, mul_neg]

variable {M}

@[to_additive (attr := simp) neg_mem_addCenter]
theorem inv_mem_center [Group M] {a : M} (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← inv_inj, mul_inv_rev, inv_inv, ha.comm, mul_inv_rev, inv_inv]
#align set.inv_mem_center Set.inv_mem_center
#align set.neg_mem_add_center Set.neg_mem_addCenter

@[simp]
theorem add_mem_center [Distrib M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a + b ∈ Set.center M  where
  comm _ := by rw [add_mul, mul_add, ha.comm, hb.comm]
  left_assoc _ _ := by rw [add_mul, ha.left_assoc, hb.left_assoc, ← add_mul, ← add_mul]
  mid_assoc _ _ := by rw [mul_add, add_mul, ha.mid_assoc, hb.mid_assoc, ← mul_add, ← add_mul]
  right_assoc _ _ := by rw [mul_add, ha.right_assoc, hb.right_assoc, ← mul_add, ← mul_add]
#align set.add_mem_center Set.add_mem_center

@[simp]
theorem neg_mem_center [NonUnitalNonAssocRing M] {a : M} (ha : a ∈ Set.center M) :
    -a ∈ Set.center M where
  comm _ := by rw [← neg_mul_comm, ← ha.comm, neg_mul_comm]
  left_assoc _ _ := by rw [neg_mul, ha.left_assoc, neg_mul, neg_mul]
  mid_assoc _ _ := by rw [← neg_mul_comm, ha.mid_assoc, neg_mul_comm, neg_mul]
  right_assoc _ _ := by rw [mul_neg, ha.right_assoc, mul_neg, mul_neg]
#align set.neg_mem_center Set.neg_mem_centerₓ

@[to_additive subset_addCenter_add_units]
theorem subset_center_units [Monoid M] : ((↑) : Mˣ → M) ⁻¹' center M ⊆ Set.center Mˣ :=
  fun _ ha => by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← Units.eq_iff, Units.val_mul, Units.val_mul, ha.comm]
#align set.subset_center_units Set.subset_center_units
#align set.subset_add_center_add_units Set.subset_addCenter_add_units

theorem center_units_subset [GroupWithZero M] : Set.center Mˣ ⊆ ((↑) : Mˣ → M) ⁻¹' center M :=
  fun _ ha => by
    rw [mem_preimage, _root_.Semigroup.mem_center_iff]
    intro b
    obtain rfl | hb := eq_or_ne b 0
    · rw [zero_mul, mul_zero]
    · exact Units.ext_iff.mp (ha.comm (Units.mk0 b hb)).symm
#align set.center_units_subset Set.center_units_subset

/-- In a group with zero, the center of the units is the preimage of the center. -/
theorem center_units_eq [GroupWithZero M] : Set.center Mˣ = ((↑) : Mˣ → M) ⁻¹' center M :=
  Subset.antisymm center_units_subset subset_center_units
#align set.center_units_eq Set.center_units_eq

@[simp]
theorem units_inv_mem_center [Monoid M] {a : Mˣ} (ha : ↑a ∈ Set.center M) :
    ↑a⁻¹ ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.units_inv_right <| ha ·)

@[simp]
theorem invOf_mem_center [Monoid M] {a : M} [Invertible a] (ha : a ∈ Set.center M) :
    ⅟a ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.invOf_right <| ha ·)

@[simp]
theorem inv_mem_center₀ [GroupWithZero M] {a : M} (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  obtain rfl | ha0 := eq_or_ne a 0
  · rw [inv_zero]
    exact zero_mem_center M
  · lift a to Mˣ using IsUnit.mk0 _ ha0
    simpa only [Units.val_inv_eq_inv_val] using units_inv_mem_center ha
#align set.inv_mem_center₀ Set.inv_mem_center₀

@[to_additive (attr := simp) sub_mem_addCenter]
theorem div_mem_center [Group M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)
#align set.div_mem_center Set.div_mem_center
#align set.sub_mem_add_center Set.sub_mem_addCenter

@[simp]
theorem div_mem_center₀ [GroupWithZero M] {a b : M} (ha : a ∈ Set.center M)
    (hb : b ∈ Set.center M) : a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center₀ hb)
#align set.div_mem_center₀ Set.div_mem_center₀

end Set

/-! ### `Set.center` as a `Subsemigroup`. -/

namespace Subsemigroup

section Mul
variable (M) [Mul M]

/-- The center of a semigroup `M` is the set of elements that commute with everything in `M` -/
@[to_additive
      "The center of a semigroup `M` is the set of elements that commute with everything in `M`"]
def center : Subsemigroup M where
  carrier := Set.center M
  mul_mem' := Set.mul_mem_center
#align subsemigroup.center Subsemigroup.center
#align add_subsemigroup.center AddSubsemigroup.center

-- porting note: `coe_center` is now redundant
#noalign subsemigroup.coe_center
#noalign add_subsemigroup.coe_center

variable {M}

/-- The center of a magma is commutative and associative. -/
@[to_additive "The center of an additive magma is commutative and associative."]
instance center.commSemigroup : CommSemigroup (center M) where
  mul_assoc _ b _ := Subtype.ext <| b.2.mid_assoc _ _
  mul_comm a _ := Subtype.ext <| a.2.comm _
#align subsemigroup.center.comm_semigroup Subsemigroup.center.commSemigroup
#align add_subsemigroup.center.add_comm_semigroup AddSubsemigroup.center.addCommSemigroup

end Mul

section Semigroup
variable [Semigroup M]

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl
#align subsemigroup.mem_center_iff Subsemigroup.mem_center_iff
#align add_subsemigroup.mem_center_iff AddSubsemigroup.mem_center_iff

@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] :
    Decidable (a ∈ center M) :=
  decidable_of_iff' _ Semigroup.mem_center_iff
#align subsemigroup.decidable_mem_center Subsemigroup.decidableMemCenter
#align add_subsemigroup.decidable_mem_center AddSubsemigroup.decidableMemCenter

end Semigroup

section CommSemigroup
variable (M) [CommSemigroup M]

@[to_additive (attr := simp)]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)
#align subsemigroup.center_eq_top Subsemigroup.center_eq_top
#align add_subsemigroup.center_eq_top AddSubsemigroup.center_eq_top

end CommSemigroup

end Subsemigroup

-- Guard against import creep
assert_not_exists Finset
