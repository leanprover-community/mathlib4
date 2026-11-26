/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Hom.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Boolean algebra structure on idempotents in a commutative (semi)ring

We show that the idempotent in a commutative ring form a Boolean algebra, with complement given
by `a ↦ 1 - a` and infimum given by multiplication. In a commutative semiring where subtraction
is not available, it is still true that pairs of elements `(a, b)` satisfying `a * b = 0` and
`a + b = 1` form a Boolean algebra (such elements are automatically idempotents, and such a pair
is uniquely determined by either `a` or `b`).
-/

@[expose] public section

variable {R : Type*}

instance [CommMonoid R] [AddCommMonoid R] :
    Compl {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  compl a := ⟨(a.val.2, a.val.1), (mul_comm ..).trans a.property.1,
    (add_comm ..).trans a.property.2⟩

lemma eq_of_mul_eq_add_eq_one [NonAssocSemiring R] (a : R) {b c : R}
    (mul : a * b = c * a) (add_ab : a + b = 1) (add_ac : a + c = 1) :
    b = c :=
  calc b = (a + c) * b := by rw [add_ac, one_mul]
       _ = c * (a + b) := by rw [add_mul, mul, mul_add]
       _ = c := by rw [add_ab, mul_one]

section CommSemiring

variable [CommSemiring R] {a b : {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1}}

lemma mul_eq_zero_add_eq_one_ext_left (eq : a.val.1 = b.val.1) : a = b := by
  refine Subtype.ext <| Prod.ext_iff.mpr ⟨eq, eq_of_mul_eq_add_eq_one a.val.1 ?_ a.property.2 ?_⟩
  · rw [a.property.1, mul_comm, eq, b.property.1]
  · rw [eq, b.property.2]

lemma mul_eq_zero_add_eq_one_ext_right (eq : a.val.2 = b.val.2) : a = b := by
  refine Subtype.ext <| Prod.ext_iff.mpr ⟨eq_of_mul_eq_add_eq_one a.val.2 ?_ ?_ ?_, eq⟩
  · rw [mul_comm, a.property.1, eq, b.property.1]
  · rw [add_comm, a.property.2]
  · rw [add_comm, eq, b.property.2]

instance : PartialOrder {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  le a b := a.val.1 * b.val.1 = a.val.1
  le_refl a := (IsIdempotentElem.of_mul_add a.property.1 a.property.2).1
  le_trans a b c hab hbc := show _ = _ by rw [← hab, mul_assoc, hbc]
  le_antisymm a b hab hba := mul_eq_zero_add_eq_one_ext_left <| by rw [← hab, mul_comm, hba]

instance : SemilatticeSup {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  sup a b := ⟨(a.val.1 + a.val.2 * b.val.1, a.val.2 * b.val.2), by simp_rw [add_mul,
      mul_mul_mul_comm _ b.val.1, b.property.1, mul_zero, ← mul_assoc, a.property.1, zero_mul,
      add_zero], by
    simp_rw [add_assoc, ← mul_add, b.property.2, mul_one, a.property.2]⟩
  le_sup_left a b := by
    simp_rw [(· ≤ ·), mul_add, ← mul_assoc, a.property.1, zero_mul, add_zero,
      (IsIdempotentElem.of_mul_add a.property.1 a.property.2).1.eq]
  le_sup_right a b := by
    simp_rw [(· ≤ ·), mul_add, mul_comm a.val.2, ← mul_assoc,
      (IsIdempotentElem.of_mul_add b.property.1 b.property.2).1.eq, ← mul_add, a.property.2,
      mul_one]
  sup_le a b c hac hbc := by simp_rw [(· ≤ ·), add_mul, mul_assoc]; rw [hac, hbc]

instance : BooleanAlgebra {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  inf a b := (aᶜ ⊔ bᶜ)ᶜ
  inf_le_left a b := by simp_rw [(· ≤ ·), (· ⊔ ·), (·ᶜ), SemilatticeSup.sup,
    mul_right_comm, (IsIdempotentElem.of_mul_add a.property.1 a.property.2).1.eq]
  inf_le_right a b := by simp_rw [(· ≤ ·), (· ⊔ ·), (·ᶜ), SemilatticeSup.sup,
    mul_assoc, (IsIdempotentElem.of_mul_add b.property.1 b.property.2).1.eq]
  le_inf a b c hab hac := by
    simp_rw [(· ≤ ·), (· ⊔ ·), (·ᶜ), SemilatticeSup.sup, ← mul_assoc]; rw [hab, hac]
  le_sup_inf a b c := Eq.le <| mul_eq_zero_add_eq_one_ext_right <| by
    simp_rw +instances [(· ⊔ ·), (· ⊓ ·), (·ᶜ), SemilatticeSup.sup, add_mul, mul_add,
      mul_mul_mul_comm _ b.val.1, (IsIdempotentElem.of_mul_add a.property.1 a.property.2).2.eq,
      ← mul_assoc, a.property.1, zero_mul, zero_add]
  top := ⟨(1, 0), mul_zero _, add_zero _⟩
  bot := ⟨(0, 1), zero_mul _, zero_add _⟩
  inf_compl_le_bot a := Eq.le <| mul_eq_zero_add_eq_one_ext_right <| by
    simp_rw +instances [(· ⊔ ·), (· ⊓ ·), (·ᶜ), SemilatticeSup.sup,
      (IsIdempotentElem.of_mul_add a.property.1 a.property.2).1.eq, add_comm, a.property.2]
  top_le_sup_compl a := Eq.le <| mul_eq_zero_add_eq_one_ext_left <| by simp_rw [(· ⊔ ·), (·ᶜ),
    SemilatticeSup.sup, (IsIdempotentElem.of_mul_add a.property.1 a.property.2).2.eq, a.property.2]
  le_top _ := mul_one _
  bot_le _ := zero_mul _
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

end CommSemiring

instance {S : Type*} [CommSemigroup S] : SemilatticeInf {a : S // IsIdempotentElem a} where
  le a b := a.val * b = a
  le_refl a := a.property
  le_trans a b c hab hbc := show _ = _ by rw [← hab, mul_assoc, hbc]
  le_antisymm a b hab hba := Subtype.ext <| by rw [← hab, mul_comm, hba]
  inf a b := ⟨_, a.property.mul b.property⟩
  inf_le_left a b := show _ = _ by simp_rw [mul_right_comm]; rw [a.property]
  inf_le_right a b := show _ = _ by simp_rw [mul_assoc]; rw [b.property]
  le_inf a b c hab hac := by simp_rw [← mul_assoc]; rw [hab, hac]

instance {M : Type*} [CommMonoid M] : OrderTop {a : M // IsIdempotentElem a} where
  top := ⟨1, .one⟩
  le_top _ := mul_one _

instance {M₀ : Type*} [CommMonoidWithZero M₀] : OrderBot {a : M₀ // IsIdempotentElem a} where
  bot := ⟨0, .zero⟩
  bot_le _ := zero_mul _

section CommRing

variable [CommRing R]

instance : Lattice {a : R // IsIdempotentElem a} where
  __ : SemilatticeInf _ := inferInstance
  sup a b := ⟨_, a.property.add_sub_mul b.property⟩
  le_sup_left a b := show _ = _ by
    simp_rw [mul_sub, mul_add]; rw [← mul_assoc, a.property, add_sub_cancel_right]
  le_sup_right a b := show _ = _ by
    simp_rw [mul_sub, mul_add]; rw [← mul_assoc, mul_right_comm, b.property, add_sub_cancel_left]
  sup_le a b c hac hbc := show _ = _ by simp_rw [sub_mul, add_mul, mul_assoc]; rw [hbc, hac]

instance : BooleanAlgebra {a : R // IsIdempotentElem a} where
  __ : DistribLattice _ := .ofInfSupLe fun a b c ↦ Eq.le <| Subtype.ext <| by
    simp_rw [(· ⊔ ·), (· ⊓ ·), SemilatticeSup.sup, SemilatticeInf.inf, Lattice.inf,
      SemilatticeInf.inf, mul_sub, mul_add, mul_mul_mul_comm]
    rw [a.property]
  __ : OrderTop _ := inferInstance
  __ : OrderBot _ := inferInstance
  compl a := ⟨_, a.property.one_sub⟩
  inf_compl_le_bot a :=
    (mul_zero _).trans ((mul_one_sub ..).trans <| by rw [a.property, sub_self]).symm
  top_le_sup_compl a := (one_mul _).trans <| by
    simp_rw [(· ⊔ ·), SemilatticeSup.sup, add_sub_cancel, mul_sub, mul_one]
    rw [a.property, sub_self, sub_zero]; rfl
  sdiff_eq _ _ := rfl
  himp a b := ⟨_, (a.property.mul b.property.one_sub).one_sub⟩
  himp_eq a b := Subtype.ext <| by simp_rw [(· ⊔ ·), SemilatticeSup.sup,
    add_comm b.val, add_sub_assoc, mul_sub, mul_one, sub_sub_cancel, sub_add, mul_comm]

/-- In a commutative ring, the idempotents are in 1-1 correspondence with pairs of elements
whose product is 0 and whose sum is 1. The correspondence is given by `a ↔ (a, 1 - a)`. -/
def OrderIso.isIdempotentElemMulZeroAddOne :
    {a : R // IsIdempotentElem a} ≃o {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  toFun a := ⟨(a, 1 - a), by simp_rw [mul_sub, mul_one, a.property.eq, sub_self],
    by rw [add_sub_cancel]⟩
  invFun a := ⟨a.val.1, (IsIdempotentElem.of_mul_add a.property.1 a.property.2).1⟩
  right_inv a := Subtype.ext <| Prod.ext rfl <| sub_eq_of_eq_add <|
    a.property.2.symm.trans (add_comm ..)
  map_rel_iff' := Iff.rfl

end CommRing
