/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Hom.Defs

#align_import algebra.field.basic from "leanprover-community/mathlib"@"05101c3df9d9cfe9430edc205860c79b6d660102"

/-!
# Lemmas about division (semi)rings and (semi)fields

-/


open Function OrderDual Set

universe u

variable {α β K : Type*}

section DivisionSemiring

variable [DivisionSemiring α] {a b c d : α}

theorem add_div (a b c : α) : (a + b) / c = a / c + b / c := by simp_rw [div_eq_mul_inv, add_mul]
#align add_div add_div

@[field_simps]
theorem div_add_div_same (a b c : α) : a / c + b / c = (a + b) / c :=
  (add_div _ _ _).symm
#align div_add_div_same div_add_div_same

theorem same_add_div (h : b ≠ 0) : (b + a) / b = 1 + a / b := by rw [← div_self h, add_div]
#align same_add_div same_add_div

theorem div_add_same (h : b ≠ 0) : (a + b) / b = a / b + 1 := by rw [← div_self h, add_div]
#align div_add_same div_add_same

theorem one_add_div (h : b ≠ 0) : 1 + a / b = (b + a) / b :=
  (same_add_div h).symm
#align one_add_div one_add_div

theorem div_add_one (h : b ≠ 0) : a / b + 1 = (a + b) / b :=
  (div_add_same h).symm
#align div_add_one div_add_one

theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (a + b) * (1 / b) = 1 / a + 1 / b := by
  rw [mul_add, one_div_mul_cancel ha, add_mul, one_mul, mul_assoc, mul_one_div_cancel hb, mul_one,
    add_comm]
#align one_div_mul_add_mul_one_div_eq_one_div_add_one_div one_div_mul_add_mul_one_div_eq_one_div_add_one_div

theorem add_div_eq_mul_add_div (a b : α) (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
  (eq_div_iff_mul_eq hc).2 <| by rw [right_distrib, div_mul_cancel _ hc]
#align add_div_eq_mul_add_div add_div_eq_mul_add_div

@[field_simps]
theorem add_div' (a b c : α) (hc : c ≠ 0) : b + a / c = (b * c + a) / c := by
  rw [add_div, mul_div_cancel _ hc]
#align add_div' add_div'

@[field_simps]
theorem div_add' (a b c : α) (hc : c ≠ 0) : a / c + b = (a + b * c) / c := by
  rwa [add_comm, add_div', add_comm]
#align div_add' div_add'

protected theorem Commute.div_add_div (hbc : Commute b c) (hbd : Commute b d) (hb : b ≠ 0)
    (hd : d ≠ 0) : a / b + c / d = (a * d + b * c) / (b * d) := by
  rw [add_div, mul_div_mul_right _ b hd, hbc.eq, hbd.eq, mul_div_mul_right c d hb]
#align commute.div_add_div Commute.div_add_div

protected theorem Commute.one_div_add_one_div (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a + 1 / b = (a + b) / (a * b) := by
  rw [(Commute.one_right a).div_add_div hab ha hb, one_mul, mul_one, add_comm]
#align commute.one_div_add_one_div Commute.one_div_add_one_div

protected theorem Commute.inv_add_inv (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ + b⁻¹ = (a + b) / (a * b) := by
  rw [inv_eq_one_div, inv_eq_one_div, hab.one_div_add_one_div ha hb]
#align commute.inv_add_inv Commute.inv_add_inv

end DivisionSemiring

section DivisionMonoid

variable [DivisionMonoid K] [HasDistribNeg K] {a b : K}

theorem one_div_neg_one_eq_neg_one : (1 : K) / -1 = -1 :=
  have : -1 * -1 = (1 : K) := by rw [neg_mul_neg, one_mul]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)
#align one_div_neg_one_eq_neg_one one_div_neg_one_eq_neg_one

theorem one_div_neg_eq_neg_one_div (a : K) : 1 / -a = -(1 / a) :=
  calc
    1 / -a = 1 / (-1 * a) := by rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by rw [mul_neg, mul_one]
#align one_div_neg_eq_neg_one_div one_div_neg_eq_neg_one_div

theorem div_neg_eq_neg_div (a b : K) : b / -a = -(b / a) :=
  calc
    b / -a = b * (1 / -a) := by rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by rw [mul_one_div]
#align div_neg_eq_neg_div div_neg_eq_neg_div

theorem neg_div (a b : K) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]
#align neg_div neg_div

@[field_simps]
theorem neg_div' (a b : K) : -(b / a) = -b / a := by simp [neg_div]
#align neg_div' neg_div'

@[simp]
theorem neg_div_neg_eq (a b : K) : -a / -b = a / b := by rw [div_neg_eq_neg_div, neg_div, neg_neg]
#align neg_div_neg_eq neg_div_neg_eq

theorem neg_inv : -a⁻¹ = (-a)⁻¹ := by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]
#align neg_inv neg_inv

theorem div_neg (a : K) : a / -b = -(a / b) := by rw [← div_neg_eq_neg_div]
#align div_neg div_neg

theorem inv_neg : (-a)⁻¹ = -a⁻¹ := by rw [neg_inv]
#align inv_neg inv_neg

theorem inv_neg_one : (-1 : K)⁻¹ = -1 := by rw [← neg_inv, inv_one]

end DivisionMonoid

section DivisionRing

variable [DivisionRing K] {a b c d : K}

@[simp]
theorem div_neg_self {a : K} (h : a ≠ 0) : a / -a = -1 := by rw [div_neg_eq_neg_div, div_self h]
#align div_neg_self div_neg_self

@[simp]
theorem neg_div_self {a : K} (h : a ≠ 0) : -a / a = -1 := by rw [neg_div, div_self h]
#align neg_div_self neg_div_self

theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by
  rw [sub_eq_add_neg, ← neg_div, div_add_div_same, sub_eq_add_neg]
#align div_sub_div_same div_sub_div_same

theorem same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm
#align same_sub_div same_sub_div

theorem one_sub_div {a b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b :=
  (same_sub_div h).symm
#align one_sub_div one_sub_div

theorem div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm
#align div_sub_same div_sub_same

theorem div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b :=
  (div_sub_same h).symm
#align div_sub_one div_sub_one

theorem sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
  (div_sub_div_same _ _ _).symm
#align sub_div sub_div

/-- See `inv_sub_inv` for the more convenient version when `K` is commutative. -/
theorem inv_sub_inv' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹ := by
  rw [mul_sub, sub_mul, mul_inv_cancel_right₀ hb, inv_mul_cancel ha, one_mul]
#align inv_sub_inv' inv_sub_inv'

theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (b - a) * (1 / b) = 1 / a - 1 / b := by
  rw [mul_sub_left_distrib (1 / a), one_div_mul_cancel ha, mul_sub_right_distrib, one_mul,
    mul_assoc, mul_one_div_cancel hb, mul_one]
#align one_div_mul_sub_mul_one_div_eq_one_div_add_one_div one_div_mul_sub_mul_one_div_eq_one_div_add_one_div

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.isDomain : IsDomain K :=
  NoZeroDivisors.to_isDomain _
#align division_ring.is_domain DivisionRing.isDomain

protected theorem Commute.div_sub_div (hbc : Commute b c) (hbd : Commute b d) (hb : b ≠ 0)
    (hd : d ≠ 0) : a / b - c / d = (a * d - b * c) / (b * d) := by
  simpa only [mul_neg, neg_div, ← sub_eq_add_neg] using hbc.neg_right.div_add_div hbd hb hd
#align commute.div_sub_div Commute.div_sub_div

protected theorem Commute.inv_sub_inv (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  simp only [inv_eq_one_div, (Commute.one_right a).div_sub_div hab ha hb, one_mul, mul_one]
#align commute.inv_sub_inv Commute.inv_sub_inv

end DivisionRing

section Semifield

variable [Semifield α] {a b c d : α}

theorem div_add_div (a : α) (c : α) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + b * c) / (b * d) :=
  (Commute.all b _).div_add_div (Commute.all _ _) hb hd
#align div_add_div div_add_div

theorem one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
  (Commute.all a _).one_div_add_one_div ha hb
#align one_div_add_one_div one_div_add_one_div

theorem inv_add_inv (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) :=
  (Commute.all a _).inv_add_inv ha hb
#align inv_add_inv inv_add_inv

end Semifield

section Field

variable [Field K]

attribute [local simp] mul_assoc mul_comm mul_left_comm

@[field_simps]
theorem div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - b * c) / (b * d) :=
  (Commute.all b _).div_sub_div (Commute.all _ _) hb hd
#align div_sub_div div_sub_div

theorem inv_sub_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mul, mul_one]
#align inv_sub_inv inv_sub_inv

@[field_simps]
theorem sub_div' (a b c : K) (hc : c ≠ 0) : b - a / c = (b * c - a) / c := by
  simpa using div_sub_div b a one_ne_zero hc
#align sub_div' sub_div'

@[field_simps]
theorem div_sub' (a b c : K) (hc : c ≠ 0) : a / c - b = (a - c * b) / c := by
  simpa using div_sub_div a b hc one_ne_zero
#align div_sub' div_sub'

-- see Note [lower instance priority]
instance (priority := 100) Field.isDomain : IsDomain K :=
  { DivisionRing.isDomain with }
#align field.is_domain Field.isDomain

end Field

namespace RingHom

protected theorem injective [DivisionRing α] [Semiring β] [Nontrivial β] (f : α →+* β) :
    Injective f :=
  (injective_iff_map_eq_zero f).2 fun _ ↦ (map_eq_zero f).1
#align ring_hom.injective RingHom.injective

end RingHom

section NoncomputableDefs

variable {R : Type*} [Nontrivial R]

/-- Constructs a `DivisionRing` structure on a `Ring` consisting only of units and 0. -/
noncomputable def divisionRingOfIsUnitOrEqZero [hR : Ring R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    DivisionRing R :=
  { groupWithZeroOfIsUnitOrEqZero h, hR with }
#align division_ring_of_is_unit_or_eq_zero divisionRingOfIsUnitOrEqZero

/-- Constructs a `Field` structure on a `CommRing` consisting only of units and 0.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def fieldOfIsUnitOrEqZero [hR : CommRing R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    Field R :=
  { groupWithZeroOfIsUnitOrEqZero h, hR with }
#align field_of_is_unit_or_eq_zero fieldOfIsUnitOrEqZero

end NoncomputableDefs

-- See note [reducible non-instances]
/-- Pullback a `DivisionSemiring` along an injective function. -/
@[reducible]
protected def Function.Injective.divisionSemiring [DivisionSemiring β] [Zero α] [Mul α] [Add α]
    [One α] [Inv α] [Div α] [SMul ℕ α] [Pow α ℕ] [Pow α ℤ] [NatCast α] (f : α → β)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : DivisionSemiring α :=
  { hf.groupWithZero f zero one mul inv div npow zpow,
    hf.semiring f zero one add mul nsmul npow nat_cast with }
#align function.injective.division_semiring Function.Injective.divisionSemiring

/-- Pullback a `DivisionSemiring` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.divisionRing [DivisionRing K] {K'} [Zero K'] [One K'] [Add K']
    [Mul K'] [Neg K'] [Sub K'] [Inv K'] [Div K'] [SMul ℕ K'] [SMul ℤ K'] [SMul ℚ K']
    [Pow K' ℕ] [Pow K' ℤ] [NatCast K'] [IntCast K'] [RatCast K'] (f : K' → K) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (qsmul : ∀ (x) (n : ℚ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (rat_cast : ∀ n : ℚ, f n = n) :
    DivisionRing K' :=
  { hf.groupWithZero f zero one mul inv div npow zpow,
    hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with
    ratCast := Rat.cast,
    ratCast_mk := fun a b h1 h2 ↦
      hf
        (by
          erw [rat_cast, mul, inv, int_cast, nat_cast]
          exact DivisionRing.ratCast_mk a b h1 h2),
    qsmul := (· • ·), qsmul_eq_mul' := fun a x ↦ hf (by erw [qsmul, mul, Rat.smul_def, rat_cast]) }
#align function.injective.division_ring Function.Injective.divisionRing

-- See note [reducible non-instances]
/-- Pullback a `Field` along an injective function. -/
@[reducible]
protected def Function.Injective.semifield [Semifield β] [Zero α] [Mul α] [Add α] [One α] [Inv α]
    [Div α] [SMul ℕ α] [Pow α ℕ] [Pow α ℤ] [NatCast α] (f : α → β) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semifield α :=
  { hf.commGroupWithZero f zero one mul inv div npow zpow,
    hf.commSemiring f zero one add mul nsmul npow nat_cast with }
#align function.injective.semifield Function.Injective.semifield

/-- Pullback a `Field` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.field [Field K] {K'} [Zero K'] [Mul K'] [Add K'] [Neg K'] [Sub K']
    [One K'] [Inv K'] [Div K'] [SMul ℕ K'] [SMul ℤ K'] [SMul ℚ K'] [Pow K' ℕ] [Pow K' ℤ]
    [NatCast K'] [IntCast K'] [RatCast K'] (f : K' → K) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (qsmul : ∀ (x) (n : ℚ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (rat_cast : ∀ n : ℚ, f n = n) :
    Field K' :=
  { hf.commGroupWithZero f zero one mul inv div npow zpow,
    hf.commRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with
    ratCast := Rat.cast,
    ratCast_mk := fun a b h1 h2 ↦
      hf
        (by
          erw [rat_cast, mul, inv, int_cast, nat_cast]
          exact DivisionRing.ratCast_mk a b h1 h2),
    qsmul := (· • ·), qsmul_eq_mul' := fun a x ↦ hf (by erw [qsmul, mul, Rat.smul_def, rat_cast]) }
#align function.injective.field Function.Injective.field

/-! ### Order dual -/


instance [h : RatCast α] : RatCast αᵒᵈ :=
  h

instance [h : DivisionSemiring α] : DivisionSemiring αᵒᵈ :=
  h

instance [h : DivisionRing α] : DivisionRing αᵒᵈ :=
  h

instance [h : Semifield α] : Semifield αᵒᵈ :=
  h

instance [h : Field α] : Field αᵒᵈ :=
  h

@[simp]
theorem toDual_rat_cast [RatCast α] (n : ℚ) : toDual (n : α) = n :=
  rfl
#align to_dual_rat_cast toDual_rat_cast

@[simp]
theorem ofDual_rat_cast [RatCast α] (n : ℚ) : (ofDual n : α) = n :=
  rfl
#align of_dual_rat_cast ofDual_rat_cast

/-! ### Lexicographic order -/

instance [h : RatCast α] : RatCast (Lex α) :=
  h

instance [h : DivisionSemiring α] : DivisionSemiring (Lex α) :=
  h

instance [h : DivisionRing α] : DivisionRing (Lex α) :=
  h

instance [h : Semifield α] : Semifield (Lex α) :=
  h

instance [h : Field α] : Field (Lex α) :=
  h

@[simp]
theorem toLex_rat_cast [RatCast α] (n : ℚ) : toLex (n : α) = n :=
  rfl
#align to_lex_rat_cast toLex_rat_cast

@[simp]
theorem ofLex_rat_cast [RatCast α] (n : ℚ) : (ofLex n : α) = n :=
  rfl
#align of_lex_rat_cast ofLex_rat_cast
