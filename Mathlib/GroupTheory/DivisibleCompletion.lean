/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.GroupTheory.Divisible
import Mathlib.Tactic.Ring.RingNF


/-!

# Rootable and divisible completion of torsion free commutative monoid

In this file, we show that a torsion free `CommMonoid` / `AddCommMonoid` `M`
can be embedded in a `RootableBy ℕ` / `DivisibleBy ℕ` monoid, namely the
`RootableCompletion` / `DivisibleCompletion` monoid. Further more, if `M` is linearly ordered,
this embedding preserves the order.

## Main definition
* `RootableCompletion` / `DivisibleCompletion`: A `RootableBy ℕ` / `DivisibleBy ℕ`
  monoid made from quotient of `(M, ℕ+)`.
* `RootableCompletion.monoidHom` / `DivisibleCompletion.monoidHom`:
  the canonical `M →* RootableCompletion M` / `M →+ DivisibleCompletion M` for monoid `M`.
* `RootableCompletion.orderMonoidHom` / `DivisibleCompletion.orderMonoidHom`:
  the canonical `M →*o RootableCompletion M` / `M →+o DivisibleCompletion M` for ordered monoid `M`.

## Main results
* `RootableCompletion.instRootableBy` / `DivisibleCompletion.instDivisibleBy`:
  the rootable / divisible completion is rootable / divisible by ℕ.
-/

/-- `M × ℕ+` represents elements in the `DivisibleCompletion` monoid. -/
structure PreDivisibleCompletion (M : Type*) [AddMonoid M] where
  /-- The "numerator" of the element. -/
  num : M
  /-- The "denominator" of the element. -/
  den : ℕ+

/-- `M × ℕ+` represents elements in the `RootableCompletion` monoid. -/
@[to_additive existing]
structure PreRootableCompletion (M : Type*) [Monoid M] where
  /-- The "numerator" of the element. -/
  num : M
  /-- The "denominator" of the element. -/
  den : ℕ+

/-- `a * b` is defined as `(a.num ^ b.den * b.num ^ a.den, a,den * b.den)`. -/
@[to_additive "`a + b` is defined as `(b.den • a.num + a.den • b.num, a,den * b.den)`."]
def PreRootableCompletion.mul {M : Type*} [Monoid M] (a b : PreRootableCompletion M) :
    PreRootableCompletion M where
  num := a.num ^ (b.den : ℕ) * b.num ^ (a.den : ℕ)
  den := a.den * b.den

/-- `a` and `b` are equivalent if `a.num ^ b.den = b.num ^ a.den`. -/
@[to_additive "`a` and `b` are equivalent if `b.den • a.num = a.ben • b.num`."]
def PreRootableCompletion.setoid (M : Type*) [Monoid M] [IsMulTorsionFree M] :
    Setoid (PreRootableCompletion M) where
  r (a b) := a.num ^ (b.den : ℕ) = b.num ^ (a.den : ℕ)
  iseqv := {
    refl (x) := by rfl
    symm {x y} (h) := h.symm
    trans {x y z} (hxy) (hyz) := by
      apply_fun (· ^ (z.den : ℕ)) at hxy
      apply_fun (· ^ (x.den : ℕ)) at hyz
      rw [← pow_mul, mul_comm, pow_mul] at hxy
      rw [← pow_mul, ← pow_mul, mul_comm (z.den : ℕ), mul_comm (y.den : ℕ), pow_mul, pow_mul] at hyz
      exact (pow_left_inj (by simp)).mp (hxy.trans hyz)
  }

/-- The rootable completion is a quotient by the equivelance on `M × ℕ+`. -/
@[to_additive "The divisible completion is a quotient by the equivelance on `M × ℕ+`"]
def RootableCompletion (M : Type*) [Monoid M] [IsMulTorsionFree M] :=
    Quotient (PreRootableCompletion.setoid M)

namespace RootableCompletion

section Monoid

variable {M : Type*} [Monoid M] [IsMulTorsionFree M]

/-- Create an element from `M` and `ℕ+`. -/
@[to_additive "Create an element from `M` and `ℕ+`."]
abbrev mk (num : M) (den : ℕ+) : RootableCompletion M :=
  Quotient.mk (PreRootableCompletion.setoid M) ⟨num, den⟩

@[to_additive]
theorem eq {n1 n2 : M} {d1 d2 : ℕ+} : mk n1 d1 = mk n2 d2 ↔ n1 ^ (d2 : ℕ) = n2 ^ (d1 : ℕ) := by
  rw [Quotient.eq]
  rfl

@[to_additive]
theorem out_eq (a : RootableCompletion M) : mk (a.out.num) (a.out.den) = a := Quotient.out_eq _

/-- An induction principle for `DivisibleCompletion`. -/
@[to_additive (attr := elab_as_elim) "An induction principle for `RootableCompletion`"]
theorem ind {motive : RootableCompletion M → Prop} (mk : ∀ num den, motive (.mk num den)) :
    ∀ x, motive x := by
  apply Quotient.ind
  intro a
  apply mk

variable {M : Type*} [CommMonoid M] [IsMulTorsionFree M]

@[to_additive]
instance instMul : Mul (RootableCompletion M) where
  mul := Quotient.lift₂ (⟦·.mul ·⟧) (by
    intro a b a' b' ha hb
    apply eq.mpr
    simp only [PNat.mul_coe]
    rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← mul_assoc]
    rw [mul_comm (b.den : ℕ) (a'.den : ℕ), mul_right_comm (a.den : ℕ) (a'.den : ℕ)]
    rw [mul_comm (a.den : ℕ) (b'.den : ℕ), mul_assoc, mul_assoc]
    rw [pow_mul a.num, pow_mul b.num, ha, hb, ← pow_mul, ← pow_mul]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    ring_nf
  )

@[to_additive]
theorem mul_mk (n1 n2 : M) (d1 d2 : ℕ+) :
    mk n1 d1 * mk n2 d2 = mk (n1 ^ (d2 : ℕ) * n2 ^ (d1 : ℕ)) (d1 * d2) := by
  rfl

variable (M) in
@[to_additive]
instance instOne : One (RootableCompletion M) where
  one := mk 1 1

variable (M) in
@[to_additive]
theorem one_eq : (1 : RootableCompletion M) = mk 1 1 := by rfl

variable (M) in
@[to_additive]
noncomputable
instance instCommMonoid : CommMonoid (RootableCompletion M) where
  mul_assoc (a b c) := by
    rw [← out_eq a, ← out_eq b, ← out_eq c, mul_mk]
    apply eq.mpr
    rw [PreRootableCompletion.mul]
    simp only [PNat.mul_coe]
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
      ← pow_mul, ← pow_mul]
    rw [← mul_assoc (a.out.num ^ _) (b.out.num ^ _)]
    ring_nf
  one_mul (a) := by
    rw [← out_eq a, one_eq, mul_mk]
    simp
  mul_one (a) := by
    rw [← out_eq a, one_eq, mul_mk]
    simp
  mul_comm (a b) := by
    rw [← out_eq a, ← out_eq b, mul_mk]
    apply eq.mpr
    simp only [PNat.mul_coe]
    congr 1
    · rw [mul_comm]
    · rw [mul_comm]
  npow (n) (a) := mk (a.out.num ^ n) a.out.den
  npow_zero (a) := by
    apply eq.mpr
    simp
  npow_succ (n) (a) := by
    rw [← out_eq a, mul_mk]
    apply eq.mpr
    rw [← (Quotient.mk_out (s := PreRootableCompletion.setoid M) a.out)]
    simp only [PNat.mul_coe]
    rw [← mul_pow, ← mul_comm, pow_mul, pow_succ]

@[to_additive]
theorem pow_mk (n : M) (d : ℕ+) (m : ℕ) : (mk n d) ^ m = (mk (n ^ m) d) := by
  apply eq.mpr
  rw [← pow_mul, ← pow_mul, mul_comm m, mul_comm m, pow_mul, pow_mul]
  congr 1
  apply eq.mp
  rw [out_eq]

variable (M) in
@[to_additive]
noncomputable
instance instRootableBy : RootableBy (RootableCompletion M) ℕ where
  root (a : RootableCompletion M) (n : ℕ) :=
    if h : n = 0 then
      1
    else
      mk a.out.num (a.out.den * ⟨n, Nat.zero_lt_of_ne_zero h⟩)
  root_zero (a) := by simp
  root_cancel {n} (a) (h) := by
    simp only [h, ↓reduceDIte]
    rw [← out_eq a, pow_mk]
    apply eq.mpr
    simp only [PNat.mul_coe, PNat.mk_coe]
    rw [← pow_mul, mul_comm, pow_mul, pow_mul, out_eq]

variable (M) in
@[to_additive]
instance : IsMulTorsionFree (RootableCompletion M) where
  pow_left_injective {n} hn := by
    intro a b hab
    induction a using ind with | mk anum aden
    induction b using ind with | mk bnum bden
    simp_rw [pow_mk] at hab
    rw [eq] at ⊢ hab
    simp_rw [pow_right_comm _ n] at hab
    exact (pow_left_inj hn).mp hab

variable (M) in
/-- The canonical `MonoidHom` maps `a` to `(a, 1)`. -/
@[to_additive "The canonical `AddMonoidHom` maps `a` to `(a, 1)`."]
noncomputable
def monoidHom : M →* RootableCompletion M where
  toFun := (mk · 1)
  map_one' := by rw [one_eq]
  map_mul' (a b) := by
    rw [mul_mk]
    simp

variable (M) in
@[to_additive]
theorem monoidHom_injective : Function.Injective (monoidHom M) := by
  intro a b hab
  simpa using eq.mp hab

@[to_additive]
theorem monoidHom_apply (a : M) : (monoidHom M) a = mk a 1 := by rfl

end Monoid

section Group

@[to_additive]
noncomputable
instance instCommGroup (M : Type*) [CommGroup M] [IsMulTorsionFree M] :
    CommGroup (RootableCompletion M) where
  inv (a) := mk (a.out.num⁻¹) a.out.den
  inv_mul_cancel (a) := by
    rw [← out_eq a, mul_mk, inv_pow]
    apply eq.mpr
    simp only [PNat.val_ofNat, pow_one, PNat.mul_coe, one_pow]
    exact inv_mul_eq_one.mpr <| Quotient.mk_out (s := PreRootableCompletion.setoid M) a.out


@[to_additive]
theorem inv_mk {M : Type*} [CommGroup M] [IsMulTorsionFree M] (n : M) (d : ℕ+) :
    (mk n d)⁻¹ = mk n⁻¹ d := by
  apply eq.mpr
  rw [inv_pow, inv_pow]
  congr 1
  apply eq.mp
  rw [out_eq]

end Group

section Order

variable {M : Type*} [CommMonoid M] [IsMulTorsionFree M]

variable (M) in
@[to_additive]
instance instLE [LE M] : LE (RootableCompletion M) where
  le (a b : RootableCompletion M) := a.out.num ^ (b.out.den : ℕ) ≤ b.out.num ^ (a.out.den : ℕ)

@[to_additive]
theorem le_def [LE M] (a b : RootableCompletion M) :
    a ≤ b ↔ a.out.num ^ (b.out.den : ℕ) ≤ b.out.num ^ (a.out.den : ℕ) := by rfl

@[to_additive]
theorem le_iff [LinearOrder M] [MulLeftStrictMono M]
    (n1 n2 : M) (d1 d2 : ℕ+) : mk n1 d1 ≤ mk n2 d2 ↔ n1 ^ (d2 : ℕ) ≤ n2 ^ (d1 : ℕ) := by
  rw [le_def]
  set n1' := (mk n1 d1).out.num
  set d1' := (mk n1 d1).out.den
  set n2' := (mk n2 d2).out.num
  set d2' := (mk n2 d2).out.den
  rw [← (pow_left_strictMono (by simp : (d1 * d2 : ℕ) ≠ 0)).le_iff_le]
  nth_rw 2 [← (pow_left_strictMono (by simp : (d1' * d2' : ℕ) ≠ 0)).le_iff_le]
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
  rw [(by ring : (d2' * (d1 * d2) : ℕ) = (d1 * (d2 * d2') : ℕ))]
  rw [(by ring : (d1' * (d1 * d2) : ℕ) = (d2 * (d1 * d1') : ℕ))]
  rw [(by ring : (d2 * (d1' * d2') : ℕ) = (d1' * (d2 * d2') : ℕ))]
  rw [(by ring : (d1 * (d1' * d2') : ℕ) = (d2' * (d1 * d1') : ℕ))]
  rw [pow_mul n1', pow_mul n2', pow_mul n1, pow_mul n2]
  rw [eq.mp (out_eq (mk n1 d1)), eq.mp (out_eq (mk n2 d2))]

@[to_additive]
theorem le_iff_left [LinearOrder M] [MulLeftStrictMono M] (n1 n2 : M) (d : ℕ+) :
    mk n1 d ≤ mk n2 d ↔ n1 ≤ n2 := by
  rw [le_iff]
  exact (pow_left_strictMono (by simp)).le_iff_le

variable (M) in
@[to_additive]
noncomputable
instance instLinearOrder [LinearOrder M] [MulLeftStrictMono M] :
    LinearOrder (RootableCompletion M) where
  lt (a b : RootableCompletion M) := a ≤ b ∧ ¬b ≤ a
  le_refl (a : RootableCompletion M) := by rw [le_def]
  le_trans (a b c : RootableCompletion M) (hab) (hbc) := by
    rw [le_def] at ⊢ hab hbc
    have : MulLeftMono M := mulLeftMono_of_mulLeftStrictMono M
    obtain hab' := pow_le_pow_left' hab c.out.den
    obtain hbc' := pow_le_pow_left' hbc a.out.den
    rw [← pow_mul, ← pow_mul] at hab'
    nth_rw 1 [mul_comm] at hab'
    nth_rw 2 [mul_comm] at hab'
    rw [pow_mul, pow_mul] at hab'
    nth_rw 2 [← pow_mul] at hbc'
    rw [mul_comm, pow_mul] at hbc'
    exact le_of_pow_le_pow_left' (by simp) (hab'.trans hbc')
  lt_iff_le_not_ge (a b : RootableCompletion M) := by rfl
  le_antisymm (a b : RootableCompletion M) (hab) (hba) := by
    rw [le_def] at hab hba
    rw [← out_eq a, ← out_eq b]
    exact eq.mpr (le_antisymm hab hba)
  le_total (a b : RootableCompletion M) := by
    rw [le_def, le_def]
    exact le_total _ _
  toDecidableLE := Classical.decRel LE.le

@[to_additive]
theorem min_left [LinearOrder M] [MulLeftStrictMono M] (n1 n2 : M) (d : ℕ+) :
    min (mk n1 d) (mk n2 d) = mk (min n1 n2) d := by
  obtain h | h := le_total n1 n2
  all_goals simpa [h] using (le_iff_left _ _ _).mpr h

@[to_additive]
theorem max_left [LinearOrder M] [MulLeftStrictMono M] (n1 n2 : M) (d : ℕ+) :
    max (mk n1 d) (mk n2 d) = mk (max n1 n2) d := by
  obtain h | h := le_total n1 n2
  all_goals simpa [h] using (le_iff_left _ _ _).mpr h

variable (M) in
@[to_additive]
noncomputable
instance instIsOrderedMonoid [LinearOrder M] [IsOrderedMonoid M] [MulLeftStrictMono M] :
    IsOrderedMonoid (RootableCompletion M) where
  mul_le_mul_left (a b) (hab) (c) := by
    rw [le_def] at hab
    rw [← out_eq a, ← out_eq b, ← out_eq c, mul_mk, mul_mk, le_iff]
    simp only [PNat.mul_coe]
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
    apply mul_le_mul' (le_of_eq (by ring_nf))
    rw [mul_comm (c.out.den : ℕ) (a.out.den : ℕ), mul_comm (c.out.den : ℕ) (b.out.den : ℕ)]
    rw [← mul_assoc, ← mul_assoc]
    rw [mul_comm (c.out.den : ℕ) (a.out.den : ℕ), mul_comm (c.out.den : ℕ) (b.out.den : ℕ)]
    rw [mul_assoc, mul_assoc, pow_mul a.out.num, pow_mul b.out.num]
    apply pow_le_pow_left' hab


variable (M) in
/-- The canonical MonoidHom is also an OrderMonoidHom. -/
@[to_additive "The canonical AddMonoidHom is also an OrderAddMonoidHom."]
noncomputable
def orderMonoidHom [LinearOrder M] [MulLeftStrictMono M] : M →*o RootableCompletion M where
  __ := monoidHom M
  monotone' {a b} (hab) := by
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
    rw [monoidHom_apply, monoidHom_apply, le_iff]
    simpa using hab

@[to_additive (attr := simp)]
theorem orderMonoidHom_apply [LinearOrder M] [MulLeftStrictMono M] (a : M) :
    (orderMonoidHom M) a = mk a 1 := by rfl

@[to_additive]
theorem orderMonoidHom_eq_monoidHom [LinearOrder M] [MulLeftStrictMono M] (a : M) :
    (orderMonoidHom M) a = (monoidHom M) a := by rfl

variable (M) in
@[to_additive]
theorem orderMonoidHom_injective [LinearOrder M] [MulLeftStrictMono M] :
    Function.Injective (orderMonoidHom M) :=
  monoidHom_injective M

end Order

section OrderGroup

variable {M : Type*} [CommGroup M] [LinearOrder M] [IsOrderedMonoid M]

@[to_additive]
theorem mabs_mk
   (n : M) (d : ℕ+) : |RootableCompletion.mk n d|ₘ = RootableCompletion.mk |n|ₘ d := by
  unfold mabs
  rw [inv_mk, max_left]

variable (M) in
/-- `OrderHom` between `MulArchimedeanClass` of `M` and of `RootableCompletion M`. -/
@[to_additive archimedeanClassOrderHom
"`OrderHom` between `ArchimedeanClass` of `M` and of `DivisibleCompletion M`."]
noncomputable
def mulArchimedeanClassOrderHom :
    MulArchimedeanClass M →o MulArchimedeanClass (RootableCompletion M) :=
  MulArchimedeanClass.orderHom (orderMonoidHom M)

variable (M) in
@[to_additive archimedeanClassOrderHom_injective]
theorem mulArchimedeanClassOrderHom_injective :
    Function.Injective (mulArchimedeanClassOrderHom M) :=
  MulArchimedeanClass.orderHom_injective (orderMonoidHom_injective M)

variable (M) in
@[to_additive archimedeanClassOrderHom_surjective]
theorem mulArchimedeanClassOrderHom_surjective :
    Function.Surjective (mulArchimedeanClassOrderHom M) := by
  intro A
  induction A using MulArchimedeanClass.ind with | mk a
  induction a using ind with | mk num den
  use MulArchimedeanClass.mk num
  suffices MulArchimedeanClass.mk (mk num 1) = MulArchimedeanClass.mk (mk num den) by
    simpa using this
  rw [MulArchimedeanClass.mk_eq_mk]
  simp_rw [mabs_mk, pow_mk, RootableCompletion.le_iff]
  refine ⟨⟨1, ?_⟩, ⟨den, by simp⟩⟩
  simpa using le_self_pow (by simp) (by simp)

variable (M) in
/-- `OrderIso` between `MulArchimedeanClass` of `M` and of `RootableCompletion M`. -/
@[to_additive archimedeanClassOrderIso
"`OrderIso` between `ArchimedeanClass` of `M` and of `DivisibleCompletion M`."]
noncomputable
def mulArchimedeanClassOrderIso :
    MulArchimedeanClass M ≃o MulArchimedeanClass (RootableCompletion M) where
  toFun := mulArchimedeanClassOrderHom M
  invFun := Function.surjInv (mulArchimedeanClassOrderHom_surjective M)
  left_inv := by
    apply Function.leftInverse_surjInv
    constructor
    · apply mulArchimedeanClassOrderHom_injective
    · apply mulArchimedeanClassOrderHom_surjective
  right_inv := Function.rightInverse_surjInv (mulArchimedeanClassOrderHom_surjective M)
  map_rel_iff' := by
    intro a b
    simp only [Equiv.coe_fn_mk]
    constructor
    · intro h
      exact ((OrderHomClass.monotone (mulArchimedeanClassOrderHom M)).strictMono_of_injective
        (mulArchimedeanClassOrderHom_injective M)).le_iff_le.mp h
    · intro h
      exact OrderHomClass.monotone _ h

variable (M) in
/-- `OrderIso` between `MulArchimedeanClass₁` of `M` and of `RootableCompletion M`. -/
@[to_additive archimedeanClass₀OrderIso
"`OrderIso` between `ArchimedeanClassₒ` of `M` and of `DivisibleCompletion M`."]
noncomputable
def mulArchimedeanClass₁OrderIso :
    MulArchimedeanClass₁ M ≃o MulArchimedeanClass₁ (RootableCompletion M) where
  __ := Equiv.subtypeEquiv (mulArchimedeanClassOrderIso M) (by simp)
  map_rel_iff' := by simp


end OrderGroup

end RootableCompletion

namespace DivisibleCompletion

noncomputable
instance (M : Type*) [AddCommGroup M] [IsAddTorsionFree M] : Module ℚ (DivisibleCompletion M) :=
    DivisibleBy.module _

instance (M : Type*) [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] :
    PosSMulStrictMono ℚ (DivisibleCompletion M) where
  elim _ ha _ _ hb := DivisibleBy.qsmul_right_strictMono (DivisibleCompletion M) ha hb

end DivisibleCompletion
