/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.regular.smul
! leanprover-community/mathlib commit 550b58538991c8977703fdeb7c9d51a5aa27df11
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.SmulWithZero
import Mathlib.Algebra.Regular.Basic

/-!
# Action of regular elements on a module

We introduce `M`-regular elements, in the context of an `R`-module `M`.  The corresponding
predicate is called `is_smul_regular`.

There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting an a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
Smultiplications involving `0` are, of course, all trivial.

The defining property is that an element `a ∈ R` is `M`-regular if the smultiplication map
`M → M`, defined by `m ↦ a • m`, is injective.

This property is the direct generalization to modules of the property `is_left_regular` defined in
`algebra/regular`.  Lemma `is_smul_regular.is_left_regular_iff` shows that indeed the two notions
coincide.
-/


variable {R S : Type _} (M : Type _) {a b : R} {s : S}

/-- An `M`-regular element is an element `c` such that multiplication on the left by `c` is an
injective map `M → M`. -/
def IsSmulRegular [SMul R M] (c : R) :=
  Function.Injective ((· • ·) c : M → M)
#align is_smul_regular IsSmulRegular

theorem IsLeftRegular.is_smul_regular [Mul R] {c : R} (h : IsLeftRegular c) : IsSmulRegular R c :=
  h
#align is_left_regular.is_smul_regular IsLeftRegular.is_smul_regular

/-- Left-regular multiplication on `R` is equivalent to `R`-regularity of `R` itself. -/
theorem is_left_regular_iff [Mul R] {a : R} : IsLeftRegular a ↔ IsSmulRegular R a :=
  Iff.rfl
#align is_left_regular_iff is_left_regular_iff

theorem IsRightRegular.is_smul_regular [Mul R] {c : R} (h : IsRightRegular c) :
    IsSmulRegular R (MulOpposite.op c) :=
  h
#align is_right_regular.is_smul_regular IsRightRegular.is_smul_regular

/-- Right-regular multiplication on `R` is equivalent to `Rᵐᵒᵖ`-regularity of `R` itself. -/
theorem is_right_regular_iff [Mul R] {a : R} :
    IsRightRegular a ↔ IsSmulRegular R (MulOpposite.op a) :=
  Iff.rfl
#align is_right_regular_iff is_right_regular_iff

namespace IsSmulRegular

variable {M}

section HasSmul

variable [HasSmul R M] [HasSmul R S] [HasSmul S M] [IsScalarTower R S M]

/-- The product of `M`-regular elements is `M`-regular. -/
theorem smul (ra : IsSmulRegular M a) (rs : IsSmulRegular M s) : IsSmulRegular M (a • s) :=
  fun a b ab => rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))
#align is_smul_regular.smul IsSmulRegular.smul

/-- If an element `b` becomes `M`-regular after multiplying it on the left by an `M`-regular
element, then `b` is `M`-regular. -/
theorem of_smul (a : R) (ab : IsSmulRegular M (a • s)) : IsSmulRegular M s :=
  @Function.Injective.of_comp _ _ _ (fun m : M => a • m) _ fun c d cd =>
    ab (by rwa [smul_assoc, smul_assoc])
#align is_smul_regular.of_smul IsSmulRegular.of_smul

/-- An element is `M`-regular if and only if multiplying it on the left by an `M`-regular element
is `M`-regular. -/
@[simp]
theorem smul_iff (b : S) (ha : IsSmulRegular M a) : IsSmulRegular M (a • b) ↔ IsSmulRegular M b :=
  ⟨of_smul _, ha.smul⟩
#align is_smul_regular.smul_iff IsSmulRegular.smul_iff

theorem is_left_regular [Mul R] {a : R} (h : IsSmulRegular R a) : IsLeftRegular a :=
  h
#align is_smul_regular.is_left_regular IsSmulRegular.is_left_regular

theorem is_right_regular [Mul R] {a : R} (h : IsSmulRegular R (MulOpposite.op a)) :
    IsRightRegular a :=
  h
#align is_smul_regular.is_right_regular IsSmulRegular.is_right_regular

theorem mul [Mul R] [IsScalarTower R R M] (ra : IsSmulRegular M a) (rb : IsSmulRegular M b) :
    IsSmulRegular M (a * b) :=
  ra.smul rb
#align is_smul_regular.mul IsSmulRegular.mul

theorem of_mul [Mul R] [IsScalarTower R R M] (ab : IsSmulRegular M (a * b)) : IsSmulRegular M b :=
  by
  rw [← smul_eq_mul] at ab
  exact ab.of_smul _
#align is_smul_regular.of_mul IsSmulRegular.of_mul

@[simp]
theorem mul_iff_right [Mul R] [IsScalarTower R R M] (ha : IsSmulRegular M a) :
    IsSmulRegular M (a * b) ↔ IsSmulRegular M b :=
  ⟨of_mul, ha.mul⟩
#align is_smul_regular.mul_iff_right IsSmulRegular.mul_iff_right

/-- Two elements `a` and `b` are `M`-regular if and only if both products `a * b` and `b * a`
are `M`-regular. -/
theorem mul_and_mul_iff [Mul R] [IsScalarTower R R M] :
    IsSmulRegular M (a * b) ∧ IsSmulRegular M (b * a) ↔ IsSmulRegular M a ∧ IsSmulRegular M b := by
  refine' ⟨_, _⟩
  · rintro ⟨ab, ba⟩
    refine' ⟨ba.of_mul, ab.of_mul⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩
#align is_smul_regular.mul_and_mul_iff IsSmulRegular.mul_and_mul_iff

end HasSmul

section Monoid

variable [Monoid R] [MulAction R M]

variable (M)

/-- One is `M`-regular always. -/
@[simp]
theorem one : IsSmulRegular M (1 : R) := fun a b ab => by rwa [one_smul, one_smul] at ab
#align is_smul_regular.one IsSmulRegular.one

variable {M}

/-- An element of `R` admitting a left inverse is `M`-regular. -/
theorem of_mul_eq_one (h : a * b = 1) : IsSmulRegular M b :=
  of_mul
    (by
      rw [h]
      exact one M)
#align is_smul_regular.of_mul_eq_one IsSmulRegular.of_mul_eq_one

/-- Any power of an `M`-regular element is `M`-regular. -/
theorem pow (n : ℕ) (ra : IsSmulRegular M a) : IsSmulRegular M (a ^ n) := by
  induction' n with n hn
  · simp only [one, pow_zero]
  · rw [pow_succ]
    exact (ra.smul_iff (a ^ n)).mpr hn
#align is_smul_regular.pow IsSmulRegular.pow

/-- An element `a` is `M`-regular if and only if a positive power of `a` is `M`-regular. -/
theorem pow_iff {n : ℕ} (n0 : 0 < n) : IsSmulRegular M (a ^ n) ↔ IsSmulRegular M a := by
  refine' ⟨_, pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0, pow_succ', ← smul_eq_mul]
  exact of_smul _
#align is_smul_regular.pow_iff IsSmulRegular.pow_iff

end Monoid

section MonoidSmul

variable [Monoid S] [HasSmul R M] [HasSmul R S] [MulAction S M] [IsScalarTower R S M]

/-- An element of `S` admitting a left inverse in `R` is `M`-regular. -/
theorem of_smul_eq_one (h : a • s = 1) : IsSmulRegular M s :=
  of_smul a
    (by
      rw [h]
      exact one M)
#align is_smul_regular.of_smul_eq_one IsSmulRegular.of_smul_eq_one

end MonoidSmul

section MonoidWithZero

variable [MonoidWithZero R] [MonoidWithZero S] [Zero M] [MulActionWithZero R M]
  [MulActionWithZero R S] [MulActionWithZero S M] [IsScalarTower R S M]

/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
protected theorem subsingleton (h : IsSmulRegular M (0 : R)) : Subsingleton M :=
  ⟨fun a b => h (by repeat' rw [MulActionWithZero.zero_smul])⟩
#align is_smul_regular.subsingleton IsSmulRegular.subsingleton

/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
theorem zero_iff_subsingleton : IsSmulRegular M (0 : R) ↔ Subsingleton M :=
  ⟨fun h => h.Subsingleton, fun H a b h => @Subsingleton.elim _ H a b⟩
#align is_smul_regular.zero_iff_subsingleton IsSmulRegular.zero_iff_subsingleton

/-- The `0` element is not `M`-regular, on a non-trivial module. -/
theorem not_zero_iff : ¬IsSmulRegular M (0 : R) ↔ Nontrivial M := by
  rw [nontrivial_iff, not_iff_comm, zero_iff_subsingleton, subsingleton_iff]
  push_neg
  exact Iff.rfl
#align is_smul_regular.not_zero_iff IsSmulRegular.not_zero_iff

/-- The element `0` is `M`-regular when `M` is trivial. -/
theorem zero [sM : Subsingleton M] : IsSmulRegular M (0 : R) :=
  zero_iff_subsingleton.mpr sM
#align is_smul_regular.zero IsSmulRegular.zero

/-- The `0` element is not `M`-regular, on a non-trivial module. -/
theorem not_zero [nM : Nontrivial M] : ¬IsSmulRegular M (0 : R) :=
  not_zero_iff.mpr nM
#align is_smul_regular.not_zero IsSmulRegular.not_zero

end MonoidWithZero

section CommSemigroup

variable [CommSemigroup R] [HasSmul R M] [IsScalarTower R R M]

/-- A product is `M`-regular if and only if the factors are. -/
theorem mul_iff : IsSmulRegular M (a * b) ↔ IsSmulRegular M a ∧ IsSmulRegular M b := by
  rw [← mul_and_mul_iff]
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩
#align is_smul_regular.mul_iff IsSmulRegular.mul_iff

end CommSemigroup

end IsSmulRegular

section Group

variable {G : Type _} [Group G]

/-- An element of a group acting on a Type is regular. This relies on the availability
of the inverse given by groups, since there is no `left_cancel_smul` typeclass. -/
theorem is_smul_regular_of_group [MulAction G R] (g : G) : IsSmulRegular R g := by
  intro x y h
  convert congr_arg ((· • ·) g⁻¹) h using 1 <;> simp [← smul_assoc]
#align is_smul_regular_of_group is_smul_regular_of_group

end Group

section Units

variable [Monoid R] [MulAction R M]

/-- Any element in `Rˣ` is `M`-regular. -/
theorem Units.is_smul_regular (a : Rˣ) : IsSmulRegular M (a : R) :=
  IsSmulRegular.of_mul_eq_one a.inv_val
#align units.is_smul_regular Units.is_smul_regular

/-- A unit is `M`-regular. -/
theorem IsUnit.is_smul_regular (ua : IsUnit a) : IsSmulRegular M a := by
  rcases ua with ⟨a, rfl⟩
  exact a.is_smul_regular M
#align is_unit.is_smul_regular IsUnit.is_smul_regular

end Units
