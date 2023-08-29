/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.SMulWithZero
import Mathlib.Algebra.Regular.Basic

#align_import algebra.regular.smul from "leanprover-community/mathlib"@"550b58538991c8977703fdeb7c9d51a5aa27df11"

/-!
# Action of regular elements on a module

We introduce `M`-regular elements, in the context of an `R`-module `M`.  The corresponding
predicate is called `IsSMulRegular`.

There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting on a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
SMultiplications involving `0` are, of course, all trivial.

The defining property is that an element `a ∈ R` is `M`-regular if the smultiplication map
`M → M`, defined by `m ↦ a • m`, is injective.

This property is the direct generalization to modules of the property `IsLeftRegular` defined in
`Algebra/Regular`.  Lemma `isLeftRegular_iff` shows that indeed the two notions
coincide.
-/


variable {R S : Type*} (M : Type*) {a b : R} {s : S}

/-- An `M`-regular element is an element `c` such that multiplication on the left by `c` is an
injective map `M → M`. -/
def IsSMulRegular [SMul R M] (c : R) :=
  Function.Injective ((c • ·) : M → M)
#align is_smul_regular IsSMulRegular

theorem IsLeftRegular.isSMulRegular [Mul R] {c : R} (h : IsLeftRegular c) : IsSMulRegular R c :=
  h
#align is_left_regular.is_smul_regular IsLeftRegular.isSMulRegular

/-- Left-regular multiplication on `R` is equivalent to `R`-regularity of `R` itself. -/
theorem isLeftRegular_iff [Mul R] {a : R} : IsLeftRegular a ↔ IsSMulRegular R a :=
  Iff.rfl
#align is_left_regular_iff isLeftRegular_iff

theorem IsRightRegular.isSMulRegular [Mul R] {c : R} (h : IsRightRegular c) :
    IsSMulRegular R (MulOpposite.op c) :=
  h
#align is_right_regular.is_smul_regular IsRightRegular.isSMulRegular

/-- Right-regular multiplication on `R` is equivalent to `Rᵐᵒᵖ`-regularity of `R` itself. -/
theorem isRightRegular_iff [Mul R] {a : R} :
    IsRightRegular a ↔ IsSMulRegular R (MulOpposite.op a) :=
  Iff.rfl
#align is_right_regular_iff isRightRegular_iff

namespace IsSMulRegular

variable {M}

section SMul

variable [SMul R M] [SMul R S] [SMul S M] [IsScalarTower R S M]

/-- The product of `M`-regular elements is `M`-regular. -/
theorem smul (ra : IsSMulRegular M a) (rs : IsSMulRegular M s) : IsSMulRegular M (a • s) :=
  fun _ _ ab => rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))
#align is_smul_regular.smul IsSMulRegular.smul

/-- If an element `b` becomes `M`-regular after multiplying it on the left by an `M`-regular
element, then `b` is `M`-regular. -/
theorem of_smul (a : R) (ab : IsSMulRegular M (a • s)) : IsSMulRegular M s :=
  @Function.Injective.of_comp _ _ _ (fun m : M => a • m) _ fun c d cd => by
  dsimp only [Function.comp] at cd
  -- ⊢ c = d
  rw [←smul_assoc, ←smul_assoc] at cd
  -- ⊢ c = d
  exact ab cd
  -- 🎉 no goals
#align is_smul_regular.of_smul IsSMulRegular.of_smul

/-- An element is `M`-regular if and only if multiplying it on the left by an `M`-regular element
is `M`-regular. -/
@[simp]
theorem smul_iff (b : S) (ha : IsSMulRegular M a) : IsSMulRegular M (a • b) ↔ IsSMulRegular M b :=
  ⟨of_smul _, ha.smul⟩
#align is_smul_regular.smul_iff IsSMulRegular.smul_iff

theorem isLeftRegular [Mul R] {a : R} (h : IsSMulRegular R a) : IsLeftRegular a :=
  h
#align is_smul_regular.is_left_regular IsSMulRegular.isLeftRegular

theorem isRightRegular [Mul R] {a : R} (h : IsSMulRegular R (MulOpposite.op a)) :
    IsRightRegular a :=
  h
#align is_smul_regular.is_right_regular IsSMulRegular.isRightRegular

theorem mul [Mul R] [IsScalarTower R R M] (ra : IsSMulRegular M a) (rb : IsSMulRegular M b) :
    IsSMulRegular M (a * b) :=
  ra.smul rb
#align is_smul_regular.mul IsSMulRegular.mul

theorem of_mul [Mul R] [IsScalarTower R R M] (ab : IsSMulRegular M (a * b)) :
    IsSMulRegular M b := by
  rw [← smul_eq_mul] at ab
  -- ⊢ IsSMulRegular M b
  exact ab.of_smul _
  -- 🎉 no goals
#align is_smul_regular.of_mul IsSMulRegular.of_mul

@[simp]
theorem mul_iff_right [Mul R] [IsScalarTower R R M] (ha : IsSMulRegular M a) :
    IsSMulRegular M (a * b) ↔ IsSMulRegular M b :=
  ⟨of_mul, ha.mul⟩
#align is_smul_regular.mul_iff_right IsSMulRegular.mul_iff_right

/-- Two elements `a` and `b` are `M`-regular if and only if both products `a * b` and `b * a`
are `M`-regular. -/
theorem mul_and_mul_iff [Mul R] [IsScalarTower R R M] :
    IsSMulRegular M (a * b) ∧ IsSMulRegular M (b * a) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  refine' ⟨_, _⟩
  -- ⊢ IsSMulRegular M (a * b) ∧ IsSMulRegular M (b * a) → IsSMulRegular M a ∧ IsSM …
  · rintro ⟨ab, ba⟩
    -- ⊢ IsSMulRegular M a ∧ IsSMulRegular M b
    refine' ⟨ba.of_mul, ab.of_mul⟩
    -- 🎉 no goals
  · rintro ⟨ha, hb⟩
    -- ⊢ IsSMulRegular M (a * b) ∧ IsSMulRegular M (b * a)
    exact ⟨ha.mul hb, hb.mul ha⟩
    -- 🎉 no goals
#align is_smul_regular.mul_and_mul_iff IsSMulRegular.mul_and_mul_iff

end SMul

section Monoid

variable [Monoid R] [MulAction R M]

variable (M)

/-- One is always `M`-regular. -/
@[simp]
theorem one : IsSMulRegular M (1 : R) := fun a b ab => by
  dsimp only [Function.comp] at ab
  -- ⊢ a = b
  rw [one_smul, one_smul] at ab
  -- ⊢ a = b
  assumption
  -- 🎉 no goals
#align is_smul_regular.one IsSMulRegular.one

variable {M}

/-- An element of `R` admitting a left inverse is `M`-regular. -/
theorem of_mul_eq_one (h : a * b = 1) : IsSMulRegular M b :=
  of_mul
    (by
      rw [h]
      -- ⊢ IsSMulRegular M 1
      exact one M)
      -- 🎉 no goals
#align is_smul_regular.of_mul_eq_one IsSMulRegular.of_mul_eq_one

/-- Any power of an `M`-regular element is `M`-regular. -/
theorem pow (n : ℕ) (ra : IsSMulRegular M a) : IsSMulRegular M (a ^ n) := by
  induction' n with n hn
  -- ⊢ IsSMulRegular M (a ^ Nat.zero)
  · rw [pow_zero]; simp only [one]
    -- ⊢ IsSMulRegular M 1
                   -- 🎉 no goals
  · rw [pow_succ]
    -- ⊢ IsSMulRegular M (a * a ^ n)
    exact (ra.smul_iff (a ^ n)).mpr hn
    -- 🎉 no goals
#align is_smul_regular.pow IsSMulRegular.pow

/-- An element `a` is `M`-regular if and only if a positive power of `a` is `M`-regular. -/
theorem pow_iff {n : ℕ} (n0 : 0 < n) : IsSMulRegular M (a ^ n) ↔ IsSMulRegular M a := by
  refine' ⟨_, pow n⟩
  -- ⊢ IsSMulRegular M (a ^ n) → IsSMulRegular M a
  rw [← Nat.succ_pred_eq_of_pos n0, pow_succ', ← smul_eq_mul]
  -- ⊢ IsSMulRegular M (a ^ Nat.pred n • a) → IsSMulRegular M a
  exact of_smul _
  -- 🎉 no goals
#align is_smul_regular.pow_iff IsSMulRegular.pow_iff

end Monoid

section MonoidSMul

variable [Monoid S] [SMul R M] [SMul R S] [MulAction S M] [IsScalarTower R S M]

/-- An element of `S` admitting a left inverse in `R` is `M`-regular. -/
theorem of_smul_eq_one (h : a • s = 1) : IsSMulRegular M s :=
  of_smul a
    (by
      rw [h]
      -- ⊢ IsSMulRegular M 1
      exact one M)
      -- 🎉 no goals
#align is_smul_regular.of_smul_eq_one IsSMulRegular.of_smul_eq_one

end MonoidSMul

section MonoidWithZero

variable [MonoidWithZero R] [MonoidWithZero S] [Zero M] [MulActionWithZero R M]
  [MulActionWithZero R S] [MulActionWithZero S M] [IsScalarTower R S M]

/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
protected theorem subsingleton (h : IsSMulRegular M (0 : R)) : Subsingleton M :=
  ⟨fun a b => h (by dsimp only [Function.comp]; repeat' rw [MulActionWithZero.zero_smul])⟩
                    -- ⊢ 0 • a = 0 • b
                                                -- 🎉 no goals
#align is_smul_regular.subsingleton IsSMulRegular.subsingleton

/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
theorem zero_iff_subsingleton : IsSMulRegular M (0 : R) ↔ Subsingleton M :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩
#align is_smul_regular.zero_iff_subsingleton IsSMulRegular.zero_iff_subsingleton

/-- The `0` element is not `M`-regular, on a non-trivial module. -/
theorem not_zero_iff : ¬IsSMulRegular M (0 : R) ↔ Nontrivial M := by
  rw [nontrivial_iff, not_iff_comm, zero_iff_subsingleton, subsingleton_iff]
  -- ⊢ (¬∃ x y, x ≠ y) ↔ ∀ (x y : M), x = y
  push_neg
  -- ⊢ (∀ (x y : M), x = y) ↔ ∀ (x y : M), x = y
  exact Iff.rfl
  -- 🎉 no goals
#align is_smul_regular.not_zero_iff IsSMulRegular.not_zero_iff

/-- The element `0` is `M`-regular when `M` is trivial. -/
theorem zero [sM : Subsingleton M] : IsSMulRegular M (0 : R) :=
  zero_iff_subsingleton.mpr sM
#align is_smul_regular.zero IsSMulRegular.zero

/-- The `0` element is not `M`-regular, on a non-trivial module. -/
theorem not_zero [nM : Nontrivial M] : ¬IsSMulRegular M (0 : R) :=
  not_zero_iff.mpr nM
#align is_smul_regular.not_zero IsSMulRegular.not_zero

end MonoidWithZero

section CommSemigroup

variable [CommSemigroup R] [SMul R M] [IsScalarTower R R M]

/-- A product is `M`-regular if and only if the factors are. -/
theorem mul_iff : IsSMulRegular M (a * b) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  rw [← mul_and_mul_iff]
  -- ⊢ IsSMulRegular M (a * b) ↔ IsSMulRegular M (a * b) ∧ IsSMulRegular M (b * a)
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩
  -- 🎉 no goals
#align is_smul_regular.mul_iff IsSMulRegular.mul_iff

end CommSemigroup

end IsSMulRegular

section Group

variable {G : Type*} [Group G]

/-- An element of a group acting on a Type is regular. This relies on the availability
of the inverse given by groups, since there is no `LeftCancelSMul` typeclass. -/
theorem isSMulRegular_of_group [MulAction G R] (g : G) : IsSMulRegular R g := by
  intro x y h
  -- ⊢ x = y
  convert congr_arg (g⁻¹ • ·) h using 1 <;> simp [← smul_assoc]
  -- ⊢ x = g⁻¹ • (fun x => g • x) x
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align is_smul_regular_of_group isSMulRegular_of_group

end Group

section Units

variable [Monoid R] [MulAction R M]

/-- Any element in `Rˣ` is `M`-regular. -/
theorem Units.isSMulRegular (a : Rˣ) : IsSMulRegular M (a : R) :=
  IsSMulRegular.of_mul_eq_one a.inv_val
#align units.is_smul_regular Units.isSMulRegular

/-- A unit is `M`-regular. -/
theorem IsUnit.isSMulRegular (ua : IsUnit a) : IsSMulRegular M a := by
  rcases ua with ⟨a, rfl⟩
  -- ⊢ IsSMulRegular M ↑a
  exact a.isSMulRegular M
  -- 🎉 no goals
#align is_unit.is_smul_regular IsUnit.isSMulRegular

end Units
