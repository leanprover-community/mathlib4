/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Push

/-!
# Action of regular elements on a module

We introduce `M`-regular elements, in the context of an `R`-module `M`.  The corresponding
predicate is called `IsSMulRegular`.

There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting on a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
Scalar multiplications involving `0` are, of course, all trivial.

The defining property is that an element `a ∈ R` is `M`-regular if the scalar multiplication map
`M → M`, defined by `m ↦ a • m`, is injective.

This property is the direct generalization to modules of the property `IsLeftRegular` defined in
`Algebra/Regular`.  Lemma `isLeftRegular_iff` shows that indeed the two notions
coincide.
-/

@[expose] public section

assert_not_exists GroupWithZero

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

/-- An `M`-regular element is an element `c` such that multiplication on the left by `c` is an
injective map `M → M`. -/
@[to_additive
  /-- An `M`-regular element is an element `c` such that left vector addition by `c` is an
  injective map `M → M`. -/]
def IsSMulRegular [SMul R M] (c : R) :=
  Function.Injective ((c • ·) : M → M)

@[to_additive]
theorem IsLeftRegular.isSMulRegular [Mul R] {c : R} (h : IsLeftRegular c) : IsSMulRegular R c :=
  h

/-- Left-regular multiplication on `R` is equivalent to `R`-regularity of `R` itself. -/
@[to_additive
  /-- Left-regular addition on `R` is equivalent to `R`-regularity of `R` itself. -/]
theorem isLeftRegular_iff [Mul R] {a : R} : IsLeftRegular a ↔ IsSMulRegular R a :=
  Iff.rfl

@[to_additive]
theorem IsRightRegular.isSMulRegular [Mul R] {c : R} (h : IsRightRegular c) :
    IsSMulRegular R (MulOpposite.op c) :=
  h

/-- Right-regular multiplication on `R` is equivalent to `Rᵐᵒᵖ`-regularity of `R` itself. -/
@[to_additive
  /-- Right-regular addition on `R` is equivalent to `Rᵃᵒᵖ`-regularity of `R` itself. -/]
theorem isRightRegular_iff [Mul R] {a : R} :
    IsRightRegular a ↔ IsSMulRegular R (MulOpposite.op a) :=
  Iff.rfl

variable {M}

@[to_additive]
lemma isSMulRegular_map [SMul R M] [SMul S M] (f : R → S) (smul : ∀ m : M, f a • m = a • m) :
    IsSMulRegular M (f a) ↔ IsSMulRegular M a := by simp [IsSMulRegular, smul]

@[to_additive]
protected alias ⟨IsSMulRegular.of_map, IsSMulRegular.map⟩ := isSMulRegular_map

theorem isAddTorsionFree_iff' [AddMonoid M] : IsAddTorsionFree M ↔ ∀ n ≠ 0, IsSMulRegular M n :=
  isAddTorsionFree_iff M

namespace IsSMulRegular

theorem nat_of_isAddTorsionFree [AddMonoid M] [IsAddTorsionFree M] {n : ℕ} (h : n ≠ 0) :
    IsSMulRegular M n :=
  isAddTorsionFree_iff'.mp ‹_› n h

@[simp] theorem natAbs_iff [SubtractionMonoid M] {n : ℤ} :
    IsSMulRegular M n.natAbs ↔ IsSMulRegular M n := by
  simp_rw [IsSMulRegular, Function.Injective]
  conv_rhs => rw [← n.sign_mul_natAbs]
  obtain h | h | h := n.sign_trichotomy
  · simp [h]
  · simp [Int.sign_eq_zero_iff_zero.mp h]
  · simp [h, neg_zsmul]

section SMul

variable [SMul R M] [SMul R S] [SMul S M] [IsScalarTower R S M]

/-- The product of `M`-regular elements is `M`-regular. -/
@[to_additive
  /-- The sum of `M`-regular elements is `M`-regular. -/]
theorem smul (ra : IsSMulRegular M a) (rs : IsSMulRegular M s) : IsSMulRegular M (a • s) :=
  fun _ _ ab => rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))

/-- If an element `b` becomes `M`-regular after multiplying it on the left by an `M`-regular
element, then `b` is `M`-regular. -/
@[to_additive
  /-- If an element `b` becomes `M`-regular after left vector addition by an `M`-regular
  element, then `b` is `M`-regular. -/]
theorem of_smul (a : R) (ab : IsSMulRegular M (a • s)) : IsSMulRegular M s :=
  @Function.Injective.of_comp _ _ _ (fun m : M => a • m) _ fun c d cd => by
  dsimp only [Function.comp_def] at cd
  rw [← smul_assoc, ← smul_assoc] at cd
  exact ab cd

/-- An element is `M`-regular if and only if multiplying it on the left by an `M`-regular element
is `M`-regular. -/
@[to_additive (attr := simp)
  /-- An element is `M`-regular if and only if left vector addition by an `M`-regular element
  is `M`-regular. -/]
theorem smul_iff (b : S) (ha : IsSMulRegular M a) : IsSMulRegular M (a • b) ↔ IsSMulRegular M b :=
  ⟨of_smul _, ha.smul⟩

@[to_additive]
theorem isLeftRegular [Mul R] {a : R} (h : IsSMulRegular R a) : IsLeftRegular a :=
  h

@[to_additive]
theorem isRightRegular [Mul R] {a : R} (h : IsSMulRegular R (MulOpposite.op a)) :
    IsRightRegular a :=
  h

@[to_additive]
theorem mul [Mul R] [IsScalarTower R R M] (ra : IsSMulRegular M a) (rb : IsSMulRegular M b) :
    IsSMulRegular M (a * b) :=
  ra.smul rb

@[to_additive]
theorem of_mul [Mul R] [IsScalarTower R R M] (ab : IsSMulRegular M (a * b)) :
    IsSMulRegular M b := by
  rw [← smul_eq_mul] at ab
  exact ab.of_smul _

@[to_additive (attr := simp)]
theorem mul_iff_right [Mul R] [IsScalarTower R R M] (ha : IsSMulRegular M a) :
    IsSMulRegular M (a * b) ↔ IsSMulRegular M b :=
  ⟨of_mul, ha.mul⟩

/-- Two elements `a` and `b` are `M`-regular if and only if both products `a * b` and `b * a`
are `M`-regular. -/
@[to_additive
  /-- Two elements `a` and `b` are `M`-regular if and only if both sums `a + b` and `b + a`
  are `M`-regular. -/]
theorem mul_and_mul_iff [Mul R] [IsScalarTower R R M] :
    IsSMulRegular M (a * b) ∧ IsSMulRegular M (b * a) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, ba⟩
    exact ⟨ba.of_mul, ab.of_mul⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩

end SMul

section Monoid

variable [Monoid R] [MulAction R M]
variable (M)

/-- One is always `M`-regular. -/
@[to_additive (attr := simp)
  /-- Zero is always `M`-regular. -/]
theorem one : IsSMulRegular M (1 : R) := fun a b ab => by
  dsimp only [Function.comp_def] at ab
  rwa [one_smul, one_smul] at ab

variable {M}

/-- An element of `R` admitting a left inverse is `M`-regular. -/
@[to_additive
  /-- An element of `R` admitting a left negative is `M`-regular. -/]
theorem of_mul_eq_one (h : a * b = 1) : IsSMulRegular M b :=
  of_mul (a := a) (by rw [h]; exact one M)

/-- Any power of an `M`-regular element is `M`-regular. -/
@[to_additive
  /-- Any multiple of an `M`-regular element is `M`-regular. -/]
theorem pow (n : ℕ) (ra : IsSMulRegular M a) : IsSMulRegular M (a ^ n) := by
  induction n with
  | zero => rw [pow_zero]; simp only [one]
  | succ n hn =>
    rw [pow_succ']
    exact (ra.smul_iff (a ^ n)).mpr hn

/-- An element `a` is `M`-regular if and only if a positive power of `a` is `M`-regular. -/
@[to_additive
  /-- An element `a` is `M`-regular if and only if a positive multiple of `a` is `M`-regular. -/]
theorem pow_iff {n : ℕ} (n0 : 0 < n) : IsSMulRegular M (a ^ n) ↔ IsSMulRegular M a := by
  refine ⟨?_, pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0, pow_succ, ← smul_eq_mul]
  exact of_smul _

end Monoid

section MonoidSMul

variable [Monoid S] [SMul R M] [SMul R S] [MulAction S M] [IsScalarTower R S M]

/-- An element of `S` admitting a left inverse in `R` is `M`-regular. -/
@[to_additive
  /-- An element of `S` admitting a left negative in `R` is `M`-regular. -/]
theorem of_smul_eq_one (h : a • s = 1) : IsSMulRegular M s :=
  of_smul a
    (by
      rw [h]
      exact one M)

end MonoidSMul

section CommSemigroup

variable [CommMagma R] [SMul R M] [IsScalarTower R R M]

/-- A product is `M`-regular if and only if the factors are. -/
@[to_additive
  /-- A sum is `M`-regular if and only if the summands are. -/]
theorem mul_iff : IsSMulRegular M (a * b) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  rw [← mul_and_mul_iff]
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

end CommSemigroup

end IsSMulRegular

/-- If scalar multiplication is left cancellative, every element is regular. -/
@[to_additive
  /-- If left vector addition is cancellative, every element is regular. -/]
theorem IsSMulRegular.all [SMul R M] [IsLeftCancelSMul R M] (a : R) :
    IsSMulRegular M a := fun _ _ ↦ IsLeftCancelSMul.left_cancel a _ _

section Group

variable {G : Type*} [Group G]

/-- An element of a group acting on a type is regular. -/
@[deprecated IsSMulRegular.all (since := "2026-09-08")]
theorem isSMulRegular_of_group [MulAction G R] (g : G) : IsSMulRegular R g :=
  IsSMulRegular.all g

end Group

section Units

variable (M) [Monoid R] [MulAction R M]

/-- Any element in `Rˣ` is `M`-regular. -/
@[to_additive
  /-- Any element in `AddUnits R` is `M`-regular. -/]
theorem Units.isSMulRegular (a : Rˣ) : IsSMulRegular M (a : R) :=
  IsSMulRegular.of_mul_eq_one a.inv_val

/-- A unit is `M`-regular. -/
@[to_additive
  /-- An additive unit is `M`-regular. -/]
theorem IsUnit.isSMulRegular (ua : IsUnit a) : IsSMulRegular M a := by
  rcases ua with ⟨a, rfl⟩
  exact a.isSMulRegular M

end Units

@[to_additive]
lemma Equiv.isSMulRegular_congr {R S M M'} [SMul R M] [SMul S M'] {e : M ≃ M'}
    {r : R} {s : S} (h : ∀ x, e (r • x) = s • e x) :
    IsSMulRegular M r ↔ IsSMulRegular M' s :=
  (e.comp_injective _).symm.trans <|
    (iff_of_eq <| congrArg _ <| funext h).trans <| e.injective_comp _
