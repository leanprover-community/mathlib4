/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma, Oliver Nash
-/
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Regular.SMul

/-!
# Non-zero divisors and smul-divisors

In this file we define the submonoid `nonZeroDivisors` and `nonZeroSMulDivisors` of a
`MonoidWithZero`. We also define `nonZeroDivisorsLeft` and `nonZeroDivisorsRight` for
non-commutative monoids.

## Notation

This file declares the notations:
- `M₀⁰` for the submonoid of non-zero-divisors of `M₀`, in the scope `nonZeroDivisors`.
- `M₀⁰[M]` for the submonoid of non-zero smul-divisors of `M₀` with respect to `M`, in the locale
  `nonZeroSMulDivisors`

Use the statement `open scoped nonZeroDivisors nonZeroSMulDivisors` to access this notation in
your own code.

-/

assert_not_exists Ring

open Function

section
variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

/-- The collection of elements of a `MonoidWithZero` that are not left zero divisors form a
`Submonoid`. -/
def nonZeroDivisorsLeft : Submonoid M₀ where
  carrier := {x | ∀ y, x * y = 0 → y = 0}
  one_mem' := by simp
  mul_mem' {x y} hx hy := fun z hz ↦ hy _ <| hx _ (mul_assoc x y z ▸ hz)

@[simp]
lemma mem_nonZeroDivisorsLeft_iff : x ∈ nonZeroDivisorsLeft M₀ ↔ ∀ y, x * y = 0 → y = 0 := .rfl

lemma notMem_nonZeroDivisorsLeft_iff :
    x ∉ nonZeroDivisorsLeft M₀ ↔ {y | x * y = 0 ∧ y ≠ 0}.Nonempty := by
  simpa [mem_nonZeroDivisorsLeft_iff] using Set.nonempty_def.symm

@[deprecated (since := "2025-05-24")]
alias nmem_nonZeroDivisorsLeft_iff := notMem_nonZeroDivisorsLeft_iff

/-- The collection of elements of a `MonoidWithZero` that are not right zero divisors form a
`Submonoid`. -/
def nonZeroDivisorsRight : Submonoid M₀ where
  carrier := {x | ∀ y, y * x = 0 → y = 0}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy z hz ↦ hx _ (hy _ ((mul_assoc z x y).symm ▸ hz))

@[simp]
lemma mem_nonZeroDivisorsRight_iff : x ∈ nonZeroDivisorsRight M₀ ↔ ∀ y, y * x = 0 → y = 0 := .rfl

lemma notMem_nonZeroDivisorsRight_iff :
    x ∉ nonZeroDivisorsRight M₀ ↔ {y | y * x = 0 ∧ y ≠ 0}.Nonempty := by
  simpa [mem_nonZeroDivisorsRight_iff] using Set.nonempty_def.symm

@[deprecated (since := "2025-05-24")]
alias nmem_nonZeroDivisorsRight_iff := notMem_nonZeroDivisorsRight_iff

lemma nonZeroDivisorsLeft_eq_right (M₀ : Type*) [CommMonoidWithZero M₀] :
    nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀ := by
  ext x; simp [mul_comm x]

@[simp] lemma coe_nonZeroDivisorsLeft_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsLeft M₀ = {x : M₀ | x ≠ 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsLeft_iff, mul_eq_zero, Set.mem_setOf_eq]
  refine ⟨fun h ↦ ?_, fun hx y hx' ↦ by simp_all⟩
  contrapose! h
  exact ⟨1, Or.inl h, one_ne_zero⟩

@[simp] lemma coe_nonZeroDivisorsRight_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsRight M₀ = {x : M₀ | x ≠ 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsRight_iff, mul_eq_zero, forall_eq_or_imp, true_and,
    Set.mem_setOf_eq]
  refine ⟨fun h ↦ ?_, fun hx y hx' ↦ by contradiction⟩
  contrapose! h
  exact ⟨1, h, one_ne_zero⟩

end

/-- The submonoid of non-zero-divisors of a `MonoidWithZero` `M₀`. -/
def nonZeroDivisors (M₀ : Type*) [MonoidWithZero M₀] : Submonoid M₀ :=
  nonZeroDivisorsLeft M₀ ⊓ nonZeroDivisorsRight M₀

/-- The notation for the submonoid of non-zero divisors. -/
scoped[nonZeroDivisors] notation:9000 M₀ "⁰" => nonZeroDivisors M₀

/-- Let `M₀` be a monoid with zero and `M` an additive monoid with an `M₀`-action, then the
collection of non-zero smul-divisors forms a submonoid.

These elements are also called `M`-regular. -/
def nonZeroSMulDivisors (M₀ : Type*) [MonoidWithZero M₀] (M : Type*) [Zero M] [MulAction M₀ M] :
    Submonoid M₀ where
  carrier := { r | ∀ m : M, r • m = 0 → m = 0}
  one_mem' m h := (one_smul M₀ m) ▸ h
  mul_mem' {r₁ r₂} h₁ h₂ m H := h₂ _ <| h₁ _ <| mul_smul r₁ r₂ m ▸ H

/-- The notation for the submonoid of non-zero smul-divisors. -/
scoped[nonZeroSMulDivisors] notation:9000 M₀ "⁰[" M "]" => nonZeroSMulDivisors M₀ M

open nonZeroDivisors

section MonoidWithZero
variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

lemma nonZeroDivisorsLeft_eq_nonZeroSMulDivisors :
    nonZeroDivisorsLeft M₀ = nonZeroSMulDivisors M₀ M₀ := rfl

@[deprecated (since := "2025-07-16")]
alias nonZeroDivisorsRight_eq_nonZeroSMulDivisors := nonZeroDivisorsLeft_eq_nonZeroSMulDivisors

theorem mem_nonZeroDivisors_iff :
    r ∈ M₀⁰ ↔ (∀ x, r * x = 0 → x = 0) ∧ ∀ x, x * r = 0 → x = 0 := Iff.rfl

lemma notMem_nonZeroDivisors_iff :
    r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s ≠ 0}.Nonempty ∨ {s | s * r = 0 ∧ s ≠ 0}.Nonempty := by
  simp [-not_and, not_and_or, mem_nonZeroDivisors_iff, Set.nonempty_def]

@[deprecated (since := "2025-05-24")] alias nmem_nonZeroDivisors_iff := notMem_nonZeroDivisors_iff

theorem mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff (hr : r ∈ nonZeroDivisorsLeft M₀) :
    r * x = 0 ↔ x = 0 :=
  ⟨hr _, by simp +contextual⟩

theorem mul_right_mem_nonZeroDivisorsRight_eq_zero_iff (hr : r ∈ nonZeroDivisorsRight M₀) :
    x * r = 0 ↔ x = 0 :=
  ⟨hr _, by simp +contextual⟩

theorem mul_right_mem_nonZeroDivisors_eq_zero_iff (hr : r ∈ M₀⁰) : x * r = 0 ↔ x = 0 :=
  mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hr.2

@[simp]
theorem mul_right_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : x * c = 0 ↔ x = 0 :=
  mul_right_mem_nonZeroDivisors_eq_zero_iff c.prop

lemma IsUnit.mem_nonZeroDivisors (hx : IsUnit x) : x ∈ M₀⁰ :=
  ⟨fun _ ↦ hx.mul_right_eq_zero.mp, fun _ ↦ hx.mul_left_eq_zero.mp⟩

section Nontrivial
variable [Nontrivial M₀]

theorem zero_notMem_nonZeroDivisorsLeft : 0 ∉ nonZeroDivisorsLeft M₀ :=
  fun h ↦ one_ne_zero <| h 1 <| zero_mul _

theorem zero_notMem_nonZeroDivisorsRight : 0 ∉ nonZeroDivisorsRight M₀ :=
  fun h ↦ one_ne_zero <| h 1 <| mul_zero _

theorem zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰ := fun h ↦ zero_notMem_nonZeroDivisorsLeft h.1

@[deprecated (since := "2025-05-23")]
alias zero_not_mem_nonZeroDivisors := zero_notMem_nonZeroDivisors

theorem nonZeroDivisors.ne_zero (hx : x ∈ M₀⁰) : x ≠ 0 :=
  ne_of_mem_of_not_mem hx zero_notMem_nonZeroDivisors

@[simp]
theorem nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x : M₀) ≠ 0 := nonZeroDivisors.ne_zero x.2

instance [IsLeftCancelMulZero M₀] :
    LeftCancelMonoid M₀⁰ where
  mul_left_cancel _ _ _ h :=  Subtype.ext <|
    mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero _) (by
      simpa only [Subtype.ext_iff, Submonoid.coe_mul] using h)

instance [IsRightCancelMulZero M₀] :
    RightCancelMonoid M₀⁰ where
  mul_right_cancel _ _ _ h := Subtype.ext <|
    mul_right_cancel₀ (nonZeroDivisors.coe_ne_zero _) (by
      simpa only [Subtype.ext_iff, Submonoid.coe_mul] using h)

end Nontrivial

section NoZeroDivisors
variable [NoZeroDivisors M₀]

theorem eq_zero_of_ne_zero_of_mul_right_eq_zero (hx : x ≠ 0) (hxy : y * x = 0) : y = 0 :=
  Or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

theorem eq_zero_of_ne_zero_of_mul_left_eq_zero (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 :=
  Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

theorem mem_nonZeroDivisors_of_ne_zero (hx : x ≠ 0) : x ∈ M₀⁰ :=
  ⟨fun _ ↦ eq_zero_of_ne_zero_of_mul_left_eq_zero hx,
   fun _ ↦ eq_zero_of_ne_zero_of_mul_right_eq_zero hx⟩

@[simp] lemma mem_nonZeroDivisors_iff_ne_zero [Nontrivial M₀] : x ∈ M₀⁰ ↔ x ≠ 0 :=
  ⟨nonZeroDivisors.ne_zero, mem_nonZeroDivisors_of_ne_zero⟩

theorem le_nonZeroDivisors_of_noZeroDivisors {S : Submonoid M₀} (hS : (0 : M₀) ∉ S) :
    S ≤ M₀⁰ := fun _ hx ↦
  mem_nonZeroDivisors_of_ne_zero <| by rintro rfl; exact hS hx

theorem powers_le_nonZeroDivisors_of_noZeroDivisors (hx : x ≠ 0) : Submonoid.powers x ≤ M₀⁰ :=
  le_nonZeroDivisors_of_noZeroDivisors fun h ↦ hx (h.recOn fun _ ↦ eq_zero_of_pow_eq_zero)

end NoZeroDivisors

lemma IsLeftRegular.mem_nonZeroDivisorsLeft (h : IsLeftRegular r) :
    r ∈ nonZeroDivisorsLeft M₀ := fun _x hx ↦ h.mul_left_eq_zero_iff.mp hx

lemma IsRightRegular.mem_nonZeroDivisorsRight (h : IsRightRegular r) :
    r ∈ nonZeroDivisorsRight M₀ := fun _x hx ↦ h.mul_right_eq_zero_iff.mp hx

lemma IsRegular.mem_nonZeroDivisors (h : IsRegular r) : r ∈ M₀⁰ :=
  ⟨h.1.mem_nonZeroDivisorsLeft, h.2.mem_nonZeroDivisorsRight⟩

lemma noZeroDivisors_iff_forall_mem_nonZeroDivisorsLeft :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → x ∈ nonZeroDivisorsLeft M₀ :=
  noZeroDivisors_iff_right_eq_zero_of_mul

lemma noZeroDivisors_iff_forall_mem_nonZeroDivisorsRight :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → x ∈ nonZeroDivisorsRight M₀ :=
  noZeroDivisors_iff_left_eq_zero_of_mul

lemma noZeroDivisors_iff_forall_mem_nonZeroDivisors :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → x ∈ M₀⁰ :=
  noZeroDivisors_iff_eq_zero_of_mul

lemma noZeroSMulDivisors_iff_forall_mem_nonZeroSMulDivisors {M : Type*} [Zero M] [MulAction M₀ M] :
    NoZeroSMulDivisors M₀ M ↔ ∀ x : M₀, x ≠ 0 → x ∈ nonZeroSMulDivisors M₀ M :=
  noZeroSMulDivisors_iff_right_eq_zero_of_smul

lemma IsSMulRegular.mem_nonZeroSMulDivisors {M : Type*} [Zero M] [MulActionWithZero M₀ M] {m₀ : M₀}
    (h : IsSMulRegular M m₀) : m₀ ∈ nonZeroSMulDivisors M₀ M :=
  fun _ ↦ h.right_eq_zero_of_smul

lemma isSMulRegular_iff_mem_nonZeroSMulDivisors {M : Type*} [AddGroup M] [DistribMulAction M₀ M]
    {m₀ : M₀} : IsSMulRegular M m₀ ↔ m₀ ∈ nonZeroSMulDivisors M₀ M :=
  isSMulRegular_iff_right_eq_zero_of_smul

variable [FunLike F M₀ M₀']

-- TODO: nonZeroDivisorsLeft/Right also works
theorem map_ne_zero_of_mem_nonZeroDivisors [Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Injective (g : M₀ → M₀')) {x : M₀} (h : x ∈ M₀⁰) : g x ≠ 0 := fun h0 ↦
  one_ne_zero (h.2 1 ((one_mul x).symm ▸ hg (h0.trans (map_zero g).symm)))

theorem map_mem_nonZeroDivisors [Nontrivial M₀] [NoZeroDivisors M₀'] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Injective g) {x : M₀} (h : x ∈ M₀⁰) : g x ∈ M₀'⁰ :=
  ⟨fun _ ↦ eq_zero_of_ne_zero_of_mul_left_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h),
    fun _ ↦ eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h)⟩

theorem MulEquivClass.map_nonZeroDivisors {M₀ S F : Type*} [MonoidWithZero M₀] [MonoidWithZero S]
    [EquivLike F M₀ S] [MulEquivClass F M₀ S] (h : F) :
    Submonoid.map h (nonZeroDivisors M₀) = nonZeroDivisors S := by
  let h : M₀ ≃* S := h
  change Submonoid.map h _ = _
  ext
  simp_rw [Submonoid.map_equiv_eq_comap_symm, Submonoid.mem_comap, mem_nonZeroDivisors_iff,
    ← h.symm.forall_congr_right, h.symm.toEquiv_eq_coe, h.symm.coe_toEquiv, ← map_mul,
    map_eq_zero_iff _ h.symm.injective]

theorem map_le_nonZeroDivisors_of_injective [NoZeroDivisors M₀'] [MonoidWithZeroHomClass F M₀ M₀']
    (f : F) (hf : Injective f) {S : Submonoid M₀} (hS : S ≤ M₀⁰) : S.map f ≤ M₀'⁰ := by
  cases subsingleton_or_nontrivial M₀
  · simp [Subsingleton.elim S ⊥]
  · refine le_nonZeroDivisors_of_noZeroDivisors ?_
    rintro ⟨x, hx, hx0⟩
    exact zero_notMem_nonZeroDivisors <| hS <| map_eq_zero_iff f hf |>.mp hx0 ▸ hx

theorem nonZeroDivisors_le_comap_nonZeroDivisors_of_injective [NoZeroDivisors M₀']
    [MonoidWithZeroHomClass F M₀ M₀'] (f : F) (hf : Injective f) : M₀⁰ ≤ M₀'⁰.comap f :=
  Submonoid.le_comap_of_map_le _ (map_le_nonZeroDivisors_of_injective _ hf le_rfl)

/-- If an element maps to a non-zero-divisor via injective homomorphism,
then it is a non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Injective f) (hx : f x ∈ M₀'⁰) : x ∈ M₀⁰ :=
  ⟨fun y hy ↦ hf <| map_zero f ▸ hx.1 (f y) (map_mul f x y ▸ map_zero f ▸ congrArg f hy),
    fun y hy ↦ hf <| map_zero f ▸ hx.2 (f y) (map_mul f y x ▸ map_zero f ▸ congrArg f hy)⟩

theorem comap_nonZeroDivisors_le_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Injective f) : M₀'⁰.comap f ≤ M₀⁰ :=
  fun _ ha ↦ mem_nonZeroDivisors_of_injective hf (Submonoid.mem_comap.mp ha)

end MonoidWithZero

section CommMonoidWithZero
variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

lemma nonZeroDivisorsLeft_eq_nonZeroDivisors : nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀ := by
  rw [nonZeroDivisors, nonZeroDivisorsLeft_eq_right, inf_idem]

lemma nonZeroDivisorsRight_eq_nonZeroDivisors : nonZeroDivisorsRight M₀ = nonZeroDivisors M₀ := by
  rw [← nonZeroDivisorsLeft_eq_right, nonZeroDivisorsLeft_eq_nonZeroDivisors]

theorem mem_nonZeroDivisors_iff_right : r ∈ M₀⁰ ↔ ∀ x, x * r = 0 → x = 0 := by
  rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]; rfl

lemma notMem_nonZeroDivisors_iff_right : r ∉ M₀⁰ ↔ {s | s * r = 0 ∧ s ≠ 0}.Nonempty := by
  simp [mem_nonZeroDivisors_iff_right, Set.nonempty_def]

lemma mul_left_mem_nonZeroDivisors_eq_zero_iff (hr : r ∈ M₀⁰) : r * x = 0 ↔ x = 0 := by
  rw [mul_comm, mul_right_mem_nonZeroDivisors_eq_zero_iff hr]

@[simp]
lemma mul_left_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : (c : M₀) * x = 0 ↔ x = 0 :=
  mul_left_mem_nonZeroDivisors_eq_zero_iff c.prop

lemma mul_mem_nonZeroDivisors : a * b ∈ M₀⁰ ↔ a ∈ M₀⁰ ∧ b ∈ M₀⁰ where
  mp h := by
    rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    constructor <;> intro x h' <;> apply h.2
    · rw [← mul_assoc, h', zero_mul]
    · rw [mul_comm a b, ← mul_assoc, h', zero_mul]
  mpr := fun h ↦ mul_mem h.1 h.2

theorem nonZeroDivisors_dvd_iff_dvd_coe {a b : M₀⁰} :
    a ∣ b ↔ (a : M₀) ∣ (b : M₀) :=
  ⟨fun ⟨c, hc⟩ ↦ by simp_rw [hc, Submonoid.coe_mul, dvd_mul_right],
  fun ⟨c, hc⟩ ↦ ⟨⟨c, (mul_mem_nonZeroDivisors.mp (hc ▸ b.prop)).2⟩,
    by simp_rw [Subtype.ext_iff, Submonoid.coe_mul, hc]⟩⟩

end CommMonoidWithZero

section GroupWithZero
variable {G₀ : Type*} [GroupWithZero G₀] {x : G₀}

/-- Canonical isomorphism between the non-zero-divisors and units of a group with zero. -/
@[simps]
noncomputable def nonZeroDivisorsEquivUnits : G₀⁰ ≃* G₀ˣ where
  toFun u := .mk0 _ <| mem_nonZeroDivisors_iff_ne_zero.1 u.2
  invFun u := ⟨u, u.isUnit.mem_nonZeroDivisors⟩
  right_inv u := by simp
  map_mul' u v := by simp

lemma isUnit_of_mem_nonZeroDivisors (hx : x ∈ nonZeroDivisors G₀) : IsUnit x :=
  (nonZeroDivisorsEquivUnits ⟨x, hx⟩).isUnit

end GroupWithZero

section nonZeroSMulDivisors

open nonZeroSMulDivisors

variable {M₀ M : Type*} [MonoidWithZero M₀] [Zero M] [MulAction M₀ M] {x : M₀}

lemma mem_nonZeroSMulDivisors_iff : x ∈ M₀⁰[M] ↔ ∀ (m : M), x • m = 0 → m = 0 := Iff.rfl

@[deprecated (since := "2025-07-16")]
alias unop_nonZeroSMulDivisors_mulOpposite_eq_nonZeroDivisors :=
  nonZeroDivisorsLeft_eq_nonZeroSMulDivisors

@[deprecated (since := "2025-07-16")]
alias nonZeroSMulDivisors_mulOpposite_eq_op_nonZeroDivisors :=
  nonZeroDivisorsLeft_eq_nonZeroSMulDivisors

end nonZeroSMulDivisors

open scoped nonZeroDivisors

variable {M₀}

section MonoidWithZero
variable [MonoidWithZero M₀] {a b : M₀⁰}

/-- The units of the monoid of non-zero divisors of `M₀` are equivalent to the units of `M₀`. -/
@[simps]
def unitsNonZeroDivisorsEquiv : M₀⁰ˣ ≃* M₀ˣ where
  __ := Units.map M₀⁰.subtype
  invFun u := ⟨⟨u, u.isUnit.mem_nonZeroDivisors⟩, ⟨(u⁻¹ : M₀ˣ), u⁻¹.isUnit.mem_nonZeroDivisors⟩,
    by simp, by simp⟩

@[simp, norm_cast] lemma nonZeroDivisors.associated_coe : Associated (a : M₀) b ↔ Associated a b :=
  unitsNonZeroDivisorsEquiv.symm.exists_congr_left.trans <| by simp [Associated]; norm_cast

end MonoidWithZero

section CommMonoidWithZero
variable {M₀ : Type*} [CommMonoidWithZero M₀] {a : M₀}

theorem mk_mem_nonZeroDivisors_associates : Associates.mk a ∈ (Associates M₀)⁰ ↔ a ∈ M₀⁰ := by
  rw [mem_nonZeroDivisors_iff_right, mem_nonZeroDivisors_iff_right, ← not_iff_not]
  push_neg
  constructor
  · rintro ⟨⟨x⟩, hx₁, hx₂⟩
    refine ⟨x, ?_, ?_⟩
    · rwa [← Associates.mk_eq_zero, ← Associates.mk_mul_mk, ← Associates.quot_mk_eq_mk]
    · rwa [← Associates.mk_ne_zero, ← Associates.quot_mk_eq_mk]
  · refine fun ⟨b, hb₁, hb₂⟩ ↦ ⟨Associates.mk b, ?_, by rwa [Associates.mk_ne_zero]⟩
    rw [Associates.mk_mul_mk, hb₁, Associates.mk_zero]

/-- The non-zero divisors of associates of a monoid with zero `M₀` are isomorphic to the associates
of the non-zero divisors of `M₀` under the map `⟨⟦a⟧, _⟩ ↦ ⟦⟨a, _⟩⟧`. -/
def associatesNonZeroDivisorsEquiv : (Associates M₀)⁰ ≃* Associates M₀⁰ where
  toEquiv := .subtypeQuotientEquivQuotientSubtype _ (s₂ := Associated.setoid _)
    (· ∈ nonZeroDivisors _)
    (by simp [mem_nonZeroDivisors_iff, Quotient.forall, Associates.mk_mul_mk])
    (by simp [Associated.setoid])
  map_mul' := by simp [Quotient.forall, Associates.mk_mul_mk]

@[simp]
lemma associatesNonZeroDivisorsEquiv_mk_mk (a : M₀) (ha) :
    associatesNonZeroDivisorsEquiv ⟨⟦a⟧, ha⟩ = ⟦⟨a, mk_mem_nonZeroDivisors_associates.1 ha⟩⟧ := rfl

@[simp]
lemma associatesNonZeroDivisorsEquiv_symm_mk_mk (a : M₀) (ha) :
    associatesNonZeroDivisorsEquiv.symm ⟦⟨a, ha⟩⟧ = ⟨⟦a⟧, mk_mem_nonZeroDivisors_associates.2 ha⟩ :=
  rfl

end CommMonoidWithZero
