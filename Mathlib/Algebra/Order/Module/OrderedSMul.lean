/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module -- shake: keep-all

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Prod
public import Mathlib.Algebra.Order.Module.Defs

/-!
# Ordered scalar product

In this file we define

* `OrderedSMul R M` : an ordered additive commutative monoid `M` is an `OrderedSMul`
  over an `OrderedSemiring` `R` if the scalar product respects the order relation on the
  monoid and on the ring. There is a correspondence between this structure and convex cones,
  which is proven in `Mathlib/Analysis/Convex/Cone.lean`.

## Implementation notes
* We choose to define `OrderedSMul` as a `Prop`-valued mixin, so that it can be
  used for actions, modules, and algebras
  (the axioms for an "ordered algebra" are exactly that the algebra is ordered as a module).
* To get ordered modules and ordered vector spaces, it suffices to replace the
  `OrderedAddCommMonoid` and the `OrderedSemiring` as desired.

## TODO

This file is now mostly useless. We should try deleting `OrderedSMul`

## References

* https://en.wikipedia.org/wiki/Ordered_vector_space

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/

@[expose] public section

deprecated_module (since := "2025-08-25")

/-- The ordered scalar product property is when an ordered additive commutative monoid
with a partial order has a scalar multiplication which is compatible with the order. Note that this
is different from `IsOrderedSMul`, which uses `≤`, has no semiring assumption, and has no positivity
constraint on the defining conditions.
-/
@[deprecated IsStrictOrderedModule (since := "2025-08-25")]
class OrderedSMul (R M : Type*) [Semiring R] [PartialOrder R]
    [AddCommMonoid M] [PartialOrder M] [SMulWithZero R M] :
  Prop where
  /-- Scalar multiplication by positive elements preserves the order. -/
  protected smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, a < b → 0 < c → c • a < c • b
  /-- If `c • a < c • b` for some positive `c`, then `a < b`. -/
  protected lt_of_smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, c • a < c • b → 0 < c → a < b

variable {ι 𝕜 R M N : Type*}

section OrderedSMul
set_option linter.deprecated false
variable [Semiring R] [PartialOrder R] [AddCommMonoid M] [PartialOrder M]
  [SMulWithZero R M] [OrderedSMul R M]

instance OrderedSMul.toPosSMulStrictMono : PosSMulStrictMono R M where
  smul_lt_smul_of_pos_left _a ha _b₁ _b₂ hb := OrderedSMul.smul_lt_smul_of_pos hb ha

instance OrderedSMul.toPosSMulReflectLT : PosSMulReflectLT R M :=
  .of_pos fun _a ha _b₁ _b₂ h ↦ OrderedSMul.lt_of_smul_lt_smul_of_pos h ha

instance OrderDual.instOrderedSMul : OrderedSMul R Mᵒᵈ where
  smul_lt_smul_of_pos := OrderedSMul.smul_lt_smul_of_pos (M := M)
  lt_of_smul_lt_smul_of_pos := OrderedSMul.lt_of_smul_lt_smul_of_pos (M := M)

end OrderedSMul

set_option linter.deprecated false in
/-- To prove that a linear ordered monoid is an ordered module, it suffices to verify only the first
axiom of `OrderedSMul`. -/
theorem OrderedSMul.mk'' [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid M] [LinearOrder M] [SMulWithZero 𝕜 M]
    (h : ∀ ⦃c : 𝕜⦄, 0 < c → StrictMono fun a : M => c • a) : OrderedSMul 𝕜 M :=
  { smul_lt_smul_of_pos := fun hab hc => h hc hab
    lt_of_smul_lt_smul_of_pos := fun hab hc => (h hc).lt_iff_lt.1 hab }

set_option linter.deprecated false in
instance Nat.orderedSMul [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M] :
    OrderedSMul ℕ M :=
  OrderedSMul.mk'' fun n hn a b hab => by
    cases n with
    | zero => cases hn
    | succ n =>
      induction n with
      | zero => dsimp; rwa [one_nsmul, one_nsmul]
      | succ n ih => simp only [succ_nsmul _ n.succ, _root_.add_lt_add (ih n.succ_pos) hab]

set_option linter.deprecated false in
instance Int.orderedSMul [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] :
    OrderedSMul ℤ M :=
  OrderedSMul.mk'' fun n hn => by
    cases n
    · simp only [Int.ofNat_eq_coe, Int.natCast_pos, natCast_zsmul] at hn ⊢
      exact strictMono_smul_left_of_pos hn
    · cases (Int.negSucc_not_pos _).1 hn

section LinearOrderedSemiring
variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

set_option linter.deprecated false in
instance LinearOrderedSemiring.toOrderedSMul : OrderedSMul R R :=
  OrderedSMul.mk'' fun _ => strictMono_mul_left_of_pos

end LinearOrderedSemiring

section LinearOrderedSemifield

variable [Semifield 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜] [PosMulReflectLT 𝕜]
  [AddCommMonoid M] [PartialOrder M]
  [AddCommMonoid N] [PartialOrder N]
  [MulActionWithZero 𝕜 M] [MulActionWithZero 𝕜 N]

set_option linter.deprecated false in
/-- To prove that a vector space over a linear ordered field is ordered, it suffices to verify only
the first axiom of `OrderedSMul`. -/
theorem OrderedSMul.mk' (h : ∀ ⦃a b : M⦄ ⦃c : 𝕜⦄, a < b → 0 < c → c • a ≤ c • b) :
    OrderedSMul 𝕜 M := by
  have hlt' : ∀ (a b : M) (c : 𝕜), a < b → 0 < c → c • a < c • b := by
    refine fun a b c hab hc => (h hab hc).lt_of_ne ?_
    rw [Ne, hc.ne'.isUnit.smul_left_cancel]
    exact hab.ne
  refine ⟨fun {a b c} => hlt' a b c, fun {a b c hab hc} => ?_⟩
  obtain ⟨c, rfl⟩ := hc.ne'.isUnit
  rw [← inv_smul_smul c a, ← inv_smul_smul c b]
  refine hlt' _ _ _ hab (pos_of_mul_pos_right ?_ hc.le)
  simp only [c.mul_inv, zero_lt_one]

set_option linter.deprecated false in
instance [OrderedSMul 𝕜 M] [OrderedSMul 𝕜 N] : OrderedSMul 𝕜 (M × N) :=
  OrderedSMul.mk' fun _ _ _ h hc =>
    ⟨smul_le_smul_of_nonneg_left h.1.1 hc.le, smul_le_smul_of_nonneg_left h.1.2 hc.le⟩

set_option linter.deprecated false in
instance Pi.orderedSMul {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, PartialOrder (M i)]
    [∀ i, MulActionWithZero 𝕜 (M i)] [∀ i, OrderedSMul 𝕜 (M i)] : OrderedSMul 𝕜 (∀ i, M i) :=
  OrderedSMul.mk' fun _ _ _ h hc i => smul_le_smul_of_nonneg_left (h.le i) hc.le

end LinearOrderedSemifield
