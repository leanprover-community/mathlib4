/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.SMulWithZero
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Basic
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.Tactic.Abel

#align_import algebra.module.basic from "leanprover-community/mathlib"@"30413fc89f202a090a54d78e540963ed3de0056e"

/-!
# Modules over a ring

In this file we define

* `Module R M` : an additive commutative monoid `M` is a `Module` over a
  `Semiring R` if for `r : R` and `x : M` their "scalar multiplication" `r • x : M` is defined, and
  the operation `•` satisfies some natural associativity and distributivity axioms similar to those
  on a ring.

## Implementation notes

In typical mathematical usage, our definition of `Module` corresponds to "semimodule", and the
word "module" is reserved for `Module R M` where `R` is a `Ring` and `M` an `AddCommGroup`.
If `R` is a `Field` and `M` an `AddCommGroup`, `M` would be called an `R`-vector space.
Since those assumptions can be made by changing the typeclasses applied to `R` and `M`,
without changing the axioms in `Module`, mathlib calls everything a `Module`.

In older versions of mathlib3, we had separate `semimodule` and `vector_space` abbreviations.
This caused inference issues in some cases, while not providing any real advantages, so we decided
to use a canonical `Module` typeclass throughout.

## Tags

semimodule, module, vector space
-/


open Function

universe u v

variable {α R k S M M₂ M₃ ι : Type*}

/-- A module is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
@[ext]
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0
#align module Module
#align module.ext Module.ext
#align module.ext_iff Module.ext_iff

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x y : M)

-- see Note [lower instance priority]
/-- A module over a semiring automatically inherits a `MulActionWithZero` structure. -/
instance (priority := 100) Module.toMulActionWithZero : MulActionWithZero R M :=
  { (inferInstance : MulAction R M) with
    smul_zero := smul_zero
    zero_smul := Module.zero_smul }
#align module.to_mul_action_with_zero Module.toMulActionWithZero

instance AddCommMonoid.natModule : Module ℕ M where
  one_smul := one_nsmul
  mul_smul m n a := mul_nsmul' a m n
  smul_add n a b := nsmul_add a b n
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
  add_smul r s x := add_nsmul x r s
#align add_comm_monoid.nat_module AddCommMonoid.natModule

theorem AddMonoid.End.nat_cast_def (n : ℕ) :
    (↑n : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℕ M n :=
  rfl
#align add_monoid.End.nat_cast_def AddMonoid.End.nat_cast_def

theorem add_smul : (r + s) • x = r • x + s • x :=
  Module.add_smul r s x
#align add_smul add_smul

theorem Convex.combo_self {a b : R} (h : a + b = 1) (x : M) : a • x + b • x = x := by
  rw [← add_smul, h, one_smul]
  -- 🎉 no goals
#align convex.combo_self Convex.combo_self

variable (R)

-- Porting note: this is the letter of the mathlib3 version, but not really the spirit
theorem two_smul : (2 : R) • x = x + x := by rw [← one_add_one_eq_two, add_smul, one_smul]
                                             -- 🎉 no goals
#align two_smul two_smul

set_option linter.deprecated false in
@[deprecated] theorem two_smul' : (2 : R) • x = bit0 x :=
  two_smul R x
#align two_smul' two_smul'

@[simp]
theorem invOf_two_smul_add_invOf_two_smul [Invertible (2 : R)] (x : M) :
    (⅟ 2 : R) • x + (⅟ 2 : R) • x = x :=
  Convex.combo_self invOf_two_add_invOf_two _
#align inv_of_two_smul_add_inv_of_two_smul invOf_two_smul_add_invOf_two_smul

/-- Pullback a `Module` structure along an injective additive monoid homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.module [AddCommMonoid M₂] [SMul R M₂] (f : M₂ →+ M)
    (hf : Injective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { hf.distribMulAction f smul with
    add_smul := fun c₁ c₂ x => hf <| by simp only [smul, f.map_add, add_smul]
                                        -- 🎉 no goals
    zero_smul := fun x => hf <| by simp only [smul, zero_smul, f.map_zero] }
                                   -- 🎉 no goals
#align function.injective.module Function.Injective.module

/-- Pushforward a `Module` structure along a surjective additive monoid homomorphism. -/
protected def Function.Surjective.module [AddCommMonoid M₂] [SMul R M₂] (f : M →+ M₂)
    (hf : Surjective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { toDistribMulAction := hf.distribMulAction f smul
    add_smul := fun c₁ c₂ x => by
      rcases hf x with ⟨x, rfl⟩
      -- ⊢ (c₁ + c₂) • ↑f x = c₁ • ↑f x + c₂ • ↑f x
      simp only [add_smul, ← smul, ← f.map_add]
      -- 🎉 no goals
    zero_smul := fun x => by
      rcases hf x with ⟨x, rfl⟩
      -- ⊢ 0 • ↑f x = 0
      rw [← f.map_zero, ← smul, zero_smul] }
      -- 🎉 no goals
#align function.surjective.module Function.Surjective.module

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →+* S`.

See also `Function.Surjective.mulActionLeft` and `Function.Surjective.distribMulActionLeft`.
-/
@[reducible]
def Function.Surjective.moduleLeft {R S M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring S] [SMul S M] (f : R →+* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : Module S M :=
  { hf.distribMulActionLeft f.toMonoidHom hsmul with
    zero_smul := fun x => by rw [← f.map_zero, hsmul, zero_smul]
                             -- 🎉 no goals
                                               -- 🎉 no goals
    add_smul := hf.forall₂.mpr fun a b x => by simp only [← f.map_add, hsmul, add_smul] }
#align function.surjective.module_left Function.Surjective.moduleLeft

variable {R} (M)

/-- Compose a `Module` with a `RingHom`, with action `f s • m`.

See note [reducible non-instances]. -/
@[reducible]
def Module.compHom [Semiring S] (f : S →+* R) : Module S M :=
  { MulActionWithZero.compHom M f.toMonoidWithZeroHom, DistribMulAction.compHom M (f : S →* R) with
    smul := SMul.comp.smul f
    -- Porting note: the `show f (r + s) • x = f r • x + f s • x ` wasn't needed in mathlib3.
    -- Somehow, now that `SMul` is heterogeneous, it can't unfold earlier fields of a definition for
    -- use in later fields.  See
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Heterogeneous.20scalar.20multiplication
    add_smul := fun r s x => show f (r + s) • x = f r • x + f s • x by simp [add_smul] }
                                                                       -- 🎉 no goals
#align module.comp_hom Module.compHom

variable (R)

/-- `(•)` as an `AddMonoidHom`.

This is a stronger version of `DistribMulAction.toAddMonoidEnd` -/
@[simps! apply_apply]
def Module.toAddMonoidEnd : R →+* AddMonoid.End M :=
  { DistribMulAction.toAddMonoidEnd R M with
    -- Porting note: the two `show`s weren't needed in mathlib3.
    -- Somehow, now that `SMul` is heterogeneous, it can't unfold earlier fields of a definition for
    -- use in later fields.  See
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Heterogeneous.20scalar.20multiplication
    map_zero' := AddMonoidHom.ext fun r => show (0:R) • r = 0 by simp
                                                                 -- 🎉 no goals
    map_add' := fun x y =>
      AddMonoidHom.ext fun r => show (x + y) • r = x • r + y • r by simp [add_smul] }
                                                                    -- 🎉 no goals
#align module.to_add_monoid_End Module.toAddMonoidEnd
#align module.to_add_monoid_End_apply_apply Module.toAddMonoidEnd_apply_apply

/-- A convenience alias for `Module.toAddMonoidEnd` as an `AddMonoidHom`, usually to allow the
use of `AddMonoidHom.flip`. -/
def smulAddHom : R →+ M →+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom
#align smul_add_hom smulAddHom

variable {R M}

@[simp]
theorem smulAddHom_apply (r : R) (x : M) : smulAddHom R M r x = r • x :=
  rfl
#align smul_add_hom_apply smulAddHom_apply

theorem Module.eq_zero_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : x = 0 := by
  rw [← one_smul R x, ← zero_eq_one, zero_smul]
  -- 🎉 no goals
#align module.eq_zero_of_zero_eq_one Module.eq_zero_of_zero_eq_one

@[simp]
theorem smul_add_one_sub_smul {R : Type*} [Ring R] [Module R M] {r : R} {m : M} :
    r • m + (1 - r) • m = m := by rw [← add_smul, add_sub_cancel'_right, one_smul]
                                  -- 🎉 no goals
#align smul_add_one_sub_smul smul_add_one_sub_smul

end AddCommMonoid


section AddCommGroup

variable (R M) [Semiring R] [AddCommGroup M]

instance AddCommGroup.intModule : Module ℤ M where
  one_smul := one_zsmul
  mul_smul m n a := mul_zsmul a m n
  smul_add n a b := zsmul_add a b n
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
  add_smul r s x := add_zsmul x r s
#align add_comm_group.int_module AddCommGroup.intModule

theorem AddMonoid.End.int_cast_def (z : ℤ) :
    (↑z : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℤ M z :=
  rfl
#align add_monoid.End.int_cast_def AddMonoid.End.int_cast_def

/-- A structure containing most informations as in a module, except the fields `zero_smul`
and `smul_zero`. As these fields can be deduced from the other ones when `M` is an `AddCommGroup`,
this provides a way to construct a module structure by checking less properties, in
`Module.ofCore`. -/
-- Porting note: removed @[nolint has_nonempty_instance]
structure Module.Core extends SMul R M where
  /-- Scalar multiplication distributes over addition from the left. -/
  smul_add : ∀ (r : R) (x y : M), r • (x + y) = r • x + r • y
  /-- Scalar multiplication distributes over addition from the right. -/
  add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication distributes over multiplication from the right. -/
  mul_smul : ∀ (r s : R) (x : M), (r * s) • x = r • s • x
  /-- Scalar multiplication by one is the identity. -/
  one_smul : ∀ x : M, (1 : R) • x = x
#align module.core Module.Core

variable {R M}

/-- Define `Module` without proving `zero_smul` and `smul_zero` by using an auxiliary
structure `Module.Core`, when the underlying space is an `AddCommGroup`. -/
def Module.ofCore (H : Module.Core R M) : Module R M :=
  letI := H.toSMul
  { H with
    zero_smul := fun x =>
      (AddMonoidHom.mk' (fun r : R => r • x) fun r s => H.add_smul r s x).map_zero
    smul_zero := fun r => (AddMonoidHom.mk' ((· • ·) r) (H.smul_add r)).map_zero }
#align module.of_core Module.ofCore

theorem Convex.combo_eq_smul_sub_add [Module R M] {x y : M} {a b : R} (h : a + b = 1) :
    a • x + b • y = b • (y - x) + x :=
  calc
    a • x + b • y = b • y - b • x + (a • x + b • x) := by abel
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
    _ = b • (y - x) + x := by rw [smul_sub, Convex.combo_self h]
                              -- 🎉 no goals
#align convex.combo_eq_smul_sub_add Convex.combo_eq_smul_sub_add

end AddCommGroup

-- We'll later use this to show `Module ℕ M` and `Module ℤ M` are subsingletons.
/-- A variant of `Module.ext` that's convenient for term-mode. -/
theorem Module.ext' {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] (P Q : Module R M)
    (w : ∀ (r : R) (m : M), (haveI := P; r • m) = (haveI := Q; r • m)) :
    P = Q := by
  ext
  -- ⊢ SMul.smul x✝¹ x✝ = SMul.smul x✝¹ x✝
  exact w _ _
  -- 🎉 no goals
#align module.ext' Module.ext'

section Module

variable [Ring R] [AddCommGroup M] [Module R M] (r s : R) (x y : M)

@[simp]
theorem neg_smul : -r • x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by rw [← add_smul, add_left_neg, zero_smul]
                                   -- 🎉 no goals
#align neg_smul neg_smul

-- Porting note: simp can prove this
--@[simp]
theorem neg_smul_neg : -r • -x = r • x := by rw [neg_smul, smul_neg, neg_neg]
                                             -- 🎉 no goals
#align neg_smul_neg neg_smul_neg

@[simp]
theorem Units.neg_smul (u : Rˣ) (x : M) : -u • x = -(u • x) := by
  rw [Units.smul_def, Units.val_neg, _root_.neg_smul, Units.smul_def]
  -- 🎉 no goals
#align units.neg_smul Units.neg_smul

variable (R)

theorem neg_one_smul (x : M) : (-1 : R) • x = -x := by simp
                                                       -- 🎉 no goals
#align neg_one_smul neg_one_smul

variable {R}

theorem sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y := by
  simp [add_smul, sub_eq_add_neg]
  -- 🎉 no goals
#align sub_smul sub_smul

end Module

variable (R)

/-- An `AddCommMonoid` that is a `Module` over a `Ring` carries a natural `AddCommGroup`
structure.
See note [reducible non-instances]. -/
@[reducible]
def Module.addCommMonoidToAddCommGroup [Ring R] [AddCommMonoid M] [Module R M] : AddCommGroup M :=
  { (inferInstance : AddCommMonoid M) with
    neg := fun a => (-1 : R) • a
    add_left_neg := fun a =>
      show (-1 : R) • a + a = 0 by
        nth_rw 2 [← one_smul R a]
        -- ⊢ -1 • a + 1 • a = 0
        rw [← add_smul, add_left_neg, zero_smul]
        -- 🎉 no goals
                               -- 🎉 no goals
    zsmul := fun z a => (z : R) • a
                                 -- 🎉 no goals
    zsmul_zero' := fun a => by simpa only [Int.cast_zero] using zero_smul R a
                                -- 🎉 no goals
    zsmul_succ' := fun z a => by simp [add_comm, add_smul]
    zsmul_neg' := fun z a => by simp [←smul_assoc, neg_one_smul] }
#align module.add_comm_monoid_to_add_comm_group Module.addCommMonoidToAddCommGroup

variable {R}

/-- A module over a `Subsingleton` semiring is a `Subsingleton`. We cannot register this
as an instance because Lean has no way to guess `R`. -/
protected theorem Module.subsingleton (R M : Type*) [Semiring R] [Subsingleton R] [AddCommMonoid M]
    [Module R M] : Subsingleton M :=
  MulActionWithZero.subsingleton R M
#align module.subsingleton Module.subsingleton

/-- A semiring is `Nontrivial` provided that there exists a nontrivial module over this semiring. -/
protected theorem Module.nontrivial (R M : Type*) [Semiring R] [Nontrivial M] [AddCommMonoid M]
    [Module R M] : Nontrivial R :=
  MulActionWithZero.nontrivial R M
#align module.nontrivial Module.nontrivial

-- see Note [lower instance priority]
instance (priority := 910) Semiring.toModule [Semiring R] : Module R R where
  smul_add := mul_add
  add_smul := add_mul
  zero_smul := zero_mul
  smul_zero := mul_zero
#align semiring.to_module Semiring.toModule

-- see Note [lower instance priority]
/-- Like `Semiring.toModule`, but multiplies on the right. -/
instance (priority := 910) Semiring.toOppositeModule [Semiring R] : Module Rᵐᵒᵖ R :=
  { MonoidWithZero.toOppositeMulActionWithZero R with
    smul_add := fun _ _ _ => add_mul _ _ _
    add_smul := fun _ _ _ => mul_add _ _ _ }
#align semiring.to_opposite_module Semiring.toOppositeModule

/-- A ring homomorphism `f : R →+* M` defines a module structure by `r • x = f r * x`. -/
def RingHom.toModule [Semiring R] [Semiring S] (f : R →+* S) : Module R S :=
  Module.compHom S f
#align ring_hom.to_module RingHom.toModule

/-- The tautological action by `R →+* R` on `R`.

This generalizes `Function.End.applyMulAction`. -/
instance RingHom.applyDistribMulAction [Semiring R] : DistribMulAction (R →+* R) R where
  smul := (· <| ·)
  smul_zero := RingHom.map_zero
  smul_add := RingHom.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align ring_hom.apply_distrib_mul_action RingHom.applyDistribMulAction

@[simp]
protected theorem RingHom.smul_def [Semiring R] (f : R →+* R) (a : R) : f • a = f a :=
  rfl
#align ring_hom.smul_def RingHom.smul_def

/-- `RingHom.applyDistribMulAction` is faithful. -/
instance RingHom.applyFaithfulSMul [Semiring R] : FaithfulSMul (R →+* R) R :=
  ⟨fun {_ _} h => RingHom.ext h⟩
#align ring_hom.apply_has_faithful_smul RingHom.applyFaithfulSMul

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

section

variable (R)

/-- `nsmul` is equal to any other module structure via a cast. -/
theorem nsmul_eq_smul_cast (n : ℕ) (b : M) : n • b = (n : R) • b := by
  induction' n with n ih
  -- ⊢ Nat.zero • b = ↑Nat.zero • b
  · rw [Nat.zero_eq, Nat.cast_zero, zero_smul, zero_smul]
    -- 🎉 no goals
  · rw [Nat.succ_eq_add_one, Nat.cast_succ, add_smul, add_smul, one_smul, ih, one_smul]
    -- 🎉 no goals
#align nsmul_eq_smul_cast nsmul_eq_smul_cast

end

/-- Convert back any exotic `ℕ`-smul to the canonical instance. This should not be needed since in
mathlib all `AddCommMonoid`s should normally have exactly one `ℕ`-module structure by design.
-/
theorem nat_smul_eq_nsmul (h : Module ℕ M) (n : ℕ) (x : M) :
    @SMul.smul ℕ M h.toSMul n x = n • x := by rw [nsmul_eq_smul_cast ℕ n x, Nat.cast_id]; rfl
                                              -- ⊢ SMul.smul n x = n • x
                                                                                          -- 🎉 no goals
#align nat_smul_eq_nsmul nat_smul_eq_nsmul

/-- All `ℕ`-module structures are equal. Not an instance since in mathlib all `AddCommMonoid`
should normally have exactly one `ℕ`-module structure by design. -/
def AddCommMonoid.natModule.unique : Unique (Module ℕ M) where
  default := by infer_instance
                -- 🎉 no goals
  uniq P := (Module.ext' P _) fun n => by convert nat_smul_eq_nsmul P n
                                          -- 🎉 no goals
#align add_comm_monoid.nat_module.unique AddCommMonoid.natModule.unique

instance AddCommMonoid.nat_isScalarTower : IsScalarTower ℕ R M where
  smul_assoc n x y :=
    Nat.recOn n (by simp only [Nat.zero_eq, zero_smul])
                    -- 🎉 no goals
    fun n ih => by simp only [Nat.succ_eq_add_one, add_smul, one_smul, ih]
                   -- 🎉 no goals
#align add_comm_monoid.nat_is_scalar_tower AddCommMonoid.nat_isScalarTower

end AddCommMonoid

section AddCommGroup

variable [Semiring S] [Ring R] [AddCommGroup M] [Module S M] [Module R M]

section

variable (R)

/-- `zsmul` is equal to any other module structure via a cast. -/
theorem zsmul_eq_smul_cast (n : ℤ) (b : M) : n • b = (n : R) • b :=
  have : (smulAddHom ℤ M).flip b = ((smulAddHom R M).flip b).comp (Int.castAddHom R) := by
    apply AddMonoidHom.ext_int
    -- ⊢ ↑(↑(AddMonoidHom.flip (smulAddHom ℤ M)) b) 1 = ↑(AddMonoidHom.comp (↑(AddMon …
    simp
    -- 🎉 no goals
  FunLike.congr_fun this n
#align zsmul_eq_smul_cast zsmul_eq_smul_cast

end

/-- Convert back any exotic `ℤ`-smul to the canonical instance. This should not be needed since in
mathlib all `AddCommGroup`s should normally have exactly one `ℤ`-module structure by design. -/
theorem int_smul_eq_zsmul (h : Module ℤ M) (n : ℤ) (x : M) :
    @SMul.smul ℤ M h.toSMul n x = n • x := by rw [zsmul_eq_smul_cast ℤ n x, Int.cast_id]; rfl
                                              -- ⊢ SMul.smul n x = n • x
                                                                                          -- 🎉 no goals
#align int_smul_eq_zsmul int_smul_eq_zsmul

/-- All `ℤ`-module structures are equal. Not an instance since in mathlib all `AddCommGroup`
should normally have exactly one `ℤ`-module structure by design. -/
def AddCommGroup.intModule.unique : Unique (Module ℤ M) where
  default := by infer_instance
                -- 🎉 no goals
  uniq P := (Module.ext' P _) fun n => by convert int_smul_eq_zsmul P n
                                          -- 🎉 no goals
#align add_comm_group.int_module.unique AddCommGroup.intModule.unique

end AddCommGroup

theorem map_int_cast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [AddMonoidHomClass F M M₂]
    (f : F) (R S : Type*) [Ring R] [Ring S] [Module R M] [Module S M₂] (x : ℤ) (a : M) :
    f ((x : R) • a) = (x : S) • f a := by simp only [← zsmul_eq_smul_cast, map_zsmul]
                                          -- 🎉 no goals
#align map_int_cast_smul map_int_cast_smul

theorem map_nat_cast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*}
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Semiring R] [Semiring S] [Module R M]
    [Module S M₂] (x : ℕ) (a : M) : f ((x : R) • a) = (x : S) • f a := by
  simp only [← nsmul_eq_smul_cast, AddMonoidHom.map_nsmul, map_nsmul]
  -- 🎉 no goals
#align map_nat_cast_smul map_nat_cast_smul

theorem map_inv_nat_cast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*}
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*)
    [DivisionSemiring R] [DivisionSemiring S] [Module R M]
    [Module S M₂] (n : ℕ) (x : M) : f ((n⁻¹ : R) • x) = (n⁻¹ : S) • f x := by
  by_cases hR : (n : R) = 0 <;> by_cases hS : (n : S) = 0
  -- ⊢ ↑f ((↑n)⁻¹ • x) = (↑n)⁻¹ • ↑f x
                                -- ⊢ ↑f ((↑n)⁻¹ • x) = (↑n)⁻¹ • ↑f x
                                -- ⊢ ↑f ((↑n)⁻¹ • x) = (↑n)⁻¹ • ↑f x
  · simp [hR, hS, map_zero f]
    -- 🎉 no goals
  · suffices ∀ y, f y = 0 by rw [this, this, smul_zero]
    -- ⊢ ∀ (y : M), ↑f y = 0
    clear x
    -- ⊢ ∀ (y : M), ↑f y = 0
    intro x
    -- ⊢ ↑f x = 0
    rw [← inv_smul_smul₀ hS (f x), ← map_nat_cast_smul f R S]
    -- ⊢ (↑n)⁻¹ • ↑f (↑n • x) = 0
    simp [hR, map_zero f]
    -- 🎉 no goals
  · suffices ∀ y, f y = 0 by simp [this]
    -- ⊢ ∀ (y : M), ↑f y = 0
    clear x
    -- ⊢ ∀ (y : M), ↑f y = 0
    intro x
    -- ⊢ ↑f x = 0
    rw [← smul_inv_smul₀ hR x, map_nat_cast_smul f R S, hS, zero_smul]
    -- 🎉 no goals
  · rw [← inv_smul_smul₀ hS (f _), ← map_nat_cast_smul f R S, smul_inv_smul₀ hR]
    -- 🎉 no goals
#align map_inv_nat_cast_smul map_inv_nat_cast_smul

theorem map_inv_int_cast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*}
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (z : ℤ) (x : M) : f ((z⁻¹ : R) • x) = (z⁻¹ : S) • f x := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  -- ⊢ ↑f ((↑↑n)⁻¹ • x) = (↑↑n)⁻¹ • ↑f x
  · rw [Int.cast_Nat_cast, Int.cast_Nat_cast, map_inv_nat_cast_smul _ R S]
    -- 🎉 no goals
  · simp_rw [Int.cast_neg, Int.cast_Nat_cast, inv_neg, neg_smul, map_neg,
      map_inv_nat_cast_smul _ R S]
#align map_inv_int_cast_smul map_inv_int_cast_smul

theorem map_rat_cast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [AddMonoidHomClass F M M₂]
    (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M] [Module S M₂] (c : ℚ)
    (x : M) : f ((c : R) • x) = (c : S) • f x := by
  rw [Rat.cast_def, Rat.cast_def, div_eq_mul_inv, div_eq_mul_inv, mul_smul, mul_smul,
    map_int_cast_smul f R S, map_inv_nat_cast_smul f R S]
#align map_rat_cast_smul map_rat_cast_smul

theorem map_rat_smul [AddCommGroup M] [AddCommGroup M₂] [Module ℚ M] [Module ℚ M₂] {F : Type*}
    [AddMonoidHomClass F M M₂] (f : F) (c : ℚ) (x : M) : f (c • x) = c • f x :=
  map_rat_cast_smul f ℚ ℚ c x
#align map_rat_smul map_rat_smul

/-- There can be at most one `Module ℚ E` structure on an additive commutative group. -/
instance subsingleton_rat_module (E : Type*) [AddCommGroup E] : Subsingleton (Module ℚ E) :=
  ⟨fun P Q => (Module.ext' P Q) fun r x => @map_rat_smul _ _ _ _ P Q _ _ (AddMonoidHom.id E) r x⟩
#align subsingleton_rat_module subsingleton_rat_module

/-- If `E` is a vector space over two division semirings `R` and `S`, then scalar multiplications
agree on inverses of natural numbers in `R` and `S`. -/
theorem inv_nat_cast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [DivisionSemiring S] [Module R E] [Module S E] (n : ℕ) (x : E) :
    (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_nat_cast_smul (AddMonoidHom.id E) R S n x
#align inv_nat_cast_smul_eq inv_nat_cast_smul_eq

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on inverses of integer numbers in `R` and `S`. -/
theorem inv_int_cast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (n : ℤ) (x : E) : (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_int_cast_smul (AddMonoidHom.id E) R S n x
#align inv_int_cast_smul_eq inv_int_cast_smul_eq

/-- If `E` is a vector space over a division semiring `R` and has a monoid action by `α`, then that
action commutes by scalar multiplication of inverses of natural numbers in `R`. -/
theorem inv_nat_cast_smul_comm {α E : Type*} (R : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [Monoid α] [Module R E] [DistribMulAction α E] (n : ℕ) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_nat_cast_smul (DistribMulAction.toAddMonoidHom E s) R R n x).symm
#align inv_nat_cast_smul_comm inv_nat_cast_smul_comm

/-- If `E` is a vector space over a division ring `R` and has a monoid action by `α`, then that
action commutes by scalar multiplication of inverses of integers in `R` -/
theorem inv_int_cast_smul_comm {α E : Type*} (R : Type*) [AddCommGroup E] [DivisionRing R]
    [Monoid α] [Module R E] [DistribMulAction α E] (n : ℤ) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_int_cast_smul (DistribMulAction.toAddMonoidHom E s) R R n x).symm
#align inv_int_cast_smul_comm inv_int_cast_smul_comm

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on rational numbers in `R` and `S`. -/
theorem rat_cast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (r : ℚ) (x : E) : (r : R) • x = (r : S) • x :=
  map_rat_cast_smul (AddMonoidHom.id E) R S r x
#align rat_cast_smul_eq rat_cast_smul_eq

instance AddCommGroup.intIsScalarTower {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] : IsScalarTower ℤ R M where
  smul_assoc n x y := ((smulAddHom R M).flip y).map_zsmul x n
#align add_comm_group.int_is_scalar_tower AddCommGroup.intIsScalarTower

instance IsScalarTower.rat {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    [Module ℚ R] [Module ℚ M] : IsScalarTower ℚ R M where
  smul_assoc r x y := map_rat_smul ((smulAddHom R M).flip y) r x
#align is_scalar_tower.rat IsScalarTower.rat

instance SMulCommClass.rat {R : Type u} {M : Type v} [Semiring R] [AddCommGroup M] [Module R M]
    [Module ℚ M] : SMulCommClass ℚ R M where
  smul_comm r x y := (map_rat_smul (smulAddHom R M x) r y).symm
#align smul_comm_class.rat SMulCommClass.rat

instance SMulCommClass.rat' {R : Type u} {M : Type v} [Semiring R] [AddCommGroup M] [Module R M]
    [Module ℚ M] : SMulCommClass R ℚ M :=
  SMulCommClass.symm _ _ _
#align smul_comm_class.rat' SMulCommClass.rat'

section NoZeroSMulDivisors

/-! ### `NoZeroSMulDivisors`

This section defines the `NoZeroSMulDivisors` class, and includes some tests
for the vanishing of elements (especially in modules over division rings).
-/


/-- `NoZeroSMulDivisors R M` states that a scalar multiple is `0` only if either argument is `0`.
This is a version of saying that `M` is torsion free, without assuming `R` is zero-divisor free.

The main application of `NoZeroSMulDivisors R M`, when `M` is a module,
is the result `smul_eq_zero`: a scalar multiple is `0` iff either argument is `0`.

It is a generalization of the `NoZeroDivisors` class to heterogeneous multiplication.
-/
class NoZeroSMulDivisors (R M : Type*) [Zero R] [Zero M] [SMul R M] : Prop where
  /-- If scalar multiplication yields zero, either the scalar or the vector was zero. -/
  eq_zero_or_eq_zero_of_smul_eq_zero : ∀ {c : R} {x : M}, c • x = 0 → c = 0 ∨ x = 0
#align no_zero_smul_divisors NoZeroSMulDivisors

export NoZeroSMulDivisors (eq_zero_or_eq_zero_of_smul_eq_zero)

/-- Pullback a `NoZeroSMulDivisors` instance along an injective function. -/
theorem Function.Injective.noZeroSMulDivisors {R M N : Type*} [Zero R] [Zero M] [Zero N]
    [SMul R M] [SMul R N] [NoZeroSMulDivisors R N] (f : M → N) (hf : Function.Injective f)
    (h0 : f 0 = 0) (hs : ∀ (c : R) (x : M), f (c • x) = c • f x) : NoZeroSMulDivisors R M :=
  ⟨fun {_ _} h =>
    Or.imp_right (@hf _ _) <| h0.symm ▸ eq_zero_or_eq_zero_of_smul_eq_zero (by rw [← hs, h, h0])⟩
                                                                               -- 🎉 no goals
#align function.injective.no_zero_smul_divisors Function.Injective.noZeroSMulDivisors

-- See note [lower instance priority]
instance (priority := 100) NoZeroDivisors.toNoZeroSMulDivisors [Zero R] [Mul R]
    [NoZeroDivisors R] : NoZeroSMulDivisors R R :=
  ⟨fun {_ _} => eq_zero_or_eq_zero_of_mul_eq_zero⟩
#align no_zero_divisors.to_no_zero_smul_divisors NoZeroDivisors.toNoZeroSMulDivisors

theorem smul_ne_zero [Zero R] [Zero M] [SMul R M] [NoZeroSMulDivisors R M] {c : R} {x : M}
    (hc : c ≠ 0) (hx : x ≠ 0) : c • x ≠ 0 := fun h =>
  (eq_zero_or_eq_zero_of_smul_eq_zero h).elim hc hx
#align smul_ne_zero smul_ne_zero

section SMulWithZero

variable [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] {c : R} {x : M}

@[simp]
theorem smul_eq_zero : c • x = 0 ↔ c = 0 ∨ x = 0 :=
  ⟨eq_zero_or_eq_zero_of_smul_eq_zero, fun h =>
    h.elim (fun h => h.symm ▸ zero_smul R x) fun h => h.symm ▸ smul_zero c⟩
#align smul_eq_zero smul_eq_zero

theorem smul_ne_zero_iff : c • x ≠ 0 ↔ c ≠ 0 ∧ x ≠ 0 := by rw [Ne.def, smul_eq_zero, not_or]
                                                           -- 🎉 no goals
#align smul_ne_zero_iff smul_ne_zero_iff

end SMulWithZero

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M]

section Nat

variable [NoZeroSMulDivisors R M] [CharZero R]
variable (R) (M)

--include R

theorem Nat.noZeroSMulDivisors : NoZeroSMulDivisors ℕ M :=
  ⟨by
    intro c x
    -- ⊢ c • x = 0 → c = 0 ∨ x = 0
    rw [nsmul_eq_smul_cast R, smul_eq_zero]
    -- ⊢ ↑c = 0 ∨ x = 0 → c = 0 ∨ x = 0
    simp⟩
    -- 🎉 no goals
#align nat.no_zero_smul_divisors Nat.noZeroSMulDivisors

-- Porting note: left-hand side never simplifies when using simp on itself
--@[simp]
theorem two_nsmul_eq_zero {v : M} : 2 • v = 0 ↔ v = 0 := by
  haveI := Nat.noZeroSMulDivisors R M
  -- ⊢ 2 • v = 0 ↔ v = 0
  simp [smul_eq_zero]
  -- 🎉 no goals
#align two_nsmul_eq_zero two_nsmul_eq_zero

end Nat

variable (R M)

/-- If `M` is an `R`-module with one and `M` has characteristic zero, then `R` has characteristic
zero as well. Usually `M` is an `R`-algebra. -/
theorem CharZero.of_module (M) [AddCommMonoidWithOne M] [CharZero M] [Module R M] : CharZero R := by
  refine' ⟨fun m n h => @Nat.cast_injective M _ _ _ _ _⟩
  -- ⊢ ↑m = ↑n
  rw [← nsmul_one, ← nsmul_one, nsmul_eq_smul_cast R m (1 : M), nsmul_eq_smul_cast R n (1 : M), h]
  -- 🎉 no goals
#align char_zero.of_module CharZero.of_module

end Module

section AddCommGroup

-- `R` can still be a semiring here
variable [Semiring R] [AddCommGroup M] [Module R M]

section SMulInjective

variable (M)

theorem smul_right_injective [NoZeroSMulDivisors R M] {c : R} (hc : c ≠ 0) :
    Function.Injective ((· • ·) c : M → M) :=
  (injective_iff_map_eq_zero (smulAddHom R M c)).2 fun _ ha => (smul_eq_zero.mp ha).resolve_left hc
#align smul_right_injective smul_right_injective

variable {M}

theorem smul_right_inj [NoZeroSMulDivisors R M] {c : R} (hc : c ≠ 0) {x y : M} :
    c • x = c • y ↔ x = y :=
  (smul_right_injective M hc).eq_iff
#align smul_right_inj smul_right_inj

end SMulInjective

section Nat

variable [NoZeroSMulDivisors R M] [CharZero R]
variable (R M)
--include R

theorem self_eq_neg {v : M} : v = -v ↔ v = 0 := by
  rw [← two_nsmul_eq_zero R M, two_smul, add_eq_zero_iff_eq_neg]
  -- 🎉 no goals
#align self_eq_neg self_eq_neg

theorem neg_eq_self {v : M} : -v = v ↔ v = 0 := by rw [eq_comm, self_eq_neg R M]
                                                   -- 🎉 no goals
#align neg_eq_self neg_eq_self

theorem self_ne_neg {v : M} : v ≠ -v ↔ v ≠ 0 :=
  (self_eq_neg R M).not
#align self_ne_neg self_ne_neg

theorem neg_ne_self {v : M} : -v ≠ v ↔ v ≠ 0 :=
  (neg_eq_self R M).not
#align neg_ne_self neg_ne_self

end Nat

end AddCommGroup

section Module

variable [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]

section SMulInjective

variable (R)

theorem smul_left_injective {x : M} (hx : x ≠ 0) : Function.Injective fun c : R => c • x :=
  fun c d h =>
  sub_eq_zero.mp
    ((smul_eq_zero.mp
          (calc
            (c - d) • x = c • x - d • x := sub_smul c d x
            _ = 0 := sub_eq_zero.mpr h
            )).resolve_right
      hx)
#align smul_left_injective smul_left_injective

end SMulInjective

end Module

section GroupWithZero

variable [GroupWithZero R] [AddMonoid M] [DistribMulAction R M]

-- see note [lower instance priority]
/-- This instance applies to `DivisionSemiring`s, in particular `NNReal` and `NNRat`. -/
instance (priority := 100) GroupWithZero.toNoZeroSMulDivisors : NoZeroSMulDivisors R M :=
  ⟨fun {_ _} h => or_iff_not_imp_left.2 fun hc => (smul_eq_zero_iff_eq' hc).1 h⟩
#align group_with_zero.to_no_zero_smul_divisors GroupWithZero.toNoZeroSMulDivisors

end GroupWithZero

-- see note [lower instance priority]
instance (priority := 100) RatModule.noZeroSMulDivisors [AddCommGroup M] [Module ℚ M] :
    NoZeroSMulDivisors ℤ M :=
  ⟨fun {k} {x : M} h => by
    simpa only [zsmul_eq_smul_cast ℚ k x, smul_eq_zero, Rat.zero_iff_num_zero] using h⟩
    -- 🎉 no goals
  -- Porting note: old proof was:
  --⟨fun {k x} h => by simpa [zsmul_eq_smul_cast ℚ k x] using h⟩
#align rat_module.no_zero_smul_divisors RatModule.noZeroSMulDivisors

end NoZeroSMulDivisors

-- Porting note: simp can prove this
--@[simp]
theorem Nat.smul_one_eq_coe {R : Type*} [Semiring R] (m : ℕ) : m • (1 : R) = ↑m := by
  rw [nsmul_eq_mul, mul_one]
  -- 🎉 no goals
#align nat.smul_one_eq_coe Nat.smul_one_eq_coe

-- Porting note: simp can prove this
--@[simp]
theorem Int.smul_one_eq_coe {R : Type*} [Ring R] (m : ℤ) : m • (1 : R) = ↑m := by
  rw [zsmul_eq_mul, mul_one]
  -- 🎉 no goals
#align int.smul_one_eq_coe Int.smul_one_eq_coe

assert_not_exists Multiset
