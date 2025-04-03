/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.GroupTheory.GroupAction.SubMulAction

#align_import algebra.module.submodule.basic from "leanprover-community/mathlib"@"8130e5155d637db35907c272de9aec9dc851c03a"

/-!

# Submodules of a module

In this file we define

* `Submodule R M` : a subset of a `Module` `M` that contains zero and is closed with respect to
  addition and scalar multiplication.

* `Subspace k M` : an abbreviation for `Submodule` assuming that `k` is a `Field`.

## Tags

submodule, subspace, linear map
-/


open Function

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] extends
  AddSubmonoid M, SubMulAction R M : Type v
#align submodule Submodule

/-- Reinterpret a `Submodule` as an `AddSubmonoid`. -/
add_decl_doc Submodule.toAddSubmonoid
#align submodule.to_add_submonoid Submodule.toAddSubmonoid

/-- Reinterpret a `Submodule` as a `SubMulAction`. -/
add_decl_doc Submodule.toSubMulAction
#align submodule.to_sub_mul_action Submodule.toSubMulAction

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

instance setLike : SetLike (Submodule R M) M where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h
#align submodule.set_like Submodule.setLike

instance addSubmonoidClass : AddSubmonoidClass (Submodule R M) M where
  zero_mem _ := AddSubmonoid.zero_mem' _
  add_mem := AddSubsemigroup.add_mem' _
#align submodule.add_submonoid_class Submodule.addSubmonoidClass

instance smulMemClass : SMulMemClass (Submodule R M) R M where
  smul_mem {s} c _ h := SubMulAction.smul_mem' s.toSubMulAction c h
#align submodule.smul_mem_class Submodule.smulMemClass

@[simp]
theorem mem_toAddSubmonoid (p : Submodule R M) (x : M) : x ∈ p.toAddSubmonoid ↔ x ∈ p :=
  Iff.rfl
#align submodule.mem_to_add_submonoid Submodule.mem_toAddSubmonoid

variable {p q : Submodule R M}

@[simp]
theorem mem_mk {S : AddSubmonoid M} {x : M} (h) : x ∈ (⟨S, h⟩ : Submodule R M) ↔ x ∈ S :=
  Iff.rfl
#align submodule.mem_mk Submodule.mem_mk

@[simp]
theorem coe_set_mk (S : AddSubmonoid M) (h) : ((⟨S, h⟩ : Submodule R M) : Set M) = S :=
  rfl
#align submodule.coe_set_mk Submodule.coe_set_mk

@[simp] theorem eta (h) : ({p with smul_mem' := h} : Submodule R M) = p :=
  rfl

-- Porting note: replaced `S ⊆ S' : Set` with `S ≤ S'`
@[simp]
theorem mk_le_mk {S S' : AddSubmonoid M} (h h') :
    (⟨S, h⟩ : Submodule R M) ≤ (⟨S', h'⟩ : Submodule R M) ↔ S ≤ S' :=
  Iff.rfl
#align submodule.mk_le_mk Submodule.mk_le_mk

@[ext]
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h
#align submodule.ext Submodule.ext

-- Porting note: adding this as the `simp`-normal form of `toSubMulAction_eq`
@[simp]
theorem carrier_inj : p.carrier = q.carrier ↔ p = q :=
  (SetLike.coe_injective (A := Submodule R M)).eq_iff

/-- Copy of a submodule with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (p : Submodule R M) (s : Set M) (hs : s = ↑p) : Submodule R M where
  carrier := s
  zero_mem' := by simpa [hs] using p.zero_mem'
  add_mem' := hs.symm ▸ p.add_mem'
  smul_mem' := by simpa [hs] using p.smul_mem'
#align submodule.copy Submodule.copy

@[simp]
theorem coe_copy (S : Submodule R M) (s : Set M) (hs : s = ↑S) : (S.copy s hs : Set M) = s :=
  rfl
#align submodule.coe_copy Submodule.coe_copy

theorem copy_eq (S : Submodule R M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align submodule.copy_eq Submodule.copy_eq

theorem toAddSubmonoid_injective : Injective (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  fun p q h => SetLike.ext'_iff.2 (show (p.toAddSubmonoid : Set M) = q from SetLike.ext'_iff.1 h)
#align submodule.to_add_submonoid_injective Submodule.toAddSubmonoid_injective

@[simp]
theorem toAddSubmonoid_eq : p.toAddSubmonoid = q.toAddSubmonoid ↔ p = q :=
  toAddSubmonoid_injective.eq_iff
#align submodule.to_add_submonoid_eq Submodule.toAddSubmonoid_eq

@[mono]
theorem toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  fun _ _ => id
#align submodule.to_add_submonoid_strict_mono Submodule.toAddSubmonoid_strictMono

theorem toAddSubmonoid_le : p.toAddSubmonoid ≤ q.toAddSubmonoid ↔ p ≤ q :=
  Iff.rfl
#align submodule.to_add_submonoid_le Submodule.toAddSubmonoid_le

@[mono]
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  toAddSubmonoid_strictMono.monotone
#align submodule.to_add_submonoid_mono Submodule.toAddSubmonoid_mono

@[simp]
theorem coe_toAddSubmonoid (p : Submodule R M) : (p.toAddSubmonoid : Set M) = p :=
  rfl
#align submodule.coe_to_add_submonoid Submodule.coe_toAddSubmonoid

theorem toSubMulAction_injective : Injective (toSubMulAction : Submodule R M → SubMulAction R M) :=
  fun p q h => SetLike.ext'_iff.2 (show (p.toSubMulAction : Set M) = q from SetLike.ext'_iff.1 h)
#align submodule.to_sub_mul_action_injective Submodule.toSubMulAction_injective

theorem toSubMulAction_eq : p.toSubMulAction = q.toSubMulAction ↔ p = q :=
  toSubMulAction_injective.eq_iff
#align submodule.to_sub_mul_action_eq Submodule.toSubMulAction_eq

@[mono]
theorem toSubMulAction_strictMono :
    StrictMono (toSubMulAction : Submodule R M → SubMulAction R M) := fun _ _ => id
#align submodule.to_sub_mul_action_strict_mono Submodule.toSubMulAction_strictMono

@[mono]
theorem toSubMulAction_mono : Monotone (toSubMulAction : Submodule R M → SubMulAction R M) :=
  toSubMulAction_strictMono.monotone
#align submodule.to_sub_mul_action_mono Submodule.toSubMulAction_mono

@[simp]
theorem coe_toSubMulAction (p : Submodule R M) : (p.toSubMulAction : Set M) = p :=
  rfl
#align submodule.coe_to_sub_mul_action Submodule.coe_toSubMulAction

end Submodule

namespace SMulMemClass

variable [Semiring R] [AddCommMonoid M] [Module R M] {A : Type*} [SetLike A M]
  [AddSubmonoidClass A M] [SMulMemClass A R M] (S' : A)

-- Prefer subclasses of `Module` over `SMulMemClass`.
/-- A submodule of a `Module` is a `Module`.  -/
instance (priority := 75) toModule : Module R S' :=
  Subtype.coe_injective.module R (AddSubmonoidClass.subtype S') (SetLike.val_smul S')
#align submodule_class.to_module SMulMemClass.toModule

/-- This can't be an instance because Lean wouldn't know how to find `R`, but we can still use
this to manually derive `Module` on specific types. -/
def toModule' (S R' R A : Type*) [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SetLike S A] [AddSubmonoidClass S A] [SMulMemClass S R A] (s : S) :
    Module R' s :=
  haveI : SMulMemClass S R' A := SMulMemClass.ofIsScalarTower S R' R A
  SMulMemClass.toModule s

end SMulMemClass

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

-- Porting note: removing `@[simp]` since it can already be proven
theorem mem_carrier : x ∈ p.carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl
#align submodule.mem_carrier Submodule.mem_carrier

@[simp]
protected theorem zero_mem : (0 : M) ∈ p :=
  zero_mem _
#align submodule.zero_mem Submodule.zero_mem

protected theorem add_mem (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p :=
  add_mem h₁ h₂
#align submodule.add_mem Submodule.add_mem

theorem smul_mem (r : R) (h : x ∈ p) : r • x ∈ p :=
  p.smul_mem' r h
#align submodule.smul_mem Submodule.smul_mem

theorem smul_of_tower_mem [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (h : x ∈ p) :
    r • x ∈ p :=
  p.toSubMulAction.smul_of_tower_mem r h
#align submodule.smul_of_tower_mem Submodule.smul_of_tower_mem

protected theorem sum_mem {t : Finset ι} {f : ι → M} : (∀ c ∈ t, f c ∈ p) → (∑ i ∈ t, f i) ∈ p :=
  sum_mem
#align submodule.sum_mem Submodule.sum_mem

theorem sum_smul_mem {t : Finset ι} {f : ι → M} (r : ι → R) (hyp : ∀ c ∈ t, f c ∈ p) :
    (∑ i ∈ t, r i • f i) ∈ p :=
  sum_mem fun i hi => smul_mem _ _ (hyp i hi)
#align submodule.sum_smul_mem Submodule.sum_smul_mem

@[simp]
theorem smul_mem_iff' [Group G] [MulAction G M] [SMul G R] [IsScalarTower G R M] (g : G) :
    g • x ∈ p ↔ x ∈ p :=
  p.toSubMulAction.smul_mem_iff' g
#align submodule.smul_mem_iff' Submodule.smul_mem_iff'

instance add : Add p :=
  ⟨fun x y => ⟨x.1 + y.1, add_mem x.2 y.2⟩⟩
#align submodule.has_add Submodule.add

instance zero : Zero p :=
  ⟨⟨0, zero_mem _⟩⟩
#align submodule.has_zero Submodule.zero

instance inhabited : Inhabited p :=
  ⟨0⟩
#align submodule.inhabited Submodule.inhabited

instance smul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S p :=
  ⟨fun c x => ⟨c • x.1, smul_of_tower_mem _ c x.2⟩⟩
#align submodule.has_smul Submodule.smul

instance isScalarTower [SMul S R] [SMul S M] [IsScalarTower S R M] : IsScalarTower S R p :=
  p.toSubMulAction.isScalarTower
#align submodule.is_scalar_tower Submodule.isScalarTower

instance isScalarTower' {S' : Type*} [SMul S R] [SMul S M] [SMul S' R] [SMul S' M] [SMul S S']
    [IsScalarTower S' R M] [IsScalarTower S S' M] [IsScalarTower S R M] : IsScalarTower S S' p :=
  p.toSubMulAction.isScalarTower'
#align submodule.is_scalar_tower' Submodule.isScalarTower'

instance isCentralScalar [SMul S R] [SMul S M] [IsScalarTower S R M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M]
    [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] : IsCentralScalar S p :=
  p.toSubMulAction.isCentralScalar
#align submodule.is_central_scalar Submodule.isCentralScalar

protected theorem nonempty : (p : Set M).Nonempty :=
  ⟨0, p.zero_mem⟩
#align submodule.nonempty Submodule.nonempty

theorem mk_eq_zero {x} (h : x ∈ p) : (⟨x, h⟩ : p) = 0 ↔ x = 0 :=
  Subtype.ext_iff_val
#align submodule.mk_eq_zero Submodule.mk_eq_zero

variable {p}

@[norm_cast] -- Porting note: removed `@[simp]` because this follows from `ZeroMemClass.coe_zero`
theorem coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0 :=
  (SetLike.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)
#align submodule.coe_eq_zero Submodule.coe_eq_zero

@[simp, norm_cast]
theorem coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y :=
  rfl
#align submodule.coe_add Submodule.coe_add

@[simp, norm_cast]
theorem coe_zero : ((0 : p) : M) = 0 :=
  rfl
#align submodule.coe_zero Submodule.coe_zero

@[norm_cast]
theorem coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • (x : M) :=
  rfl
#align submodule.coe_smul Submodule.coe_smul

@[simp, norm_cast]
theorem coe_smul_of_tower [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (x : p) :
    ((r • x : p) : M) = r • (x : M) :=
  rfl
#align submodule.coe_smul_of_tower Submodule.coe_smul_of_tower

@[norm_cast] -- Porting note: removed `@[simp]` because this is now structure eta
theorem coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x :=
  rfl
#align submodule.coe_mk Submodule.coe_mk

-- Porting note: removed `@[simp]` because this is exactly `SetLike.coe_mem`
theorem coe_mem (x : p) : (x : M) ∈ p :=
  x.2
#align submodule.coe_mem Submodule.coe_mem

variable (p)

instance addCommMonoid : AddCommMonoid p :=
  { p.toAddSubmonoid.toAddCommMonoid with }
#align submodule.add_comm_monoid Submodule.addCommMonoid

instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] : Module S p :=
  { (show MulAction S p from p.toSubMulAction.mulAction') with
    smul_zero := fun a => by ext; simp
    zero_smul := fun a => by ext; simp
    add_smul := fun a b x => by ext; simp [add_smul]
    smul_add := fun a x y => by ext; simp [smul_add] }
#align submodule.module' Submodule.module'

instance module : Module R p :=
  p.module'
#align submodule.module Submodule.module

instance noZeroSMulDivisors [NoZeroSMulDivisors R M] : NoZeroSMulDivisors R p :=
  ⟨fun {c} {x : p} h =>
    have : c = 0 ∨ (x : M) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg Subtype.val h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩
#align submodule.no_zero_smul_divisors Submodule.noZeroSMulDivisors

section AddAction

/-! ### Additive actions by `Submodule`s
These instances transfer the action by an element `m : M` of an `R`-module `M` written as `m +ᵥ a`
onto the action by an element `s : S` of a submodule `S : Submodule R M` such that
`s +ᵥ a = (s : M) +ᵥ a`.
These instances work particularly well in conjunction with `AddGroup.toAddAction`, enabling
`s +ᵥ m` as an alias for `↑s + m`.
-/


variable {α β : Type*}

instance [VAdd M α] : VAdd p α :=
  p.toAddSubmonoid.vadd

instance vaddCommClass [VAdd M β] [VAdd α β] [VAddCommClass M α β] : VAddCommClass p α β :=
  ⟨fun a => (vadd_comm (a : M) : _)⟩
#align submodule.vadd_comm_class Submodule.vaddCommClass

instance [VAdd M α] [FaithfulVAdd M α] : FaithfulVAdd p α :=
  ⟨fun h => Subtype.ext <| eq_of_vadd_eq_vadd h⟩

variable {p}

theorem vadd_def [VAdd M α] (g : p) (m : α) : g +ᵥ m = (g : M) +ᵥ m :=
  rfl
#align submodule.vadd_def Submodule.vadd_def

end AddAction

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M]
variable {module_M : Module R M}
variable (p p' : Submodule R M)
variable {r : R} {x y : M}

instance addSubgroupClass [Module R M] : AddSubgroupClass (Submodule R M) M :=
  { Submodule.addSubmonoidClass with neg_mem := fun p {_} => p.toSubMulAction.neg_mem }
#align submodule.add_subgroup_class Submodule.addSubgroupClass

protected theorem neg_mem (hx : x ∈ p) : -x ∈ p :=
  neg_mem hx
#align submodule.neg_mem Submodule.neg_mem

/-- Reinterpret a submodule as an additive subgroup. -/
def toAddSubgroup : AddSubgroup M :=
  { p.toAddSubmonoid with neg_mem' := fun {_} => p.neg_mem }
#align submodule.to_add_subgroup Submodule.toAddSubgroup

@[simp]
theorem coe_toAddSubgroup : (p.toAddSubgroup : Set M) = p :=
  rfl
#align submodule.coe_to_add_subgroup Submodule.coe_toAddSubgroup

@[simp]
theorem mem_toAddSubgroup : x ∈ p.toAddSubgroup ↔ x ∈ p :=
  Iff.rfl
#align submodule.mem_to_add_subgroup Submodule.mem_toAddSubgroup

theorem toAddSubgroup_injective : Injective (toAddSubgroup : Submodule R M → AddSubgroup M)
  | _, _, h => SetLike.ext (SetLike.ext_iff.1 h : _)
#align submodule.to_add_subgroup_injective Submodule.toAddSubgroup_injective

@[simp]
theorem toAddSubgroup_eq : p.toAddSubgroup = p'.toAddSubgroup ↔ p = p' :=
  toAddSubgroup_injective.eq_iff
#align submodule.to_add_subgroup_eq Submodule.toAddSubgroup_eq

@[mono]
theorem toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Submodule R M → AddSubgroup M) :=
  fun _ _ => id
#align submodule.to_add_subgroup_strict_mono Submodule.toAddSubgroup_strictMono

theorem toAddSubgroup_le : p.toAddSubgroup ≤ p'.toAddSubgroup ↔ p ≤ p' :=
  Iff.rfl
#align submodule.to_add_subgroup_le Submodule.toAddSubgroup_le

@[mono]
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : Submodule R M → AddSubgroup M) :=
  toAddSubgroup_strictMono.monotone
#align submodule.to_add_subgroup_mono Submodule.toAddSubgroup_mono

protected theorem sub_mem : x ∈ p → y ∈ p → x - y ∈ p :=
  sub_mem
#align submodule.sub_mem Submodule.sub_mem

protected theorem neg_mem_iff : -x ∈ p ↔ x ∈ p :=
  neg_mem_iff
#align submodule.neg_mem_iff Submodule.neg_mem_iff

protected theorem add_mem_iff_left : y ∈ p → (x + y ∈ p ↔ x ∈ p) :=
  add_mem_cancel_right
#align submodule.add_mem_iff_left Submodule.add_mem_iff_left

protected theorem add_mem_iff_right : x ∈ p → (x + y ∈ p ↔ y ∈ p) :=
  add_mem_cancel_left
#align submodule.add_mem_iff_right Submodule.add_mem_iff_right

protected theorem coe_neg (x : p) : ((-x : p) : M) = -x :=
  NegMemClass.coe_neg _
#align submodule.coe_neg Submodule.coe_neg

protected theorem coe_sub (x y : p) : (↑(x - y) : M) = ↑x - ↑y :=
  AddSubgroupClass.coe_sub _ _
#align submodule.coe_sub Submodule.coe_sub

theorem sub_mem_iff_left (hy : y ∈ p) : x - y ∈ p ↔ x ∈ p := by
  rw [sub_eq_add_neg, p.add_mem_iff_left (p.neg_mem hy)]
#align submodule.sub_mem_iff_left Submodule.sub_mem_iff_left

theorem sub_mem_iff_right (hx : x ∈ p) : x - y ∈ p ↔ y ∈ p := by
  rw [sub_eq_add_neg, p.add_mem_iff_right hx, p.neg_mem_iff]
#align submodule.sub_mem_iff_right Submodule.sub_mem_iff_right

instance addCommGroup : AddCommGroup p :=
  { p.toAddSubgroup.toAddCommGroup with }
#align submodule.add_comm_group Submodule.addCommGroup

-- See `neg_coe_set`
theorem neg_coe : -(p : Set M) = p :=
  Set.ext fun _ => p.neg_mem_iff
#align submodule.neg_coe Submodule.neg_coe

end AddCommGroup

section IsDomain

variable [Ring R] [IsDomain R]
variable [AddCommGroup M] [Module R M] {b : ι → M}

theorem not_mem_of_ortho {x : M} {N : Submodule R M}
    (ortho : ∀ (c : R), ∀ y ∈ N, c • x + y = (0 : M) → c = 0) : x ∉ N := by
  intro hx
  simpa using ortho (-1) x hx
#align submodule.not_mem_of_ortho Submodule.not_mem_of_ortho

theorem ne_zero_of_ortho {x : M} {N : Submodule R M}
    (ortho : ∀ (c : R), ∀ y ∈ N, c • x + y = (0 : M) → c = 0) : x ≠ 0 :=
  mt (fun h => show x ∈ N from h.symm ▸ N.zero_mem) (not_mem_of_ortho ortho)
#align submodule.ne_zero_of_ortho Submodule.ne_zero_of_ortho

end IsDomain

end Submodule

namespace SubmoduleClass

instance (priority := 75) module' {T : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
    [Module R M] [SMul S R] [Module S M] [IsScalarTower S R M] [SetLike T M] [AddSubmonoidClass T M]
    [SMulMemClass T R M] (t : T) : Module S t where
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  zero_smul _ := by ext; simp
  add_smul _ _ _ := by ext; simp [add_smul]
  smul_add _ _ _ := by ext; simp [smul_add]

instance (priority := 75) module [Semiring R] [AddCommMonoid M] [Module R M] [SetLike S M]
    [AddSubmonoidClass S M] [SMulMemClass S R M] (s : S) : Module R s :=
  module' s

end SubmoduleClass

namespace Submodule

variable [DivisionSemiring S] [Semiring R] [AddCommMonoid M] [Module R M]
variable [SMul S R] [Module S M] [IsScalarTower S R M]
variable (p : Submodule R M) {s : S} {x y : M}

theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
  p.toSubMulAction.smul_mem_iff s0
#align submodule.smul_mem_iff Submodule.smul_mem_iff

end Submodule

/-- Subspace of a vector space. Defined to equal `Submodule`. -/
abbrev Subspace (R : Type u) (M : Type v) [DivisionRing R] [AddCommGroup M] [Module R M] :=
  Submodule R M
#align subspace Subspace
