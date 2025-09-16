/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Algebra.Group.Submonoid.Basic

/-!

# Submodules of a module

In this file we define

* `Submodule R M` : a subset of a `Module` `M` that contains zero and is closed with respect to
  addition and scalar multiplication.

* `Subspace k M` : an abbreviation for `Submodule` assuming that `k` is a `Field`.

## Tags

submodule, subspace, linear map
-/

assert_not_exists DivisionRing

open Function

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v
    extends AddSubmonoid M, SubMulAction R M

/-- Reinterpret a `Submodule` as an `AddSubmonoid`. -/
add_decl_doc Submodule.toAddSubmonoid

/-- Reinterpret a `Submodule` as a `SubMulAction`. -/
add_decl_doc Submodule.toSubMulAction

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

instance setLike : SetLike (Submodule R M) M where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

initialize_simps_projections Submodule (carrier → coe, as_prefix coe)

@[simp] lemma carrier_eq_coe (s : Submodule R M) : s.carrier = s := rfl

/-- The actual `Submodule` obtained from an element of a `SMulMemClass` and `AddSubmonoidClass`. -/
@[simps]
def ofClass {S R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [SetLike S M]
    [AddSubmonoidClass S M] [SMulMemClass S R M] (s : S) : Submodule R M where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' := SMulMemClass.smul_mem

instance (priority := 100) : CanLift (Set M) (Submodule R M) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ ∀ (r : R) {x}, x ∈ s → r • x ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        smul_mem' := h.2.2 },
      rfl ⟩

instance addSubmonoidClass : AddSubmonoidClass (Submodule R M) M where
  zero_mem _ := AddSubmonoid.zero_mem' _
  add_mem := AddSubsemigroup.add_mem' _

instance smulMemClass : SMulMemClass (Submodule R M) R M where
  smul_mem {s} c _ h := SubMulAction.smul_mem' s.toSubMulAction c h

@[simp]
theorem mem_toAddSubmonoid (p : Submodule R M) (x : M) : x ∈ p.toAddSubmonoid ↔ x ∈ p :=
  Iff.rfl

variable {p q : Submodule R M}

@[simp]
theorem mem_mk {S : AddSubmonoid M} {x : M} (h) : x ∈ (⟨S, h⟩ : Submodule R M) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_set_mk (S : AddSubmonoid M) (h) : ((⟨S, h⟩ : Submodule R M) : Set M) = S :=
  rfl

@[simp] theorem eta (h) : ({p with smul_mem' := h} : Submodule R M) = p :=
  rfl

@[simp]
theorem mk_le_mk {S S' : AddSubmonoid M} (h h') :
    (⟨S, h⟩ : Submodule R M) ≤ (⟨S', h'⟩ : Submodule R M) ↔ S ≤ S' :=
  Iff.rfl

@[ext]
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h

@[deprecated SetLike.coe_set_eq (since := "2025-04-20")]
theorem carrier_inj : p.carrier = q.carrier ↔ p = q :=
  (SetLike.coe_injective (A := Submodule R M)).eq_iff

/-- Copy of a submodule with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps]
protected def copy (p : Submodule R M) (s : Set M) (hs : s = ↑p) : Submodule R M where
  carrier := s
  zero_mem' := by simp [hs]
  add_mem' := hs.symm ▸ p.add_mem'
  smul_mem' := by simpa [hs] using p.smul_mem'

theorem copy_eq (S : Submodule R M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem toAddSubmonoid_injective : Injective (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  fun p q h => SetLike.ext'_iff.2 (show (p.toAddSubmonoid : Set M) = q from SetLike.ext'_iff.1 h)

@[simp]
theorem toAddSubmonoid_inj : p.toAddSubmonoid = q.toAddSubmonoid ↔ p = q :=
  toAddSubmonoid_injective.eq_iff

@[simp]
theorem coe_toAddSubmonoid (p : Submodule R M) : (p.toAddSubmonoid : Set M) = p :=
  rfl

theorem toSubMulAction_injective : Injective (toSubMulAction : Submodule R M → SubMulAction R M) :=
  fun p q h => SetLike.ext'_iff.2 (show (p.toSubMulAction : Set M) = q from SetLike.ext'_iff.1 h)

theorem toSubMulAction_inj : p.toSubMulAction = q.toSubMulAction ↔ p = q :=
  toSubMulAction_injective.eq_iff

@[simp]
theorem coe_toSubMulAction (p : Submodule R M) : (p.toSubMulAction : Set M) = p :=
  rfl

end Submodule

namespace SMulMemClass

variable [Semiring R] [AddCommMonoid M] [Module R M] {A : Type*} [SetLike A M]
  [AddSubmonoidClass A M] [SMulMemClass A R M] (S' : A)

-- Prefer subclasses of `Module` over `SMulMemClass`.
/-- A submodule of a `Module` is a `Module`. -/
instance (priority := 75) toModule : Module R S' := fast_instance%
  Subtype.coe_injective.module R (AddSubmonoidClass.subtype S') (SetLike.val_smul S')

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

theorem mem_carrier : x ∈ p.carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl

protected theorem zero_mem : (0 : M) ∈ p :=
  zero_mem _

protected theorem add_mem (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p :=
  add_mem h₁ h₂

theorem smul_mem (r : R) (h : x ∈ p) : r • x ∈ p :=
  p.smul_mem' r h

theorem smul_of_tower_mem [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (h : x ∈ p) :
    r • x ∈ p :=
  p.toSubMulAction.smul_of_tower_mem r h

@[simp]
theorem smul_mem_iff' [Group G] [MulAction G M] [SMul G R] [IsScalarTower G R M] (g : G) :
    g • x ∈ p ↔ x ∈ p :=
  p.toSubMulAction.smul_mem_iff' g

@[simp]
lemma smul_mem_iff'' [Invertible r] :
    r • x ∈ p ↔ x ∈ p := by
  refine ⟨fun h ↦ ?_, p.smul_mem r⟩
  rw [← invOf_smul_smul r x]
  exact p.smul_mem _ h

lemma smul_mem_iff_of_isUnit (hr : IsUnit r) :
    r • x ∈ p ↔ x ∈ p :=
  let _ : Invertible r := hr.invertible
  smul_mem_iff'' p

instance add : Add p :=
  ⟨fun x y => ⟨x.1 + y.1, add_mem x.2 y.2⟩⟩

instance zero : Zero p :=
  ⟨⟨0, zero_mem _⟩⟩

instance inhabited : Inhabited p :=
  ⟨0⟩

instance smul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S p :=
  ⟨fun c x => ⟨c • x.1, smul_of_tower_mem _ c x.2⟩⟩

instance isScalarTower [SMul S R] [SMul S M] [IsScalarTower S R M] : IsScalarTower S R p :=
  p.toSubMulAction.isScalarTower

instance isScalarTower' {S' : Type*} [SMul S R] [SMul S M] [SMul S' R] [SMul S' M] [SMul S S']
    [IsScalarTower S' R M] [IsScalarTower S S' M] [IsScalarTower S R M] : IsScalarTower S S' p :=
  p.toSubMulAction.isScalarTower'

protected theorem nonempty : (p : Set M).Nonempty :=
  ⟨0, p.zero_mem⟩

@[simp]
theorem mk_eq_zero {x} (h : x ∈ p) : (⟨x, h⟩ : p) = 0 ↔ x = 0 :=
  Subtype.ext_iff

variable {p}

@[norm_cast]
theorem coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0 :=
  (SetLike.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)

@[simp, norm_cast]
theorem coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : p) : M) = 0 :=
  rfl

@[norm_cast]
theorem coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • (x : M) :=
  rfl

@[simp, norm_cast]
theorem coe_smul_of_tower [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (x : p) :
    ((r • x : p) : M) = r • (x : M) :=
  rfl

@[norm_cast]
theorem coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x :=
  rfl

theorem coe_mem (x : p) : (x : M) ∈ p :=
  x.2

variable (p)

instance addCommMonoid : AddCommMonoid p := fast_instance%
  { p.toAddSubmonoid.toAddCommMonoid with }

instance isLeftCancelAdd [IsLeftCancelAdd M] : IsLeftCancelAdd p :=
  p.toAddSubmonoid.isLeftCancelAdd

instance isRightCancelAdd [IsRightCancelAdd M] : IsRightCancelAdd p :=
  p.toAddSubmonoid.isRightCancelAdd

instance isCancelAdd [IsCancelAdd M] : IsCancelAdd p where

instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S p := fast_instance%
  { (show MulAction S p from p.toSubMulAction.mulAction') with
    smul_zero := fun a => by ext; simp
    zero_smul := fun a => by ext; simp
    add_smul := fun a b x => by ext; simp [add_smul]
    smul_add := fun a x y => by ext; simp [smul_add] }

instance module : Module R p :=
  p.module'

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M]
variable {module_M : Module R M}
variable (p p' : Submodule R M)
variable {r : R} {x y : M}

instance addSubgroupClass [Module R M] : AddSubgroupClass (Submodule R M) M :=
  { Submodule.addSubmonoidClass with neg_mem := fun p {_} => p.toSubMulAction.neg_mem }

protected theorem neg_mem (hx : x ∈ p) : -x ∈ p :=
  neg_mem hx

/-- Reinterpret a submodule as an additive subgroup. -/
def toAddSubgroup : AddSubgroup M :=
  { p.toAddSubmonoid with neg_mem' := fun {_} => p.neg_mem }

@[simp]
theorem coe_toAddSubgroup : (p.toAddSubgroup : Set M) = p :=
  rfl

@[simp]
theorem mem_toAddSubgroup : x ∈ p.toAddSubgroup ↔ x ∈ p :=
  Iff.rfl

theorem toAddSubgroup_injective : Injective (toAddSubgroup : Submodule R M → AddSubgroup M)
  | _, _, h => SetLike.ext (SetLike.ext_iff.1 h :)

@[simp]
theorem toAddSubgroup_inj : p.toAddSubgroup = p'.toAddSubgroup ↔ p = p' :=
  toAddSubgroup_injective.eq_iff

protected theorem sub_mem : x ∈ p → y ∈ p → x - y ∈ p :=
  sub_mem

protected theorem neg_mem_iff : -x ∈ p ↔ x ∈ p :=
  neg_mem_iff

protected theorem add_mem_iff_left : y ∈ p → (x + y ∈ p ↔ x ∈ p) :=
  add_mem_cancel_right

protected theorem add_mem_iff_right : x ∈ p → (x + y ∈ p ↔ y ∈ p) :=
  add_mem_cancel_left

protected theorem coe_neg (x : p) : ((-x : p) : M) = -x :=
  NegMemClass.coe_neg _

protected theorem coe_sub (x y : p) : (↑(x - y) : M) = ↑x - ↑y :=
  AddSubgroupClass.coe_sub _ _

theorem sub_mem_iff_left (hy : y ∈ p) : x - y ∈ p ↔ x ∈ p := by
  rw [sub_eq_add_neg, p.add_mem_iff_left (p.neg_mem hy)]

theorem sub_mem_iff_right (hx : x ∈ p) : x - y ∈ p ↔ y ∈ p := by
  rw [sub_eq_add_neg, p.add_mem_iff_right hx, p.neg_mem_iff]

instance addCommGroup : AddCommGroup p := fast_instance%
  { p.toAddSubgroup.toAddCommGroup with }

end AddCommGroup

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
