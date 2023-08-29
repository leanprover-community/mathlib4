/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Hom.GroupAction
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Basic

#align_import group_theory.group_action.sub_mul_action from "leanprover-community/mathlib"@"feb99064803fd3108e37c18b0f77d0a8344677a3"

/-!

# Sets invariant to a `MulAction`

In this file we define `SubMulAction R M`; a subset of a `MulAction R M` which is closed with
respect to scalar multiplication.

For most uses, typically `Submodule R M` is more powerful.

## Main definitions

* `SubMulAction.mulAction` - the `MulAction R M` transferred to the subtype.
* `SubMulAction.mulAction'` - the `MulAction S M` transferred to the subtype when
  `IsScalarTower S R M`.
* `SubMulAction.isScalarTower` - the `IsScalarTower S R M` transferred to the subtype.

## Tags

submodule, mul_action
-/


open Function

universe u u' u'' v

variable {S : Type u'} {T : Type u''} {R : Type u} {M : Type v}

/-- `SMulMemClass S R M` says `S` is a type of subsets `s ≤ M` that are closed under the
scalar action of `R` on `M`.

Note that only `R` is marked as an `outParam` here, since `M` is supplied by the `SetLike`
class instead.
-/
class SMulMemClass (S : Type*) (R : outParam <| Type*) (M : Type*) [SMul R M] [SetLike S M] :
    Prop where
  /-- Multiplication by a scalar on an element of the set remains in the set. -/
  smul_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r • m ∈ s
#align smul_mem_class SMulMemClass

/-- `VAddMemClass S R M` says `S` is a type of subsets `s ≤ M` that are closed under the
additive action of `R` on `M`.

Note that only `R` is marked as an `outParam` here, since `M` is supplied by the `SetLike`
class instead. -/
class VAddMemClass (S : Type*) (R : outParam <| Type*) (M : Type*) [VAdd R M] [SetLike S M] :
    Prop where
  /-- Addition by a scalar with an element of the set remains in the set. -/
  vadd_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r +ᵥ m ∈ s
#align vadd_mem_class VAddMemClass

attribute [to_additive] SMulMemClass

namespace SetLike

variable [SMul R M] [SetLike S M] [hS : SMulMemClass S R M] (s : S)

open SMulMemClass

-- lower priority so other instances are found first
/-- A subset closed under the scalar action inherits that action. -/
@[to_additive "A subset closed under the additive action inherits that action."]
instance (priority := 900) smul : SMul R s :=
  ⟨fun r x => ⟨r • x.1, smul_mem r x.2⟩⟩
#align set_like.has_smul SetLike.smul
#align set_like.has_vadd SetLike.vadd

/-- This can't be an instance because Lean wouldn't know how to find `N`, but we can still use
this to manually derive `SMulMemClass` on specific types. -/
theorem _root_.SMulMemClass.ofIsScalarTower (S M N α : Type*) [SetLike S α] [SMul M N]
  [SMul M α] [Monoid N] [MulAction N α] [SMulMemClass S N α] [IsScalarTower M N α] :
  SMulMemClass S M α :=
{ smul_mem := fun m a ha => smul_one_smul N m a ▸ SMulMemClass.smul_mem _ ha }

-- Porting note: TODO lower priority not actually there
-- lower priority so later simp lemmas are used first; to appease simp_nf
@[to_additive (attr := simp, norm_cast)]
protected theorem val_smul (r : R) (x : s) : (↑(r • x) : M) = r • (x : M) :=
  rfl
#align set_like.coe_smul SetLike.val_smul
#align set_like.coe_vadd SetLike.val_vadd

-- Porting note: TODO lower priority not actually there
-- lower priority so later simp lemmas are used first; to appease simp_nf
@[to_additive (attr := simp)]
theorem mk_smul_mk (r : R) (x : M) (hx : x ∈ s) : r • (⟨x, hx⟩ : s) = ⟨r • x, smul_mem r hx⟩ :=
  rfl
#align set_like.mk_smul_mk SetLike.mk_smul_mk
#align set_like.mk_vadd_mk SetLike.mk_vadd_mk

@[to_additive]
theorem smul_def (r : R) (x : s) : r • x = ⟨r • x, smul_mem r x.2⟩ :=
  rfl
#align set_like.smul_def SetLike.smul_def
#align set_like.vadd_def SetLike.vadd_def

@[simp]
theorem forall_smul_mem_iff {R M S : Type*} [Monoid R] [MulAction R M] [SetLike S M]
    [SMulMemClass S R M] {N : S} {x : M} : (∀ a : R, a • x ∈ N) ↔ x ∈ N :=
  ⟨fun h => by simpa using h 1, fun h a => SMulMemClass.smul_mem a h⟩
               -- 🎉 no goals
#align set_like.forall_smul_mem_iff SetLike.forall_smul_mem_iff

end SetLike

/-- A SubMulAction is a set which is closed under scalar multiplication.  -/
structure SubMulAction (R : Type u) (M : Type v) [SMul R M] : Type v where
  /-- The underlying set of a `SubMulAction`. -/
  carrier : Set M
  /-- The carrier set is closed under scalar multiplication. -/
  smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier
#align sub_mul_action SubMulAction

namespace SubMulAction

variable [SMul R M]

instance : SetLike (SubMulAction R M) M :=
  ⟨SubMulAction.carrier, fun p q h => by cases p; cases q; congr ⟩
                                         -- ⊢ { carrier := carrier✝, smul_mem' := smul_mem'✝ } = q
                                                  -- ⊢ { carrier := carrier✝¹, smul_mem' := smul_mem'✝¹ } = { carrier := carrier✝,  …
                                                           -- 🎉 no goals

instance : SMulMemClass (SubMulAction R M) R M where smul_mem := smul_mem' _

@[simp]
theorem mem_carrier {p : SubMulAction R M} {x : M} : x ∈ p.carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl
#align sub_mul_action.mem_carrier SubMulAction.mem_carrier

@[ext]
theorem ext {p q : SubMulAction R M} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h
#align sub_mul_action.ext SubMulAction.ext

/-- Copy of a sub_mul_action with a new `carrier` equal to the old one. Useful to fix definitional
equalities.-/
protected def copy (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : SubMulAction R M
    where
  carrier := s
  smul_mem' := hs.symm ▸ p.smul_mem'
#align sub_mul_action.copy SubMulAction.copy

@[simp]
theorem coe_copy (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : (p.copy s hs : Set M) = s :=
  rfl
#align sub_mul_action.coe_copy SubMulAction.coe_copy

theorem copy_eq (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs
#align sub_mul_action.copy_eq SubMulAction.copy_eq

instance : Bot (SubMulAction R M) where
  bot :=
    { carrier := ∅
      smul_mem' := fun _c h => Set.not_mem_empty h }

instance : Inhabited (SubMulAction R M) :=
  ⟨⊥⟩

end SubMulAction

namespace SubMulAction

section SMul

variable [SMul R M]

variable (p : SubMulAction R M)

variable {r : R} {x : M}

theorem smul_mem (r : R) (h : x ∈ p) : r • x ∈ p :=
  p.smul_mem' r h
#align sub_mul_action.smul_mem SubMulAction.smul_mem

instance : SMul R p where smul c x := ⟨c • x.1, smul_mem _ c x.2⟩

variable {p}

@[simp, norm_cast]
theorem val_smul (r : R) (x : p) : (↑(r • x) : M) = r • (x : M) :=
  rfl
#align sub_mul_action.coe_smul SubMulAction.val_smul

-- porting note: no longer needed because of defeq structure eta
#noalign sub_mul_action.coe_mk

variable (p)

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →[R] M := by refine' { toFun := Subtype.val.. }; simp [val_smul]
                                       -- ⊢ ∀ (m : R) (x : { x // x ∈ p }), ↑(m • x) = m • ↑x
                                                                           -- 🎉 no goals
#align sub_mul_action.subtype SubMulAction.subtype

@[simp]
theorem subtype_apply (x : p) : p.subtype x = x :=
  rfl
#align sub_mul_action.subtype_apply SubMulAction.subtype_apply

theorem subtype_eq_val : (SubMulAction.subtype p : p → M) = Subtype.val :=
  rfl
#align sub_mul_action.subtype_eq_val SubMulAction.subtype_eq_val

end SMul

namespace SMulMemClass

variable [Monoid R] [MulAction R M] {A : Type*} [SetLike A M]

variable [hA : SMulMemClass A R M] (S' : A)

-- Prefer subclasses of `MulAction` over `SMulMemClass`.
/-- A `SubMulAction` of a `MulAction` is a `MulAction`.  -/
instance (priority := 75) toMulAction : MulAction R S' :=
  Subtype.coe_injective.mulAction Subtype.val (SetLike.val_smul S')
#align sub_mul_action.smul_mem_class.to_mul_action SubMulAction.SMulMemClass.toMulAction

/-- The natural `MulActionHom` over `R` from a `SubMulAction` of `M` to `M`. -/
protected def subtype : S' →[R] M :=
  ⟨Subtype.val, fun _ _ => rfl⟩
#align sub_mul_action.smul_mem_class.subtype SubMulAction.SMulMemClass.subtype

@[simp]
protected theorem coeSubtype : (SMulMemClass.subtype S' : S' → M) = Subtype.val :=
  rfl
#align sub_mul_action.smul_mem_class.coe_subtype SubMulAction.SMulMemClass.coeSubtype

end SMulMemClass

section MulActionMonoid

variable [Monoid R] [MulAction R M]

section

variable [SMul S R] [SMul S M] [IsScalarTower S R M]

variable (p : SubMulAction R M)

theorem smul_of_tower_mem (s : S) {x : M} (h : x ∈ p) : s • x ∈ p := by
  rw [← one_smul R x, ← smul_assoc]
  -- ⊢ (s • 1) • x ∈ p
  exact p.smul_mem _ h
  -- 🎉 no goals
#align sub_mul_action.smul_of_tower_mem SubMulAction.smul_of_tower_mem

instance smul' : SMul S p where smul c x := ⟨c • x.1, smul_of_tower_mem _ c x.2⟩
#align sub_mul_action.has_smul' SubMulAction.smul'

instance isScalarTower : IsScalarTower S R p where
  smul_assoc s r x := Subtype.ext <| smul_assoc s r (x : M)
#align sub_mul_action.is_scalar_tower SubMulAction.isScalarTower

instance isScalarTower' {S' : Type*} [SMul S' R] [SMul S' S] [SMul S' M] [IsScalarTower S' R M]
    [IsScalarTower S' S M] : IsScalarTower S' S p
    where smul_assoc s r x := Subtype.ext <| smul_assoc s r (x : M)
#align sub_mul_action.is_scalar_tower' SubMulAction.isScalarTower'

@[simp, norm_cast]
theorem val_smul_of_tower (s : S) (x : p) : ((s • x : p) : M) = s • (x : M) :=
  rfl
#align sub_mul_action.coe_smul_of_tower SubMulAction.val_smul_of_tower

@[simp]
theorem smul_mem_iff' {G} [Group G] [SMul G R] [MulAction G M] [IsScalarTower G R M] (g : G)
    {x : M} : g • x ∈ p ↔ x ∈ p :=
  ⟨fun h => inv_smul_smul g x ▸ p.smul_of_tower_mem g⁻¹ h, p.smul_of_tower_mem g⟩
#align sub_mul_action.smul_mem_iff' SubMulAction.smul_mem_iff'

instance isCentralScalar [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
    [IsCentralScalar S M] :
    IsCentralScalar S p where
  op_smul_eq_smul r x := Subtype.ext <| op_smul_eq_smul r (x : M)

end

section

variable [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]

variable (p : SubMulAction R M)

/-- If the scalar product forms a `MulAction`, then the subset inherits this action -/
instance mulAction' : MulAction S p where
  smul := (· • ·)
  one_smul x := Subtype.ext <| one_smul _ (x : M)
  mul_smul c₁ c₂ x := Subtype.ext <| mul_smul c₁ c₂ (x : M)
#align sub_mul_action.mul_action' SubMulAction.mulAction'

instance mulAction : MulAction R p :=
  p.mulAction'
#align sub_mul_action.mul_action SubMulAction.mulAction

end

/-- Orbits in a `SubMulAction` coincide with orbits in the ambient space. -/
theorem val_image_orbit {p : SubMulAction R M} (m : p) :
    Subtype.val '' MulAction.orbit R m = MulAction.orbit R (m : M) :=
  (Set.range_comp _ _).symm
#align sub_mul_action.coe_image_orbit SubMulAction.val_image_orbit

/- -- Previously, the relatively useless :
lemma orbit_of_sub_mul {p : SubMulAction R M} (m : p) :
  (mul_action.orbit R m : set M) = MulAction.orbit R (m : M) := rfl
-/
/-- Stabilizers in monoid SubMulAction coincide with stabilizers in the ambient space -/
theorem stabilizer_of_subMul.submonoid {p : SubMulAction R M} (m : p) :
    MulAction.Stabilizer.submonoid R m = MulAction.Stabilizer.submonoid R (m : M) := by
  ext
  -- ⊢ x✝ ∈ MulAction.Stabilizer.submonoid R m ↔ x✝ ∈ MulAction.Stabilizer.submonoi …
  simp only [MulAction.mem_stabilizer_submonoid_iff, ← SubMulAction.val_smul, SetLike.coe_eq_coe]
  -- 🎉 no goals
#align sub_mul_action.stabilizer_of_sub_mul.submonoid SubMulAction.stabilizer_of_subMul.submonoid

end MulActionMonoid

section MulActionGroup

variable [Group R] [MulAction R M]

/-- Stabilizers in group SubMulAction coincide with stabilizers in the ambient space -/
theorem stabilizer_of_subMul {p : SubMulAction R M} (m : p) :
    MulAction.stabilizer R m = MulAction.stabilizer R (m : M) := by
  rw [← Subgroup.toSubmonoid_eq]
  -- ⊢ (MulAction.stabilizer R m).toSubmonoid = (MulAction.stabilizer R ↑m).toSubmo …
  exact stabilizer_of_subMul.submonoid m
  -- 🎉 no goals
#align sub_mul_action.stabilizer_of_sub_mul SubMulAction.stabilizer_of_subMul

end MulActionGroup

section Module

variable [Semiring R] [AddCommMonoid M]

variable [Module R M]

variable (p : SubMulAction R M)

theorem zero_mem (h : (p : Set M).Nonempty) : (0 : M) ∈ p :=
  let ⟨x, hx⟩ := h
  zero_smul R (x : M) ▸ p.smul_mem 0 hx
#align sub_mul_action.zero_mem SubMulAction.zero_mem

/-- If the scalar product forms a `Module`, and the `SubMulAction` is not `⊥`, then the
subset inherits the zero. -/
instance [n_empty : Nonempty p] : Zero p where
  zero := ⟨0, n_empty.elim fun x => p.zero_mem ⟨x, x.prop⟩⟩

end Module

section AddCommGroup

variable [Ring R] [AddCommGroup M]

variable [Module R M]

variable (p p' : SubMulAction R M)

variable {r : R} {x y : M}

theorem neg_mem (hx : x ∈ p) : -x ∈ p := by
  rw [← neg_one_smul R]
  -- ⊢ -1 • x ∈ p
  exact p.smul_mem _ hx
  -- 🎉 no goals
#align sub_mul_action.neg_mem SubMulAction.neg_mem

@[simp]
theorem neg_mem_iff : -x ∈ p ↔ x ∈ p :=
  ⟨fun h => by
    rw [← neg_neg x]
    -- ⊢ - -x ∈ p
    exact neg_mem _ h, neg_mem _⟩
    -- 🎉 no goals
#align sub_mul_action.neg_mem_iff SubMulAction.neg_mem_iff

instance : Neg p :=
  ⟨fun x => ⟨-x.1, neg_mem _ x.2⟩⟩

@[simp, norm_cast]
theorem val_neg (x : p) : ((-x : p) : M) = -x :=
  rfl
#align sub_mul_action.coe_neg SubMulAction.val_neg

end AddCommGroup

end SubMulAction

namespace SubMulAction

variable [GroupWithZero S] [Monoid R] [MulAction R M]

variable [SMul S R] [MulAction S M] [IsScalarTower S R M]

variable (p : SubMulAction R M) {s : S} {x y : M}

theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
  p.smul_mem_iff' (Units.mk0 s s0)
#align sub_mul_action.smul_mem_iff SubMulAction.smul_mem_iff

end SubMulAction
