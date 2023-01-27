/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.group_action.sub_mul_action
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.GroupAction
import Mathbin.Algebra.Module.Basic
import Mathbin.Data.SetLike.Basic
import Mathbin.GroupTheory.GroupAction.Basic

/-!

# Sets invariant to a `mul_action`

In this file we define `sub_mul_action R M`; a subset of a `mul_action R M` which is closed with
respect to scalar multiplication.

For most uses, typically `submodule R M` is more powerful.

## Main definitions

* `sub_mul_action.mul_action` - the `mul_action R M` transferred to the subtype.
* `sub_mul_action.mul_action'` - the `mul_action S M` transferred to the subtype when
  `is_scalar_tower S R M`.
* `sub_mul_action.is_scalar_tower` - the `is_scalar_tower S R M` transferred to the subtype.

## Tags

submodule, mul_action
-/


open Function

universe u u' u'' v

variable {S : Type u'} {T : Type u''} {R : Type u} {M : Type v}

/-- `smul_mem_class S R M` says `S` is a type of subsets `s ≤ M` that are closed under the
scalar action of `R` on `M`. -/
class SmulMemClass (S : Type _) (R M : outParam <| Type _) [SMul R M] [SetLike S M] where
  smul_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r • m ∈ s
#align smul_mem_class SmulMemClass

/-- `vadd_mem_class S R M` says `S` is a type of subsets `s ≤ M` that are closed under the
additive action of `R` on `M`. -/
class VaddMemClass (S : Type _) (R M : outParam <| Type _) [VAdd R M] [SetLike S M] where
  vadd_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r +ᵥ m ∈ s
#align vadd_mem_class VaddMemClass

attribute [to_additive] SmulMemClass

namespace SetLike

variable [SMul R M] [SetLike S M] [hS : SmulMemClass S R M] (s : S)

include hS

open SmulMemClass

-- lower priority so other instances are found first
/-- A subset closed under the scalar action inherits that action. -/
@[to_additive "A subset closed under the additive action inherits that action."]
instance (priority := 900) hasSmul : SMul R s :=
  ⟨fun r x => ⟨r • x.1, smul_mem r x.2⟩⟩
#align set_like.has_smul SetLike.hasSmul
#align set_like.has_vadd SetLike.hasVadd

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[simp, norm_cast, to_additive]
protected theorem coe_smul (r : R) (x : s) : (↑(r • x) : M) = r • x :=
  rfl
#align set_like.coe_smul SetLike.coe_smul
#align set_like.coe_vadd SetLike.coe_vadd

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[simp, to_additive]
theorem mk_smul_mk (r : R) (x : M) (hx : x ∈ s) : r • (⟨x, hx⟩ : s) = ⟨r • x, smul_mem r hx⟩ :=
  rfl
#align set_like.mk_smul_mk SetLike.mk_smul_mk
#align set_like.mk_vadd_mk SetLike.mk_vadd_mk

@[to_additive]
theorem smul_def (r : R) (x : s) : r • x = ⟨r • x, smul_mem r x.2⟩ :=
  rfl
#align set_like.smul_def SetLike.smul_def
#align set_like.vadd_def SetLike.vadd_def

omit hS

@[simp]
theorem forall_smul_mem_iff {R M S : Type _} [Monoid R] [MulAction R M] [SetLike S M]
    [SmulMemClass S R M] {N : S} {x : M} : (∀ a : R, a • x ∈ N) ↔ x ∈ N :=
  ⟨fun h => by simpa using h 1, fun h a => SmulMemClass.smul_mem a h⟩
#align set_like.forall_smul_mem_iff SetLike.forall_smul_mem_iff

end SetLike

/-- A sub_mul_action is a set which is closed under scalar multiplication.  -/
structure SubMulAction (R : Type u) (M : Type v) [SMul R M] : Type v where
  carrier : Set M
  smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier
#align sub_mul_action SubMulAction

namespace SubMulAction

variable [SMul R M]

instance : SetLike (SubMulAction R M) M :=
  ⟨SubMulAction.carrier, fun p q h => by cases p <;> cases q <;> congr ⟩

instance : SmulMemClass (SubMulAction R M) R M where smul_mem := smul_mem'

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

instance : Bot (SubMulAction R M) :=
  ⟨{  carrier := ∅
      smul_mem' := fun c => Set.not_mem_empty }⟩

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
theorem coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • ↑x :=
  rfl
#align sub_mul_action.coe_smul SubMulAction.coe_smul

@[simp, norm_cast]
theorem coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x :=
  rfl
#align sub_mul_action.coe_mk SubMulAction.coe_mk

variable (p)

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →[R] M := by refine' { toFun := coe.. } <;> simp [coe_smul]
#align sub_mul_action.subtype SubMulAction.subtype

@[simp]
theorem subtype_apply (x : p) : p.Subtype x = x :=
  rfl
#align sub_mul_action.subtype_apply SubMulAction.subtype_apply

theorem subtype_eq_val : (SubMulAction.subtype p : p → M) = Subtype.val :=
  rfl
#align sub_mul_action.subtype_eq_val SubMulAction.subtype_eq_val

end SMul

namespace SmulMemClass

variable [Monoid R] [MulAction R M] {A : Type _} [SetLike A M]

variable [hA : SmulMemClass A R M] (S' : A)

include hA

-- Prefer subclasses of `mul_action` over `smul_mem_class`.
/-- A `sub_mul_action` of a `mul_action` is a `mul_action`.  -/
instance (priority := 75) toMulAction : MulAction R S' :=
  Subtype.coe_injective.MulAction coe (SetLike.coe_smul S')
#align sub_mul_action.smul_mem_class.to_mul_action SubMulAction.smulMemClass.toMulAction

/-- The natural `mul_action_hom` over `R` from a `sub_mul_action` of `M` to `M`. -/
protected def subtype : S' →[R] M :=
  ⟨coe, fun _ _ => rfl⟩
#align sub_mul_action.smul_mem_class.subtype SubMulAction.smulMemClass.subtype

@[simp]
protected theorem coeSubtype : (smulMemClass.subtype S' : S' → M) = coe :=
  rfl
#align sub_mul_action.smul_mem_class.coe_subtype SubMulAction.smulMemClass.coeSubtype

end SmulMemClass

section MulActionMonoid

variable [Monoid R] [MulAction R M]

section

variable [SMul S R] [SMul S M] [IsScalarTower S R M]

variable (p : SubMulAction R M)

theorem smul_of_tower_mem (s : S) {x : M} (h : x ∈ p) : s • x ∈ p :=
  by
  rw [← one_smul R x, ← smul_assoc]
  exact p.smul_mem _ h
#align sub_mul_action.smul_of_tower_mem SubMulAction.smul_of_tower_mem

instance hasSmul' : SMul S p where smul c x := ⟨c • x.1, smul_of_tower_mem _ c x.2⟩
#align sub_mul_action.has_smul' SubMulAction.hasSmul'

instance : IsScalarTower S R p where smul_assoc s r x := Subtype.ext <| smul_assoc s r ↑x

instance is_scalar_tower' {S' : Type _} [SMul S' R] [SMul S' S] [SMul S' M] [IsScalarTower S' R M]
    [IsScalarTower S' S M] : IsScalarTower S' S p
    where smul_assoc s r x := Subtype.ext <| smul_assoc s r ↑x
#align sub_mul_action.is_scalar_tower' SubMulAction.is_scalar_tower'

@[simp, norm_cast]
theorem coe_smul_of_tower (s : S) (x : p) : ((s • x : p) : M) = s • ↑x :=
  rfl
#align sub_mul_action.coe_smul_of_tower SubMulAction.coe_smul_of_tower

@[simp]
theorem smul_mem_iff' {G} [Group G] [SMul G R] [MulAction G M] [IsScalarTower G R M] (g : G)
    {x : M} : g • x ∈ p ↔ x ∈ p :=
  ⟨fun h => inv_smul_smul g x ▸ p.smul_of_tower_mem g⁻¹ h, p.smul_of_tower_mem g⟩
#align sub_mul_action.smul_mem_iff' SubMulAction.smul_mem_iff'

instance [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] :
    IsCentralScalar S p where op_smul_eq_smul r x := Subtype.ext <| op_smul_eq_smul r x

end

section

variable [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]

variable (p : SubMulAction R M)

/-- If the scalar product forms a `mul_action`, then the subset inherits this action -/
instance mulAction' : MulAction S p where
  smul := (· • ·)
  one_smul x := Subtype.ext <| one_smul _ x
  mul_smul c₁ c₂ x := Subtype.ext <| mul_smul c₁ c₂ x
#align sub_mul_action.mul_action' SubMulAction.mulAction'

instance : MulAction R p :=
  p.mulAction'

end

/-- Orbits in a `sub_mul_action` coincide with orbits in the ambient space. -/
theorem coe_image_orbit {p : SubMulAction R M} (m : p) :
    coe '' MulAction.orbit R m = MulAction.orbit R (m : M) :=
  (Set.range_comp _ _).symm
#align sub_mul_action.coe_image_orbit SubMulAction.coe_image_orbit

/- -- Previously, the relatively useless :
lemma orbit_of_sub_mul {p : sub_mul_action R M} (m : p) :
  (mul_action.orbit R m : set M) = mul_action.orbit R (m : M) := rfl
-/
/-- Stabilizers in monoid sub_mul_action coincide with stabilizers in the ambient space -/
theorem StabilizerOfSubMul.submonoid {p : SubMulAction R M} (m : p) :
    MulAction.Stabilizer.submonoid R m = MulAction.Stabilizer.submonoid R (m : M) :=
  by
  ext
  simp only [MulAction.mem_stabilizer_submonoid_iff, ← SubMulAction.coe_smul, SetLike.coe_eq_coe]
#align sub_mul_action.stabilizer_of_sub_mul.submonoid SubMulAction.StabilizerOfSubMul.submonoid

end MulActionMonoid

section MulActionGroup

variable [Group R] [MulAction R M]

/-- Stabilizers in group sub_mul_action coincide with stabilizers in the ambient space -/
theorem stabilizer_of_sub_mul {p : SubMulAction R M} (m : p) :
    MulAction.stabilizer R m = MulAction.stabilizer R (m : M) :=
  by
  rw [← Subgroup.toSubmonoid_eq]
  exact stabilizer_of_sub_mul.submonoid m
#align sub_mul_action.stabilizer_of_sub_mul SubMulAction.stabilizer_of_sub_mul

end MulActionGroup

section Module

variable [Semiring R] [AddCommMonoid M]

variable [Module R M]

variable (p : SubMulAction R M)

theorem zero_mem (h : (p : Set M).Nonempty) : (0 : M) ∈ p :=
  let ⟨x, hx⟩ := h
  zero_smul R (x : M) ▸ p.smul_mem 0 hx
#align sub_mul_action.zero_mem SubMulAction.zero_mem

/-- If the scalar product forms a `module`, and the `sub_mul_action` is not `⊥`, then the
subset inherits the zero. -/
instance [n_empty : Nonempty p] : Zero p
    where zero := ⟨0, n_empty.elim fun x => p.zero_mem ⟨x, x.Prop⟩⟩

end Module

section AddCommGroup

variable [Ring R] [AddCommGroup M]

variable [Module R M]

variable (p p' : SubMulAction R M)

variable {r : R} {x y : M}

theorem neg_mem (hx : x ∈ p) : -x ∈ p :=
  by
  rw [← neg_one_smul R]
  exact p.smul_mem _ hx
#align sub_mul_action.neg_mem SubMulAction.neg_mem

@[simp]
theorem neg_mem_iff : -x ∈ p ↔ x ∈ p :=
  ⟨fun h => by
    rw [← neg_neg x]
    exact neg_mem _ h, neg_mem _⟩
#align sub_mul_action.neg_mem_iff SubMulAction.neg_mem_iff

instance : Neg p :=
  ⟨fun x => ⟨-x.1, neg_mem _ x.2⟩⟩

@[simp, norm_cast]
theorem coe_neg (x : p) : ((-x : p) : M) = -x :=
  rfl
#align sub_mul_action.coe_neg SubMulAction.coe_neg

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

