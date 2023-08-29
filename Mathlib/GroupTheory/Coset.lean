/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/
import Mathlib.Algebra.Quotient
import Mathlib.Data.Fintype.Prod
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Subgroup.MulOpposite

#align_import group_theory.coset from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Cosets

This file develops the basic theory of left and right cosets.

## Main definitions

* `leftCoset a s`: the left coset `a * s` for an element `a : α` and a subset `s ⊆ α`, for an
  `AddGroup` this is `leftAddCoset a s`.
* `rightCoset s a`: the right coset `s * a` for an element `a : α` and a subset `s ⊆ α`, for an
  `AddGroup` this is `rightAddCoset s a`.
* `QuotientGroup.quotient s`: the quotient type representing the left cosets with respect to a
  subgroup `s`, for an `AddGroup` this is `QuotientAddGroup.quotient s`.
* `QuotientGroup.mk`: the canonical map from `α` to `α/s` for a subgroup `s` of `α`, for an
  `AddGroup` this is `QuotientAddGroup.mk`.
* `Subgroup.leftCosetEquivSubgroup`: the natural bijection between a left coset and the subgroup,
  for an `AddGroup` this is `AddSubgroup.leftCosetEquivAddSubgroup`.

## Notation

* `a *l s`: for `leftCoset a s`.
* `a +l s`: for `leftAddCoset a s`.
* `s *r a`: for `rightCoset s a`.
* `s +r a`: for `rightAddCoset s a`.

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`
-/


open Set Function

variable {α : Type*}

/-- The left coset `a * s` for an element `a : α` and a subset `s : Set α` -/
@[to_additive leftAddCoset "The left coset `a+s` for an element `a : α` and a subset `s : set α`"]
def leftCoset [Mul α] (a : α) (s : Set α) : Set α :=
  (fun x => a * x) '' s
#align left_coset leftCoset
#align left_add_coset leftAddCoset

/-- The right coset `s * a` for an element `a : α` and a subset `s : Set α` -/
@[to_additive rightAddCoset
      "The right coset `s+a` for an element `a : α` and a subset `s : set α`"]
def rightCoset [Mul α] (s : Set α) (a : α) : Set α :=
  (fun x => x * a) '' s
#align right_coset rightCoset
#align right_add_coset rightAddCoset

@[inherit_doc]
scoped[Coset] infixl:70 " *l " => leftCoset

@[inherit_doc]
scoped[Coset] infixl:70 " +l " => leftAddCoset

@[inherit_doc]
scoped[Coset] infixl:70 " *r " => rightCoset

@[inherit_doc]
scoped[Coset] infixl:70 " +r " => rightAddCoset

open Coset

section CosetMul

variable [Mul α]

@[to_additive mem_leftAddCoset]
theorem mem_leftCoset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ a *l s :=
  mem_image_of_mem (fun b : α => a * b) hxS
#align mem_left_coset mem_leftCoset
#align mem_left_add_coset mem_leftAddCoset

@[to_additive mem_rightAddCoset]
theorem mem_rightCoset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ s *r a :=
  mem_image_of_mem (fun b : α => b * a) hxS
#align mem_right_coset mem_rightCoset
#align mem_right_add_coset mem_rightAddCoset

/-- Equality of two left cosets `a * s` and `b * s`. -/
@[to_additive LeftAddCosetEquivalence "Equality of two left cosets `a + s` and `b + s`."]
def LeftCosetEquivalence (s : Set α) (a b : α) :=
  a *l s = b *l s
#align left_coset_equivalence LeftCosetEquivalence
#align left_add_coset_equivalence LeftAddCosetEquivalence

@[to_additive leftAddCosetEquivalence_rel]
theorem leftCosetEquivalence_rel (s : Set α) : Equivalence (LeftCosetEquivalence s) :=
  @Equivalence.mk _ (LeftCosetEquivalence s) (fun _ => rfl) Eq.symm Eq.trans
#align left_coset_equivalence_rel leftCosetEquivalence_rel
#align left_add_coset_equivalence_rel leftAddCosetEquivalence_rel

/-- Equality of two right cosets `s * a` and `s * b`. -/
@[to_additive RightAddCosetEquivalence "Equality of two right cosets `s + a` and `s + b`."]
def RightCosetEquivalence (s : Set α) (a b : α) :=
  s *r a = s *r b
#align right_coset_equivalence RightCosetEquivalence
#align right_add_coset_equivalence RightAddCosetEquivalence

@[to_additive rightAddCosetEquivalence_rel]
theorem rightCosetEquivalence_rel (s : Set α) : Equivalence (RightCosetEquivalence s) :=
  @Equivalence.mk _ (RightCosetEquivalence s) (fun _a => rfl) Eq.symm Eq.trans
#align right_coset_equivalence_rel rightCosetEquivalence_rel
#align right_add_coset_equivalence_rel rightAddCosetEquivalence_rel

end CosetMul

section CosetSemigroup

variable [Semigroup α]

@[to_additive (attr := simp) leftAddCoset_assoc]
theorem leftCoset_assoc (s : Set α) (a b : α) : a *l (b *l s) = a * b *l s := by
  simp [leftCoset, rightCoset, (image_comp _ _ _).symm, Function.comp, mul_assoc]
  -- 🎉 no goals
#align left_coset_assoc leftCoset_assoc
#align left_add_coset_assoc leftAddCoset_assoc

@[to_additive (attr := simp) rightAddCoset_assoc]
theorem rightCoset_assoc (s : Set α) (a b : α) : s *r a *r b = s *r (a * b) := by
  simp [leftCoset, rightCoset, (image_comp _ _ _).symm, Function.comp, mul_assoc]
  -- 🎉 no goals
#align right_coset_assoc rightCoset_assoc
#align right_add_coset_assoc rightAddCoset_assoc

@[to_additive leftAddCoset_rightAddCoset]
theorem leftCoset_rightCoset (s : Set α) (a b : α) : a *l s *r b = a *l (s *r b) := by
  simp [leftCoset, rightCoset, (image_comp _ _ _).symm, Function.comp, mul_assoc]
  -- 🎉 no goals
#align left_coset_right_coset leftCoset_rightCoset
#align left_add_coset_right_add_coset leftAddCoset_rightAddCoset

end CosetSemigroup

section CosetMonoid

variable [Monoid α] (s : Set α)

@[to_additive (attr := simp) zero_leftAddCoset]
theorem one_leftCoset : 1 *l s = s :=
  Set.ext <| by simp [leftCoset]
                -- 🎉 no goals
#align one_left_coset one_leftCoset
#align zero_left_add_coset zero_leftAddCoset

@[to_additive (attr := simp) rightAddCoset_zero]
theorem rightCoset_one : s *r 1 = s :=
  Set.ext <| by simp [rightCoset]
                -- 🎉 no goals
#align right_coset_one rightCoset_one
#align right_add_coset_zero rightAddCoset_zero

end CosetMonoid

section CosetSubmonoid

open Submonoid

variable [Monoid α] (s : Submonoid α)

@[to_additive mem_own_leftAddCoset]
theorem mem_own_leftCoset (a : α) : a ∈ a *l s :=
  suffices a * 1 ∈ a *l s by simpa
                             -- 🎉 no goals
  mem_leftCoset a (one_mem s : 1 ∈ s)
#align mem_own_left_coset mem_own_leftCoset
#align mem_own_left_add_coset mem_own_leftAddCoset

@[to_additive mem_own_rightAddCoset]
theorem mem_own_rightCoset (a : α) : a ∈ (s : Set α) *r a :=
  suffices 1 * a ∈ (s : Set α) *r a by simpa
                                       -- 🎉 no goals
  mem_rightCoset a (one_mem s : 1 ∈ s)
#align mem_own_right_coset mem_own_rightCoset
#align mem_own_right_add_coset mem_own_rightAddCoset

@[to_additive mem_leftAddCoset_leftAddCoset]
theorem mem_leftCoset_leftCoset {a : α} (ha : a *l s = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha]; exact mem_own_leftCoset s a
  -- ⊢ a ∈ a *l ↑s
                                -- 🎉 no goals
#align mem_left_coset_left_coset mem_leftCoset_leftCoset
#align mem_left_add_coset_left_add_coset mem_leftAddCoset_leftAddCoset

@[to_additive mem_rightAddCoset_rightAddCoset]
theorem mem_rightCoset_rightCoset {a : α} (ha : (s : Set α) *r a = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha]; exact mem_own_rightCoset s a
  -- ⊢ a ∈ ↑s *r a
                                -- 🎉 no goals
#align mem_right_coset_right_coset mem_rightCoset_rightCoset
#align mem_right_add_coset_right_add_coset mem_rightAddCoset_rightAddCoset

end CosetSubmonoid

section CosetGroup

variable [Group α] {s : Set α} {x : α}

@[to_additive mem_leftAddCoset_iff]
theorem mem_leftCoset_iff (a : α) : x ∈ a *l s ↔ a⁻¹ * x ∈ s :=
  Iff.intro (fun ⟨b, hb, Eq⟩ => by simp [Eq.symm, hb]) fun h => ⟨a⁻¹ * x, h, by simp⟩
                                   -- 🎉 no goals
                                                                                -- 🎉 no goals
#align mem_left_coset_iff mem_leftCoset_iff
#align mem_left_add_coset_iff mem_leftAddCoset_iff

@[to_additive mem_rightAddCoset_iff]
theorem mem_rightCoset_iff (a : α) : x ∈ s *r a ↔ x * a⁻¹ ∈ s :=
  Iff.intro (fun ⟨b, hb, Eq⟩ => by simp [Eq.symm, hb]) fun h => ⟨x * a⁻¹, h, by simp⟩
                                   -- 🎉 no goals
                                                                                -- 🎉 no goals
#align mem_right_coset_iff mem_rightCoset_iff
#align mem_right_add_coset_iff mem_rightAddCoset_iff

end CosetGroup

section CosetSubgroup

open Subgroup

variable [Group α] (s : Subgroup α)

@[to_additive leftAddCoset_mem_leftAddCoset]
theorem leftCoset_mem_leftCoset {a : α} (ha : a ∈ s) : a *l s = s :=
  Set.ext <| by simp [mem_leftCoset_iff, mul_mem_cancel_left (s.inv_mem ha)]
                -- 🎉 no goals
#align left_coset_mem_left_coset leftCoset_mem_leftCoset
#align left_add_coset_mem_left_add_coset leftAddCoset_mem_leftAddCoset

@[to_additive rightAddCoset_mem_rightAddCoset]
theorem rightCoset_mem_rightCoset {a : α} (ha : a ∈ s) : (s : Set α) *r a = s :=
  Set.ext fun b => by simp [mem_rightCoset_iff, mul_mem_cancel_right (s.inv_mem ha)]
                      -- 🎉 no goals
#align right_coset_mem_right_coset rightCoset_mem_rightCoset
#align right_add_coset_mem_right_add_coset rightAddCoset_mem_rightAddCoset

@[to_additive]
theorem orbit_subgroup_eq_rightCoset (a : α) : MulAction.orbit s a = s *r a :=
  Set.ext fun _b => ⟨fun ⟨c, d⟩ => ⟨c, c.2, d⟩, fun ⟨c, d, e⟩ => ⟨⟨c, d⟩, e⟩⟩
#align orbit_subgroup_eq_right_coset orbit_subgroup_eq_rightCoset
#align orbit_add_subgroup_eq_right_coset orbit_addSubgroup_eq_rightCoset

@[to_additive]
theorem orbit_subgroup_eq_self_of_mem {a : α} (ha : a ∈ s) : MulAction.orbit s a = s :=
  (orbit_subgroup_eq_rightCoset s a).trans (rightCoset_mem_rightCoset s ha)
#align orbit_subgroup_eq_self_of_mem orbit_subgroup_eq_self_of_mem
#align orbit_add_subgroup_eq_self_of_mem orbit_addSubgroup_eq_self_of_mem

@[to_additive]
theorem orbit_subgroup_one_eq_self : MulAction.orbit s (1 : α) = s :=
  orbit_subgroup_eq_self_of_mem s s.one_mem
#align orbit_subgroup_one_eq_self orbit_subgroup_one_eq_self
#align orbit_add_subgroup_zero_eq_self orbit_addSubgroup_zero_eq_self

@[to_additive eq_addCosets_of_normal]
theorem eq_cosets_of_normal (N : s.Normal) (g : α) : g *l s = s *r g :=
  Set.ext fun a => by simp [mem_leftCoset_iff, mem_rightCoset_iff]; rw [N.mem_comm_iff]
                      -- ⊢ g⁻¹ * a ∈ s ↔ a * g⁻¹ ∈ s
                                                                    -- 🎉 no goals
#align eq_cosets_of_normal eq_cosets_of_normal
#align eq_add_cosets_of_normal eq_addCosets_of_normal

@[to_additive normal_of_eq_addCosets]
theorem normal_of_eq_cosets (h : ∀ g : α, g *l s = s *r g) : s.Normal :=
  ⟨fun a ha g =>
    show g * a * g⁻¹ ∈ (s : Set α) by rw [← mem_rightCoset_iff, ← h]; exact mem_leftCoset g ha⟩
                                      -- ⊢ g * a ∈ g *l ↑s
                                                                      -- 🎉 no goals
#align normal_of_eq_cosets normal_of_eq_cosets
#align normal_of_eq_add_cosets normal_of_eq_addCosets

@[to_additive normal_iff_eq_addCosets]
theorem normal_iff_eq_cosets : s.Normal ↔ ∀ g : α, g *l s = s *r g :=
  ⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩
#align normal_iff_eq_cosets normal_iff_eq_cosets
#align normal_iff_eq_add_cosets normal_iff_eq_addCosets

@[to_additive leftAddCoset_eq_iff]
theorem leftCoset_eq_iff {x y : α} : leftCoset x s = leftCoset y s ↔ x⁻¹ * y ∈ s := by
  rw [Set.ext_iff]
  -- ⊢ (∀ (x_1 : α), x_1 ∈ x *l ↑s ↔ x_1 ∈ y *l ↑s) ↔ x⁻¹ * y ∈ s
  simp_rw [mem_leftCoset_iff, SetLike.mem_coe]
  -- ⊢ (∀ (x_1 : α), x⁻¹ * x_1 ∈ s ↔ y⁻¹ * x_1 ∈ s) ↔ x⁻¹ * y ∈ s
  constructor
  -- ⊢ (∀ (x_1 : α), x⁻¹ * x_1 ∈ s ↔ y⁻¹ * x_1 ∈ s) → x⁻¹ * y ∈ s
  · intro h
    -- ⊢ x⁻¹ * y ∈ s
    apply (h y).mpr
    -- ⊢ y⁻¹ * y ∈ s
    rw [mul_left_inv]
    -- ⊢ 1 ∈ s
    exact s.one_mem
    -- 🎉 no goals
  · intro h z
    -- ⊢ x⁻¹ * z ∈ s ↔ y⁻¹ * z ∈ s
    rw [← mul_inv_cancel_right x⁻¹ y]
    -- ⊢ x⁻¹ * y * y⁻¹ * z ∈ s ↔ y⁻¹ * z ∈ s
    rw [mul_assoc]
    -- ⊢ x⁻¹ * y * (y⁻¹ * z) ∈ s ↔ y⁻¹ * z ∈ s
    exact s.mul_mem_cancel_left h
    -- 🎉 no goals
#align left_coset_eq_iff leftCoset_eq_iff
#align left_add_coset_eq_iff leftAddCoset_eq_iff

@[to_additive rightAddCoset_eq_iff]
theorem rightCoset_eq_iff {x y : α} : rightCoset (↑s) x = rightCoset s y ↔ y * x⁻¹ ∈ s := by
  rw [Set.ext_iff]
  -- ⊢ (∀ (x_1 : α), x_1 ∈ ↑s *r x ↔ x_1 ∈ ↑s *r y) ↔ y * x⁻¹ ∈ s
  simp_rw [mem_rightCoset_iff, SetLike.mem_coe]
  -- ⊢ (∀ (x_1 : α), x_1 * x⁻¹ ∈ s ↔ x_1 * y⁻¹ ∈ s) ↔ y * x⁻¹ ∈ s
  constructor
  -- ⊢ (∀ (x_1 : α), x_1 * x⁻¹ ∈ s ↔ x_1 * y⁻¹ ∈ s) → y * x⁻¹ ∈ s
  · intro h
    -- ⊢ y * x⁻¹ ∈ s
    apply (h y).mpr
    -- ⊢ y * y⁻¹ ∈ s
    rw [mul_right_inv]
    -- ⊢ 1 ∈ s
    exact s.one_mem
    -- 🎉 no goals
  · intro h z
    -- ⊢ z * x⁻¹ ∈ s ↔ z * y⁻¹ ∈ s
    rw [← inv_mul_cancel_left y x⁻¹]
    -- ⊢ z * (y⁻¹ * (y * x⁻¹)) ∈ s ↔ z * y⁻¹ ∈ s
    rw [← mul_assoc]
    -- ⊢ z * y⁻¹ * (y * x⁻¹) ∈ s ↔ z * y⁻¹ ∈ s
    exact s.mul_mem_cancel_right h
    -- 🎉 no goals
#align right_coset_eq_iff rightCoset_eq_iff
#align right_add_coset_eq_iff rightAddCoset_eq_iff

end CosetSubgroup

-- porting note: see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.E2.9C.94.20to_additive.2Emap_namespace
run_cmd Lean.Elab.Command.liftCoreM <| ToAdditive.insertTranslation `QuotientGroup `QuotientAddGroup

namespace QuotientGroup

variable [Group α] (s : Subgroup α)

/-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup.-/
@[to_additive "The equivalence relation corresponding to the partition of a group by left cosets
 of a subgroup."]
def leftRel : Setoid α :=
  MulAction.orbitRel (Subgroup.opposite s) α
#align quotient_group.left_rel QuotientGroup.leftRel
#align quotient_add_group.left_rel QuotientAddGroup.leftRel

variable {s}

@[to_additive]
theorem leftRel_apply {x y : α} : @Setoid.r _ (leftRel s) x y ↔ x⁻¹ * y ∈ s :=
  calc
    (∃ a : Subgroup.opposite s, y * MulOpposite.unop a = x) ↔ ∃ a : s, y * a = x :=
      s.oppositeEquiv.symm.exists_congr_left
    _ ↔ ∃ a : s, x⁻¹ * y = a⁻¹ :=
      by simp only [inv_mul_eq_iff_eq_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq]
         -- 🎉 no goals
    _ ↔ x⁻¹ * y ∈ s := by simp [exists_inv_mem_iff_exists_mem]
                          -- 🎉 no goals
#align quotient_group.left_rel_apply QuotientGroup.leftRel_apply
#align quotient_add_group.left_rel_apply QuotientAddGroup.leftRel_apply

variable (s)

@[to_additive]
theorem leftRel_eq : @Setoid.r _ (leftRel s) = fun x y => x⁻¹ * y ∈ s :=
  funext₂ <| by
    simp only [eq_iff_iff]
    -- ⊢ ∀ (a b : α), Setoid.r a b ↔ a⁻¹ * b ∈ s
    apply leftRel_apply
    -- 🎉 no goals
#align quotient_group.left_rel_eq QuotientGroup.leftRel_eq
#align quotient_add_group.left_rel_eq QuotientAddGroup.leftRel_eq

theorem leftRel_r_eq_leftCosetEquivalence :
    @Setoid.r _ (QuotientGroup.leftRel s) = LeftCosetEquivalence s := by
  ext
  -- ⊢ Setoid.r x✝¹ x✝ ↔ LeftCosetEquivalence (↑s) x✝¹ x✝
  rw [leftRel_eq]
  -- ⊢ (fun x y => x⁻¹ * y ∈ s) x✝¹ x✝ ↔ LeftCosetEquivalence (↑s) x✝¹ x✝
  exact (leftCoset_eq_iff s).symm
  -- 🎉 no goals
#align quotient_group.left_rel_r_eq_left_coset_equivalence QuotientGroup.leftRel_r_eq_leftCosetEquivalence

@[to_additive]
instance leftRelDecidable [DecidablePred (· ∈ s)] : DecidableRel (leftRel s).r := fun x y => by
  rw [leftRel_eq]
  -- ⊢ Decidable ((fun x y => x⁻¹ * y ∈ s) x y)
  exact ‹DecidablePred (· ∈ s)› _
  -- 🎉 no goals
#align quotient_group.left_rel_decidable QuotientGroup.leftRelDecidable
#align quotient_add_group.left_rel_decidable QuotientAddGroup.leftRelDecidable

/-- `α ⧸ s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `α ⧸ s` is a group -/
@[to_additive "`α ⧸ s` is the quotient type representing the left cosets of `s`.  If `s` is a normal
 subgroup, `α ⧸ s` is a group"]
instance instHasQuotientSubgroup : HasQuotient α (Subgroup α) :=
  ⟨fun s => Quotient (leftRel s)⟩

/-- The equivalence relation corresponding to the partition of a group by right cosets of a
subgroup. -/
@[to_additive "The equivalence relation corresponding to the partition of a group by right cosets
 of a subgroup."]
def rightRel : Setoid α :=
  MulAction.orbitRel s α
#align quotient_group.right_rel QuotientGroup.rightRel
#align quotient_add_group.right_rel QuotientAddGroup.rightRel

variable {s}

@[to_additive]
theorem rightRel_apply {x y : α} : @Setoid.r _ (rightRel s) x y ↔ y * x⁻¹ ∈ s :=
  calc
    (∃ a : s, (a : α) * y = x) ↔ ∃ a : s, y * x⁻¹ = a⁻¹ :=
      by simp only [mul_inv_eq_iff_eq_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
         -- 🎉 no goals
    _ ↔ y * x⁻¹ ∈ s := by simp [exists_inv_mem_iff_exists_mem]
                          -- 🎉 no goals
#align quotient_group.right_rel_apply QuotientGroup.rightRel_apply
#align quotient_add_group.right_rel_apply QuotientAddGroup.rightRel_apply

variable (s)

@[to_additive]
theorem rightRel_eq : @Setoid.r _ (rightRel s) = fun x y => y * x⁻¹ ∈ s :=
  funext₂ <| by
    simp only [eq_iff_iff]
    -- ⊢ ∀ (a b : α), Setoid.r a b ↔ b * a⁻¹ ∈ s
    apply rightRel_apply
    -- 🎉 no goals
#align quotient_group.right_rel_eq QuotientGroup.rightRel_eq
#align quotient_add_group.right_rel_eq QuotientAddGroup.rightRel_eq

theorem rightRel_r_eq_rightCosetEquivalence :
    @Setoid.r _ (QuotientGroup.rightRel s) = RightCosetEquivalence s := by
  ext
  -- ⊢ Setoid.r x✝¹ x✝ ↔ RightCosetEquivalence (↑s) x✝¹ x✝
  rw [rightRel_eq]
  -- ⊢ (fun x y => y * x⁻¹ ∈ s) x✝¹ x✝ ↔ RightCosetEquivalence (↑s) x✝¹ x✝
  exact (rightCoset_eq_iff s).symm
  -- 🎉 no goals
#align quotient_group.right_rel_r_eq_right_coset_equivalence QuotientGroup.rightRel_r_eq_rightCosetEquivalence

@[to_additive]
instance rightRelDecidable [DecidablePred (· ∈ s)] : DecidableRel (rightRel s).r := fun x y => by
  rw [rightRel_eq]
  -- ⊢ Decidable ((fun x y => y * x⁻¹ ∈ s) x y)
  exact ‹DecidablePred (· ∈ s)› _
  -- 🎉 no goals
#align quotient_group.right_rel_decidable QuotientGroup.rightRelDecidable
#align quotient_add_group.right_rel_decidable QuotientAddGroup.rightRelDecidable

/-- Right cosets are in bijection with left cosets. -/
@[to_additive "Right cosets are in bijection with left cosets."]
def quotientRightRelEquivQuotientLeftRel : Quotient (QuotientGroup.rightRel s) ≃ α ⧸ s
    where
  toFun :=
    Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply, rightRel_apply]
      -- ⊢ b * a⁻¹ ∈ s → ((fun g => g⁻¹) a)⁻¹ * (fun g => g⁻¹) b ∈ s
      exact fun h => (congr_arg (· ∈ s) (by simp [mul_assoc])).mp (s.inv_mem h)
      -- 🎉 no goals
      -- porting note: replace with `by group`
  invFun :=
    Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply, rightRel_apply]
      -- ⊢ a⁻¹ * b ∈ s → (fun g => g⁻¹) b * ((fun g => g⁻¹) a)⁻¹ ∈ s
      exact fun h => (congr_arg (· ∈ s) (by simp [mul_assoc])).mp (s.inv_mem h)
      -- 🎉 no goals
      -- porting note: replace with `by group`
  left_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          -- ⊢ Setoid.r g g
          exact Quotient.exact' rfl)
          -- 🎉 no goals
  right_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          -- ⊢ Setoid.r g g
          exact Quotient.exact' rfl)
          -- 🎉 no goals
#align quotient_group.quotient_right_rel_equiv_quotient_left_rel QuotientGroup.quotientRightRelEquivQuotientLeftRel
#align quotient_add_group.quotient_right_rel_equiv_quotient_left_rel QuotientAddGroup.quotientRightRelEquivQuotientLeftRel

@[to_additive]
instance fintypeQuotientRightRel [Fintype (α ⧸ s)] :
    Fintype (Quotient (QuotientGroup.rightRel s)) :=
  Fintype.ofEquiv (α ⧸ s) (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm
#align quotient_group.fintype_quotient_right_rel QuotientGroup.fintypeQuotientRightRel
#align quotient_add_group.fintype_quotient_right_rel QuotientAddGroup.fintypeQuotientRightRel

@[to_additive]
theorem card_quotient_rightRel [Fintype (α ⧸ s)] :
    Fintype.card (Quotient (QuotientGroup.rightRel s)) = Fintype.card (α ⧸ s) :=
  Fintype.ofEquiv_card (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm
#align quotient_group.card_quotient_right_rel QuotientGroup.card_quotient_rightRel
#align quotient_add_group.card_quotient_right_rel QuotientAddGroup.card_quotient_rightRel

end QuotientGroup

namespace QuotientGroup

variable [Group α] {s : Subgroup α}

@[to_additive]
instance fintype [Fintype α] (s : Subgroup α) [DecidableRel (leftRel s).r] : Fintype (α ⧸ s) :=
  Quotient.fintype (leftRel s)
#align quotient_group.fintype QuotientGroup.fintype
#align quotient_add_group.fintype QuotientAddGroup.fintype

/-- The canonical map from a group `α` to the quotient `α ⧸ s`. -/
@[to_additive (attr := coe) "The canonical map from an `AddGroup` `α` to the quotient `α ⧸ s`."]
abbrev mk (a : α) : α ⧸ s :=
  Quotient.mk'' a
#align quotient_group.mk QuotientGroup.mk
#align quotient_add_group.mk QuotientAddGroup.mk

@[to_additive]
theorem mk_surjective : Function.Surjective <| @mk _ _ s :=
  Quotient.surjective_Quotient_mk''
#align quotient_group.mk_surjective QuotientGroup.mk_surjective
#align quotient_add_group.mk_surjective QuotientAddGroup.mk_surjective

@[to_additive (attr := simp)]
lemma range_mk : range (QuotientGroup.mk (s := s)) = univ := range_iff_surjective.mpr mk_surjective

@[to_additive (attr := elab_as_elim)]
theorem induction_on {C : α ⧸ s → Prop} (x : α ⧸ s) (H : ∀ z, C (QuotientGroup.mk z)) : C x :=
  Quotient.inductionOn' x H
#align quotient_group.induction_on QuotientGroup.induction_on
#align quotient_add_group.induction_on QuotientAddGroup.induction_on

@[to_additive]
instance : Coe α (α ⧸ s) :=
  ⟨mk⟩

@[to_additive (attr := elab_as_elim)]
theorem induction_on' {C : α ⧸ s → Prop} (x : α ⧸ s) (H : ∀ z : α, C z) : C x :=
  Quotient.inductionOn' x H
#align quotient_group.induction_on' QuotientGroup.induction_on'
#align quotient_add_group.induction_on' QuotientAddGroup.induction_on'

@[to_additive (attr := simp)]
theorem quotient_liftOn_mk {β} (f : α → β) (h) (x : α) : Quotient.liftOn' (x : α ⧸ s) f h = f x :=
  rfl
#align quotient_group.quotient_lift_on_coe QuotientGroup.quotient_liftOn_mk
#align quotient_add_group.quotient_lift_on_coe QuotientAddGroup.quotient_liftOn_mk

@[to_additive]
theorem forall_mk {C : α ⧸ s → Prop} : (∀ x : α ⧸ s, C x) ↔ ∀ x : α, C x :=
  mk_surjective.forall
#align quotient_group.forall_coe QuotientGroup.forall_mk
#align quotient_add_group.forall_coe QuotientAddGroup.forall_mk

@[to_additive]
theorem exists_mk {C : α ⧸ s → Prop} : (∃ x : α ⧸ s, C x) ↔ ∃ x : α, C x :=
  mk_surjective.exists
#align quotient_group.exists_coe QuotientGroup.exists_mk
#align quotient_add_group.exists_coe QuotientAddGroup.exists_mk

@[to_additive]
instance (s : Subgroup α) : Inhabited (α ⧸ s) :=
  ⟨((1 : α) : α ⧸ s)⟩

@[to_additive]
protected theorem eq {a b : α} : (a : α ⧸ s) = b ↔ a⁻¹ * b ∈ s :=
  calc
    _ ↔ @Setoid.r _ (leftRel s) a b := Quotient.eq''
    _ ↔ _ := by rw [leftRel_apply]
                -- 🎉 no goals
#align quotient_group.eq QuotientGroup.eq
#align quotient_add_group.eq QuotientAddGroup.eq

@[to_additive]
theorem eq' {a b : α} : (mk a : α ⧸ s) = mk b ↔ a⁻¹ * b ∈ s :=
  QuotientGroup.eq
#align quotient_group.eq' QuotientGroup.eq'
#align quotient_add_group.eq' QuotientAddGroup.eq'

@[to_additive] -- porting note: `simp` can prove this.
theorem out_eq' (a : α ⧸ s) : mk a.out' = a :=
  Quotient.out_eq' a
#align quotient_group.out_eq' QuotientGroup.out_eq'
#align quotient_add_group.out_eq' QuotientAddGroup.out_eq'

variable (s)

/- It can be useful to write `obtain ⟨h, H⟩ := mk_out'_eq_mul ...`, and then `rw [H]` or
  `simp_rw [H]` or `simp only [H]`. In order for `simp_rw` and `simp only` to work, this lemma is
  stated in terms of an arbitrary `h : s`, rather than the specific `h = g⁻¹ * (mk g).out'`. -/
@[to_additive QuotientAddGroup.mk_out'_eq_mul]
theorem mk_out'_eq_mul (g : α) : ∃ h : s, (mk g : α ⧸ s).out' = g * h :=
  ⟨⟨g⁻¹ * (mk g).out', eq'.mp (mk g).out_eq'.symm⟩, by rw [mul_inv_cancel_left]⟩
                                                       -- 🎉 no goals
#align quotient_group.mk_out'_eq_mul QuotientGroup.mk_out'_eq_mul
#align quotient_add_group.mk_out'_eq_mul QuotientAddGroup.mk_out'_eq_mul

variable {s} {a b : α}

@[to_additive (attr := simp)]
theorem mk_mul_of_mem (a : α) (hb : b ∈ s) : (mk (a * b) : α ⧸ s) = mk a := by
  rwa [eq', mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]
  -- 🎉 no goals
#align quotient_group.mk_mul_of_mem QuotientGroup.mk_mul_of_mem
#align quotient_add_group.mk_add_of_mem QuotientAddGroup.mk_add_of_mem

@[to_additive]
theorem eq_class_eq_leftCoset (s : Subgroup α) (g : α) :
    { x : α | (x : α ⧸ s) = g } = leftCoset g s :=
  Set.ext fun z => by
    rw [mem_leftCoset_iff, Set.mem_setOf_eq, eq_comm, QuotientGroup.eq, SetLike.mem_coe]
    -- 🎉 no goals
#align quotient_group.eq_class_eq_left_coset QuotientGroup.eq_class_eq_leftCoset
#align quotient_add_group.eq_class_eq_left_coset QuotientAddGroup.eq_class_eq_leftCoset

@[to_additive]
theorem preimage_image_mk (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α → α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) ⁻¹' s := by
  ext x
  -- ⊢ x ∈ mk ⁻¹' (mk '' s) ↔ x ∈ ⋃ (x : { x // x ∈ N }), (fun x_1 => x_1 * ↑x) ⁻¹' s
  simp only [QuotientGroup.eq, SetLike.exists, exists_prop, Set.mem_preimage, Set.mem_iUnion,
    Set.mem_image, ← eq_inv_mul_iff_mul_eq]
  exact
    ⟨fun ⟨y, hs, hN⟩ => ⟨_, N.inv_mem hN, by simpa using hs⟩, fun ⟨z, hz, hxz⟩ =>
      ⟨x * z, hxz, by simpa using hz⟩⟩
#align quotient_group.preimage_image_coe QuotientGroup.preimage_image_mk
#align quotient_add_group.preimage_image_coe QuotientAddGroup.preimage_image_mk

@[to_additive]
theorem preimage_image_mk_eq_iUnion_image (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α → α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) '' s := by
  rw [preimage_image_mk, iUnion_congr_of_surjective (·⁻¹) inv_surjective]
  -- ⊢ ∀ (x : { x // x ∈ N }), (fun x_1 => x_1 * ↑x⁻¹) '' s = (fun x_1 => x_1 * ↑x) …
  exact fun x ↦ image_mul_right'
  -- 🎉 no goals

end QuotientGroup

namespace Subgroup

open QuotientGroup

variable [Group α] {s : Subgroup α}

/-- The natural bijection between a left coset `g * s` and `s`. -/
@[to_additive "The natural bijection between the cosets `g + s` and `s`."]
def leftCosetEquivSubgroup (g : α) : leftCoset g s ≃ s :=
  ⟨fun x => ⟨g⁻¹ * x.1, (mem_leftCoset_iff _).1 x.2⟩, fun x => ⟨g * x.1, x.1, x.2, rfl⟩,
    fun ⟨x, hx⟩ => Subtype.eq <| by simp, fun ⟨g, hg⟩ => Subtype.eq <| by simp⟩
                                    -- 🎉 no goals
                                                                          -- 🎉 no goals
#align subgroup.left_coset_equiv_subgroup Subgroup.leftCosetEquivSubgroup
#align add_subgroup.left_coset_equiv_add_subgroup AddSubgroup.leftCosetEquivAddSubgroup

/-- The natural bijection between a right coset `s * g` and `s`. -/
@[to_additive "The natural bijection between the cosets `s + g` and `s`."]
def rightCosetEquivSubgroup (g : α) : rightCoset (↑s) g ≃ s :=
  ⟨fun x => ⟨x.1 * g⁻¹, (mem_rightCoset_iff _).1 x.2⟩, fun x => ⟨x.1 * g, x.1, x.2, rfl⟩,
    fun ⟨x, hx⟩ => Subtype.eq <| by simp, fun ⟨g, hg⟩ => Subtype.eq <| by simp⟩
                                    -- 🎉 no goals
                                                                          -- 🎉 no goals
#align subgroup.right_coset_equiv_subgroup Subgroup.rightCosetEquivSubgroup
#align add_subgroup.right_coset_equiv_add_subgroup AddSubgroup.rightCosetEquivAddSubgroup

/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
@[to_additive addGroupEquivQuotientProdAddSubgroup
  "A (non-canonical) bijection between an add_group `α` and the product `(α/s) × s`"]
noncomputable def groupEquivQuotientProdSubgroup : α ≃ (α ⧸ s) × s :=
  calc
    α ≃ ΣL : α ⧸ s, { x : α // (x : α ⧸ s) = L } := (Equiv.sigmaFiberEquiv QuotientGroup.mk).symm
    _ ≃ ΣL : α ⧸ s, leftCoset (Quotient.out' L) s :=
      Equiv.sigmaCongrRight fun L => by
        rw [← eq_class_eq_leftCoset]
        -- ⊢ { x // ↑x = L } ≃ ↑{x | ↑x = ↑(Quotient.out' L)}
        show
          (_root_.Subtype fun x : α => Quotient.mk'' x = L) ≃
            _root_.Subtype fun x : α => Quotient.mk'' x = Quotient.mk'' _
        simp [-Quotient.eq'']
        -- ⊢ { x // Quotient.mk'' x = L } ≃ { x // Quotient.mk'' x = L }
        rfl
        -- 🎉 no goals
    _ ≃ Σ _L : α ⧸ s, s := Equiv.sigmaCongrRight fun L => leftCosetEquivSubgroup _
    _ ≃ (α ⧸ s) × s := Equiv.sigmaEquivProd _ _
#align subgroup.group_equiv_quotient_times_subgroup Subgroup.groupEquivQuotientProdSubgroup
#align add_subgroup.add_group_equiv_quotient_times_add_subgroup AddSubgroup.addGroupEquivQuotientProdAddSubgroup

variable {t : Subgroup α}

/-- If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection. -/
@[to_additive "If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection."]
def quotientEquivOfEq (h : s = t) : α ⧸ s ≃ α ⧸ t
    where
  toFun := Quotient.map' id fun _a _b h' => h ▸ h'
  invFun := Quotient.map' id fun _a _b h' => h.symm ▸ h'
  left_inv q := induction_on' q fun _g => rfl
  right_inv q := induction_on' q fun _g => rfl
#align subgroup.quotient_equiv_of_eq Subgroup.quotientEquivOfEq
#align add_subgroup.quotient_equiv_of_eq AddSubgroup.quotientEquivOfEq

theorem quotientEquivOfEq_mk (h : s = t) (a : α) :
    quotientEquivOfEq h (QuotientGroup.mk a) = QuotientGroup.mk a :=
  rfl
#align subgroup.quotient_equiv_of_eq_mk Subgroup.quotientEquivOfEq_mk

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
of the quotient map `G → G/K`. The classical version is `Subgroup.quotientEquivProdOfLE`. -/
@[to_additive (attr := simps)
  "If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
  of the quotient map `G → G/K`. The classical version is `AddSubgroup.quotientEquivSumOfLE`."]
def quotientEquivProdOfLE' (h_le : s ≤ t) (f : α ⧸ t → α)
    (hf : Function.RightInverse f QuotientGroup.mk) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t
    where
  toFun a :=
    ⟨a.map' id fun b c h => leftRel_apply.mpr (h_le (leftRel_apply.mp h)),
      a.map' (fun g : α => ⟨(f (Quotient.mk'' g))⁻¹ * g, leftRel_apply.mp (Quotient.exact' (hf g))⟩)
        fun b c h => by
        rw [leftRel_apply]
        -- ⊢ ((fun g => { val := (f (Quotient.mk'' g))⁻¹ * g, property := (_ : (f (Quotie …
        change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) ∈ s
        -- ⊢ ((f ↑b)⁻¹ * b)⁻¹ * ((f ↑c)⁻¹ * c) ∈ s
        have key : f b = f c :=
          congr_arg f (Quotient.sound' (leftRel_apply.mpr (h_le (leftRel_apply.mp h))))
        rwa [key, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, ← leftRel_apply]⟩
        -- 🎉 no goals
  invFun a := by
    refine a.2.map' (fun (b : { x // x ∈ t}) => f a.1 * b) fun b c h => by
      rw [leftRel_apply] at h ⊢
      change (f a.1 * b)⁻¹ * (f a.1 * c) ∈ s
      rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  left_inv := by
    refine' Quotient.ind' fun a => _
    -- ⊢ (fun a => Quotient.map' (fun b => f a.fst * ↑b) (_ : ∀ (b c : { x // x ∈ t } …
    simp_rw [Quotient.map'_mk'', id.def, mul_inv_cancel_left]
    -- 🎉 no goals
  right_inv := by
    refine' Prod.rec _
    -- ⊢ ∀ (fst : α ⧸ t) (snd : { x // x ∈ t } ⧸ subgroupOf s t), (fun a => (Quotient …
    refine' Quotient.ind' fun a => _
    -- ⊢ ∀ (snd : { x // x ∈ t } ⧸ subgroupOf s t), (fun a => (Quotient.map' id (_ :  …
    refine' Quotient.ind' fun b => _
    -- ⊢ (fun a => (Quotient.map' id (_ : ∀ (b c : α), Setoid.r b c → Setoid.r (id b) …
    have key : Quotient.mk'' (f (Quotient.mk'' a) * b) = Quotient.mk'' a :=
      (QuotientGroup.mk_mul_of_mem (f a) b.2).trans (hf a)
    simp_rw [Quotient.map'_mk'', id.def, key, inv_mul_cancel_left]
    -- 🎉 no goals
#align subgroup.quotient_equiv_prod_of_le' Subgroup.quotientEquivProdOfLE'
#align add_subgroup.quotient_equiv_sum_of_le' AddSubgroup.quotientEquivSumOfLE'

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.
The constructive version is `quotientEquivProdOfLE'`. -/
@[to_additive (attr := simps!) "If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively. The
 constructive version is `quotientEquivProdOfLE'`."]
noncomputable def quotientEquivProdOfLE (h_le : s ≤ t) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t :=
  quotientEquivProdOfLE' h_le Quotient.out' Quotient.out_eq'
#align subgroup.quotient_equiv_prod_of_le Subgroup.quotientEquivProdOfLE
#align add_subgroup.quotient_equiv_sum_of_le AddSubgroup.quotientEquivSumOfLE

/-- If `s ≤ t`, then there is an embedding `s ⧸ H.subgroupOf s ↪ t ⧸ H.subgroupOf t`. -/
@[to_additive "If `s ≤ t`, then there is an embedding
 `s ⧸ H.addSubgroupOf s ↪ t ⧸ H.addSubgroupOf t`."]
def quotientSubgroupOfEmbeddingOfLE (H : Subgroup α) (h : s ≤ t) :
    s ⧸ H.subgroupOf s ↪ t ⧸ H.subgroupOf t
    where
  toFun :=
    Quotient.map' (inclusion h) fun a b => by
      simp_rw [leftRel_eq]
      -- ⊢ a⁻¹ * b ∈ subgroupOf H s → (↑(inclusion h) a)⁻¹ * ↑(inclusion h) b ∈ subgrou …
      exact id
      -- 🎉 no goals
  inj' :=
    Quotient.ind₂' <| by
      intro a b h
      -- ⊢ Quotient.mk'' a = Quotient.mk'' b
      simpa only [Quotient.map'_mk'', eq'] using h
      -- 🎉 no goals
#align subgroup.quotient_subgroup_of_embedding_of_le Subgroup.quotientSubgroupOfEmbeddingOfLE
#align add_subgroup.quotient_add_subgroup_of_embedding_of_le AddSubgroup.quotientAddSubgroupOfEmbeddingOfLE

-- porting note: I had to add the type ascription to the right-hand side or else Lean times out.
@[to_additive (attr := simp)]
theorem quotientSubgroupOfEmbeddingOfLE_apply_mk (H : Subgroup α) (h : s ≤ t) (g : s) :
    quotientSubgroupOfEmbeddingOfLE H h (QuotientGroup.mk g) =
      (QuotientGroup.mk (inclusion h g) : (fun _ => { x // x ∈ t } ⧸ subgroupOf H t) ↑g) :=
  rfl
#align subgroup.quotient_subgroup_of_embedding_of_le_apply_mk Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk
#align add_subgroup.quotient_add_subgroup_of_embedding_of_le_apply_mk AddSubgroup.quotientAddSubgroupOfEmbeddingOfLE_apply_mk

/-- If `s ≤ t`, then there is a map `H ⧸ s.subgroupOf H → H ⧸ t.subgroupOf H`. -/
@[to_additive "If `s ≤ t`, then there is a map `H ⧸ s.addSubgroupOf H → H ⧸ t.addSubgroupOf H`."]
def quotientSubgroupOfMapOfLE (H : Subgroup α) (h : s ≤ t) :
    H ⧸ s.subgroupOf H → H ⧸ t.subgroupOf H :=
  Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    -- ⊢ a⁻¹ * b ∈ subgroupOf s H → (id a)⁻¹ * id b ∈ subgroupOf t H
    apply h
    -- 🎉 no goals
#align subgroup.quotient_subgroup_of_map_of_le Subgroup.quotientSubgroupOfMapOfLE
#align add_subgroup.quotient_add_subgroup_of_map_of_le AddSubgroup.quotientAddSubgroupOfMapOfLE

-- porting note: I had to add the type ascription to the right-hand side or else Lean times out.
@[to_additive (attr := simp)]
theorem quotientSubgroupOfMapOfLE_apply_mk (H : Subgroup α) (h : s ≤ t) (g : H) :
    quotientSubgroupOfMapOfLE H h (QuotientGroup.mk g) =
      (QuotientGroup.mk g : { x // x ∈ H } ⧸ subgroupOf t H) :=
  rfl
#align subgroup.quotient_subgroup_of_map_of_le_apply_mk Subgroup.quotientSubgroupOfMapOfLE_apply_mk
#align add_subgroup.quotient_add_subgroup_of_map_of_le_apply_mk AddSubgroup.quotientAddSubgroupOfMapOfLE_apply_mk

/-- If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`. -/
@[to_additive "If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`."]
def quotientMapOfLE (h : s ≤ t) : α ⧸ s → α ⧸ t :=
  Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    -- ⊢ a⁻¹ * b ∈ s → (id a)⁻¹ * id b ∈ t
    apply h
    -- 🎉 no goals
#align subgroup.quotient_map_of_le Subgroup.quotientMapOfLE
#align add_subgroup.quotient_map_of_le AddSubgroup.quotientMapOfLE

@[to_additive (attr := simp)]
theorem quotientMapOfLE_apply_mk (h : s ≤ t) (g : α) :
    quotientMapOfLE h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl
#align subgroup.quotient_map_of_le_apply_mk Subgroup.quotientMapOfLE_apply_mk
#align add_subgroup.quotient_map_of_le_apply_mk AddSubgroup.quotientMapOfLE_apply_mk

/-- The natural embedding `H ⧸ (⨅ i, f i).subgroupOf H ↪ Π i, H ⧸ (f i).subgroupOf H`. -/
@[to_additive (attr := simps) "The natural embedding
 `H ⧸ (⨅ i, f i).addSubgroupOf H) ↪ Π i, H ⧸ (f i).addSubgroupOf H`."]
def quotientiInfSubgroupOfEmbedding {ι : Type*} (f : ι → Subgroup α) (H : Subgroup α) :
    H ⧸ (⨅ i, f i).subgroupOf H ↪ ∀ i, H ⧸ (f i).subgroupOf H
    where
  toFun q i := quotientSubgroupOfMapOfLE H (iInf_le f i) q
  inj' :=
    Quotient.ind₂' <| by
      simp_rw [funext_iff, quotientSubgroupOfMapOfLE_apply_mk, eq', mem_subgroupOf, mem_iInf,
        imp_self, forall_const]
#align subgroup.quotient_infi_subgroup_of_embedding Subgroup.quotientiInfSubgroupOfEmbedding
#align add_subgroup.quotient_infi_add_subgroup_of_embedding AddSubgroup.quotientiInfAddSubgroupOfEmbedding

-- porting note: I had to add the type ascription to the right-hand side or else Lean times out.
@[to_additive (attr := simp)]
theorem quotientiInfSubgroupOfEmbedding_apply_mk {ι : Type*} (f : ι → Subgroup α) (H : Subgroup α)
    (g : H) (i : ι) :
    quotientiInfSubgroupOfEmbedding f H (QuotientGroup.mk g) i =
      (QuotientGroup.mk g : { x // x ∈ H } ⧸ subgroupOf (f i) H) :=
  rfl
#align subgroup.quotient_infi_subgroup_of_embedding_apply_mk Subgroup.quotientiInfSubgroupOfEmbedding_apply_mk
#align add_subgroup.quotient_infi_add_subgroup_of_embedding_apply_mk AddSubgroup.quotientiInfAddSubgroupOfEmbedding_apply_mk

/-- The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`. -/
@[to_additive (attr := simps) "The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`."]
def quotientiInfEmbedding {ι : Type*} (f : ι → Subgroup α) : (α ⧸ ⨅ i, f i) ↪ ∀ i, α ⧸ f i
    where
  toFun q i := quotientMapOfLE (iInf_le f i) q
  inj' :=
    Quotient.ind₂' <| by
      simp_rw [funext_iff, quotientMapOfLE_apply_mk, eq', mem_iInf, imp_self, forall_const]
      -- 🎉 no goals
#align subgroup.quotient_infi_embedding Subgroup.quotientiInfEmbedding
#align add_subgroup.quotient_infi_embedding AddSubgroup.quotientiInfEmbedding

@[to_additive (attr := simp)]
theorem quotientiInfEmbedding_apply_mk {ι : Type*} (f : ι → Subgroup α) (g : α) (i : ι) :
    quotientiInfEmbedding f (QuotientGroup.mk g) i = QuotientGroup.mk g :=
  rfl
#align subgroup.quotient_infi_embedding_apply_mk Subgroup.quotientiInfEmbedding_apply_mk
#align add_subgroup.quotient_infi_embedding_apply_mk AddSubgroup.quotientiInfEmbedding_apply_mk

@[to_additive]
theorem card_eq_card_quotient_mul_card_subgroup [Fintype α] (s : Subgroup α) [Fintype s]
    [DecidablePred fun a => a ∈ s] : Fintype.card α = Fintype.card (α ⧸ s) * Fintype.card s := by
  rw [← Fintype.card_prod]; exact Fintype.card_congr Subgroup.groupEquivQuotientProdSubgroup
  -- ⊢ Fintype.card α = Fintype.card ((α ⧸ s) × { x // x ∈ s })
                            -- 🎉 no goals
#align subgroup.card_eq_card_quotient_mul_card_subgroup Subgroup.card_eq_card_quotient_mul_card_subgroup
#align add_subgroup.card_eq_card_quotient_add_card_add_subgroup AddSubgroup.card_eq_card_quotient_add_card_addSubgroup

/-- **Lagrange's Theorem**: The order of a subgroup divides the order of its ambient group. -/
@[to_additive "**Lagrange's Theorem**: The order of an additive subgroup divides the order of its
 ambient additive group."]
theorem card_subgroup_dvd_card [Fintype α] (s : Subgroup α) [Fintype s] :
    Fintype.card s ∣ Fintype.card α := by
  classical simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left ℕ]
  -- 🎉 no goals
#align subgroup.card_subgroup_dvd_card Subgroup.card_subgroup_dvd_card
#align add_subgroup.card_add_subgroup_dvd_card AddSubgroup.card_addSubgroup_dvd_card

@[to_additive]
theorem card_quotient_dvd_card [Fintype α] (s : Subgroup α) [DecidablePred (· ∈ s)] :
    Fintype.card (α ⧸ s) ∣ Fintype.card α := by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_right ℕ]
  -- 🎉 no goals
#align subgroup.card_quotient_dvd_card Subgroup.card_quotient_dvd_card
#align add_subgroup.card_quotient_dvd_card AddSubgroup.card_quotient_dvd_card

open Fintype

variable {H : Type*} [Group H]

@[to_additive]
theorem card_dvd_of_injective [Fintype α] [Fintype H] (f : α →* H) (hf : Function.Injective f) :
    card α ∣ card H := by
  classical calc
      card α = card (f.range : Subgroup H) := card_congr (Equiv.ofInjective f hf)
      _ ∣ card H := card_subgroup_dvd_card _
#align subgroup.card_dvd_of_injective Subgroup.card_dvd_of_injective
#align add_subgroup.card_dvd_of_injective AddSubgroup.card_dvd_of_injective

@[to_additive]
theorem card_dvd_of_le {H K : Subgroup α} [Fintype H] [Fintype K] (hHK : H ≤ K) : card H ∣ card K :=
  card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)
#align subgroup.card_dvd_of_le Subgroup.card_dvd_of_le
#align add_subgroup.card_dvd_of_le AddSubgroup.card_dvd_of_le

@[to_additive]
theorem card_comap_dvd_of_injective (K : Subgroup H) [Fintype K] (f : α →* H) [Fintype (K.comap f)]
    (hf : Function.Injective f) : Fintype.card (K.comap f) ∣ Fintype.card K := by
  haveI : Fintype ((K.comap f).map f) :=
      Fintype.ofEquiv _ (equivMapOfInjective _ _ hf).toEquiv;
    calc
      Fintype.card (K.comap f) = Fintype.card ((K.comap f).map f) :=
        Fintype.card_congr (equivMapOfInjective _ _ hf).toEquiv
      _ ∣ Fintype.card K := card_dvd_of_le (map_comap_le _ _)
#align subgroup.card_comap_dvd_of_injective Subgroup.card_comap_dvd_of_injective
#align add_subgroup.card_comap_dvd_of_injective AddSubgroup.card_comap_dvd_of_injective

end Subgroup

namespace QuotientGroup

variable [Group α]

/-- If `s` is a subgroup of the group `α`, and `t` is a subset of `α ⧸ s`, then there is a
(typically non-canonical) bijection between the preimage of `t` in `α` and the product `s × t`. -/
@[to_additive preimageMkEquivAddSubgroupProdSet
"If `s` is a subgroup of the additive group `α`, and `t` is a subset of `α ⧸ s`, then
 there is a (typically non-canonical) bijection between the preimage of `t` in `α` and the product
 `s × t`."]
noncomputable def preimageMkEquivSubgroupProdSet (s : Subgroup α) (t : Set (α ⧸ s)) :
    QuotientGroup.mk ⁻¹' t ≃ s × t
    where
  toFun a :=
    ⟨⟨((Quotient.out' (QuotientGroup.mk a)) : α)⁻¹ * a,
        leftRel_apply.mp (@Quotient.exact' _ (leftRel s) _ _ <| Quotient.out_eq' _)⟩,
      ⟨QuotientGroup.mk a, a.2⟩⟩
  invFun a :=
    ⟨Quotient.out' a.2.1 * a.1.1,
      show QuotientGroup.mk _ ∈ t by
        rw [mk_mul_of_mem _ a.1.2, out_eq']
        -- ⊢ ↑a.snd ∈ t
        exact a.2.2⟩
        -- 🎉 no goals
  left_inv := fun ⟨a, ha⟩ => Subtype.eq <| show _ * _ = a by simp
                                                             -- 🎉 no goals
  right_inv := fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ => by ext <;> simp [ha]
                                            -- ⊢ ↑((fun a => ({ val := (Quotient.out' ↑↑a)⁻¹ * ↑a, property := (_ : (Quotient …
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align quotient_group.preimage_mk_equiv_subgroup_times_set QuotientGroup.preimageMkEquivSubgroupProdSet
#align quotient_add_group.preimage_mk_equiv_add_subgroup_times_set QuotientAddGroup.preimageMkEquivAddSubgroupProdSet

end QuotientGroup
