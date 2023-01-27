/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison

! This file was ported from Lean 3 source module group_theory.coset
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Quotient
import Mathbin.Data.Fintype.Prod
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.GroupTheory.Subgroup.MulOpposite
import Mathbin.Tactic.Group

/-!
# Cosets

This file develops the basic theory of left and right cosets.

## Main definitions

* `left_coset a s`: the left coset `a * s` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `left_add_coset a s`.
* `right_coset s a`: the right coset `s * a` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `right_add_coset s a`.
* `quotient_group.quotient s`: the quotient type representing the left cosets with respect to a
  subgroup `s`, for an `add_group` this is `quotient_add_group.quotient s`.
* `quotient_group.mk`: the canonical map from `α` to `α/s` for a subgroup `s` of `α`, for an
  `add_group` this is `quotient_add_group.mk`.
* `subgroup.left_coset_equiv_subgroup`: the natural bijection between a left coset and the subgroup,
  for an `add_group` this is `add_subgroup.left_coset_equiv_add_subgroup`.

## Notation

* `a *l s`: for `left_coset a s`.
* `a +l s`: for `left_add_coset a s`.
* `s *r a`: for `right_coset s a`.
* `s +r a`: for `right_add_coset s a`.

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`
-/


open Set Function

variable {α : Type _}

/-- The left coset `a * s` for an element `a : α` and a subset `s : set α` -/
@[to_additive leftAddCoset "The left coset `a+s` for an element `a : α`\nand a subset `s : set α`"]
def leftCoset [Mul α] (a : α) (s : Set α) : Set α :=
  (fun x => a * x) '' s
#align left_coset leftCoset
#align left_add_coset leftAddCoset

/-- The right coset `s * a` for an element `a : α` and a subset `s : set α` -/
@[to_additive rightAddCoset
      "The right coset `s+a` for an element `a : α`\nand a subset `s : set α`"]
def rightCoset [Mul α] (s : Set α) (a : α) : Set α :=
  (fun x => x * a) '' s
#align right_coset rightCoset
#align right_add_coset rightAddCoset

-- mathport name: left_coset
scoped[Coset] infixl:70 " *l " => leftCoset

-- mathport name: left_add_coset
scoped[Coset] infixl:70 " +l " => leftAddCoset

-- mathport name: right_coset
scoped[Coset] infixl:70 " *r " => rightCoset

-- mathport name: right_add_coset
scoped[Coset] infixl:70 " +r " => rightAddCoset

section CosetMul

variable [Mul α]

@[to_additive mem_left_add_coset]
theorem mem_leftCoset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ a *l s :=
  mem_image_of_mem (fun b : α => a * b) hxS
#align mem_left_coset mem_leftCoset
#align mem_left_add_coset mem_left_add_coset

@[to_additive mem_right_add_coset]
theorem mem_rightCoset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ s *r a :=
  mem_image_of_mem (fun b : α => b * a) hxS
#align mem_right_coset mem_rightCoset
#align mem_right_add_coset mem_right_add_coset

/-- Equality of two left cosets `a * s` and `b * s`. -/
@[to_additive LeftAddCosetEquivalence "Equality of two left cosets `a + s` and `b + s`."]
def LeftCosetEquivalence (s : Set α) (a b : α) :=
  a *l s = b *l s
#align left_coset_equivalence LeftCosetEquivalence
#align left_add_coset_equivalence LeftAddCosetEquivalence

@[to_additive left_add_coset_equivalence_rel]
theorem leftCosetEquivalence_rel (s : Set α) : Equivalence (LeftCosetEquivalence s) :=
  Equivalence.mk (LeftCosetEquivalence s) (fun a => rfl) (fun a b => Eq.symm) fun a b c => Eq.trans
#align left_coset_equivalence_rel leftCosetEquivalence_rel
#align left_add_coset_equivalence_rel left_add_coset_equivalence_rel

/-- Equality of two right cosets `s * a` and `s * b`. -/
@[to_additive RightAddCosetEquivalence "Equality of two right cosets `s + a` and `s + b`."]
def RightCosetEquivalence (s : Set α) (a b : α) :=
  s *r a = s *r b
#align right_coset_equivalence RightCosetEquivalence
#align right_add_coset_equivalence RightAddCosetEquivalence

@[to_additive right_add_coset_equivalence_rel]
theorem rightCosetEquivalence_rel (s : Set α) : Equivalence (RightCosetEquivalence s) :=
  Equivalence.mk (RightCosetEquivalence s) (fun a => rfl) (fun a b => Eq.symm) fun a b c => Eq.trans
#align right_coset_equivalence_rel rightCosetEquivalence_rel
#align right_add_coset_equivalence_rel right_add_coset_equivalence_rel

end CosetMul

section CosetSemigroup

variable [Semigroup α]

@[simp, to_additive left_add_coset_assoc]
theorem leftCoset_assoc (s : Set α) (a b : α) : a *l (b *l s) = a * b *l s := by
  simp [leftCoset, rightCoset, (image_comp _ _ _).symm, Function.comp, mul_assoc]
#align left_coset_assoc leftCoset_assoc
#align left_add_coset_assoc left_add_coset_assoc

@[simp, to_additive right_add_coset_assoc]
theorem rightCoset_assoc (s : Set α) (a b : α) : s *r a *r b = s *r (a * b) := by
  simp [leftCoset, rightCoset, (image_comp _ _ _).symm, Function.comp, mul_assoc]
#align right_coset_assoc rightCoset_assoc
#align right_add_coset_assoc right_add_coset_assoc

@[to_additive left_add_coset_right_add_coset]
theorem leftCoset_rightCoset (s : Set α) (a b : α) : a *l s *r b = a *l (s *r b) := by
  simp [leftCoset, rightCoset, (image_comp _ _ _).symm, Function.comp, mul_assoc]
#align left_coset_right_coset leftCoset_rightCoset
#align left_add_coset_right_add_coset left_add_coset_right_add_coset

end CosetSemigroup

section CosetMonoid

variable [Monoid α] (s : Set α)

@[simp, to_additive zero_left_add_coset]
theorem one_leftCoset : 1 *l s = s :=
  Set.ext <| by simp [leftCoset]
#align one_left_coset one_leftCoset
#align zero_left_add_coset zero_left_add_coset

@[simp, to_additive right_add_coset_zero]
theorem rightCoset_one : s *r 1 = s :=
  Set.ext <| by simp [rightCoset]
#align right_coset_one rightCoset_one
#align right_add_coset_zero right_add_coset_zero

end CosetMonoid

section CosetSubmonoid

open Submonoid

variable [Monoid α] (s : Submonoid α)

@[to_additive mem_own_left_add_coset]
theorem mem_own_leftCoset (a : α) : a ∈ a *l s :=
  suffices a * 1 ∈ a *l s by simpa
  mem_leftCoset a (one_mem s : 1 ∈ s)
#align mem_own_left_coset mem_own_leftCoset
#align mem_own_left_add_coset mem_own_left_add_coset

@[to_additive mem_own_right_add_coset]
theorem mem_own_rightCoset (a : α) : a ∈ (s : Set α) *r a :=
  suffices 1 * a ∈ (s : Set α) *r a by simpa
  mem_rightCoset a (one_mem s : 1 ∈ s)
#align mem_own_right_coset mem_own_rightCoset
#align mem_own_right_add_coset mem_own_right_add_coset

@[to_additive mem_left_add_coset_left_add_coset]
theorem mem_leftCoset_leftCoset {a : α} (ha : a *l s = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha] <;> exact mem_own_leftCoset s a
#align mem_left_coset_left_coset mem_leftCoset_leftCoset
#align mem_left_add_coset_left_add_coset mem_left_add_coset_left_add_coset

@[to_additive mem_right_add_coset_right_add_coset]
theorem mem_rightCoset_rightCoset {a : α} (ha : (s : Set α) *r a = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha] <;> exact mem_own_rightCoset s a
#align mem_right_coset_right_coset mem_rightCoset_rightCoset
#align mem_right_add_coset_right_add_coset mem_right_add_coset_right_add_coset

end CosetSubmonoid

section CosetGroup

variable [Group α] {s : Set α} {x : α}

@[to_additive mem_left_add_coset_iff]
theorem mem_leftCoset_iff (a : α) : x ∈ a *l s ↔ a⁻¹ * x ∈ s :=
  Iff.intro (fun ⟨b, hb, Eq⟩ => by simp [Eq.symm, hb]) fun h => ⟨a⁻¹ * x, h, by simp⟩
#align mem_left_coset_iff mem_leftCoset_iff
#align mem_left_add_coset_iff mem_left_add_coset_iff

@[to_additive mem_right_add_coset_iff]
theorem mem_rightCoset_iff (a : α) : x ∈ s *r a ↔ x * a⁻¹ ∈ s :=
  Iff.intro (fun ⟨b, hb, Eq⟩ => by simp [Eq.symm, hb]) fun h => ⟨x * a⁻¹, h, by simp⟩
#align mem_right_coset_iff mem_rightCoset_iff
#align mem_right_add_coset_iff mem_right_add_coset_iff

end CosetGroup

section CosetSubgroup

open Subgroup

variable [Group α] (s : Subgroup α)

@[to_additive left_add_coset_mem_left_add_coset]
theorem leftCoset_mem_leftCoset {a : α} (ha : a ∈ s) : a *l s = s :=
  Set.ext <| by simp [mem_leftCoset_iff, mul_mem_cancel_left (s.inv_mem ha)]
#align left_coset_mem_left_coset leftCoset_mem_leftCoset
#align left_add_coset_mem_left_add_coset left_add_coset_mem_left_add_coset

@[to_additive right_add_coset_mem_right_add_coset]
theorem rightCoset_mem_rightCoset {a : α} (ha : a ∈ s) : (s : Set α) *r a = s :=
  Set.ext fun b => by simp [mem_rightCoset_iff, mul_mem_cancel_right (s.inv_mem ha)]
#align right_coset_mem_right_coset rightCoset_mem_rightCoset
#align right_add_coset_mem_right_add_coset right_add_coset_mem_right_add_coset

@[to_additive]
theorem orbit_subgroup_eq_rightCoset (a : α) : MulAction.orbit s a = s *r a :=
  Set.ext fun b => ⟨fun ⟨c, d⟩ => ⟨c, c.2, d⟩, fun ⟨c, d, e⟩ => ⟨⟨c, d⟩, e⟩⟩
#align orbit_subgroup_eq_right_coset orbit_subgroup_eq_rightCoset
#align orbit_add_subgroup_eq_right_coset orbit_add_subgroup_eq_right_coset

@[to_additive]
theorem orbit_subgroup_eq_self_of_mem {a : α} (ha : a ∈ s) : MulAction.orbit s a = s :=
  (orbit_subgroup_eq_rightCoset s a).trans (rightCoset_mem_rightCoset s ha)
#align orbit_subgroup_eq_self_of_mem orbit_subgroup_eq_self_of_mem
#align orbit_add_subgroup_eq_self_of_mem orbit_add_subgroup_eq_self_of_mem

@[to_additive]
theorem orbit_subgroup_one_eq_self : MulAction.orbit s (1 : α) = s :=
  orbit_subgroup_eq_self_of_mem s s.one_mem
#align orbit_subgroup_one_eq_self orbit_subgroup_one_eq_self
#align orbit_add_subgroup_zero_eq_self orbit_add_subgroup_zero_eq_self

@[to_additive eq_add_cosets_of_normal]
theorem eq_cosets_of_normal (N : s.Normal) (g : α) : g *l s = s *r g :=
  Set.ext fun a => by simp [mem_leftCoset_iff, mem_rightCoset_iff] <;> rw [N.mem_comm_iff]
#align eq_cosets_of_normal eq_cosets_of_normal
#align eq_add_cosets_of_normal eq_add_cosets_of_normal

@[to_additive normal_of_eq_add_cosets]
theorem normal_of_eq_cosets (h : ∀ g : α, g *l s = s *r g) : s.Normal :=
  ⟨fun a ha g =>
    show g * a * g⁻¹ ∈ (s : Set α) by rw [← mem_rightCoset_iff, ← h] <;> exact mem_leftCoset g ha⟩
#align normal_of_eq_cosets normal_of_eq_cosets
#align normal_of_eq_add_cosets normal_of_eq_add_cosets

@[to_additive normal_iff_eq_add_cosets]
theorem normal_iff_eq_cosets : s.Normal ↔ ∀ g : α, g *l s = s *r g :=
  ⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩
#align normal_iff_eq_cosets normal_iff_eq_cosets
#align normal_iff_eq_add_cosets normal_iff_eq_add_cosets

@[to_additive left_add_coset_eq_iff]
theorem leftCoset_eq_iff {x y : α} : leftCoset x s = leftCoset y s ↔ x⁻¹ * y ∈ s :=
  by
  rw [Set.ext_iff]
  simp_rw [mem_leftCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [mul_left_inv]
    exact s.one_mem
  · intro h z
    rw [← mul_inv_cancel_right x⁻¹ y]
    rw [mul_assoc]
    exact s.mul_mem_cancel_left h
#align left_coset_eq_iff leftCoset_eq_iff
#align left_add_coset_eq_iff left_add_coset_eq_iff

@[to_additive right_add_coset_eq_iff]
theorem rightCoset_eq_iff {x y : α} : rightCoset (↑s) x = rightCoset s y ↔ y * x⁻¹ ∈ s :=
  by
  rw [Set.ext_iff]
  simp_rw [mem_rightCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [mul_right_inv]
    exact s.one_mem
  · intro h z
    rw [← inv_mul_cancel_left y x⁻¹]
    rw [← mul_assoc]
    exact s.mul_mem_cancel_right h
#align right_coset_eq_iff rightCoset_eq_iff
#align right_add_coset_eq_iff right_add_coset_eq_iff

end CosetSubgroup

run_cmd
  to_additive.map_namespace `quotient_group `quotient_add_group

namespace QuotientGroup

variable [Group α] (s : Subgroup α)

/-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup.-/
@[to_additive
      "The equivalence relation corresponding to the partition of a group by left cosets\nof a subgroup."]
def leftRel : Setoid α :=
  MulAction.orbitRel s.opposite α
#align quotient_group.left_rel QuotientGroup.leftRel
#align quotient_add_group.left_rel quotientAddGroup.leftRel

variable {s}

@[to_additive]
theorem leftRel_apply {x y : α} : @Setoid.r _ (leftRel s) x y ↔ x⁻¹ * y ∈ s :=
  calc
    (∃ a : s.opposite, y * MulOpposite.unop a = x) ↔ ∃ a : s, y * a = x :=
      s.oppositeEquiv.symm.exists_congr_left
    _ ↔ ∃ a : s, x⁻¹ * y = a⁻¹ := by simp only [inv_mul_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq]
    _ ↔ x⁻¹ * y ∈ s := by simp [SetLike.exists]
    
#align quotient_group.left_rel_apply QuotientGroup.leftRel_apply
#align quotient_add_group.left_rel_apply quotientAddGroup.leftRel_apply

variable (s)

@[to_additive]
theorem leftRel_eq : @Setoid.r _ (leftRel s) = fun x y => x⁻¹ * y ∈ s :=
  funext₂ <| by
    simp only [eq_iff_iff]
    apply left_rel_apply
#align quotient_group.left_rel_eq QuotientGroup.leftRel_eq
#align quotient_add_group.left_rel_eq quotientAddGroup.leftRel_eq

theorem leftRel_r_eq_leftCosetEquivalence :
    @Setoid.r _ (QuotientGroup.leftRel s) = LeftCosetEquivalence s :=
  by
  ext
  rw [left_rel_eq]
  exact (leftCoset_eq_iff s).symm
#align quotient_group.left_rel_r_eq_left_coset_equivalence QuotientGroup.leftRel_r_eq_leftCosetEquivalence

@[to_additive]
instance leftRelDecidable [DecidablePred (· ∈ s)] : DecidableRel (leftRel s).R := fun x y =>
  by
  rw [left_rel_eq]
  exact ‹DecidablePred (· ∈ s)› _
#align quotient_group.left_rel_decidable QuotientGroup.leftRelDecidable
#align quotient_add_group.left_rel_decidable quotientAddGroup.leftRelDecidable

/-- `α ⧸ s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `α ⧸ s` is a group -/
@[to_additive
      "`α ⧸ s` is the quotient type representing the left cosets of `s`.  If `s` is a\nnormal subgroup, `α ⧸ s` is a group"]
instance : HasQuotient α (Subgroup α) :=
  ⟨fun s => Quotient (leftRel s)⟩

/-- The equivalence relation corresponding to the partition of a group by right cosets of a
subgroup. -/
@[to_additive
      "The equivalence relation corresponding to the partition of a group by right cosets of\na subgroup."]
def rightRel : Setoid α :=
  MulAction.orbitRel s α
#align quotient_group.right_rel QuotientGroup.rightRel
#align quotient_add_group.right_rel quotientAddGroup.rightRel

variable {s}

@[to_additive]
theorem rightRel_apply {x y : α} : @Setoid.r _ (rightRel s) x y ↔ y * x⁻¹ ∈ s :=
  calc
    (∃ a : s, (a : α) * y = x) ↔ ∃ a : s, y * x⁻¹ = a⁻¹ := by
      simp only [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq]
    _ ↔ y * x⁻¹ ∈ s := by simp [SetLike.exists]
    
#align quotient_group.right_rel_apply QuotientGroup.rightRel_apply
#align quotient_add_group.right_rel_apply quotientAddGroup.rightRel_apply

variable (s)

@[to_additive]
theorem rightRel_eq : @Setoid.r _ (rightRel s) = fun x y => y * x⁻¹ ∈ s :=
  funext₂ <| by
    simp only [eq_iff_iff]
    apply right_rel_apply
#align quotient_group.right_rel_eq QuotientGroup.rightRel_eq
#align quotient_add_group.right_rel_eq quotientAddGroup.rightRel_eq

theorem rightRel_r_eq_rightCosetEquivalence :
    @Setoid.r _ (QuotientGroup.rightRel s) = RightCosetEquivalence s :=
  by
  ext
  rw [right_rel_eq]
  exact (rightCoset_eq_iff s).symm
#align quotient_group.right_rel_r_eq_right_coset_equivalence QuotientGroup.rightRel_r_eq_rightCosetEquivalence

@[to_additive]
instance rightRelDecidable [DecidablePred (· ∈ s)] : DecidableRel (rightRel s).R := fun x y =>
  by
  rw [right_rel_eq]
  exact ‹DecidablePred (· ∈ s)› _
#align quotient_group.right_rel_decidable QuotientGroup.rightRelDecidable
#align quotient_add_group.right_rel_decidable quotientAddGroup.rightRelDecidable

/-- Right cosets are in bijection with left cosets. -/
@[to_additive "Right cosets are in bijection with left cosets."]
def quotientRightRelEquivQuotientLeftRel : Quotient (QuotientGroup.rightRel s) ≃ α ⧸ s
    where
  toFun :=
    Quotient.map' (fun g => g⁻¹) fun a b =>
      by
      rw [left_rel_apply, right_rel_apply]
      exact fun h => (congr_arg (· ∈ s) (by group)).mp (s.inv_mem h)
  invFun :=
    Quotient.map' (fun g => g⁻¹) fun a b =>
      by
      rw [left_rel_apply, right_rel_apply]
      exact fun h => (congr_arg (· ∈ s) (by group)).mp (s.inv_mem h)
  left_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          exact Quotient.exact' rfl)
  right_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          exact Quotient.exact' rfl)
#align quotient_group.quotient_right_rel_equiv_quotient_left_rel QuotientGroup.quotientRightRelEquivQuotientLeftRel
#align quotient_add_group.quotient_right_rel_equiv_quotient_left_rel quotientAddGroup.quotientRightRelEquivQuotientLeftRel

@[to_additive]
instance fintypeQuotientRightRel [Fintype (α ⧸ s)] :
    Fintype (Quotient (QuotientGroup.rightRel s)) :=
  Fintype.ofEquiv (α ⧸ s) (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm
#align quotient_group.fintype_quotient_right_rel QuotientGroup.fintypeQuotientRightRel
#align quotient_add_group.fintype_quotient_right_rel quotientAddGroup.fintypeQuotientRightRel

@[to_additive]
theorem card_quotient_rightRel [Fintype (α ⧸ s)] :
    Fintype.card (Quotient (QuotientGroup.rightRel s)) = Fintype.card (α ⧸ s) :=
  Fintype.ofEquiv_card (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm
#align quotient_group.card_quotient_right_rel QuotientGroup.card_quotient_rightRel
#align quotient_add_group.card_quotient_right_rel quotientAddGroup.card_quotient_rightRel

end QuotientGroup

namespace QuotientGroup

variable [Group α] {s : Subgroup α}

@[to_additive]
instance fintype [Fintype α] (s : Subgroup α) [DecidableRel (leftRel s).R] : Fintype (α ⧸ s) :=
  Quotient.fintype (leftRel s)
#align quotient_group.fintype QuotientGroup.fintype
#align quotient_add_group.fintype quotientAddGroup.fintype

/-- The canonical map from a group `α` to the quotient `α ⧸ s`. -/
@[to_additive "The canonical map from an `add_group` `α` to the quotient `α ⧸ s`."]
abbrev mk (a : α) : α ⧸ s :=
  Quotient.mk'' a
#align quotient_group.mk QuotientGroup.mk
#align quotient_add_group.mk quotientAddGroup.mk

@[to_additive]
theorem mk_surjective : Function.Surjective <| @mk _ _ s :=
  Quotient.surjective_Quotient_mk''
#align quotient_group.mk_surjective QuotientGroup.mk_surjective
#align quotient_add_group.mk_surjective quotientAddGroup.mk_surjective

@[elab_as_elim, to_additive]
theorem induction_on {C : α ⧸ s → Prop} (x : α ⧸ s) (H : ∀ z, C (QuotientGroup.mk z)) : C x :=
  Quotient.inductionOn' x H
#align quotient_group.induction_on QuotientGroup.induction_on
#align quotient_add_group.induction_on quotientAddGroup.induction_on

@[to_additive]
instance : CoeTC α (α ⧸ s) :=
  ⟨mk⟩

-- note [use has_coe_t]
@[elab_as_elim, to_additive]
theorem induction_on' {C : α ⧸ s → Prop} (x : α ⧸ s) (H : ∀ z : α, C z) : C x :=
  Quotient.inductionOn' x H
#align quotient_group.induction_on' QuotientGroup.induction_on'
#align quotient_add_group.induction_on' quotientAddGroup.induction_on'

@[simp, to_additive]
theorem quotient_lift_on_coe {β} (f : α → β) (h) (x : α) : Quotient.liftOn' (x : α ⧸ s) f h = f x :=
  rfl
#align quotient_group.quotient_lift_on_coe QuotientGroup.quotient_lift_on_coe
#align quotient_add_group.quotient_lift_on_coe quotientAddGroup.quotient_lift_on_coe

@[to_additive]
theorem forall_coe {C : α ⧸ s → Prop} : (∀ x : α ⧸ s, C x) ↔ ∀ x : α, C x :=
  mk_surjective.forall
#align quotient_group.forall_coe QuotientGroup.forall_coe
#align quotient_add_group.forall_coe quotientAddGroup.forall_coe

@[to_additive]
theorem exists_coe {C : α ⧸ s → Prop} : (∃ x : α ⧸ s, C x) ↔ ∃ x : α, C x :=
  mk_surjective.exists
#align quotient_group.exists_coe QuotientGroup.exists_coe
#align quotient_add_group.exists_coe quotientAddGroup.exists_coe

@[to_additive]
instance (s : Subgroup α) : Inhabited (α ⧸ s) :=
  ⟨((1 : α) : α ⧸ s)⟩

@[to_additive quotientAddGroup.eq]
protected theorem eq {a b : α} : (a : α ⧸ s) = b ↔ a⁻¹ * b ∈ s :=
  calc
    _ ↔ @Setoid.r _ (leftRel s) a b := Quotient.eq''
    _ ↔ _ := by rw [left_rel_apply]
    
#align quotient_group.eq QuotientGroup.eq
#align quotient_add_group.eq quotientAddGroup.eq

@[to_additive quotientAddGroup.eq']
theorem eq' {a b : α} : (mk a : α ⧸ s) = mk b ↔ a⁻¹ * b ∈ s :=
  QuotientGroup.eq
#align quotient_group.eq' QuotientGroup.eq'
#align quotient_add_group.eq' quotientAddGroup.eq'

@[simp, to_additive quotientAddGroup.out_eq']
theorem out_eq' (a : α ⧸ s) : mk a.out' = a :=
  Quotient.out_eq' a
#align quotient_group.out_eq' QuotientGroup.out_eq'
#align quotient_add_group.out_eq' quotientAddGroup.out_eq'

variable (s)

/- It can be useful to write `obtain ⟨h, H⟩ := mk_out'_eq_mul ...`, and then `rw [H]` or
  `simp_rw [H]` or `simp only [H]`. In order for `simp_rw` and `simp only` to work, this lemma is
  stated in terms of an arbitrary `h : s`, rathern that the specific `h = g⁻¹ * (mk g).out'`. -/
@[to_additive quotientAddGroup.mk_out'_eq_mul]
theorem mk_out'_eq_mul (g : α) : ∃ h : s, (mk g : α ⧸ s).out' = g * h :=
  ⟨⟨g⁻¹ * (mk g).out', eq'.mp (mk g).out_eq'.symm⟩, by rw [[anonymous], mul_inv_cancel_left]⟩
#align quotient_group.mk_out'_eq_mul QuotientGroup.mk_out'_eq_mul
#align quotient_add_group.mk_out'_eq_mul quotientAddGroup.mk_out'_eq_mul

variable {s} {a b : α}

@[simp, to_additive quotientAddGroup.mk_add_of_mem]
theorem mk_mul_of_mem (a : α) (hb : b ∈ s) : (mk (a * b) : α ⧸ s) = mk a := by
  rwa [eq', mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]
#align quotient_group.mk_mul_of_mem QuotientGroup.mk_mul_of_mem
#align quotient_add_group.mk_add_of_mem quotientAddGroup.mk_add_of_mem

@[to_additive]
theorem eq_class_eq_leftCoset (s : Subgroup α) (g : α) :
    { x : α | (x : α ⧸ s) = g } = leftCoset g s :=
  Set.ext fun z => by
    rw [mem_leftCoset_iff, Set.mem_setOf_eq, eq_comm, QuotientGroup.eq, SetLike.mem_coe]
#align quotient_group.eq_class_eq_left_coset QuotientGroup.eq_class_eq_leftCoset
#align quotient_add_group.eq_class_eq_left_coset quotientAddGroup.eq_class_eq_leftCoset

@[to_additive]
theorem preimage_image_coe (N : Subgroup α) (s : Set α) :
    coe ⁻¹' ((coe : α → α ⧸ N) '' s) = ⋃ x : N, (fun y : α => y * x) ⁻¹' s :=
  by
  ext x
  simp only [QuotientGroup.eq, SetLike.exists, exists_prop, Set.mem_preimage, Set.mem_unionᵢ,
    Set.mem_image, [anonymous], ← eq_inv_mul_iff_mul_eq]
  exact
    ⟨fun ⟨y, hs, hN⟩ => ⟨_, N.inv_mem hN, by simpa using hs⟩, fun ⟨z, hz, hxz⟩ =>
      ⟨x * z, hxz, by simpa using hz⟩⟩
#align quotient_group.preimage_image_coe QuotientGroup.preimage_image_coe
#align quotient_add_group.preimage_image_coe quotientAddGroup.preimage_image_coe

end QuotientGroup

namespace Subgroup

open QuotientGroup

variable [Group α] {s : Subgroup α}

/-- The natural bijection between a left coset `g * s` and `s`. -/
@[to_additive "The natural bijection between the cosets `g + s` and `s`."]
def leftCosetEquivSubgroup (g : α) : leftCoset g s ≃ s :=
  ⟨fun x => ⟨g⁻¹ * x.1, (mem_leftCoset_iff _).1 x.2⟩, fun x => ⟨g * x.1, x.1, x.2, rfl⟩,
    fun ⟨x, hx⟩ => Subtype.eq <| by simp, fun ⟨g, hg⟩ => Subtype.eq <| by simp⟩
#align subgroup.left_coset_equiv_subgroup Subgroup.leftCosetEquivSubgroup
#align add_subgroup.left_coset_equiv_add_subgroup AddSubgroup.leftCosetEquivAddSubgroup

/-- The natural bijection between a right coset `s * g` and `s`. -/
@[to_additive "The natural bijection between the cosets `s + g` and `s`."]
def rightCosetEquivSubgroup (g : α) : rightCoset (↑s) g ≃ s :=
  ⟨fun x => ⟨x.1 * g⁻¹, (mem_rightCoset_iff _).1 x.2⟩, fun x => ⟨x.1 * g, x.1, x.2, rfl⟩,
    fun ⟨x, hx⟩ => Subtype.eq <| by simp, fun ⟨g, hg⟩ => Subtype.eq <| by simp⟩
#align subgroup.right_coset_equiv_subgroup Subgroup.rightCosetEquivSubgroup
#align add_subgroup.right_coset_equiv_add_subgroup AddSubgroup.rightCosetEquivAddSubgroup

/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
@[to_additive "A (non-canonical) bijection between an add_group `α` and the product `(α/s) × s`"]
noncomputable def groupEquivQuotientTimesSubgroup : α ≃ (α ⧸ s) × s :=
  calc
    α ≃ ΣL : α ⧸ s, { x : α // (x : α ⧸ s) = L } := (Equiv.sigmaFiberEquiv QuotientGroup.mk).symm
    _ ≃ ΣL : α ⧸ s, leftCoset (Quotient.out' L) s :=
      Equiv.sigmaCongrRight fun L => by
        rw [← eq_class_eq_left_coset]
        show
          (_root_.subtype fun x : α => Quotient.mk'' x = L) ≃
            _root_.subtype fun x : α => Quotient.mk'' x = Quotient.mk'' _
        simp [-Quotient.eq'']
    _ ≃ ΣL : α ⧸ s, s := Equiv.sigmaCongrRight fun L => leftCosetEquivSubgroup _
    _ ≃ (α ⧸ s) × s := Equiv.sigmaEquivProd _ _
    
#align subgroup.group_equiv_quotient_times_subgroup Subgroup.groupEquivQuotientTimesSubgroup
#align add_subgroup.add_group_equiv_quotient_times_add_subgroup AddSubgroup.addGroupEquivQuotientTimesAddSubgroup

variable {t : Subgroup α}

/-- If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection. -/
@[to_additive "If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection."]
def quotientEquivOfEq (h : s = t) : α ⧸ s ≃ α ⧸ t
    where
  toFun := Quotient.map' id fun a b h' => h ▸ h'
  invFun := Quotient.map' id fun a b h' => h.symm ▸ h'
  left_inv q := induction_on' q fun g => rfl
  right_inv q := induction_on' q fun g => rfl
#align subgroup.quotient_equiv_of_eq Subgroup.quotientEquivOfEq
#align add_subgroup.quotient_equiv_of_eq AddSubgroup.quotientEquivOfEq

theorem quotientEquivOfEq_mk (h : s = t) (a : α) :
    quotientEquivOfEq h (QuotientGroup.mk a) = QuotientGroup.mk a :=
  rfl
#align subgroup.quotient_equiv_of_eq_mk Subgroup.quotientEquivOfEq_mk

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
of the quotient map `G → G/K`. The classical version is `quotient_equiv_prod_of_le`. -/
@[to_additive
      "If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse\nof the quotient map `G → G/K`. The classical version is `quotient_equiv_prod_of_le`.",
  simps]
def quotientEquivProdOfLe' (h_le : s ≤ t) (f : α ⧸ t → α)
    (hf : Function.RightInverse f QuotientGroup.mk) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t
    where
  toFun a :=
    ⟨a.map' id fun b c h => leftRel_apply.mpr (h_le (leftRel_apply.mp h)),
      a.map' (fun g : α => ⟨(f (Quotient.mk'' g))⁻¹ * g, leftRel_apply.mp (Quotient.exact' (hf g))⟩)
        fun b c h => by
        rw [left_rel_apply]
        change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) ∈ s
        have key : f b = f c :=
          congr_arg f (Quotient.sound' (left_rel_apply.mpr (h_le (left_rel_apply.mp h))))
        rwa [key, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, ← left_rel_apply]⟩
  invFun a :=
    a.2.map' (fun b => f a.1 * b) fun b c h =>
      by
      rw [left_rel_apply] at h⊢
      change (f a.1 * b)⁻¹ * (f a.1 * c) ∈ s
      rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  left_inv := by
    refine' Quotient.ind' fun a => _
    simp_rw [Quotient.map'_mk'', id.def, [anonymous], mul_inv_cancel_left]
  right_inv := by
    refine' Prod.rec _
    refine' Quotient.ind' fun a => _
    refine' Quotient.ind' fun b => _
    have key : Quotient.mk'' (f (Quotient.mk'' a) * b) = Quotient.mk'' a :=
      (QuotientGroup.mk_mul_of_mem (f a) b.2).trans (hf a)
    simp_rw [Quotient.map'_mk'', id.def, key, inv_mul_cancel_left, Subtype.coe_eta]
#align subgroup.quotient_equiv_prod_of_le' Subgroup.quotientEquivProdOfLe'
#align add_subgroup.quotient_equiv_sum_of_le' AddSubgroup.quotientEquivSumOfLe'

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.
The constructive version is `quotient_equiv_prod_of_le'`. -/
@[to_additive
      "If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.\nThe constructive version is `quotient_equiv_prod_of_le'`.",
  simps]
noncomputable def quotientEquivProdOfLe (h_le : s ≤ t) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t :=
  quotientEquivProdOfLe' h_le Quotient.out' Quotient.out_eq'
#align subgroup.quotient_equiv_prod_of_le Subgroup.quotientEquivProdOfLe
#align add_subgroup.quotient_equiv_sum_of_le AddSubgroup.quotientEquivSumOfLe

/-- If `s ≤ t`, then there is an embedding `s ⧸ H.subgroup_of s ↪ t ⧸ H.subgroup_of t`. -/
@[to_additive
      "If `s ≤ t`, then there is an embedding\n  `s ⧸ H.add_subgroup_of s ↪ t ⧸ H.add_subgroup_of t`."]
def quotientSubgroupOfEmbeddingOfLe (H : Subgroup α) (h : s ≤ t) :
    s ⧸ H.subgroupOf s ↪ t ⧸ H.subgroupOf t
    where
  toFun :=
    Quotient.map' (inclusion h) fun a b =>
      by
      simp_rw [left_rel_eq]
      exact id
  inj' :=
    Quotient.ind₂' <| by
      intro a b h
      simpa only [Quotient.map'_mk'', eq'] using h
#align subgroup.quotient_subgroup_of_embedding_of_le Subgroup.quotientSubgroupOfEmbeddingOfLe
#align add_subgroup.quotient_add_subgroup_of_embedding_of_le AddSubgroup.quotientAddSubgroupOfEmbeddingOfLe

@[simp, to_additive]
theorem quotientSubgroupOfEmbeddingOfLe_apply_mk (H : Subgroup α) (h : s ≤ t) (g : s) :
    quotientSubgroupOfEmbeddingOfLe H h (QuotientGroup.mk g) = QuotientGroup.mk (inclusion h g) :=
  rfl
#align subgroup.quotient_subgroup_of_embedding_of_le_apply_mk Subgroup.quotientSubgroupOfEmbeddingOfLe_apply_mk
#align add_subgroup.quotient_add_subgroup_of_embedding_of_le_apply_mk AddSubgroup.quotient_add_subgroup_of_embedding_of_le_apply_mk

/-- If `s ≤ t`, then there is a map `H ⧸ s.subgroup_of H → H ⧸ t.subgroup_of H`. -/
@[to_additive
      "If `s ≤ t`, then there is an map\n  `H ⧸ s.add_subgroup_of H → H ⧸ t.add_subgroup_of H`."]
def quotientSubgroupOfMapOfLe (H : Subgroup α) (h : s ≤ t) :
    H ⧸ s.subgroupOf H → H ⧸ t.subgroupOf H :=
  Quotient.map' id fun a b => by
    simp_rw [left_rel_eq]
    apply h
#align subgroup.quotient_subgroup_of_map_of_le Subgroup.quotientSubgroupOfMapOfLe
#align add_subgroup.quotient_add_subgroup_of_map_of_le AddSubgroup.quotientAddSubgroupOfMapOfLe

@[simp, to_additive]
theorem quotientSubgroupOfMapOfLe_apply_mk (H : Subgroup α) (h : s ≤ t) (g : H) :
    quotientSubgroupOfMapOfLe H h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl
#align subgroup.quotient_subgroup_of_map_of_le_apply_mk Subgroup.quotientSubgroupOfMapOfLe_apply_mk
#align add_subgroup.quotient_add_subgroup_of_map_of_le_apply_mk AddSubgroup.quotient_add_subgroup_of_map_of_le_apply_mk

/-- If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`. -/
@[to_additive "If `s ≤ t`, then there is an map `α ⧸ s → α ⧸ t`."]
def quotientMapOfLe (h : s ≤ t) : α ⧸ s → α ⧸ t :=
  Quotient.map' id fun a b => by
    simp_rw [left_rel_eq]
    apply h
#align subgroup.quotient_map_of_le Subgroup.quotientMapOfLe
#align add_subgroup.quotient_map_of_le AddSubgroup.quotientMapOfLe

@[simp, to_additive]
theorem quotientMapOfLe_apply_mk (h : s ≤ t) (g : α) :
    quotientMapOfLe h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl
#align subgroup.quotient_map_of_le_apply_mk Subgroup.quotientMapOfLe_apply_mk
#align add_subgroup.quotient_map_of_le_apply_mk AddSubgroup.quotientMapOfLe_apply_mk

/-- The natural embedding `H ⧸ (⨅ i, f i).subgroup_of H ↪ Π i, H ⧸ (f i).subgroup_of H`. -/
@[to_additive
      "The natural embedding\n  `H ⧸ (⨅ i, f i).add_subgroup_of H) ↪ Π i, H ⧸ (f i).add_subgroup_of H`.",
  simps]
def quotientInfiSubgroupOfEmbedding {ι : Type _} (f : ι → Subgroup α) (H : Subgroup α) :
    H ⧸ (⨅ i, f i).subgroupOf H ↪ ∀ i, H ⧸ (f i).subgroupOf H
    where
  toFun q i := quotientSubgroupOfMapOfLe H (infᵢ_le f i) q
  inj' :=
    Quotient.ind₂' <| by
      simp_rw [funext_iff, quotient_subgroup_of_map_of_le_apply_mk, eq', mem_subgroup_of, mem_infi,
        imp_self, forall_const]
#align subgroup.quotient_infi_subgroup_of_embedding Subgroup.quotientInfiSubgroupOfEmbedding
#align add_subgroup.quotient_infi_add_subgroup_of_embedding AddSubgroup.quotientInfiAddSubgroupOfEmbedding

@[simp, to_additive]
theorem quotientInfiSubgroupOfEmbedding_apply_mk {ι : Type _} (f : ι → Subgroup α) (H : Subgroup α)
    (g : H) (i : ι) :
    quotientInfiSubgroupOfEmbedding f H (QuotientGroup.mk g) i = QuotientGroup.mk g :=
  rfl
#align subgroup.quotient_infi_subgroup_of_embedding_apply_mk Subgroup.quotientInfiSubgroupOfEmbedding_apply_mk
#align add_subgroup.quotient_infi_add_subgroup_of_embedding_apply_mk AddSubgroup.quotient_infi_add_subgroup_of_embedding_apply_mk

/-- The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`. -/
@[to_additive "The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`.", simps]
def quotientInfiEmbedding {ι : Type _} (f : ι → Subgroup α) : (α ⧸ ⨅ i, f i) ↪ ∀ i, α ⧸ f i
    where
  toFun q i := quotientMapOfLe (infᵢ_le f i) q
  inj' :=
    Quotient.ind₂' <| by
      simp_rw [funext_iff, quotient_map_of_le_apply_mk, eq', mem_infi, imp_self, forall_const]
#align subgroup.quotient_infi_embedding Subgroup.quotientInfiEmbedding
#align add_subgroup.quotient_infi_embedding AddSubgroup.quotientInfiEmbedding

@[simp, to_additive]
theorem quotientInfiEmbedding_apply_mk {ι : Type _} (f : ι → Subgroup α) (g : α) (i : ι) :
    quotientInfiEmbedding f (QuotientGroup.mk g) i = QuotientGroup.mk g :=
  rfl
#align subgroup.quotient_infi_embedding_apply_mk Subgroup.quotientInfiEmbedding_apply_mk
#align add_subgroup.quotient_infi_embedding_apply_mk AddSubgroup.quotient_infi_embedding_apply_mk

@[to_additive]
theorem card_eq_card_quotient_mul_card_subgroup [Fintype α] (s : Subgroup α) [Fintype s]
    [DecidablePred fun a => a ∈ s] : Fintype.card α = Fintype.card (α ⧸ s) * Fintype.card s := by
  rw [← Fintype.card_prod] <;> exact Fintype.card_congr Subgroup.groupEquivQuotientTimesSubgroup
#align subgroup.card_eq_card_quotient_mul_card_subgroup Subgroup.card_eq_card_quotient_mul_card_subgroup
#align add_subgroup.card_eq_card_quotient_add_card_add_subgroup AddSubgroup.card_eq_card_quotient_add_card_add_subgroup

/-- **Lagrange's Theorem**: The order of a subgroup divides the order of its ambient group. -/
@[to_additive
      "**Lagrange's Theorem**: The order of an additive subgroup divides the order of its\nambient group."]
theorem card_subgroup_dvd_card [Fintype α] (s : Subgroup α) [Fintype s] :
    Fintype.card s ∣ Fintype.card α := by
  classical simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left ℕ]
#align subgroup.card_subgroup_dvd_card Subgroup.card_subgroup_dvd_card
#align add_subgroup.card_add_subgroup_dvd_card AddSubgroup.card_add_subgroup_dvd_card

@[to_additive]
theorem card_quotient_dvd_card [Fintype α] (s : Subgroup α) [DecidablePred (· ∈ s)] :
    Fintype.card (α ⧸ s) ∣ Fintype.card α := by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_right ℕ]
#align subgroup.card_quotient_dvd_card Subgroup.card_quotient_dvd_card
#align add_subgroup.card_quotient_dvd_card AddSubgroup.card_quotient_dvd_card

open Fintype

variable {H : Type _} [Group H]

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
      Fintype.ofEquiv _ (equiv_map_of_injective _ _ hf).toEquiv <;>
    calc
      Fintype.card (K.comap f) = Fintype.card ((K.comap f).map f) :=
        Fintype.card_congr (equiv_map_of_injective _ _ hf).toEquiv
      _ ∣ Fintype.card K := card_dvd_of_le (map_comap_le _ _)
      
#align subgroup.card_comap_dvd_of_injective Subgroup.card_comap_dvd_of_injective
#align add_subgroup.card_comap_dvd_of_injective AddSubgroup.card_comap_dvd_of_injective

end Subgroup

namespace QuotientGroup

variable [Group α]

/-- If `s` is a subgroup of the group `α`, and `t` is a subset of `α ⧸ s`, then there is a
(typically non-canonical) bijection between the preimage of `t` in `α` and the product `s × t`. -/
@[to_additive
      "If `s` is a subgroup of the additive group `α`, and `t` is a subset of `α ⧸ s`, then\nthere is a (typically non-canonical) bijection between the preimage of `t` in `α` and the product\n`s × t`."]
noncomputable def preimageMkEquivSubgroupTimesSet (s : Subgroup α) (t : Set (α ⧸ s)) :
    QuotientGroup.mk ⁻¹' t ≃ s × t
    where
  toFun a :=
    ⟨⟨(Quotient.out' (QuotientGroup.mk a))⁻¹ * a,
        leftRel_apply.mp (@Quotient.exact' _ (leftRel s) _ _ <| Quotient.out_eq' _)⟩,
      ⟨QuotientGroup.mk a, a.2⟩⟩
  invFun a :=
    ⟨Quotient.out' a.2.1 * a.1.1,
      show QuotientGroup.mk _ ∈ t by
        rw [mk_mul_of_mem _ a.1.2, out_eq']
        exact a.2.2⟩
  left_inv := fun ⟨a, ha⟩ => Subtype.eq <| show _ * _ = a by simp
  right_inv := fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ => by ext <;> simp [ha]
#align quotient_group.preimage_mk_equiv_subgroup_times_set QuotientGroup.preimageMkEquivSubgroupTimesSet
#align quotient_add_group.preimage_mk_equiv_add_subgroup_times_set quotientAddGroup.preimageMkEquivAddSubgroupTimesSet

end QuotientGroup

library_note "use has_coe_t"/--
We use the class `has_coe_t` instead of `has_coe` if the first argument is a variable,
or if the second argument is a variable not occurring in the first.
Using `has_coe` would cause looping of type-class inference. See
<https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/remove.20all.20instances.20with.20variable.20domain>
-/


