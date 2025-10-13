/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Kim Morrison
-/
import Mathlib.Algebra.Quotient
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Subgroup.MulOpposite
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Cosets

This file develops the basic theory of left and right cosets.

When `G` is a group and `a : G`, `s : Set G`, with  `open scoped Pointwise` we can write:
* the left coset of `s` by `a` as `a • s`
* the right coset of `s` by `a` as `MulOpposite.op a • s` (or `op a • s` with `open MulOpposite`)

If instead `G` is an additive group, we can write (with  `open scoped Pointwise` still)
* the left coset of `s` by `a` as `a +ᵥ s`
* the right coset of `s` by `a` as `AddOpposite.op a +ᵥ s` (or `op a • s` with `open AddOpposite`)

## Main definitions

* `QuotientGroup.quotient s`: the quotient type representing the left cosets with respect to a
  subgroup `s`, for an `AddGroup` this is `QuotientAddGroup.quotient s`.
* `QuotientGroup.mk`: the canonical map from `α` to `α/s` for a subgroup `s` of `α`, for an
  `AddGroup` this is `QuotientAddGroup.mk`.

## Notation

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`

## TODO

Properly merge with pointwise actions on sets, by renaming and deduplicating lemmas as appropriate.
-/

assert_not_exists Cardinal

open Function Set
open scoped Pointwise

variable {α : Type*}

-- Porting note: see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.E2.9C.94.20to_additive.2Emap_namespace
run_cmd Lean.Elab.Command.liftCoreM <| ToAdditive.insertTranslation `QuotientGroup `QuotientAddGroup

namespace QuotientGroup

variable [Group α] (s : Subgroup α)

/-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup. -/
@[to_additive /-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup. -/]
def leftRel : Setoid α :=
  MulAction.orbitRel s.op α

variable {s} in
@[to_additive]
theorem leftRel_apply {x y : α} : leftRel s x y ↔ x⁻¹ * y ∈ s :=
  calc
    (∃ a : s.op, y * MulOpposite.unop a = x) ↔ ∃ a : s, y * a = x :=
      s.equivOp.symm.exists_congr_left
    _ ↔ ∃ a : s, x⁻¹ * y = a⁻¹ := by
      simp only [inv_mul_eq_iff_eq_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq]
    _ ↔ x⁻¹ * y ∈ s := by simp [exists_inv_mem_iff_exists_mem]

@[to_additive]
theorem leftRel_eq : ⇑(leftRel s) = fun x y => x⁻¹ * y ∈ s :=
  funext₂ <| by
    simp only [eq_iff_iff]
    apply leftRel_apply

@[to_additive]
instance leftRelDecidable [DecidablePred (· ∈ s)] : DecidableRel (leftRel s).r := fun x y => by
  rw [leftRel_eq]
  exact ‹DecidablePred (· ∈ s)› _

/-- `α ⧸ s` is the quotient type representing the left cosets of `s`. If `s` is a normal subgroup,
`α ⧸ s` is a group -/
@[to_additive /-- `α ⧸ s` is the quotient type representing the left cosets of `s`. If `s` is a
normal subgroup, `α ⧸ s` is a group -/]
instance instHasQuotientSubgroup : HasQuotient α (Subgroup α) :=
  ⟨fun s => Quotient (leftRel s)⟩

@[to_additive]
instance [DecidablePred (· ∈ s)] : DecidableEq (α ⧸ s) :=
  @Quotient.decidableEq _ _ (leftRelDecidable _)

/-- The equivalence relation corresponding to the partition of a group by right cosets of a
subgroup. -/
@[to_additive /-- The equivalence relation corresponding to the partition of a group by right cosets
of a subgroup. -/]
def rightRel : Setoid α :=
  MulAction.orbitRel s α

variable {s} in
@[to_additive]
theorem rightRel_apply {x y : α} : rightRel s x y ↔ y * x⁻¹ ∈ s :=
  calc
    (∃ a : s, (a : α) * y = x) ↔ ∃ a : s, y * x⁻¹ = a⁻¹ := by
      simp only [mul_inv_eq_iff_eq_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
    _ ↔ y * x⁻¹ ∈ s := by simp [exists_inv_mem_iff_exists_mem]

@[to_additive]
theorem rightRel_eq : ⇑(rightRel s) = fun x y => y * x⁻¹ ∈ s :=
  funext₂ <| by
    simp only [eq_iff_iff]
    apply rightRel_apply

@[to_additive]
instance rightRelDecidable [DecidablePred (· ∈ s)] : DecidableRel (rightRel s).r := fun x y => by
  rw [rightRel_eq]
  exact ‹DecidablePred (· ∈ s)› _

/-- Right cosets are in bijection with left cosets. -/
@[to_additive /-- Right cosets are in bijection with left cosets. -/]
def quotientRightRelEquivQuotientLeftRel : Quotient (QuotientGroup.rightRel s) ≃ α ⧸ s where
  toFun :=
    Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply, rightRel_apply]
      exact fun h => (congr_arg (· ∈ s) (by simp)).mp (s.inv_mem h)
      -- Porting note: replace with `by group`
  invFun :=
    Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply, rightRel_apply]
      exact fun h => (congr_arg (· ∈ s) (by simp)).mp (s.inv_mem h)
      -- Porting note: replace with `by group`
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

end QuotientGroup

namespace QuotientGroup

variable [Group α] {s : Subgroup α}

/-- The canonical map from a group `α` to the quotient `α ⧸ s`. -/
@[to_additive (attr := coe)
/-- The canonical map from an `AddGroup` `α` to the quotient `α ⧸ s`. -/]
abbrev mk (a : α) : α ⧸ s :=
  Quotient.mk'' a

@[to_additive]
theorem mk_surjective : Function.Surjective <| @mk _ _ s :=
  Quotient.mk''_surjective

@[to_additive (attr := simp)]
lemma range_mk : range (QuotientGroup.mk (s := s)) = univ := range_eq_univ.mpr mk_surjective

@[to_additive (attr := elab_as_elim)]
theorem induction_on {C : α ⧸ s → Prop} (x : α ⧸ s) (H : ∀ z, C (QuotientGroup.mk z)) : C x :=
  Quotient.inductionOn' x H

@[to_additive]
instance : Coe α (α ⧸ s) :=
  ⟨mk⟩

@[to_additive] alias induction_on' := induction_on

@[to_additive (attr := simp)]
theorem quotient_liftOn_mk {β} (f : α → β) (h) (x : α) : Quotient.liftOn' (x : α ⧸ s) f h = f x :=
  rfl

@[to_additive]
theorem forall_mk {C : α ⧸ s → Prop} : (∀ x : α ⧸ s, C x) ↔ ∀ x : α, C x :=
  mk_surjective.forall

@[to_additive]
theorem exists_mk {C : α ⧸ s → Prop} : (∃ x : α ⧸ s, C x) ↔ ∃ x : α, C x :=
  mk_surjective.exists

@[to_additive]
instance (s : Subgroup α) : Inhabited (α ⧸ s) :=
  ⟨((1 : α) : α ⧸ s)⟩

@[to_additive]
protected theorem eq {a b : α} : (a : α ⧸ s) = b ↔ a⁻¹ * b ∈ s :=
  calc
    _ ↔ leftRel s a b := Quotient.eq''
    _ ↔ _ := by rw [leftRel_apply]

@[to_additive]
theorem out_eq' (a : α ⧸ s) : mk a.out = a :=
  Quotient.out_eq' a

variable (s)

/- It can be useful to write `obtain ⟨h, H⟩ := mk_out_eq_mul ...`, and then `rw [H]` or
  `simp_rw [H]` or `simp only [H]`. In order for `simp_rw` and `simp only` to work, this lemma is
  stated in terms of an arbitrary `h : s`, rather than the specific `h = g⁻¹ * (mk g).out`. -/
@[to_additive QuotientAddGroup.mk_out_eq_mul]
theorem mk_out_eq_mul (g : α) : ∃ h : s, (mk g : α ⧸ s).out = g * h :=
  ⟨⟨g⁻¹ * (mk g).out, QuotientGroup.eq.mp (mk g).out_eq'.symm⟩, by rw [mul_inv_cancel_left]⟩

variable {s} {a b : α}

@[to_additive (attr := simp)]
theorem mk_mul_of_mem (a : α) (hb : b ∈ s) : (mk (a * b) : α ⧸ s) = mk a := by
  rwa [QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]

@[to_additive]
theorem preimage_image_mk (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α → α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) ⁻¹' s := by
  ext x
  simp only [QuotientGroup.eq, SetLike.exists, exists_prop, Set.mem_preimage, Set.mem_iUnion,
    Set.mem_image]
  exact
    ⟨fun ⟨y, hs, hN⟩ => ⟨_, N.inv_mem hN, by simpa using hs⟩, fun ⟨z, hz, hxz⟩ =>
      ⟨x * z, hxz, by simpa using hz⟩⟩

@[to_additive]
theorem preimage_image_mk_eq_iUnion_image (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α → α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) '' s := by
  rw [preimage_image_mk, iUnion_congr_of_surjective (·⁻¹) inv_surjective]
  exact fun x ↦ image_mul_right'

@[to_additive]
theorem preimage_image_mk_eq_mul (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α → α ⧸ N) '' s) = s * N := by
  rw [preimage_image_mk_eq_iUnion_image, iUnion_subtype, ← image2_mul, ← iUnion_image_right]
  simp only [SetLike.mem_coe]

end QuotientGroup

namespace Subgroup

open QuotientGroup

variable [Group α] {s : Subgroup α}

variable {t : Subgroup α}

/-- If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection. -/
@[to_additive
/-- If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection. -/]
def quotientEquivOfEq (h : s = t) : α ⧸ s ≃ α ⧸ t where
  toFun := Quotient.map' id fun _a _b h' => h ▸ h'
  invFun := Quotient.map' id fun _a _b h' => h.symm ▸ h'
  left_inv q := induction_on q fun _g => rfl
  right_inv q := induction_on q fun _g => rfl

theorem quotientEquivOfEq_mk (h : s = t) (a : α) :
    quotientEquivOfEq h (QuotientGroup.mk a) = QuotientGroup.mk a :=
  rfl

end Subgroup
