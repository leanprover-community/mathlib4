/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Order.WellFoundedSet

/-!
# Pointwise instances on `Submonoid`s and `AddSubmonoid`s

This file provides:

* `Submonoid.inv`
* `AddSubmonoid.neg`

and the actions

* `Submonoid.pointwiseMulAction`
* `AddSubmonoid.pointwiseAddAction`

which matches the action of `Set.mulActionSet`.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from
`Mathlib/Algebra/Group/Pointwise/Set/Basic.lean` and
`Mathlib/Algebra/Group/Action/Pointwise/Set/Basic.lean`.
While the statements of these lemmas are defeq, we repeat them here due to them not being
syntactically equal. Before adding new lemmas here, consider if they would also apply to the action
on `Set`s.
-/

assert_not_exists GroupWithZero

open Set Pointwise

variable {α G M R A S : Type*}
variable [Monoid M] [AddMonoid A]

@[to_additive (attr := simp, norm_cast)]
lemma coe_mul_coe [SetLike S M] [SubmonoidClass S M] (H : S) : H * H = (H : Set M) := by
  aesop (add simp mem_mul)

@[to_additive (attr := simp)]
lemma coe_set_pow [SetLike S M] [SubmonoidClass S M] :
    ∀ {n} (_ : n ≠ 0) (H : S), (H ^ n : Set M) = H
  | 1, _, H => by simp
  | n + 2, _, H => by rw [pow_succ, coe_set_pow n.succ_ne_zero, coe_mul_coe]

/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `GroupTheory.Submonoid.Basic`, but currently we cannot because that file is imported by this. -/

namespace Submonoid

variable {s t u : Set M}

@[to_additive]
theorem mul_subset {S : Submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : s * t ⊆ S :=
  mul_subset_iff.2 fun _x hx _y hy ↦ mul_mem (hs hx) (ht hy)

@[to_additive]
theorem mul_subset_closure (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ Submonoid.closure u :=
  mul_subset (Subset.trans hs Submonoid.subset_closure) (Subset.trans ht Submonoid.subset_closure)

@[to_additive]
theorem coe_mul_self_eq (s : Submonoid M) : (s : Set M) * s = s := by
  simp

@[to_additive]
theorem closure_mul_le (S T : Set M) : closure (S * T) ≤ closure S ⊔ closure T :=
  sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)

@[to_additive]
lemma closure_pow_le : ∀ {n}, n ≠ 0 → closure (s ^ n) ≤ closure s
  | 1, _ => by simp
  | n + 2, _ =>
    calc
      closure (s ^ (n + 2))
      _ = closure (s ^ (n + 1) * s) := by rw [pow_succ]
      _ ≤ closure (s ^ (n + 1)) ⊔ closure s := closure_mul_le ..
      _ ≤ closure s ⊔ closure s := by gcongr ?_ ⊔ _; exact closure_pow_le n.succ_ne_zero
      _ = closure s := sup_idem _

@[to_additive]
lemma closure_pow {n : ℕ} (hs : 1 ∈ s) (hn : n ≠ 0) : closure (s ^ n) = closure s :=
  (closure_pow_le hn).antisymm <| by gcongr; exact subset_pow hs hn

@[to_additive]
theorem sup_eq_closure_mul (H K : Submonoid M) : H ⊔ K = closure ((H : Set M) * (K : Set M)) :=
  le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

@[to_additive]
theorem coe_sup {N : Type*} [CommMonoid N] (H K : Submonoid N) :
    ↑(H ⊔ K) = (H * K : Set N) := by
  ext x
  simp [mem_sup, Set.mem_mul]

@[to_additive]
theorem pow_smul_mem_closure_smul {N : Type*} [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
    (r : M) (s : Set N) {x : N} (hx : x ∈ closure s) : ∃ n : ℕ, r ^ n • x ∈ closure (r • s) := by
  induction hx using closure_induction with
  | mem x hx => exact ⟨1, subset_closure ⟨_, hx, by rw [pow_one]⟩⟩
  | one => exact ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨⟨nx, hx⟩, ⟨ny, hy⟩⟩ := And.intro hx hy
    use ny + nx
    rw [pow_add, mul_smul, ← smul_mul_assoc, mul_comm, ← smul_mul_assoc]
    exact mul_mem hy hx

variable [Group G]

/-- The submonoid with every element inverted. -/
@[to_additive /-- The additive submonoid with every element negated. -/]
protected def inv : Inv (Submonoid G) where
  inv S :=
    { carrier := (S : Set G)⁻¹
      mul_mem' := fun ha hb => by rw [mem_inv, mul_inv_rev]; exact mul_mem hb ha
      one_mem' := mem_inv.2 <| by rw [inv_one]; exact S.one_mem' }

scoped[Pointwise] attribute [instance] Submonoid.inv AddSubmonoid.neg

@[to_additive (attr := simp)]
theorem coe_inv (S : Submonoid G) : ↑S⁻¹ = (S : Set G)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem mem_inv {g : G} {S : Submonoid G} : g ∈ S⁻¹ ↔ g⁻¹ ∈ S :=
  Iff.rfl

/-- Inversion is involutive on submonoids. -/
@[to_additive /-- Inversion is involutive on additive submonoids. -/]
def involutiveInv : InvolutiveInv (Submonoid G) :=
  SetLike.coe_injective.involutiveInv _ fun _ => rfl

scoped[Pointwise] attribute [instance] Submonoid.involutiveInv AddSubmonoid.involutiveNeg

@[to_additive (attr := simp)]
theorem inv_le_inv (S T : Submonoid G) : S⁻¹ ≤ T⁻¹ ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset_inv

@[to_additive]
theorem inv_le (S T : Submonoid G) : S⁻¹ ≤ T ↔ S ≤ T⁻¹ :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset

/-- Pointwise inversion of submonoids as an order isomorphism. -/
@[to_additive (attr := simps!)
/-- Pointwise negation of additive submonoids as an order isomorphism -/]
def invOrderIso : Submonoid G ≃o Submonoid G where
  toEquiv := Equiv.inv _
  map_rel_iff' := inv_le_inv _ _

@[to_additive]
theorem closure_inv (s : Set G) : closure s⁻¹ = (closure s)⁻¹ := by
  apply le_antisymm
  · rw [closure_le, coe_inv, ← Set.inv_subset, inv_inv]
    exact subset_closure
  · rw [inv_le, closure_le, coe_inv, ← Set.inv_subset]
    exact subset_closure

@[to_additive]
lemma mem_closure_inv (s : Set G) (x : G) : x ∈ closure s⁻¹ ↔ x⁻¹ ∈ closure s := by
  rw [closure_inv, mem_inv]

@[to_additive (attr := simp)]
theorem inv_inf (S T : Submonoid G) : (S ⊓ T)⁻¹ = S⁻¹ ⊓ T⁻¹ :=
  SetLike.coe_injective Set.inter_inv

@[to_additive (attr := simp)]
theorem inv_sup (S T : Submonoid G) : (S ⊔ T)⁻¹ = S⁻¹ ⊔ T⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_sup S T

@[to_additive (attr := simp)]
theorem inv_bot : (⊥ : Submonoid G)⁻¹ = ⊥ :=
  SetLike.coe_injective <| (Set.inv_singleton 1).trans <| congr_arg _ inv_one

@[to_additive (attr := simp)]
theorem inv_top : (⊤ : Submonoid G)⁻¹ = ⊤ :=
  SetLike.coe_injective <| Set.inv_univ

@[to_additive (attr := simp)]
theorem inv_iInf {ι : Sort*} (S : ι → Submonoid G) : (⨅ i, S i)⁻¹ = ⨅ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_iInf _

@[to_additive (attr := simp)]
theorem inv_iSup {ι : Sort*} (S : ι → Submonoid G) : (⨆ i, S i)⁻¹ = ⨆ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_iSup _

end Submonoid

namespace Submonoid

section Monoid

variable [Monoid α] [MulDistribMulAction α M]

-- todo: add `to_additive`?
/-- The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (Submonoid M) where
  smul a S := S.map (MulDistribMulAction.toMonoidEnd _ M a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : Monoid.End M => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Submonoid.pointwiseMulAction

@[simp]
theorem coe_pointwise_smul (a : α) (S : Submonoid M) : ↑(a • S) = a • (S : Set M) :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submonoid M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

instance : CovariantClass α (Submonoid M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_mono⟩

theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submonoid M) :
    m ∈ a • S ↔ ∃ s : M, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set M) ↔ _)

@[simp]
theorem smul_bot (a : α) : a • (⊥ : Submonoid M) = ⊥ :=
  map_bot _

theorem smul_sup (a : α) (S T : Submonoid M) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

theorem smul_closure (a : α) (s : Set M) : a • closure s = closure (a • s) :=
  MonoidHom.map_mclosure _ _

lemma pointwise_isCentralScalar [MulDistribMulAction αᵐᵒᵖ M] [IsCentralScalar α M] :
    IsCentralScalar α (Submonoid M) :=
  ⟨fun _ S => (congr_arg fun f : Monoid.End M => S.map f) <| MonoidHom.ext <| op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] Submonoid.pointwise_isCentralScalar

end Monoid

section Group

variable [Group α] [MulDistribMulAction α M]

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Submonoid M} {x : M} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Submonoid M} : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff

theorem pointwise_smul_subset_iff {a : α} {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set

theorem subset_pointwise_smul_iff {a : α} {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff

end Group
end Submonoid

namespace Set.IsPWO

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Set α}

@[to_additive]
theorem submonoid_closure (hpos : ∀ x : α, x ∈ s → 1 ≤ x) (h : s.IsPWO) :
    IsPWO (Submonoid.closure s : Set α) := by
  rw [Submonoid.closure_eq_image_prod]
  refine (h.partiallyWellOrderedOn_sublistForall₂ (· ≤ ·)).image_of_monotone_on ?_
  exact fun l1 _ l2 hl2 h12 => h12.prod_le_prod' fun x hx => hpos x <| hl2 x hx

end Set.IsPWO
