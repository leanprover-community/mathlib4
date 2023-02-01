/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.submonoid.pointwise
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Smul
import Mathbin.GroupTheory.Submonoid.Membership
import Mathbin.Order.WellFoundedSet

/-! # Pointwise instances on `submonoid`s and `add_submonoid`s

This file provides:

* `submonoid.has_inv`
* `add_submonoid.has_neg`

and the actions

* `submonoid.pointwise_mul_action`
* `add_submonoid.pointwise_mul_action`

which matches the action of `mul_action_set`.

These are all available in the `pointwise` locale.

Additionally, it provides various degrees of monoid structure:
* `add_submonoid.has_one`
* `add_submonoid.has_mul`
* `add_submonoid.mul_one_class`
* `add_submonoid.semigroup`
* `add_submonoid.monoid`
which is available globally to match the monoid structure implied by `submodule.semiring`.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from `algebra/pointwise.lean`.
While the statements of these lemmas are defeq, we repeat them here due to them not being
syntactically equal. Before adding new lemmas here, consider if they would also apply to the action
on `set`s.

-/


open Set

variable {α : Type _} {G : Type _} {M : Type _} {R : Type _} {A : Type _}

variable [Monoid M] [AddMonoid A]

/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `group_theory.submonoid.basic`, but currently we cannot because that file is imported by this. -/


namespace Submonoid

open Pointwise

variable {s t u : Set M}

@[to_additive]
theorem mul_subset {S : Submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : s * t ⊆ S :=
  by
  rintro _ ⟨p, q, hp, hq, rfl⟩
  exact Submonoid.mul_mem _ (hs hp) (ht hq)
#align submonoid.mul_subset Submonoid.mul_subset
#align add_submonoid.add_subset AddSubmonoid.add_subset

@[to_additive]
theorem mul_subset_closure (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ Submonoid.closure u :=
  mul_subset (Subset.trans hs Submonoid.subset_closure) (Subset.trans ht Submonoid.subset_closure)
#align submonoid.mul_subset_closure Submonoid.mul_subset_closure
#align add_submonoid.add_subset_closure AddSubmonoid.add_subset_closure

@[to_additive]
theorem coe_mul_self_eq (s : Submonoid M) : (s : Set M) * s = s :=
  by
  ext x
  refine' ⟨_, fun h => ⟨x, 1, h, s.one_mem, mul_one x⟩⟩
  rintro ⟨a, b, ha, hb, rfl⟩
  exact s.mul_mem ha hb
#align submonoid.coe_mul_self_eq Submonoid.coe_mul_self_eq
#align add_submonoid.coe_add_self_eq AddSubmonoid.coe_add_self_eq

@[to_additive]
theorem closure_mul_le (S T : Set M) : closure (S * T) ≤ closure S ⊔ closure T :=
  infₛ_le fun x ⟨s, t, hs, ht, hx⟩ =>
    hx ▸
      (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
        (SetLike.le_def.mp le_sup_right <| subset_closure ht)
#align submonoid.closure_mul_le Submonoid.closure_mul_le
#align add_submonoid.closure_add_le AddSubmonoid.closure_add_le

@[to_additive]
theorem sup_eq_closure (H K : Submonoid M) : H ⊔ K = closure (H * K) :=
  le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, 1, hh, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, k, H.one_mem, hk, one_mul k⟩)
    (by conv_rhs => rw [← closure_eq H, ← closure_eq K] <;> apply closure_mul_le)
#align submonoid.sup_eq_closure Submonoid.sup_eq_closure
#align add_submonoid.sup_eq_closure AddSubmonoid.sup_eq_closure

@[to_additive]
theorem pow_smul_mem_closure_smul {N : Type _} [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
    (r : M) (s : Set N) {x : N} (hx : x ∈ closure s) : ∃ n : ℕ, r ^ n • x ∈ closure (r • s) :=
  by
  apply @closure_induction N _ s (fun x : N => ∃ n : ℕ, r ^ n • x ∈ closure (r • s)) _ hx
  · intro x hx
    exact ⟨1, subset_closure ⟨_, hx, by rw [pow_one]⟩⟩
  · exact ⟨0, by simpa using one_mem _⟩
  · rintro x y ⟨nx, hx⟩ ⟨ny, hy⟩
    use nx + ny
    convert mul_mem hx hy
    rw [pow_add, smul_mul_assoc, mul_smul, mul_comm, ← smul_mul_assoc, mul_comm]
#align submonoid.pow_smul_mem_closure_smul Submonoid.pow_smul_mem_closure_smul
#align add_submonoid.nsmul_vadd_mem_closure_vadd AddSubmonoid.nsmul_vadd_mem_closure_vadd

variable [Group G]

open Pointwise

/-- The submonoid with every element inverted. -/
@[to_additive " The additive submonoid with every element negated. "]
protected def hasInv : Inv (Submonoid G)
    where inv S :=
    { carrier := (S : Set G)⁻¹
      one_mem' :=
        show (1 : G)⁻¹ ∈ S by
          rw [inv_one]
          exact S.one_mem
      mul_mem' := fun a b (ha : a⁻¹ ∈ S) (hb : b⁻¹ ∈ S) =>
        show (a * b)⁻¹ ∈ S by
          rw [mul_inv_rev]
          exact S.mul_mem hb ha }
#align submonoid.has_inv Submonoid.hasInv
#align add_submonoid.has_neg AddSubmonoid.hasNeg

scoped[Pointwise] attribute [instance] Submonoid.hasInv

open Pointwise

@[simp, to_additive]
theorem coe_inv (S : Submonoid G) : ↑S⁻¹ = (S : Set G)⁻¹ :=
  rfl
#align submonoid.coe_inv Submonoid.coe_inv
#align add_submonoid.coe_neg AddSubmonoid.coe_neg

@[simp, to_additive]
theorem mem_inv {g : G} {S : Submonoid G} : g ∈ S⁻¹ ↔ g⁻¹ ∈ S :=
  Iff.rfl
#align submonoid.mem_inv Submonoid.mem_inv
#align add_submonoid.mem_neg AddSubmonoid.mem_neg

@[to_additive]
instance : InvolutiveInv (Submonoid G) :=
  SetLike.coe_injective.InvolutiveInv _ fun _ => rfl

@[simp, to_additive]
theorem inv_le_inv (S T : Submonoid G) : S⁻¹ ≤ T⁻¹ ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset_inv
#align submonoid.inv_le_inv Submonoid.inv_le_inv
#align add_submonoid.neg_le_neg AddSubmonoid.neg_le_neg

@[to_additive]
theorem inv_le (S T : Submonoid G) : S⁻¹ ≤ T ↔ S ≤ T⁻¹ :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset
#align submonoid.inv_le Submonoid.inv_le
#align add_submonoid.neg_le AddSubmonoid.neg_le

/-- `submonoid.has_inv` as an order isomorphism. -/
@[to_additive " `add_submonoid.has_neg` as an order isomorphism ", simps]
def invOrderIso : Submonoid G ≃o Submonoid G
    where
  toEquiv := Equiv.inv _
  map_rel_iff' := inv_le_inv
#align submonoid.inv_order_iso Submonoid.invOrderIso
#align add_submonoid.neg_order_iso AddSubmonoid.negOrderIso

@[to_additive]
theorem closure_inv (s : Set G) : closure s⁻¹ = (closure s)⁻¹ :=
  by
  apply le_antisymm
  · rw [closure_le, coe_inv, ← Set.inv_subset, inv_inv]
    exact subset_closure
  · rw [inv_le, closure_le, coe_inv, ← Set.inv_subset]
    exact subset_closure
#align submonoid.closure_inv Submonoid.closure_inv
#align add_submonoid.closure_neg AddSubmonoid.closure_neg

@[simp, to_additive]
theorem inv_inf (S T : Submonoid G) : (S ⊓ T)⁻¹ = S⁻¹ ⊓ T⁻¹ :=
  SetLike.coe_injective Set.inter_inv
#align submonoid.inv_inf Submonoid.inv_inf
#align add_submonoid.neg_inf AddSubmonoid.neg_inf

@[simp, to_additive]
theorem inv_sup (S T : Submonoid G) : (S ⊔ T)⁻¹ = S⁻¹ ⊔ T⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_sup S T
#align submonoid.inv_sup Submonoid.inv_sup
#align add_submonoid.neg_sup AddSubmonoid.neg_sup

@[simp, to_additive]
theorem inv_bot : (⊥ : Submonoid G)⁻¹ = ⊥ :=
  SetLike.coe_injective <| (Set.inv_singleton 1).trans <| congr_arg _ inv_one
#align submonoid.inv_bot Submonoid.inv_bot
#align add_submonoid.neg_bot AddSubmonoid.neg_bot

@[simp, to_additive]
theorem inv_top : (⊤ : Submonoid G)⁻¹ = ⊤ :=
  SetLike.coe_injective <| Set.inv_univ
#align submonoid.inv_top Submonoid.inv_top
#align add_submonoid.neg_top AddSubmonoid.neg_top

@[simp, to_additive]
theorem inv_infᵢ {ι : Sort _} (S : ι → Submonoid G) : (⨅ i, S i)⁻¹ = ⨅ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_infᵢ _
#align submonoid.inv_infi Submonoid.inv_infᵢ
#align add_submonoid.neg_infi AddSubmonoid.neg_infi

@[simp, to_additive]
theorem inv_supᵢ {ι : Sort _} (S : ι → Submonoid G) : (⨆ i, S i)⁻¹ = ⨆ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_supᵢ _
#align submonoid.inv_supr Submonoid.inv_supᵢ
#align add_submonoid.neg_supr AddSubmonoid.neg_supᵢ

end Submonoid

namespace Submonoid

section Monoid

variable [Monoid α] [MulDistribMulAction α M]

/-- The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (Submonoid M)
    where
  smul a S := S.map (MulDistribMulAction.toMonoidEnd _ M a)
  one_smul S := by
    ext
    simp
  mul_smul a₁ a₂ S :=
    (congr_arg (fun f : Monoid.End M => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm
#align submonoid.pointwise_mul_action Submonoid.pointwiseMulAction

scoped[Pointwise] attribute [instance] Submonoid.pointwiseMulAction

open Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : Submonoid M) : ↑(a • S) = a • (S : Set M) :=
  rfl
#align submonoid.coe_pointwise_smul Submonoid.coe_pointwise_smul

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submonoid M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))
#align submonoid.smul_mem_pointwise_smul Submonoid.smul_mem_pointwise_smul

theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submonoid M) :
    m ∈ a • S ↔ ∃ s : M, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set M) ↔ _)
#align submonoid.mem_smul_pointwise_iff_exists Submonoid.mem_smul_pointwise_iff_exists

@[simp]
theorem smul_bot (a : α) : a • (⊥ : Submonoid M) = ⊥ :=
  map_bot _
#align submonoid.smul_bot Submonoid.smul_bot

theorem smul_sup (a : α) (S T : Submonoid M) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
#align submonoid.smul_sup Submonoid.smul_sup

theorem smul_closure (a : α) (s : Set M) : a • closure s = closure (a • s) :=
  MonoidHom.map_mclosure _ _
#align submonoid.smul_closure Submonoid.smul_closure

instance pointwise_central_scalar [MulDistribMulAction αᵐᵒᵖ M] [IsCentralScalar α M] :
    IsCentralScalar α (Submonoid M) :=
  ⟨fun a S => (congr_arg fun f : Monoid.End M => S.map f) <| MonoidHom.ext <| op_smul_eq_smul _⟩
#align submonoid.pointwise_central_scalar Submonoid.pointwise_central_scalar

end Monoid

section Group

variable [Group α] [MulDistribMulAction α M]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
#align submonoid.smul_mem_pointwise_smul_iff Submonoid.smul_mem_pointwise_smul_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Submonoid M} {x : M} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
#align submonoid.mem_pointwise_smul_iff_inv_smul_mem Submonoid.mem_pointwise_smul_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff
#align submonoid.mem_inv_pointwise_smul_iff Submonoid.mem_inv_pointwise_smul_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Submonoid M} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff
#align submonoid.pointwise_smul_le_pointwise_smul_iff Submonoid.pointwise_smul_le_pointwise_smul_iff

theorem pointwise_smul_subset_iff {a : α} {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff
#align submonoid.pointwise_smul_subset_iff Submonoid.pointwise_smul_subset_iff

theorem subset_pointwise_smul_iff {a : α} {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff
#align submonoid.subset_pointwise_smul_iff Submonoid.subset_pointwise_smul_iff

end Group

section GroupWithZero

variable [GroupWithZero α] [MulDistribMulAction α M]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set M) x
#align submonoid.smul_mem_pointwise_smul_iff₀ Submonoid.smul_mem_pointwise_smul_iff₀

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set M) x
#align submonoid.mem_pointwise_smul_iff_inv_smul_mem₀ Submonoid.mem_pointwise_smul_iff_inv_smul_mem₀

theorem mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set M) x
#align submonoid.mem_inv_pointwise_smul_iff₀ Submonoid.mem_inv_pointwise_smul_iff₀

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha
#align submonoid.pointwise_smul_le_pointwise_smul_iff₀ Submonoid.pointwise_smul_le_pointwise_smul_iff₀

theorem pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha
#align submonoid.pointwise_smul_le_iff₀ Submonoid.pointwise_smul_le_iff₀

theorem le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha
#align submonoid.le_pointwise_smul_iff₀ Submonoid.le_pointwise_smul_iff₀

end GroupWithZero

open Pointwise

@[to_additive]
theorem mem_closure_inv {G : Type _} [Group G] (S : Set G) (x : G) :
    x ∈ Submonoid.closure S⁻¹ ↔ x⁻¹ ∈ Submonoid.closure S := by rw [closure_inv, mem_inv]
#align submonoid.mem_closure_inv Submonoid.mem_closure_inv
#align add_submonoid.mem_closure_neg AddSubmonoid.mem_closure_neg

end Submonoid

namespace AddSubmonoid

section Monoid

variable [Monoid α] [DistribMulAction α A]

/-- The action on an additive submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (AddSubmonoid A)
    where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_one _)).trans S.map_id
  mul_smul a₁ a₂ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm
#align add_submonoid.pointwise_mul_action AddSubmonoid.pointwiseMulAction

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwiseMulAction

open Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : AddSubmonoid A) : ↑(a • S) = a • (S : Set A) :=
  rfl
#align add_submonoid.coe_pointwise_smul AddSubmonoid.coe_pointwise_smul

theorem smul_mem_pointwise_smul (m : A) (a : α) (S : AddSubmonoid A) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set A))
#align add_submonoid.smul_mem_pointwise_smul AddSubmonoid.smul_mem_pointwise_smul

theorem mem_smul_pointwise_iff_exists (m : A) (a : α) (S : AddSubmonoid A) :
    m ∈ a • S ↔ ∃ s : A, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set A) ↔ _)
#align add_submonoid.mem_smul_pointwise_iff_exists AddSubmonoid.mem_smul_pointwise_iff_exists

@[simp]
theorem smul_bot (a : α) : a • (⊥ : AddSubmonoid A) = ⊥ :=
  map_bot _
#align add_submonoid.smul_bot AddSubmonoid.smul_bot

theorem smul_sup (a : α) (S T : AddSubmonoid A) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
#align add_submonoid.smul_sup AddSubmonoid.smul_sup

@[simp]
theorem smul_closure (a : α) (s : Set A) : a • closure s = closure (a • s) :=
  AddMonoidHom.map_mclosure _ _
#align add_submonoid.smul_closure AddSubmonoid.smul_closure

instance pointwise_central_scalar [DistribMulAction αᵐᵒᵖ A] [IsCentralScalar α A] :
    IsCentralScalar α (AddSubmonoid A) :=
  ⟨fun a S =>
    (congr_arg fun f : AddMonoid.End A => S.map f) <| AddMonoidHom.ext <| op_smul_eq_smul _⟩
#align add_submonoid.pointwise_central_scalar AddSubmonoid.pointwise_central_scalar

end Monoid

section Group

variable [Group α] [DistribMulAction α A]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : AddSubmonoid A} {x : A} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
#align add_submonoid.smul_mem_pointwise_smul_iff AddSubmonoid.smul_mem_pointwise_smul_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : AddSubmonoid A} {x : A} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
#align add_submonoid.mem_pointwise_smul_iff_inv_smul_mem AddSubmonoid.mem_pointwise_smul_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : α} {S : AddSubmonoid A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff
#align add_submonoid.mem_inv_pointwise_smul_iff AddSubmonoid.mem_inv_pointwise_smul_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : AddSubmonoid A} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff
#align add_submonoid.pointwise_smul_le_pointwise_smul_iff AddSubmonoid.pointwise_smul_le_pointwise_smul_iff

theorem pointwise_smul_le_iff {a : α} {S T : AddSubmonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff
#align add_submonoid.pointwise_smul_le_iff AddSubmonoid.pointwise_smul_le_iff

theorem le_pointwise_smul_iff {a : α} {S T : AddSubmonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff
#align add_submonoid.le_pointwise_smul_iff AddSubmonoid.le_pointwise_smul_iff

end Group

section GroupWithZero

variable [GroupWithZero α] [DistribMulAction α A]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x
#align add_submonoid.smul_mem_pointwise_smul_iff₀ AddSubmonoid.smul_mem_pointwise_smul_iff₀

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x
#align add_submonoid.mem_pointwise_smul_iff_inv_smul_mem₀ AddSubmonoid.mem_pointwise_smul_iff_inv_smul_mem₀

theorem mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set A) x
#align add_submonoid.mem_inv_pointwise_smul_iff₀ AddSubmonoid.mem_inv_pointwise_smul_iff₀

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha
#align add_submonoid.pointwise_smul_le_pointwise_smul_iff₀ AddSubmonoid.pointwise_smul_le_pointwise_smul_iff₀

theorem pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} :
    a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha
#align add_submonoid.pointwise_smul_le_iff₀ AddSubmonoid.pointwise_smul_le_iff₀

theorem le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} :
    S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha
#align add_submonoid.le_pointwise_smul_iff₀ AddSubmonoid.le_pointwise_smul_iff₀

end GroupWithZero

end AddSubmonoid

/-! ### Elementwise monoid structure of additive submonoids

These definitions are a cut-down versions of the ones around `submodule.has_mul`, as that API is
usually more useful. -/


namespace AddSubmonoid

open Pointwise

section AddMonoidWithOne

variable [AddMonoidWithOne R]

instance : One (AddSubmonoid R) :=
  ⟨(Nat.castAddMonoidHom R).mrange⟩

theorem one_eq_mrange : (1 : AddSubmonoid R) = (Nat.castAddMonoidHom R).mrange :=
  rfl
#align add_submonoid.one_eq_mrange AddSubmonoid.one_eq_mrange

theorem nat_cast_mem_one (n : ℕ) : (n : R) ∈ (1 : AddSubmonoid R) :=
  ⟨_, rfl⟩
#align add_submonoid.nat_cast_mem_one AddSubmonoid.nat_cast_mem_one

@[simp]
theorem mem_one {x : R} : x ∈ (1 : AddSubmonoid R) ↔ ∃ n : ℕ, ↑n = x :=
  Iff.rfl
#align add_submonoid.mem_one AddSubmonoid.mem_one

theorem one_eq_closure : (1 : AddSubmonoid R) = closure {1} :=
  by
  simp only [closure_singleton_eq, mul_one, one_eq_mrange]
  congr 1 with n
  simp
#align add_submonoid.one_eq_closure AddSubmonoid.one_eq_closure

theorem one_eq_closure_one_set : (1 : AddSubmonoid R) = closure 1 :=
  one_eq_closure
#align add_submonoid.one_eq_closure_one_set AddSubmonoid.one_eq_closure_one_set

end AddMonoidWithOne

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

/-- Multiplication of additive submonoids of a semiring R. The additive submonoid `S * T` is the
smallest R-submodule of `R` containing the elements `s * t` for `s ∈ S` and `t ∈ T`. -/
instance : Mul (AddSubmonoid R) :=
  ⟨fun M N => ⨆ s : M, N.map <| AddMonoidHom.mul s.1⟩

theorem mul_mem_mul {M N : AddSubmonoid R} {m n : R} (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N :=
  (le_supᵢ _ ⟨m, hm⟩ : _ ≤ M * N) ⟨n, hn, rfl⟩
#align add_submonoid.mul_mem_mul AddSubmonoid.mul_mem_mul

theorem mul_le {M N P : AddSubmonoid R} : M * N ≤ P ↔ ∀ m ∈ M, ∀ n ∈ N, m * n ∈ P :=
  ⟨fun H m hm n hn => H <| mul_mem_mul hm hn, fun H =>
    supᵢ_le fun ⟨m, hm⟩ => map_le_iff_le_comap.2 fun n hn => H m hm n hn⟩
#align add_submonoid.mul_le AddSubmonoid.mul_le

@[elab_as_elim]
protected theorem mul_induction_on {M N : AddSubmonoid R} {C : R → Prop} {r : R} (hr : r ∈ M * N)
    (hm : ∀ m ∈ M, ∀ n ∈ N, C (m * n)) (ha : ∀ x y, C x → C y → C (x + y)) : C r :=
  (@mul_le _ _ _ _ ⟨C, ha, by simpa only [zero_mul] using hm _ (zero_mem _) _ (zero_mem _)⟩).2 hm hr
#align add_submonoid.mul_induction_on AddSubmonoid.mul_induction_on

open Pointwise

-- this proof is copied directly from `submodule.span_mul_span`
theorem closure_mul_closure (S T : Set R) : closure S * closure T = closure (S * T) :=
  by
  apply le_antisymm
  · rw [mul_le]
    intro a ha b hb
    apply closure_induction ha
    on_goal 1 =>
      intros ; apply closure_induction hb
      on_goal 1 => intros ; exact subset_closure ⟨_, _, ‹_›, ‹_›, rfl⟩
    all_goals intros ;
      simp only [mul_zero, zero_mul, zero_mem, left_distrib, right_distrib, mul_smul_comm,
          smul_mul_assoc] <;>
        solve_by_elim (config :=
          { max_depth := 4
            discharger := tactic.interactive.apply_instance }) [add_mem _ _, zero_mem _]
  · rw [closure_le]
    rintro _ ⟨a, b, ha, hb, rfl⟩
    exact mul_mem_mul (subset_closure ha) (subset_closure hb)
#align add_submonoid.closure_mul_closure AddSubmonoid.closure_mul_closure

theorem mul_eq_closure_mul_set (M N : AddSubmonoid R) : M * N = closure (M * N) := by
  rw [← closure_mul_closure, closure_eq, closure_eq]
#align add_submonoid.mul_eq_closure_mul_set AddSubmonoid.mul_eq_closure_mul_set

@[simp]
theorem mul_bot (S : AddSubmonoid R) : S * ⊥ = ⊥ :=
  eq_bot_iff.2 <|
    mul_le.2 fun m hm n hn => by rw [AddSubmonoid.mem_bot] at hn⊢ <;> rw [hn, mul_zero]
#align add_submonoid.mul_bot AddSubmonoid.mul_bot

@[simp]
theorem bot_mul (S : AddSubmonoid R) : ⊥ * S = ⊥ :=
  eq_bot_iff.2 <|
    mul_le.2 fun m hm n hn => by rw [AddSubmonoid.mem_bot] at hm⊢ <;> rw [hm, zero_mul]
#align add_submonoid.bot_mul AddSubmonoid.bot_mul

@[mono]
theorem mul_le_mul {M N P Q : AddSubmonoid R} (hmp : M ≤ P) (hnq : N ≤ Q) : M * N ≤ P * Q :=
  mul_le.2 fun m hm n hn => mul_mem_mul (hmp hm) (hnq hn)
#align add_submonoid.mul_le_mul AddSubmonoid.mul_le_mul

theorem mul_le_mul_left {M N P : AddSubmonoid R} (h : M ≤ N) : M * P ≤ N * P :=
  mul_le_mul h (le_refl P)
#align add_submonoid.mul_le_mul_left AddSubmonoid.mul_le_mul_left

theorem mul_le_mul_right {M N P : AddSubmonoid R} (h : N ≤ P) : M * N ≤ M * P :=
  mul_le_mul (le_refl M) h
#align add_submonoid.mul_le_mul_right AddSubmonoid.mul_le_mul_right

theorem mul_subset_mul {M N : AddSubmonoid R} : (↑M : Set R) * (↑N : Set R) ⊆ (↑(M * N) : Set R) :=
  by
  rintro _ ⟨i, j, hi, hj, rfl⟩
  exact mul_mem_mul hi hj
#align add_submonoid.mul_subset_mul AddSubmonoid.mul_subset_mul

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing R]

/-- `add_submonoid.has_pointwise_neg` distributes over multiplication.

This is available as an instance in the `pointwise` locale. -/
protected def hasDistribNeg : HasDistribNeg (AddSubmonoid R) :=
  { AddSubmonoid.hasInvolutiveNeg with
    neg := Neg.neg
    neg_mul := fun x y =>
      by
      refine'
          le_antisymm (mul_le.2 fun m hm n hn => _)
            ((AddSubmonoid.neg_le _ _).2 <| mul_le.2 fun m hm n hn => _) <;>
        simp only [AddSubmonoid.mem_neg, ← neg_mul] at *
      · exact mul_mem_mul hm hn
      · exact mul_mem_mul (neg_mem_neg.2 hm) hn
    mul_neg := fun x y =>
      by
      refine'
          le_antisymm (mul_le.2 fun m hm n hn => _)
            ((AddSubmonoid.neg_le _ _).2 <| mul_le.2 fun m hm n hn => _) <;>
        simp only [AddSubmonoid.mem_neg, ← mul_neg] at *
      · exact mul_mem_mul hm hn
      · exact mul_mem_mul hm (neg_mem_neg.2 hn) }
#align add_submonoid.has_distrib_neg AddSubmonoid.hasDistribNeg

scoped[Pointwise] attribute [instance] AddSubmonoid.hasDistribNeg

end NonUnitalNonAssocRing

section NonAssocSemiring

variable [NonAssocSemiring R]

instance : MulOneClass (AddSubmonoid R) where
  one := 1
  mul := (· * ·)
  one_mul M := by rw [one_eq_closure_one_set, ← closure_eq M, closure_mul_closure, one_mul]
  mul_one M := by rw [one_eq_closure_one_set, ← closure_eq M, closure_mul_closure, mul_one]

end NonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring R]

instance : Semigroup (AddSubmonoid R) where
  mul := (· * ·)
  mul_assoc M N P :=
    le_antisymm
      (mul_le.2 fun mn hmn p hp =>
        suffices M * N ≤ (M * (N * P)).comap (AddMonoidHom.mulRight p) from this hmn
        mul_le.2 fun m hm n hn =>
          show m * n * p ∈ M * (N * P) from
            (mul_assoc m n p).symm ▸ mul_mem_mul hm (mul_mem_mul hn hp))
      (mul_le.2 fun m hm np hnp =>
        suffices N * P ≤ (M * N * P).comap (AddMonoidHom.mulLeft m) from this hnp
        mul_le.2 fun n hn p hp =>
          show m * (n * p) ∈ M * N * P from mul_assoc m n p ▸ mul_mem_mul (mul_mem_mul hm hn) hp)

end NonUnitalSemiring

section Semiring

variable [Semiring R]

instance : Monoid (AddSubmonoid R) :=
  { AddSubmonoid.semigroup,
    AddSubmonoid.mulOneClass with
    one := 1
    mul := (· * ·) }

theorem closure_pow (s : Set R) : ∀ n : ℕ, closure s ^ n = closure (s ^ n)
  | 0 => by rw [pow_zero, pow_zero, one_eq_closure_one_set]
  | n + 1 => by rw [pow_succ, pow_succ, closure_pow, closure_mul_closure]
#align add_submonoid.closure_pow AddSubmonoid.closure_pow

theorem pow_eq_closure_pow_set (s : AddSubmonoid R) (n : ℕ) : s ^ n = closure ((s : Set R) ^ n) :=
  by rw [← closure_pow, closure_eq]
#align add_submonoid.pow_eq_closure_pow_set AddSubmonoid.pow_eq_closure_pow_set

theorem pow_subset_pow {s : AddSubmonoid R} {n : ℕ} : (↑s : Set R) ^ n ⊆ ↑(s ^ n) :=
  (pow_eq_closure_pow_set s n).symm ▸ subset_closure
#align add_submonoid.pow_subset_pow AddSubmonoid.pow_subset_pow

end Semiring

end AddSubmonoid

namespace Set.IsPwo

variable [OrderedCancelCommMonoid α] {s : Set α}

@[to_additive]
theorem submonoid_closure (hpos : ∀ x : α, x ∈ s → 1 ≤ x) (h : s.IsPwo) :
    IsPwo (Submonoid.closure s : Set α) :=
  by
  rw [Submonoid.closure_eq_image_prod]
  refine' (h.partially_well_ordered_on_sublist_forall₂ (· ≤ ·)).image_of_monotone_on _
  exact fun l1 hl1 l2 hl2 h12 => h12.prod_le_prod' fun x hx => hpos x <| hl2 x hx
#align set.is_pwo.submonoid_closure Set.IsPwo.submonoid_closure
#align set.is_pwo.add_submonoid_closure Set.IsPwo.add_submonoid_closure

end Set.IsPwo

