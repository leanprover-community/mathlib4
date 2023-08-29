/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Hom.Aut
import Mathlib.GroupTheory.GroupAction.Units

#align_import group_theory.group_action.group from "leanprover-community/mathlib"@"ba2245edf0c8bb155f1569fd9b9492a9b384cde6"

/-!
# Group actions applied to various types of group

This file contains lemmas about `SMul` on `GroupWithZero`, and `Group`.
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

section MulAction

/-- `Monoid.toMulAction` is faithful on cancellative monoids. -/
@[to_additive " `AddMonoid.toAddAction` is faithful on additive cancellative monoids. "]
instance RightCancelMonoid.faithfulSMul [RightCancelMonoid α] : FaithfulSMul α α :=
  ⟨fun h => mul_right_cancel (h 1)⟩
#align right_cancel_monoid.to_has_faithful_smul RightCancelMonoid.faithfulSMul
#align add_right_cancel_monoid.to_has_faithful_vadd AddRightCancelMonoid.faithfulVAdd

section Group

variable [Group α] [MulAction α β]

@[to_additive (attr := simp)]
theorem inv_smul_smul (c : α) (x : β) : c⁻¹ • c • x = x := by rw [smul_smul, mul_left_inv, one_smul]
                                                              -- 🎉 no goals
#align inv_smul_smul inv_smul_smul
#align neg_vadd_vadd neg_vadd_vadd

@[to_additive (attr := simp)]
theorem smul_inv_smul (c : α) (x : β) : c • c⁻¹ • x = x := by
  rw [smul_smul, mul_right_inv, one_smul]
  -- 🎉 no goals
#align smul_inv_smul smul_inv_smul
#align vadd_neg_vadd vadd_neg_vadd

/-- Given an action of a group `α` on `β`, each `g : α` defines a permutation of `β`. -/
@[to_additive (attr := simps)]
def MulAction.toPerm (a : α) : Equiv.Perm β :=
  ⟨fun x => a • x, fun x => a⁻¹ • x, inv_smul_smul a, smul_inv_smul a⟩
#align mul_action.to_perm MulAction.toPerm
#align add_action.to_perm AddAction.toPerm
#align add_action.to_perm_apply AddAction.toPerm_apply
#align mul_action.to_perm_apply MulAction.toPerm_apply
#align add_action.to_perm_symm_apply AddAction.toPerm_symm_apply
#align mul_action.to_perm_symm_apply MulAction.toPerm_symm_apply

/-- Given an action of an additive group `α` on `β`, each `g : α` defines a permutation of `β`. -/
add_decl_doc AddAction.toPerm

/-- `MulAction.toPerm` is injective on faithful actions. -/
@[to_additive "`AddAction.toPerm` is injective on faithful actions."]
theorem MulAction.toPerm_injective [FaithfulSMul α β] :
    Function.Injective (MulAction.toPerm : α → Equiv.Perm β) :=
  (show Function.Injective (Equiv.toFun ∘ MulAction.toPerm) from smul_left_injective').of_comp
#align mul_action.to_perm_injective MulAction.toPerm_injective
#align add_action.to_perm_injective AddAction.toPerm_injective

variable (α) (β)

/-- Given an action of a group `α` on a set `β`, each `g : α` defines a permutation of `β`. -/
@[simps]
def MulAction.toPermHom : α →* Equiv.Perm β where
  toFun := MulAction.toPerm
  map_one' := Equiv.ext <| one_smul α
  map_mul' u₁ u₂ := Equiv.ext <| mul_smul (u₁ : α) u₂
#align mul_action.to_perm_hom MulAction.toPermHom
#align mul_action.to_perm_hom_apply MulAction.toPermHom_apply

/-- Given an action of an additive group `α` on a set `β`, each `g : α` defines a permutation of
`β`. -/
@[simps!]
def AddAction.toPermHom (α : Type*) [AddGroup α] [AddAction α β] :
    α →+ Additive (Equiv.Perm β) :=
  MonoidHom.toAdditive'' <| MulAction.toPermHom (Multiplicative α) β
#align add_action.to_perm_hom AddAction.toPermHom

/-- The tautological action by `Equiv.Perm α` on `α`.

This generalizes `Function.End.applyMulAction`.-/
instance Equiv.Perm.applyMulAction (α : Type*) : MulAction (Equiv.Perm α) α where
  smul f a := f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align equiv.perm.apply_mul_action Equiv.Perm.applyMulAction

@[simp]
protected theorem Equiv.Perm.smul_def {α : Type*} (f : Equiv.Perm α) (a : α) : f • a = f a :=
  rfl
#align equiv.perm.smul_def Equiv.Perm.smul_def

/-- `Equiv.Perm.applyMulAction` is faithful. -/
instance Equiv.Perm.applyFaithfulSMul (α : Type*) : FaithfulSMul (Equiv.Perm α) α :=
  ⟨Equiv.ext⟩
#align equiv.perm.apply_has_faithful_smul Equiv.Perm.applyFaithfulSMul

variable {α} {β}

@[to_additive]
theorem inv_smul_eq_iff {a : α} {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
  (MulAction.toPerm a).symm_apply_eq
#align inv_smul_eq_iff inv_smul_eq_iff
#align neg_vadd_eq_iff neg_vadd_eq_iff

@[to_additive]
theorem eq_inv_smul_iff {a : α} {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
  (MulAction.toPerm a).eq_symm_apply
#align eq_inv_smul_iff eq_inv_smul_iff
#align eq_neg_vadd_iff eq_neg_vadd_iff

theorem smul_inv [Group β] [SMulCommClass α β β] [IsScalarTower α β β] (c : α) (x : β) :
    (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, smul_mul_smul, mul_right_inv, mul_right_inv, one_smul]
  -- 🎉 no goals
#align smul_inv smul_inv

theorem smul_zpow [Group β] [SMulCommClass α β β] [IsScalarTower α β β] (c : α) (x : β) (p : ℤ) :
    (c • x) ^ p = c ^ p • x ^ p := by
  cases p <;>
  -- ⊢ (c • x) ^ Int.ofNat a✝ = c ^ Int.ofNat a✝ • x ^ Int.ofNat a✝
  simp [smul_pow, smul_inv]
  -- 🎉 no goals
  -- 🎉 no goals
#align smul_zpow smul_zpow

@[simp]
theorem Commute.smul_right_iff [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β}
    (r : α) : Commute a (r • b) ↔ Commute a b :=
  ⟨fun h => inv_smul_smul r b ▸ h.smul_right r⁻¹, fun h => h.smul_right r⟩
#align commute.smul_right_iff Commute.smul_right_iff

@[simp]
theorem Commute.smul_left_iff [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β}
    (r : α) : Commute (r • a) b ↔ Commute a b := by
  rw [Commute.symm_iff, Commute.smul_right_iff, Commute.symm_iff]
  -- 🎉 no goals
#align commute.smul_left_iff Commute.smul_left_iff

@[to_additive]
protected theorem MulAction.bijective (g : α) : Function.Bijective ((· • ·) g : β → β) :=
  (MulAction.toPerm g).bijective
#align mul_action.bijective MulAction.bijective
#align add_action.bijective AddAction.bijective

@[to_additive]
protected theorem MulAction.injective (g : α) : Function.Injective ((· • ·) g : β → β) :=
  (MulAction.bijective g).injective
#align mul_action.injective MulAction.injective
#align add_action.injective AddAction.injective

@[to_additive]
protected theorem MulAction.surjective (g : α) : Function.Surjective ((· • ·) g : β → β) :=
  (MulAction.bijective g).surjective
#align mul_action.surjective MulAction.surjective
#align add_action.surjective AddAction.surjective

@[to_additive]
theorem smul_left_cancel (g : α) {x y : β} (h : g • x = g • y) : x = y :=
  MulAction.injective g h
#align smul_left_cancel smul_left_cancel
#align vadd_left_cancel vadd_left_cancel

@[to_additive (attr := simp)]
theorem smul_left_cancel_iff (g : α) {x y : β} : g • x = g • y ↔ x = y :=
  (MulAction.injective g).eq_iff
#align smul_left_cancel_iff smul_left_cancel_iff
#align vadd_left_cancel_iff vadd_left_cancel_iff

@[to_additive]
theorem smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g • x = y ↔ x = g⁻¹ • y :=
  (MulAction.toPerm g).apply_eq_iff_eq_symm_apply
#align smul_eq_iff_eq_inv_smul smul_eq_iff_eq_inv_smul
#align vadd_eq_iff_eq_neg_vadd vadd_eq_iff_eq_neg_vadd

end Group

/-- `Monoid.toMulAction` is faithful on nontrivial cancellative monoids with zero. -/
instance CancelMonoidWithZero.faithfulSMul [CancelMonoidWithZero α] [Nontrivial α] :
    FaithfulSMul α α :=
  ⟨fun h => mul_left_injective₀ one_ne_zero (h 1)⟩
#align cancel_monoid_with_zero.to_has_faithful_smul CancelMonoidWithZero.faithfulSMul

section Gwz

variable [GroupWithZero α] [MulAction α β] {a : α}

@[simp]
theorem inv_smul_smul₀ {c : α} (hc : c ≠ 0) (x : β) : c⁻¹ • c • x = x :=
  inv_smul_smul (Units.mk0 c hc) x
#align inv_smul_smul₀ inv_smul_smul₀

@[simp]
theorem smul_inv_smul₀ {c : α} (hc : c ≠ 0) (x : β) : c • c⁻¹ • x = x :=
  smul_inv_smul (Units.mk0 c hc) x
#align smul_inv_smul₀ smul_inv_smul₀

theorem inv_smul_eq_iff₀ {a : α} (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
  ⟨fun h => by rw [← h, smul_inv_smul₀ ha], fun h => by rw [h, inv_smul_smul₀ ha]⟩
               -- 🎉 no goals
                                                        -- 🎉 no goals
#align inv_smul_eq_iff₀ inv_smul_eq_iff₀

theorem eq_inv_smul_iff₀ {a : α} (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
  (MulAction.toPerm (Units.mk0 a ha)).eq_symm_apply
#align eq_inv_smul_iff₀ eq_inv_smul_iff₀

@[simp]
theorem Commute.smul_right_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β}
    {c : α} (hc : c ≠ 0) : Commute a (c • b) ↔ Commute a b :=
  Commute.smul_right_iff (Units.mk0 c hc)
#align commute.smul_right_iff₀ Commute.smul_right_iff₀

@[simp]
theorem Commute.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β} {c : α}
    (hc : c ≠ 0) : Commute (c • a) b ↔ Commute a b :=
  Commute.smul_left_iff (Units.mk0 c hc)
#align commute.smul_left_iff₀ Commute.smul_left_iff₀

protected theorem MulAction.bijective₀ (ha : a ≠ 0) : Function.Bijective ((· • ·) a : β → β) :=
  MulAction.bijective <| Units.mk0 a ha
#align mul_action.bijective₀ MulAction.bijective₀

protected theorem MulAction.injective₀ (ha : a ≠ 0) : Function.Injective ((· • ·) a : β → β) :=
  (MulAction.bijective₀ ha).injective
#align mul_action.injective₀ MulAction.injective₀

protected theorem MulAction.surjective₀ (ha : a ≠ 0) : Function.Surjective ((· • ·) a : β → β) :=
  (MulAction.bijective₀ ha).surjective
#align mul_action.surjective₀ MulAction.surjective₀

end Gwz

end MulAction

section DistribMulAction

section Group

variable [Group α] [AddMonoid β] [DistribMulAction α β]

variable (β)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps (config := { simpRhs := true })]
def DistribMulAction.toAddEquiv (x : α) : β ≃+ β :=
  { DistribMulAction.toAddMonoidHom β x, MulAction.toPermHom α β x with }
#align distrib_mul_action.to_add_equiv DistribMulAction.toAddEquiv
#align distrib_mul_action.to_add_equiv_apply DistribMulAction.toAddEquiv_apply
#align distrib_mul_action.to_add_equiv_symm_apply DistribMulAction.toAddEquiv_symm_apply

variable (α)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
def DistribMulAction.toAddAut : α →* AddAut β where
  toFun := DistribMulAction.toAddEquiv β
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)
#align distrib_mul_action.to_add_aut DistribMulAction.toAddAut
#align distrib_mul_action.to_add_aut_apply DistribMulAction.toAddAut_apply

variable {α β}

theorem smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← inv_smul_smul a x, h, smul_zero], fun h => h.symm ▸ smul_zero _⟩
               -- 🎉 no goals
#align smul_eq_zero_iff_eq smul_eq_zero_iff_eq

theorem smul_ne_zero_iff_ne (a : α) {x : β} : a • x ≠ 0 ↔ x ≠ 0 :=
  not_congr <| smul_eq_zero_iff_eq a
#align smul_ne_zero_iff_ne smul_ne_zero_iff_ne

end Group

section Gwz

variable [GroupWithZero α] [AddMonoid β] [DistribMulAction α β]

theorem smul_eq_zero_iff_eq' {a : α} (ha : a ≠ 0) {x : β} : a • x = 0 ↔ x = 0 :=
  show Units.mk0 a ha • x = 0 ↔ x = 0 from smul_eq_zero_iff_eq _
#align smul_eq_zero_iff_eq' smul_eq_zero_iff_eq'

theorem smul_ne_zero_iff_ne' {a : α} (ha : a ≠ 0) {x : β} : a • x ≠ 0 ↔ x ≠ 0 :=
  show Units.mk0 a ha • x ≠ 0 ↔ x ≠ 0 from smul_ne_zero_iff_ne _
#align smul_ne_zero_iff_ne' smul_ne_zero_iff_ne'

end Gwz

end DistribMulAction

section MulDistribMulAction

variable [Group α] [Monoid β] [MulDistribMulAction α β]

variable (β)

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps (config := { simpRhs := true })]
def MulDistribMulAction.toMulEquiv (x : α) : β ≃* β :=
  { MulDistribMulAction.toMonoidHom β x, MulAction.toPermHom α β x with }
#align mul_distrib_mul_action.to_mul_equiv MulDistribMulAction.toMulEquiv
#align mul_distrib_mul_action.to_mul_equiv_symm_apply MulDistribMulAction.toMulEquiv_symm_apply
#align mul_distrib_mul_action.to_mul_equiv_apply MulDistribMulAction.toMulEquiv_apply

variable (α)

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
def MulDistribMulAction.toMulAut : α →* MulAut β where
  toFun := MulDistribMulAction.toMulEquiv β
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)
#align mul_distrib_mul_action.to_mul_aut MulDistribMulAction.toMulAut
#align mul_distrib_mul_action.to_mul_aut_apply MulDistribMulAction.toMulAut_apply

variable {α β}

end MulDistribMulAction

section Arrow

/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g • F) a = F (g⁻¹ • a)`. -/
@[to_additive (attr := simps) arrowAddAction
      "If `G` acts on `A`, then it acts also on `A → B`, by `(g +ᵥ F) a = F (g⁻¹ +ᵥ a)`"]
def arrowAction {G A B : Type*} [DivisionMonoid G] [MulAction G A] : MulAction G (A → B) where
  smul g F a := F (g⁻¹ • a)
  one_smul := by
    intro f
    -- ⊢ 1 • f = f
    show (fun x => f ((1 : G)⁻¹ • x)) = f
    -- ⊢ (fun x => f (1⁻¹ • x)) = f
    simp only [inv_one, one_smul]
    -- 🎉 no goals
  mul_smul := by
    intros x y f
    -- ⊢ (x * y) • f = x • y • f
    show (fun a => f ((x*y)⁻¹ • a)) = (fun a => f (y⁻¹ • x⁻¹ • a))
    -- ⊢ (fun a => f ((x * y)⁻¹ • a)) = fun a => f (y⁻¹ • x⁻¹ • a)
    simp only [mul_smul, mul_inv_rev]
    -- 🎉 no goals
#align arrow_action arrowAction
#align arrow_add_action arrowAddAction

attribute [local instance] arrowAction

/-- When `B` is a monoid, `ArrowAction` is additionally a `MulDistribMulAction`. -/
def arrowMulDistribMulAction {G A B : Type*} [Group G] [MulAction G A] [Monoid B] :
    MulDistribMulAction G (A → B) where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl
#align arrow_mul_distrib_mul_action arrowMulDistribMulAction

attribute [local instance] arrowMulDistribMulAction

/-- Given groups `G H` with `G` acting on `A`, `G` acts by
  multiplicative automorphisms on `A → H`. -/
@[simps!]
def mulAutArrow {G A H} [Group G] [MulAction G A] [Monoid H] : G →* MulAut (A → H) :=
  MulDistribMulAction.toMulAut _ _
#align mul_aut_arrow mulAutArrow
#align mul_aut_arrow_apply_apply mulAutArrow_apply_apply
#align mul_aut_arrow_apply_symm_apply mulAutArrow_apply_symm_apply

end Arrow

namespace IsUnit

section MulAction

variable [Monoid α] [MulAction α β]

@[to_additive]
theorem smul_left_cancel {a : α} (ha : IsUnit a) {x y : β} : a • x = a • y ↔ x = y :=
  let ⟨u, hu⟩ := ha
  hu ▸ smul_left_cancel_iff u
#align is_unit.smul_left_cancel IsUnit.smul_left_cancel
#align is_add_unit.vadd_left_cancel IsAddUnit.vadd_left_cancel

end MulAction

section DistribMulAction

variable [Monoid α] [AddMonoid β] [DistribMulAction α β]

@[simp]
theorem smul_eq_zero {u : α} (hu : IsUnit u) {x : β} : u • x = 0 ↔ x = 0 :=
  (Exists.elim hu) fun u hu => hu ▸ show u • x = 0 ↔ x = 0 from smul_eq_zero_iff_eq u
#align is_unit.smul_eq_zero IsUnit.smul_eq_zero

end DistribMulAction

end IsUnit

section SMul

variable [Group α] [Monoid β]

@[simp]
theorem isUnit_smul_iff [MulAction α β] [SMulCommClass α β β] [IsScalarTower α β β] (g : α)
    (m : β) : IsUnit (g • m) ↔ IsUnit m :=
  ⟨fun h => inv_smul_smul g m ▸ h.smul g⁻¹, IsUnit.smul g⟩
#align is_unit_smul_iff isUnit_smul_iff

theorem IsUnit.smul_sub_iff_sub_inv_smul [AddGroup β] [DistribMulAction α β] [IsScalarTower α β β]
    [SMulCommClass α β β] (r : α) (a : β) : IsUnit (r • (1 : β) - a) ↔ IsUnit (1 - r⁻¹ • a) := by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a), smul_sub, smul_inv_smul]
  -- 🎉 no goals
#align is_unit.smul_sub_iff_sub_inv_smul IsUnit.smul_sub_iff_sub_inv_smul

end SMul
