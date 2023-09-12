/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apahe 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.PushoutI
import Mathlib.GroupTheory.HNNExtension
import Mathlib.GroupTheory.SemidirectProduct

namespace OneRelator

variable {α G : Type*} [Group G] (r : FreeGroup α)

def OneRelator (r : FreeGroup α) : Type _ :=
  FreeGroup α ⧸ Subgroup.normalClosure {r}

instance : Group (OneRelator r) := by
  delta OneRelator; infer_instance

variable {r}

def lift (f : α → G) (hf : FreeGroup.lift f r = 1) : OneRelator r →* G :=
  QuotientGroup.lift _ (FreeGroup.lift f)
    (show Subgroup.normalClosure {r} ≤ (FreeGroup.lift f).ker from
      Subgroup.normalClosure_le_normal (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hf))

def of (x : α) : OneRelator r := QuotientGroup.mk (FreeGroup.of x)

@[simp]
theorem lift_of (f : α → G) (hf : FreeGroup.lift f r = 1) (x : α) :
    lift f hf (of x) = f x := by
  rw [lift, of, QuotientGroup.lift_mk', FreeGroup.lift_of]

@[ext high]
theorem hom_ext {f g : OneRelator r →* G} (h : ∀ x, f (of x) = g (of x)) : f = g := by
  delta OneRelator
  ext
  exact h _

end OneRelator

section Equivs

open SemidirectProduct Multiplicative FreeGroup

def FreeGroup.mapPermHom (α : Type*) :
    Equiv.Perm α →* MulAut (FreeGroup α) :=
  { toFun := fun e =>
      MonoidHom.toMulEquiv
        (FreeGroup.lift (fun a => FreeGroup.of (e a)))
        (FreeGroup.lift (fun a => FreeGroup.of (e.symm a)))
        (FreeGroup.ext_hom _ _ (fun _ => by simp))
        (FreeGroup.ext_hom _ _ (fun _ => by simp))
    map_one' := MulEquiv.toMonoidHom_injective
      (FreeGroup.ext_hom _ _ (fun _ => by simp))
    map_mul' := fun _ _ => MulEquiv.toMonoidHom_injective
      (FreeGroup.ext_hom _ _ (fun _ => by simp)) }

def prodPerm (α : Type*) : Multiplicative ℤ →*
    Equiv.Perm (α × Multiplicative ℤ) :=
  { toFun := fun g => Equiv.prodCongr 1 (MulAction.toPermHom _ _ g),
    map_one' := by ext <;> simp,
    map_mul' := fun _ _ => by ext <;> simp }

theorem MulAut.conj_pow_apply {G : Type*} [Group G]
    (g₁ g₂: G) (n : ℕ) : (MulAut.conj g₁ ^ n) g₂ =
    g₁ ^ n * g₂ * (g₁ ^ n)⁻¹ := by
  rw [← map_pow, MulAut.conj_apply]

theorem MulAut.conj_zpow_apply {G : Type*} [Group G]
    (g₁ g₂: G) (n : ℤ) : (MulAut.conj g₁ ^ n) g₂ =
    g₁ ^ n * g₂ * (g₁ ^ n)⁻¹ := by
  rw [← map_zpow, MulAut.conj_apply]

def freeGroupEquivSemidirectProduct {α : Type*} [DecidableEq α] (a : α) :
    FreeGroup α ≃* FreeGroup ({b // b ≠ a} × Multiplicative ℤ)
      ⋊[(FreeGroup.mapPermHom _).comp (prodPerm _)] (Multiplicative ℤ) :=
  MonoidHom.toMulEquiv
    (FreeGroup.lift
      (fun b =>
        if hb : b = a
        then inr (ofAdd 1)
        else inl (FreeGroup.of (⟨b, hb⟩, 1))))
    (SemidirectProduct.lift
      (FreeGroup.lift (fun b => (of a) ^ toAdd b.2 * of b.1.1 * (of a) ^ (-toAdd b.2)))
      (zpowersHom _ (of a))
      (fun z => FreeGroup.ext_hom _ _ <| by
        intro b
        simp [mapPermHom, prodPerm, mul_assoc, MulAut.conj_zpow_apply, zpow_add]
        group))
    (FreeGroup.ext_hom _ _ <| fun _ => by
      simp; split_ifs <;> simp_all)
    (SemidirectProduct.hom_ext
      (FreeGroup.ext_hom _ _ <| by
        rintro ⟨⟨b, hb⟩, z⟩
        simp only [ne_eq, zpow_neg, MonoidHom.coe_comp, Function.comp_apply, lift_inl,
          lift_of, _root_.map_mul, map_zpow, dite_true, hb, dite_false, _root_.map_inv,
          MonoidHom.id_comp]
        rw [← _root_.map_zpow, ← _root_.map_inv, ← inl_aut, ← Int.ofAdd_mul, one_mul,
          ofAdd_toAdd]
        simp [mapPermHom, prodPerm])
      (MonoidHom.ext_mint (by simp)))

axiom FreeGroup.vars {α : Type*} : FreeGroup α → Finset α

axiom FreeGroup.conjVars {α : Type*} : FreeGroup α → Finset α

end Equivs

namespace OneRelator

section HNNExtension

variable {α : Type*} [DecidableEq α] (r : FreeGroup α) (t : α)

def newRelator (r : FreeGroup α) (t : α) :
    FreeGroup ({ b // b ≠ t } × Multiplicative ℤ) :=
  (freeGroupEquivSemidirectProduct t r).left

def HNNSet (r : FreeGroup α) (t : α) : Set ({ b : α // b ≠ t } × Multiplicative ℤ) :=
  { p : { b : α // b ≠ t } × Multiplicative ℤ |
      ∃ z₁ z₂, (p.1, z₁) ∈ (newRelator r t).vars ∧
               (p.1, z₂) ∈ (newRelator r t).vars ∧
        z₁ ≤ p.2 ∧ ↑p.2 ≤ z₂ }

def SubgroupASet (r : FreeGroup α) (t : α) : Set ({ b : α // b ≠ t } × Multiplicative ℤ) :=
  { p : { b : α // b ≠ t } × Multiplicative ℤ |
        ∃ z₁ z₂, (p.1, z₁) ∈ (newRelator r t).vars ∧
                 (p.1, z₂) ∈ (newRelator r t).vars ∧
          z₁ ≤ p.2 ∧ ↑p.2 < z₂ }

def SubgroupBSet (r : FreeGroup α) (t : α) : Set ({ b : α // b ≠ t } × Multiplicative ℤ) :=
  { p : { b : α // b ≠ t } × Multiplicative ℤ |
        ∃ z₁ z₂, (p.1, z₁) ∈ (newRelator r t).vars ∧
                 (p.1, z₂) ∈ (newRelator r t).vars ∧
          z₁ < p.2 ∧ ↑p.2 ≤ z₂ }

theorem subgroupASet_subset_HNNSet :
    SubgroupASet r t ⊆ HNNSet r t :=
  fun _ ⟨z₁, z₂, hz₁, hz₂, hz₁p, hz₂p⟩ =>
    ⟨z₁, z₂, hz₁, hz₂, hz₁p, le_of_lt hz₂p⟩

theorem subgroupBSet_subset_HNNSet :
    SubgroupBSet r t ⊆ HNNSet r t :=
  fun _ ⟨z₁, z₂, hz₁, hz₂, hz₁p, hz₂p⟩ =>
    ⟨z₁, z₂, hz₁, hz₂, le_of_lt hz₁p, hz₂p⟩

instance : Coe (SubgroupASet r t) (HNNSet r t) :=
  ⟨Set.inclusion (subgroupASet_subset_HNNSet r t)⟩

instance : Coe (SubgroupBSet r t) (HNNSet r t) :=
  ⟨Set.inclusion (subgroupBSet_subset_HNNSet r t)⟩

def subgroupA : Subgroup (FreeGroup (HNNSet r t)) :=
  MonoidHom.range (FreeGroup.map ((↑) : SubgroupASet r t → HNNSet r t))

def subgroupB : Subgroup (FreeGroup (HNNSet r t)) :=
  MonoidHom.range (FreeGroup.map ((↑) : SubgroupASet r t → HNNSet r t))

noncomputable def subgroupEquiv : subgroupA r t ≃* subgroupB r t :=
  MulEquiv.trans
    (MonoidHom.ofInjective (FreeGroup.map_injective
      (Set.inclusion_injective _))).symm
    ((MonoidHom.ofInjective (FreeGroup.map_injective
      (Set.inclusion_injective _))))

noncomputable def equivHNNExtension :
    OneRelator r ≃* HNNExtension _ (subgroupA r t) (subgroupB r t) (subgroupEquiv r t) :=
  MonoidHom.toMulEquiv
    (OneRelator.lift
      (fun a => sorry)
      sorry)
    (HNNExtension.lift
      _
      _
      _)
    _
    _

end HNNExtension

end OneRelator
