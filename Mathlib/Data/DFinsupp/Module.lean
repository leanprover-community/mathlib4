/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.DFinsupp.Defs

/-!
# Group actions on `DFinsupp`

## Main results

* `DFinsupp.module`: pointwise scalar multiplication on `DFinsupp` gives a module structure
-/

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section Algebra

/-- Dependent functions with finite support inherit a semiring action from an action on each
coordinate. -/
instance [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] : SMulZeroClass γ (Π₀ i, β i) where
  smul c v := v.mapRange (fun _ => (c • ·)) fun _ => smul_zero _
  smul_zero _ := mapRange_zero _ _

theorem smul_apply [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] (b : γ)
    (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl

@[simp, norm_cast]
theorem coe_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] (b : γ)
    (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl

instance smulCommClass {δ : Type*} [∀ i, Zero (β i)]
    [∀ i, SMulZeroClass γ (β i)] [∀ i, SMulZeroClass δ (β i)] [∀ i, SMulCommClass γ δ (β i)] :
    SMulCommClass γ δ (Π₀ i, β i) where
  smul_comm r s m := ext fun i => by simp only [smul_apply, smul_comm r s (m i)]

instance isScalarTower {δ : Type*} [∀ i, Zero (β i)]
    [∀ i, SMulZeroClass γ (β i)] [∀ i, SMulZeroClass δ (β i)] [SMul γ δ]
    [∀ i, IsScalarTower γ δ (β i)] : IsScalarTower γ δ (Π₀ i, β i) where
  smul_assoc r s m := ext fun i => by simp only [smul_apply, smul_assoc r s (m i)]

instance isCentralScalar [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]
    [∀ i, SMulZeroClass γᵐᵒᵖ (β i)] [∀ i, IsCentralScalar γ (β i)] :
    IsCentralScalar γ (Π₀ i, β i) where
  op_smul_eq_smul r m := ext fun i => by simp only [smul_apply, op_smul_eq_smul r (m i)]

/-- Dependent functions with finite support inherit a `DistribMulAction` structure from such a
structure on each coordinate. -/
instance distribMulAction [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] :
    DistribMulAction γ (Π₀ i, β i) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom DFunLike.coe_injective coe_smul

/-- Dependent functions with finite support inherit a module structure from such a structure on
each coordinate. -/
instance module [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] :
    Module γ (Π₀ i, β i) :=
  { inferInstanceAs (DistribMulAction γ (Π₀ i, β i)) with
    zero_smul := fun c => ext fun i => by simp only [smul_apply, zero_smul, zero_apply]
    add_smul := fun c x y => ext fun i => by simp only [add_apply, smul_apply, add_smul] }

end Algebra

variable (γ) in
/-- Coercion from a `DFinsupp` to a pi type is a `LinearMap`. -/
def coeFnLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] :
    (Π₀ i, β i) →ₗ[γ] ∀ i, β i where
  toFun := (⇑)
  map_add' := coe_add
  map_smul' := coe_smul

@[simp]
lemma coeFnLinearMap_apply [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)]
    (v : Π₀ i, β i) : coeFnLinearMap γ v = v :=
  rfl

section FilterAndSubtypeDomain

@[simp]
theorem filter_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] (p : ι → Prop)
    [DecidablePred p] (r : γ) (f : Π₀ i, β i) : (r • f).filter p = r • f.filter p := by
  ext
  simp [smul_apply, smul_ite]

variable (γ β)

/-- `DFinsupp.filter` as a `LinearMap`. -/
@[simps]
def filterLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] (p : ι → Prop)
    [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i, β i where
  toFun := filter p
  map_add' := filter_add p
  map_smul' := filter_smul p

variable {γ β}

@[simp]
theorem subtypeDomain_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]
    {p : ι → Prop} [DecidablePred p] (r : γ) (f : Π₀ i, β i) :
    (r • f).subtypeDomain p = r • f.subtypeDomain p :=
  DFunLike.coe_injective rfl

variable (γ β)

/-- `DFinsupp.subtypeDomain` as a `LinearMap`. -/
@[simps]
def subtypeDomainLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)]
    (p : ι → Prop) [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i : Subtype p, β i where
  toFun := subtypeDomain p
  map_add' := subtypeDomain_add
  map_smul' := subtypeDomain_smul

end FilterAndSubtypeDomain

section DecidableEq
variable [DecidableEq ι]

section

variable [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]

@[simp]
theorem mk_smul {s : Finset ι} (c : γ) (x : ∀ i : (↑s : Set ι), β (i : ι)) :
    mk s (c • x) = c • mk s x :=
  ext fun i => by simp only [smul_apply, mk_apply]; split_ifs <;> [rfl; rw [smul_zero]]

@[simp]
theorem single_smul {i : ι} (c : γ) (x : β i) : single i (c • x) = c • single i x :=
  ext fun i => by
    simp only [smul_apply, single_apply]
    split_ifs with h
    · cases h; rfl
    · rw [smul_zero]

end

theorem support_smul {γ : Type w} [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (b : γ) (v : Π₀ i, β i) :
    (b • v).support ⊆ v.support :=
  support_mapRange

end DecidableEq

section Equiv

open Finset

variable {κ : Type*}

@[simp]
theorem comapDomain_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]
    (h : κ → ι) (hh : Function.Injective h) (r : γ) (f : Π₀ i, β i) :
    comapDomain h hh (r • f) = r • comapDomain h hh f := by
  ext
  rw [smul_apply, comapDomain_apply, smul_apply, comapDomain_apply]

@[simp]
theorem comapDomain'_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]
    (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h) (r : γ) (f : Π₀ i, β i) :
    comapDomain' h hh' (r • f) = r • comapDomain' h hh' f := by
  ext
  rw [smul_apply, comapDomain'_apply, smul_apply, comapDomain'_apply]

section SigmaCurry

variable {α : ι → Type*} {δ : ∀ i, α i → Type v}

instance distribMulAction₂ [Monoid γ] [∀ i j, AddMonoid (δ i j)]
    [∀ i j, DistribMulAction γ (δ i j)] : DistribMulAction γ (Π₀ (i : ι) (j : α i), δ i j) :=
  @DFinsupp.distribMulAction ι _ (fun i => Π₀ j, δ i j) _ _ _

end SigmaCurry

variable {α : Option ι → Type v}

theorem equivProdDFinsupp_smul [∀ i, Zero (α i)] [∀ i, SMulZeroClass γ (α i)]
    (r : γ) (f : Π₀ i, α i) : equivProdDFinsupp (r • f) = r • equivProdDFinsupp f :=
  Prod.ext (smul_apply _ _ _) (comapDomain_smul _ (Option.some_injective _) _ _)

end Equiv

end DFinsupp
