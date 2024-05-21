/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner with enormous help from Jeremy Avigad and Patrick Massot
-/

import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup

/-!
# Defining a monoid given by generators and relations

Given a subset `rels` of relations of the free monoid on a type `α`, this file constructs the monoid
given by generators `x : α` and relations `r ∈ rels`.

## Main definitions

* `PresentedMonoid rels`: the quot group of the free group on a type `α` by the steps-to closure
  of a subset `rels` of relations of the free monoid on `α`.
* `of`: The canonical map from `α` to a presented monoid with generators `α`.
* `toMonoid f`: the canonical monoid homomorphism `PresentedMonoid rels → M`, given a function
  `f : α → G` from a type `α` to a monoid `M` which satisfies the relations `rels`.

## Tags

generators, relations, monoid presentations
-/

variable {α : Type*}

/-- the steps-to closure of a relation -/
inductive PresentedMonoid.StepsTo {β : Type*} [Mul β] (R : β → β → Prop) : β → β → Prop
  | basic : ∀ {x y}, R x y → StepsTo R x y
  | left  : ∀ {x y z}, StepsTo R x y → StepsTo R (z * x) (z * y)
  | right : ∀ {x y z}, StepsTo R x y → StepsTo R (x * z) (y * z)

/-- Given a set of relations, `rels`, over a type `α`, `PresentedMonoid` constructs the monoid with
generators `x : α` and relations `rels` as a quot of `FreeMonoid α`. -/
def PresentedMonoid (rel : FreeMonoid α → FreeMonoid α → Prop) :=
  Quot (PresentedMonoid.StepsTo rel)

namespace PresentedMonoid

open Set Submonoid

/-- The quotient map from the free monoid on `α` to the presented monoid with the same generators
and the given relations `rels`. -/
def mk (rels : FreeMonoid α → FreeMonoid α → Prop) (a : FreeMonoid α) : PresentedMonoid rels :=
  Quot.mk (StepsTo rels) a

/-- `of` is the canonical map from `α` to a presented monoid with generators `x : α`. The term `x`
is mapped to the equivalence class of the image of `x` in `FreeMonoid α`. -/
def of (rels : FreeMonoid α → FreeMonoid α → Prop) (x : α) : PresentedMonoid rels :=
  Quot.mk (StepsTo rels) (FreeMonoid.of x)

section inductionOn

variable {α₁ α₂ α₃ : Type* } {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop}
  {rels₂ : FreeMonoid α₂ → FreeMonoid α₂ → Prop} {rels₃ : FreeMonoid α₃ → FreeMonoid α₃ → Prop}

local notation "P₁" => PresentedMonoid rels₁
local notation "P₂" => PresentedMonoid rels₂
local notation "P₃" => PresentedMonoid rels₃

@[elab_as_elim, induction_eliminator]
protected theorem inductionOn {δ : P₁ → Prop} (q : P₁) (h : ∀ a, δ (mk rels₁ a)) : δ q :=
  Quot.ind h q

@[elab_as_elim]
protected theorem inductionOn₂ {δ : P₁ → P₂ → Prop} (q₁ : P₁) (q₂ : P₂)
    (h : ∀ a b, δ (mk rels₁ a) (mk rels₂ b)) : δ q₁ q₂ :=
  Quot.induction_on₂ q₁ q₂ h

@[elab_as_elim]
protected theorem inductionOn₃ {δ : P₁ → P₂ → P₃ → Prop} (q₁ : P₁)
    (q₂ : P₂) (q₃ : P₃) (h : ∀ a b c, δ (mk rels₁ a) (mk rels₂ b) (mk rels₃ c)) :
    δ q₁ q₂ q₃ :=
  Quot.induction_on₃ q₁ q₂ q₃ h

end inductionOn

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop}

instance instMonoidPresentedMonoid : Monoid (PresentedMonoid rels) where
  mul := Quot.map₂ (· * ·) (fun _ _ _ ↦ StepsTo.left) (fun _ _ _ ↦ StepsTo.right)
  one := mk rels 1
  mul_assoc := fun a b c => Quot.induction_on₃ a b c (fun a b c => congr_arg _ (mul_assoc _ _ _))
  one_mul := fun a => a.inductionOn (fun a' => congr_arg _ (one_mul _))
  mul_one := fun a => a.inductionOn (fun a' => congr_arg _ (mul_one _))

theorem mul_mk (a b : FreeMonoid α) : mk rels a * (mk rels b) = mk rels (a*b) := rfl

theorem one_def : (1 : PresentedMonoid rels) = mk rels 1 := rfl

/-- Given a type α, any binary relation rels on α, a function f : α → β, and a proof h that f
  respects the Steps-To closure of the relation r, then PresentedMonoid.lift f h is the
  corresponding function on PresentedMonoid rels -/
protected def lift {M : Type*} [Monoid M] (f : α → M)
  (h : ∀ (a b : FreeMonoid α), StepsTo rels a b → (FreeMonoid.lift f) a = (FreeMonoid.lift f) b) :
    PresentedMonoid rels → M :=
  Quot.lift (FreeMonoid.lift f) h

/-- The generators of a presented monoid generate the presented monoid. That is, the submonoid
closure of the set of generators equals `⊤`. -/
@[simp] theorem closure_range_of (rels : FreeMonoid α → FreeMonoid α → Prop) :
  Submonoid.closure (Set.range (PresentedMonoid.of rels)) = ⊤ := by
  rw [Submonoid.eq_top_iff']
  intro x
  induction' x with a
  induction a
  · exact Submonoid.one_mem _
  · rename_i x
    exact subset_closure (Exists.intro x rfl)
  rename_i x y hx hy
  exact Submonoid.mul_mem _ hx hy

section ToMonoid
variable {α M : Type*} [Monoid M] (f : α → M)
variable {rels : FreeMonoid α → FreeMonoid α → Prop}
variable (h : ∀ a b : FreeMonoid α, rels a b →  FreeMonoid.lift f a = FreeMonoid.lift f b)

theorem universal_helper (a b : FreeMonoid α) (st : StepsTo rels a b) :
    FreeMonoid.lift f a = FreeMonoid.lift f b := by
  induction st with
  | basic ih => exact h _ _ ih
  | left _ ih => rw [map_mul, map_mul, ih]
  | right _ ih => rw [map_mul, map_mul, ih]

/-- The extension of a map `f : α → M` that satisfies the given relations to a monoid homomorphism
from `PresentedaMonoid rels → M`. -/
instance toMonoid : MonoidHom (PresentedMonoid rels) M where
  toFun := PresentedMonoid.lift f (universal_helper f h)
  map_one' := rfl
  map_mul' := fun a b => PresentedMonoid.inductionOn₂ a b (map_mul (FreeMonoid.lift f))

theorem toMonoid.unique (g : MonoidHom (PresentedMonoid rels) M)
    (hg : ∀ a : α, g (of rels a) = f a) : g = toMonoid f h := by
  ext x
  induction' x with a
  induction a
  · rw [← one_def, MonoidHom.map_one]
    exact rfl
  · rename_i x
    exact hg x
  rename_i x y hx hy
  show g ((mk rels x) * (mk rels y)) = (toMonoid f h) ((mk rels x) * (mk rels y))
  rw [map_mul, hx, hy, map_mul]

@[simp]
theorem toMonoid.of {x : α} : (PresentedMonoid.toMonoid f h) (PresentedMonoid.of rels x) =
    f x := by
  simp only [PresentedMonoid.of, PresentedMonoid.lift, toMonoid, MonoidHom.coe_mk, OneHom.coe_mk,
    FreeMonoid.lift_eval_of]

end ToMonoid

@[ext]
theorem ext {M : Type*} [Monoid M] (rels : FreeMonoid α → FreeMonoid α → Prop)
  {φ ψ : PresentedMonoid rels →* M} (hx : ∀ (x : α), φ (.of rels x) = ψ (.of rels x)) :
    φ = ψ := by
  ext a
  induction' a with b
  induction b
  · rw [← one_def, map_one, map_one]
  · rename_i x
    exact hx x
  rename_i x y hx hy
  rw [← mul_mk, map_mul, map_mul, hx, hy]

section Isomorphism
variable {β : Type*} (e : α ≃ β) (rels : FreeMonoid α → FreeMonoid α → Prop)

/--given an isomorphism between two types, convert a relation function to take in the iso type -/
def rels_iso : FreeMonoid β → FreeMonoid β → Prop :=
  fun a b => rels ((FreeMonoid.congr_iso e).invFun a) ((FreeMonoid.congr_iso e).invFun b)

theorem iso_helper : (StepsTo rels ⇒ StepsTo (rels_iso e rels))
  (FreeMonoid.congr_iso e).toEquiv.toFun (FreeMonoid.congr_iso e).toEquiv.toFun := by
  intro x y h
  induction h with
  | basic rxy =>
    apply StepsTo.basic
    unfold rels_iso
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, Equiv.invFun_as_coe,
      EquivLike.coe_symm_apply_apply]
    exact rxy
  | left _ ih =>
    rw [(FreeMonoid.congr_iso e).map_mul', (FreeMonoid.congr_iso e).map_mul']
    exact StepsTo.left ih
  | right _ ih =>
    rw [(FreeMonoid.congr_iso e).map_mul', (FreeMonoid.congr_iso e).map_mul']
    exact StepsTo.right ih

theorem iso_helper_inv : (StepsTo (rels_iso e rels) ⇒ StepsTo rels)
  (FreeMonoid.congr_iso e).toEquiv.invFun (FreeMonoid.congr_iso e).toEquiv.invFun := by
  intro x y h
  have H : ∀ x y, ((FreeMonoid.congr_iso e).toEquiv.invFun (x*y)) =
      ((FreeMonoid.congr_iso e).toEquiv.invFun x) *
      ((FreeMonoid.congr_iso e).toEquiv.invFun y) := by
    intro x y
    rcases (Equiv.surjective (FreeMonoid.congr_iso e).toEquiv x) with ⟨_, ha⟩
    rcases (Equiv.surjective (FreeMonoid.congr_iso e).toEquiv y) with ⟨_, hb⟩
    rw [← ha, ← hb]
    simp
  induction h with
  | basic rxy =>
    unfold rels_iso at rxy
    exact StepsTo.basic rxy
  | left _ ih =>
    rw [H, H]
    exact StepsTo.left ih
  | right _ ih =>
    rw [H, H]
    exact StepsTo.right ih

/-- forward direction of the bijection for the isomorphism -/
def iso_function : PresentedMonoid rels → PresentedMonoid (rels_iso e rels) :=
  Quot.map ((FreeMonoid.congr_iso e).toFun) (iso_helper e rels)

/-- reverse direction of the bijection for the isomorphism -/
def iso_function_inv : PresentedMonoid (rels_iso e rels) → PresentedMonoid rels :=
  Quot.map ((FreeMonoid.congr_iso e).invFun) (iso_helper_inv e rels)

/-- Presented groups of isomorphic types are isomorphic. -/
def equivPresentedMonoid : PresentedMonoid rels ≃* PresentedMonoid (rels_iso e rels) := by
  apply MulEquiv.mk' ⟨iso_function e rels, iso_function_inv e rels, _, _⟩
  · intro x t
    show iso_function e rels (x * t) = (iso_function e rels x) * (iso_function e rels t)
    refine PresentedMonoid.inductionOn₂ x t ?_
    intro a b
    show PresentedMonoid.mk (rels_iso e rels) ((FreeMonoid.congr_iso e).toEquiv.toFun (a * b)) = _
    rw [(FreeMonoid.congr_iso e).map_mul']
    exact mul_mk _ _
  · intro a
    induction' a with a
    show mk rels _ = _
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, Equiv.invFun_as_coe,
      EquivLike.coe_symm_apply_apply]
  intro b
  induction' b with b
  show mk (rels_iso e rels) _ = _
  simp

theorem equivPresentedMonoid_apply_of (x : α) : (((equivPresentedMonoid e rels).toFun)
  (PresentedMonoid.of rels x)) = (PresentedMonoid.of (rels_iso e rels) (e x)) := rfl

theorem equivPresentedMonoid_symm_apply_of (x : β) : (equivPresentedMonoid e rels).symm
  (PresentedMonoid.of (rels_iso e rels) x) = PresentedMonoid.of rels (e.symm x) := rfl

end Isomorphism
