/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes, Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The abelianization of a group

This file defines the commutator and the abelianization of a group. It furthermore prepares for the
result that the abelianization is left adjoint to the forgetful functor from abelian groups to
groups, which can be found in `Mathlib/Algebra/Category/GrpCat/Adjunctions.lean`.

## Main definitions

* `Abelianization`: defines the abelianization of a group `G` as the quotient of a group by its
  commutator subgroup.
* `Abelianization.map`: lifts a group homomorphism to a homomorphism between the abelianizations
* `MulEquiv.abelianizationCongr`: Equivalent groups have equivalent abelianizations

-/

assert_not_exists Cardinal Field

universe u v w

-- Let G be a group.
variable (G : Type u) [Group G]

open Subgroup (centralizer)

/-- The abelianization of G is the quotient of G by its commutator subgroup. -/
def Abelianization : Type u :=
  G ⧸ commutator G

namespace Abelianization

attribute [local instance] QuotientGroup.leftRel

instance commGroup : CommGroup (Abelianization G) where
  __ := QuotientGroup.Quotient.group _
  mul_comm x y := Quotient.inductionOn₂ x y fun a b ↦ Quotient.sound' <|
    QuotientGroup.leftRel_apply.mpr <| Subgroup.subset_closure
      -- We avoid `group` here to minimize imports while low in the hierarchy;
      -- typically it would be better to invoke the tactic.
      ⟨b⁻¹, Subgroup.mem_top _, a⁻¹, Subgroup.mem_top _, by simp [commutatorElement_def, mul_assoc]⟩

instance : Inhabited (Abelianization G) :=
  ⟨1⟩

variable {G}

/-- `of` is the canonical projection from G to its abelianization. -/
def of : G →* Abelianization G where
  toFun := QuotientGroup.mk
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem mk_eq_of (a : G) : Quot.mk _ a = of a :=
  rfl

variable (G) in
@[simp]
theorem ker_of : of.ker = commutator G :=
  QuotientGroup.ker_mk' (commutator G)

section lift

-- So far we have built Gᵃᵇ and proved it's an abelian group.
-- Furthermore we defined the canonical projection `of : G → Gᵃᵇ`
-- Let `A` be an abelian group and let `f` be a group homomorphism from `G` to `A`.
variable {A : Type v} [CommGroup A] (f : G →* A)

theorem commutator_subset_ker : commutator G ≤ f.ker := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro x ⟨p, q, rfl⟩
  simp [MonoidHom.mem_ker, mul_right_comm (f p) (f q), commutatorElement_def]

/-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map
  from the abelianization of a `G` to `A` that factors through `f`. -/
def lift : (G →* A) ≃ (Abelianization G →* A) where
  toFun f := QuotientGroup.lift _ f fun _ h => MonoidHom.mem_ker.2 <| commutator_subset_ker _ h
  invFun F := F.comp of
  right_inv _ := MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

@[simp]
theorem lift_apply_of (x : G) : lift f (of x) = f x :=
  rfl

@[deprecated (since := "2025-07-23")]
alias lift.of := lift_apply_of

theorem coe_lift_symm : (lift.symm : (Abelianization G →* A) → (G →* A)) = (·.comp of) := rfl

@[simp]
theorem lift_symm_apply (f : Abelianization G →* A) : lift.symm f = f.comp of := rfl

theorem lift_unique (φ : Abelianization G →* A)
    -- hφ : φ agrees with f on the image of G in Gᵃᵇ
    (hφ : ∀ x : G, φ (Abelianization.of x) = f x)
    {x : Abelianization G} : φ x = lift f x :=
  QuotientGroup.induction_on x hφ

@[deprecated (since := "2025-07-23")] alias lift.unique := lift_unique

@[simp]
theorem lift_of : lift of = MonoidHom.id (Abelianization G) :=
  lift.apply_symm_apply <| MonoidHom.id _

end lift

variable {A : Type v} [Monoid A]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext (φ ψ : Abelianization G →* A) (h : φ.comp of = ψ.comp of) : φ = ψ :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x <| DFunLike.congr_fun h

section Map

variable {H : Type v} [Group H] (f : G →* H)

/-- The map operation of the `Abelianization` functor -/
def map : Abelianization G →* Abelianization H :=
  lift (of.comp f)

/-- Use `map` as the preferred simp normal form. -/
@[simp] theorem lift_of_comp :
    Abelianization.lift (Abelianization.of.comp f) = Abelianization.map f := rfl

@[simp]
theorem map_of (x : G) : map f (of x) = of (f x) :=
  rfl

@[simp]
theorem map_id : map (MonoidHom.id G) = MonoidHom.id (Abelianization G) :=
  hom_ext _ _ rfl

@[simp]
theorem map_comp {I : Type w} [Group I] (g : H →* I) : (map g).comp (map f) = map (g.comp f) :=
  hom_ext _ _ rfl

@[simp]
theorem map_map_apply {I : Type w} [Group I] {g : H →* I} {x : Abelianization G} :
    map g (map f x) = map (g.comp f) x :=
  DFunLike.congr_fun (map_comp _ _) x

end Map

end Abelianization

section AbelianizationCongr

variable {G} {H : Type v} [Group H]

/-- Equivalent groups have equivalent abelianizations -/
def MulEquiv.abelianizationCongr (e : G ≃* H) : Abelianization G ≃* Abelianization H where
  toFun := Abelianization.map e.toMonoidHom
  invFun := Abelianization.map e.symm.toMonoidHom
  left_inv := by
    rintro ⟨a⟩
    simp
  right_inv := by
    rintro ⟨a⟩
    simp
  map_mul' := MonoidHom.map_mul _

@[simp]
theorem abelianizationCongr_of (e : G ≃* H) (x : G) :
    e.abelianizationCongr (Abelianization.of x) = Abelianization.of (e x) :=
  rfl

@[simp]
theorem abelianizationCongr_refl :
    (MulEquiv.refl G).abelianizationCongr = MulEquiv.refl (Abelianization G) :=
  MulEquiv.toMonoidHom_injective Abelianization.lift_of

@[simp]
theorem abelianizationCongr_symm (e : G ≃* H) :
    e.abelianizationCongr.symm = e.symm.abelianizationCongr :=
  rfl

@[simp]
theorem abelianizationCongr_trans {I : Type v} [Group I] (e : G ≃* H) (e₂ : H ≃* I) :
    e.abelianizationCongr.trans e₂.abelianizationCongr = (e.trans e₂).abelianizationCongr :=
  MulEquiv.toMonoidHom_injective (Abelianization.hom_ext _ _ rfl)

end AbelianizationCongr

/-- An Abelian group is equivalent to its own abelianization. -/
@[simps]
def Abelianization.equivOfComm {H : Type*} [CommGroup H] : H ≃* Abelianization H :=
  { Abelianization.of with
    toFun := Abelianization.of
    invFun := Abelianization.lift (MonoidHom.id H)
    right_inv := by
      rintro ⟨a⟩
      rfl }

instance [Unique G] : Unique (Abelianization G) := Quotient.instUniqueQuotient _
