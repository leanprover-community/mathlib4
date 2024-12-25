/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes
-/
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finite.Prod
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Finiteness

/-!
# The abelianization of a group

This file defines the commutator and the abelianization of a group. It furthermore prepares for the
result that the abelianization is left adjoint to the forgetful functor from abelian groups to
groups, which can be found in `Algebra/Category/Group/Adjunctions`.

## Main definitions

* `commutator`: defines the commutator of a group `G` as a subgroup of `G`.
* `Abelianization`: defines the abelianization of a group `G` as the quotient of a group by its
  commutator subgroup.
* `Abelianization.map`: lifts a group homomorphism to a homomorphism between the abelianizations
* `MulEquiv.abelianizationCongr`: Equivalent groups have equivalent abelianizations

-/


universe u v w

-- Let G be a group.
variable (G : Type u) [Group G]

open Subgroup (centralizer)

/-- The commutator subgroup of a group G is the normal subgroup
  generated by the commutators [p,q]=`p*q*p⁻¹*q⁻¹`. -/
def commutator : Subgroup G := ⁅(⊤ : Subgroup G), ⊤⁆

-- Porting note: this instance should come from `deriving Subgroup.Normal`
instance : Subgroup.Normal (commutator G) := Subgroup.commutator_normal ⊤ ⊤

theorem commutator_def : commutator G = ⁅(⊤ : Subgroup G), ⊤⁆ :=
  rfl

theorem commutator_eq_closure : commutator G = Subgroup.closure (commutatorSet G) := by
  simp [commutator, Subgroup.commutator_def, commutatorSet]

theorem commutator_eq_normalClosure : commutator G = Subgroup.normalClosure (commutatorSet G) := by
  simp [commutator, Subgroup.commutator_def', commutatorSet]

instance commutator_characteristic : (commutator G).Characteristic :=
  Subgroup.commutator_characteristic ⊤ ⊤

instance [Finite (commutatorSet G)] : Group.FG (commutator G) := by
  rw [commutator_eq_closure]
  apply Group.closure_finite_fg

theorem rank_commutator_le_card [Finite (commutatorSet G)] :
    Group.rank (commutator G) ≤ Nat.card (commutatorSet G) := by
  rw [Subgroup.rank_congr (commutator_eq_closure G)]
  apply Subgroup.rank_closure_finite_le_nat_card

theorem commutator_centralizer_commutator_le_center :
    ⁅centralizer (commutator G : Set G), centralizer (commutator G)⁆ ≤ Subgroup.center G := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ←
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  suffices ⁅⁅⊤, centralizer (commutator G : Set G)⁆, centralizer (commutator G : Set G)⁆ = ⊥ by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ this
    rwa [Subgroup.commutator_comm (centralizer (commutator G : Set G))]
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Set.centralizer_subset (Subgroup.commutator_mono le_top le_top)

/-- The abelianization of G is the quotient of G by its commutator subgroup. -/
def Abelianization : Type u :=
  G ⧸ commutator G

namespace Abelianization

attribute [local instance] QuotientGroup.leftRel

instance commGroup : CommGroup (Abelianization G) :=
  { QuotientGroup.Quotient.group _ with
    mul_comm := fun x y =>
      Quotient.inductionOn₂' x y fun a b =>
        Quotient.sound' <|
          QuotientGroup.leftRel_apply.mpr <|
            Subgroup.subset_closure
              ⟨b⁻¹, Subgroup.mem_top b⁻¹, a⁻¹, Subgroup.mem_top a⁻¹, by group⟩ }

instance : Inhabited (Abelianization G) :=
  ⟨1⟩

instance [Unique G] : Unique (Abelianization G) := Quotient.instUniqueQuotient _

instance [Fintype G] [DecidablePred (· ∈ commutator G)] : Fintype (Abelianization G) :=
  QuotientGroup.fintype (commutator G)

instance [Finite G] : Finite (Abelianization G) :=
  Quotient.finite _

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
  left_inv _ := MonoidHom.ext fun _ => rfl
  right_inv _ := MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

@[simp]
theorem lift.of (x : G) : lift f (of x) = f x :=
  rfl

theorem lift.unique (φ : Abelianization G →* A)
    -- hφ : φ agrees with f on the image of G in Gᵃᵇ
    (hφ : ∀ x : G, φ (Abelianization.of x) = f x)
    {x : Abelianization G} : φ x = lift f x :=
  QuotientGroup.induction_on x hφ

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

-- Porting note: `[Group G]` should not be necessary here
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
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨a⟩
      rfl }

section commutatorRepresentatives

open Subgroup

/-- Representatives `(g₁, g₂) : G × G` of commutators `⁅g₁, g₂⁆ ∈ G`. -/
def commutatorRepresentatives : Set (G × G) :=
  Set.range fun g : commutatorSet G => (g.2.choose, g.2.choose_spec.choose)

instance [Finite (commutatorSet G)] : Finite (commutatorRepresentatives G) :=
  Set.finite_coe_iff.mpr (Set.finite_range _)

/-- Subgroup generated by representatives `g₁ g₂ : G` of commutators `⁅g₁, g₂⁆ ∈ G`. -/
def closureCommutatorRepresentatives : Subgroup G :=
  closure (Prod.fst '' commutatorRepresentatives G ∪ Prod.snd '' commutatorRepresentatives G)

instance closureCommutatorRepresentatives_fg [Finite (commutatorSet G)] :
    Group.FG (closureCommutatorRepresentatives G) :=
  Group.closure_finite_fg _

theorem rank_closureCommutatorRepresentatives_le [Finite (commutatorSet G)] :
    Group.rank (closureCommutatorRepresentatives G) ≤ 2 * Nat.card (commutatorSet G) := by
  rw [two_mul]
  exact
    (Subgroup.rank_closure_finite_le_nat_card _).trans
      ((Set.card_union_le _ _).trans
        (add_le_add ((Finite.card_image_le _).trans (Finite.card_range_le _))
          ((Finite.card_image_le _).trans (Finite.card_range_le _))))

theorem image_commutatorSet_closureCommutatorRepresentatives :
    (closureCommutatorRepresentatives G).subtype ''
        commutatorSet (closureCommutatorRepresentatives G) =
      commutatorSet G := by
  apply Set.Subset.antisymm
  · rintro - ⟨-, ⟨g₁, g₂, rfl⟩, rfl⟩
    exact ⟨g₁, g₂, rfl⟩
  · exact fun g hg =>
      ⟨_,
        ⟨⟨_, subset_closure (Or.inl ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩)⟩,
          ⟨_, subset_closure (Or.inr ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩)⟩, rfl⟩,
        hg.choose_spec.choose_spec⟩

theorem card_commutatorSet_closureCommutatorRepresentatives :
    Nat.card (commutatorSet (closureCommutatorRepresentatives G)) = Nat.card (commutatorSet G) := by
  rw [← image_commutatorSet_closureCommutatorRepresentatives G]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

theorem card_commutator_closureCommutatorRepresentatives :
    Nat.card (commutator (closureCommutatorRepresentatives G)) = Nat.card (commutator G) := by
  rw [commutator_eq_closure G, ← image_commutatorSet_closureCommutatorRepresentatives, ←
    MonoidHom.map_closure, ← commutator_eq_closure]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

instance [Finite (commutatorSet G)] :
    Finite (commutatorSet (closureCommutatorRepresentatives G)) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_commutatorSet_closureCommutatorRepresentatives]
  exact Finite.card_pos.ne'

end commutatorRepresentatives
