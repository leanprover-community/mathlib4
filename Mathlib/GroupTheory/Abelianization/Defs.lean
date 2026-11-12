/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes, Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The abelianization of a group

This file defines the commutator and the abelianization of a group. It furthermore prepares for the
result that the abelianization is left adjoint to the forgetful functor from abelian groups to
groups, which can be found in `Mathlib/Algebra/Category/Grp/Adjunctions.lean`.

## Main definitions

* `Group.Abelianization`: defines the abelianization of a group `G` as the quotient of a group by
  its commutator subgroup.
* `Group.Abelianization.map`: lifts a group homomorphism to a homomorphism between the
  abelianizations.
* `Group.Abelianization.quotientMulEquiv`: The abelianization of a quotient `G ⧸ N` is isomorphic
  to the quotient of the abelianization of `G` by the image of `N`.
* `MulEquiv.abelianizationCongr`: Isomorphic groups have isomorphic abelianizations.
-/

@[expose] public section

assert_not_exists Cardinal Field

universe u v w

-- Let G be a group.
variable (G : Type u) [Group G]

open Subgroup (centralizer)

namespace Group

/-- The abelianization of the group `G` is the quotient of `G` by its commutator subgroup. -/
@[to_additive /-- The abelianization of the additive group `G` is the quotient of `G` by its
commutator subgroup. -/]
def Abelianization : Type u :=
  G ⧸ commutator G

-- Instantiating the abelianization as a commutative group
open scoped IsMulCommutative in
@[to_additive]
instance : CommGroup (Abelianization G) :=
  inferInstanceAs (CommGroup (G ⧸ commutator G))

namespace Abelianization

@[to_additive]
instance : Inhabited (Abelianization G) :=
  ⟨1⟩

variable {G}

/-- `of` is the canonical projection from the group `G` to its abelianization. -/
@[to_additive
/-- `of` is the canonical projection from the additive group `G` to its abelianization. -/]
def of : G →* Abelianization G where
  toFun := QuotientGroup.mk
  map_one' := rfl
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
theorem mk_eq_of (a : G) : Quot.mk _ a = of a :=
  rfl

variable (G) in
@[to_additive (attr := simp)]
theorem ker_of : of.ker = commutator G :=
  QuotientGroup.ker_mk' (commutator G)

section lift

-- So far we have built `Gᵃᵇ` and proved it's an abelian group.
-- Furthermore we defined the canonical projection `of : G → Gᵃᵇ`
-- Let `A` be an abelian group and let `f` be a group homomorphism from `G` to `A`.
variable {A : Type v} [Group A] [IsMulCommutative A] (f : G →* A)

@[to_additive]
theorem commutator_le_ker : commutator G ≤ f.ker := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro x ⟨p, q, rfl⟩
  simp [MonoidHom.mem_ker, mul_comm' (f p) (f q), commutatorElement_def]

/-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map
from the abelianization of `G` to `A` that factors through `f`. -/
@[to_additive
/-- If `f : G → A` is an additive group homomorphism to an abelian group, then `lift f` is the
unique map from the abelianization of `G` to `A` that factors through `f`. -/]
def lift : (G →* A) ≃ (Abelianization G →* A) where
  toFun f := QuotientGroup.lift _ f fun _ h => MonoidHom.mem_ker.2 <| commutator_le_ker _ h
  invFun F := F.comp of
  right_inv _ := MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

@[to_additive (attr := simp)]
theorem lift_apply_of (x : G) : lift f (of x) = f x :=
  rfl
@[to_additive]
theorem coe_lift_symm : (lift.symm : (Abelianization G →* A) → (G →* A)) = (·.comp of) := rfl

@[to_additive (attr := simp)]
theorem lift_symm_apply (f : Abelianization G →* A) : lift.symm f = f.comp of := rfl

@[to_additive]
theorem lift_unique (φ : Abelianization G →* A)
    -- `hφ : φ` agrees with `f` on the image of `G` in `Gᵃᵇ`
    (hφ : ∀ x : G, φ (Abelianization.of x) = f x)
    {x : Abelianization G} : φ x = lift f x :=
  QuotientGroup.induction_on x hφ

@[to_additive (attr := simp)]
theorem lift_of : lift of = MonoidHom.id (Abelianization G) :=
  lift.apply_symm_apply <| MonoidHom.id _

end lift

variable {A : Type v} [Monoid A]

-- See note [partially-applied ext lemmas].
@[to_additive (attr := ext)]
theorem hom_ext (φ ψ : Abelianization G →* A) (h : φ.comp of = ψ.comp of) : φ = ψ :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x <| DFunLike.congr_fun h

section Map

variable {H : Type v} [Group H] (f : G →* H)

/-- The map operation of the `Abelianization` functor. -/
@[to_additive /-- The map operation of the `Abelianization` functor. -/]
def map : Abelianization G →* Abelianization H :=
  lift (of.comp f)

/-- Use `map` as the preferred simp normal form. -/
@[to_additive (attr := simp) /-- Use `map` as the preferred simp normal form. -/]
theorem lift_of_comp :
    Abelianization.lift (Abelianization.of.comp f) = Abelianization.map f := rfl

@[to_additive (attr := simp)]
theorem map_of (x : G) : map f (of x) = of (f x) :=
  rfl

@[to_additive]
lemma map_ker_le_ker_map (f : G →* H) : f.ker.map of ≤ (Abelianization.map f).ker := by
  rintro _ ⟨x, hx, rfl⟩
  simp_all [MonoidHom.mem_ker]

@[to_additive]
lemma map_ker_eq_ker_map (f : G →* H) (hf : Function.Surjective f) :
    f.ker.map of = (Abelianization.map f).ker :=
  le_antisymm (map_ker_le_ker_map f) fun y h ↦ by
    obtain ⟨x, rfl⟩ : ∃ x, of x = y := QuotientGroup.mk_surjective y
    rw [MonoidHom.mem_ker, map_of, ← MonoidHom.mem_ker, ker_of,
      ← map_commutator_of_surjective hf] at h
    obtain ⟨c, hc, hfc⟩ := h
    have hc' : of c = 1 := by rwa [← MonoidHom.mem_ker, ker_of]
    exact ⟨x * c⁻¹, by simp [hfc], by simp [hc']⟩

@[to_additive (attr := simp)]
theorem map_id : map (MonoidHom.id G) = MonoidHom.id (Abelianization G) :=
  hom_ext _ _ rfl

@[to_additive (attr := simp)]
theorem map_comp {I : Type w} [Group I] (g : H →* I) : (map g).comp (map f) = map (g.comp f) :=
  hom_ext _ _ rfl

@[to_additive (attr := simp)]
theorem map_map_apply {I : Type w} [Group I] {g : H →* I} {x : Abelianization G} :
    map g (map f x) = map (g.comp f) x :=
  congr($(map_comp _ _) x)

end Map

section Quotient

variable (N : Subgroup G) [N.Normal]

/-- Abelianizing a quotient `G ⧸ N` is the same as abelianizing `G`
and then quotienting by the image of `N`. -/
@[to_additive
/-- Abelianizing a quotient `G ⧸ N` is the same as abelianizing `G`
and then quotienting by the image of `N`. -/]
def quotientMulEquiv : Abelianization (G ⧸ N) ≃* Abelianization G ⧸ N.map of :=
 MonoidHom.toMulEquiv
    (lift <| QuotientGroup.lift N ((QuotientGroup.mk' _).comp of) <|
      by simp [← MonoidHom.comap_ker, Subgroup.le_comap_map])
    (QuotientGroup.lift _ (map (QuotientGroup.mk' N)) <|
      by simpa using map_ker_le_ker_map (QuotientGroup.mk' N))
    (by ext; simp)
    (by ext; simp)

@[to_additive (attr := simp)]
theorem quotientMulEquiv_of_mk (x : G) :
    quotientMulEquiv N (of (x : G ⧸ N)) = (of x : Abelianization G ⧸ N.map of) :=
  rfl

@[to_additive (attr := simp)]
theorem quotientMulEquiv_symm_mk (x : Abelianization G) :
    (quotientMulEquiv N).symm x = map (QuotientGroup.mk' N) x :=
  rfl

end Quotient

end Abelianization

section AbelianizationCongr

variable {G} {H : Type v} [Group H]

/-- Isomorphic groups have isomorphic abelianizations. -/
@[to_additive /-- Isomorphic additive groups have isomorphic abelianizations. -/]
def _root_.MulEquiv.abelianizationCongr (e : G ≃* H) : Abelianization G ≃* Abelianization H where
  toFun := Abelianization.map e.toMonoidHom
  invFun := Abelianization.map e.symm.toMonoidHom
  left_inv := by
    rintro ⟨a⟩
    simp
  right_inv := by
    rintro ⟨a⟩
    simp
  map_mul' := map_mul _

@[to_additive (attr := simp)]
theorem abelianizationCongr_of (e : G ≃* H) (x : G) :
    e.abelianizationCongr (Abelianization.of x) = Abelianization.of (e x) :=
  rfl

@[to_additive (attr := simp)]
theorem abelianizationCongr_refl :
    (MulEquiv.refl G).abelianizationCongr = MulEquiv.refl (Abelianization G) :=
  MulEquiv.toMonoidHom_injective Abelianization.lift_of

@[to_additive (attr := simp)]
theorem abelianizationCongr_symm (e : G ≃* H) :
    e.abelianizationCongr.symm = e.symm.abelianizationCongr :=
  rfl

@[to_additive (attr := simp)]
theorem abelianizationCongr_trans {I : Type v} [Group I] (e : G ≃* H) (e₂ : H ≃* I) :
    e.abelianizationCongr.trans e₂.abelianizationCongr = (e.trans e₂).abelianizationCongr :=
  MulEquiv.toMonoidHom_injective (Abelianization.hom_ext _ _ rfl)

end AbelianizationCongr

/-- An Abelian group is equivalent to its own abelianization. -/
@[to_additive (attr := simps)
/-- An additive Abelian group is equivalent to its own abelianization. -/]
def Abelianization.equivOfComm {H : Type*} [CommGroup H] : H ≃* Abelianization H :=
  { Abelianization.of with
    toFun := Abelianization.of
    invFun := Abelianization.lift (MonoidHom.id H)
    right_inv := by
      rintro ⟨a⟩
      rfl }

@[to_additive]
instance [Unique G] :
  Unique (Abelianization G) := Quotient.instUniqueQuotient _

end Group

@[deprecated (since := "2026-11-03")] alias Abelianization := Group.Abelianization
@[deprecated (since := "2026-11-03")]
alias Abelianization.instInhabited := Group.Abelianization.instInhabited
@[deprecated (since := "2026-11-03")] alias Abelianization.of := Group.Abelianization.of
@[deprecated (since := "2026-11-03")] alias Abelianization.mk_eq_of := Group.Abelianization.mk_eq_of
@[deprecated (since := "2026-11-03")] alias Abelianization.ker_of := Group.Abelianization.ker_of
@[deprecated (since := "2026-11-03")]
alias Abelianization.commutator_le_ker := Group.Abelianization.commutator_le_ker
@[deprecated (since := "2026-11-03")]
alias Abelianization.addCommutator_le_ker := AddGroup.Abelianization.addCommutator_le_ker
@[deprecated (since := "2026-10-17")]
alias Abelianization.commutator_subset_ker := Group.Abelianization.commutator_le_ker
@[deprecated (since := "2026-11-03")] alias Abelianization.lift := Group.Abelianization.lift
@[deprecated (since := "2026-11-03")]
alias Abelianization.lift_apply_of := Group.Abelianization.lift_apply_of
@[deprecated (since := "2026-11-03")]
alias Abelianization.coe_lift_symm := Group.Abelianization.coe_lift_symm
@[deprecated (since := "2026-11-03")]
alias Abelianization.lift_symm_apply := Group.Abelianization.lift_symm_apply
@[deprecated (since := "2026-11-03")]
alias Abelianization.lift_unique := Group.Abelianization.lift_unique
@[deprecated (since := "2026-11-03")] alias Abelianization.lift_of := Group.Abelianization.lift_of
@[deprecated (since := "2026-11-03")] alias Abelianization.hom_ext := Group.Abelianization.hom_ext
@[deprecated (since := "2026-11-03")]
alias Abelianization.hom_ext_iff := Group.Abelianization.hom_ext_iff
@[deprecated (since := "2026-11-03")] alias Abelianization.map := Group.Abelianization.map
@[deprecated (since := "2026-11-03")]
alias Abelianization.lift_of_comp := Group.Abelianization.lift_of_comp
@[deprecated (since := "2026-11-03")] alias Abelianization.map_of := Group.Abelianization.map_of
@[deprecated (since := "2026-11-03")] alias Abelianization.map_id := Group.Abelianization.map_id
@[deprecated (since := "2026-11-03")] alias Abelianization.map_comp := Group.Abelianization.map_comp
@[deprecated (since := "2026-11-03")]
alias Abelianization.map_map_apply := Group.Abelianization.map_map_apply
@[deprecated (since := "2026-11-03")] alias abelianizationCongr_of := Group.abelianizationCongr_of
@[deprecated (since := "2026-11-03")]
alias abelianizationCongr_refl := Group.abelianizationCongr_refl
@[deprecated (since := "2026-11-03")]
alias abelianizationCongr_symm := Group.abelianizationCongr_symm
@[deprecated (since := "2026-11-03")]
alias abelianizationCongr_trans := Group.abelianizationCongr_trans
@[deprecated (since := "2026-11-03")]
alias Abelianization.equivOfComm := Group.Abelianization.equivOfComm
@[deprecated (since := "2026-11-03")]
alias Abelianization.equivOfComm_apply := Group.Abelianization.equivOfComm_apply
@[deprecated (since := "2026-11-03")]
alias Abelianization.equivOfComm_symm_apply := Group.Abelianization.equivOfComm_symm_apply
