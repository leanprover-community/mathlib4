/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes, Antoine Chambert-Loir, Osman Safa
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
@[to_additive
/-- The abelianization of the additive group `G` is the quotient of `G` by its commutator
subgroup. -/]
def Abelianization : Type u :=
  G ⧸ commutator G

-- Instantiating the abelianization as a commutative group
open scoped IsMulCommutative in
@[to_additive]
instance : CommGroup (Abelianization G) :=
  inferInstanceAs (CommGroup (G ⧸ commutator G))

/-- `f` exhibits `A` as an additive abelianization of `G`: it is surjective with kernel the
additive commutator subgroup. -/
structure _root_.AddGroup.IsAbelianization {G A : Type*} [AddGroup G] [AddGroup A] (f : G →+ A) :
    Prop where
  surjective : Function.Surjective f
  ker_eq : f.ker = addCommutator G

/-- `f` exhibits `A` as an abelianization of `G`: it is surjective with kernel the
commutator subgroup. -/
@[to_additive existing]
structure IsAbelianization {G : Type u} [Group G] {A : Type v} [Group A] (f : G →* A) : Prop where
  surjective : Function.Surjective f
  ker_eq : f.ker = commutator G

namespace Abelianization

@[to_additive]
instance : Inhabited (Abelianization G) :=
  ⟨1⟩

variable {G}

/-- `of` is the canonical projection from the group `G` to its abelianization. -/
@[to_additive
/-- `of` is the canonical projection from the additive group `G` to its abelianization. -/]
def of : G →* Abelianization G := QuotientGroup.mk' (commutator G)

@[to_additive (attr := simp)]
theorem mk_eq_of (a : G) : Quot.mk _ a = of a :=
  rfl

variable (G) in
@[to_additive (attr := simp)]
theorem ker_of : of.ker = commutator G :=
  QuotientGroup.ker_mk' (commutator G)

variable (G) in
@[to_additive]
lemma surjective_of : Function.Surjective (of : G →* Abelianization G) :=
  QuotientGroup.mk'_surjective (commutator G)

variable (G) in
@[to_additive]
theorem isAbelianization_of : IsAbelianization (of : G →* Abelianization G) where
  surjective := surjective_of _
  ker_eq := ker_of _

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
    Abelianization.lift (Abelianization.of.comp f) = Abelianization.map f :=
  rfl

@[to_additive (attr := simp)]
theorem map_of (x : G) : map f (of x) = of (f x) :=
  rfl

@[to_additive (attr := simp)]
theorem map_comp_of : (map f).comp of = of.comp f :=
  rfl

@[to_additive]
lemma ker_map (f : G →* H) : (map f).ker = ((commutator H).comap f).map of := by
  rw [← ker_of, MonoidHom.comap_ker, ← map_comp_of, ← MonoidHom.comap_ker,
    Subgroup.map_comap_eq_self_of_surjective (surjective_of G)]

@[to_additive]
lemma map_ker_le_ker_map (f : G →* H) : f.ker.map of ≤ (Abelianization.map f).ker := by
  grw [ker_map, Subgroup.ker_le_comap]

@[to_additive]
lemma map_ker_eq_ker_map (f : G →* H) (hf : Function.Surjective f) :
    f.ker.map of = (map f).ker := by
  rw [ker_map, ← map_commutator_of_surjective hf, Subgroup.comap_map_eq, Subgroup.map_sup,
    ← ker_of, Subgroup.map_ker_self, bot_sup_eq]

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

namespace IsAbelianization

-- Let `A` be a group and let `f` be a group homomorphism from `G` to `A`.
variable {G} {A : Type v} [Group A] {f : G →* A}

/-- If `f : G →* A` exhibits `A` as an abelianization of `G`, then `A` is isomorphic to
`Abelianization G`. -/
@[to_additive
/-- If `f : G →+ A` exhibits `A` as an additive abelianization of `G`, then `A` is isomorphic
to `Abelianization G`. -/]
noncomputable def mulEquiv (hf : IsAbelianization f) : Abelianization G ≃* A :=
  QuotientGroup.liftEquiv (commutator G) hf.surjective hf.ker_eq.symm

@[to_additive (attr := simp)]
theorem mulEquiv_of (hf : IsAbelianization f) (x : G) :
    hf.mulEquiv (Abelianization.of x) = f x :=
  rfl

@[to_additive (attr := simp)]
theorem mulEquiv_symm_apply (hf : IsAbelianization f) (x : G) :
    hf.mulEquiv.symm (f x) = Abelianization.of x := by
  rw [MulEquiv.symm_apply_eq, mulEquiv_of]

@[to_additive]
theorem mulEquiv_comp_of (hf : IsAbelianization f) :
    (hf.mulEquiv : Abelianization G →* A).comp Abelianization.of = f :=
  MonoidHom.ext hf.mulEquiv_of

@[to_additive]
theorem isMulCommutative (hf : IsAbelianization f) : IsMulCommutative A :=
  hf.mulEquiv.surjective.isMulCommutative

@[to_additive]
theorem subsingleton_iff (hf : IsAbelianization f) : Subsingleton A ↔ commutator G = ⊤ :=
  hf.mulEquiv.toEquiv.subsingleton_congr.symm.trans QuotientGroup.subsingleton_iff

/-- If `B` is isomorphic to `A` and `A` is an abelianization of `G`, then `B` is an abelianization
of `G` -/
@[to_additive
/-- If `B` is isomorphic to `A` and `A` is an additive abelianization of `G`, then `B` is an
additive abelianization of `G` -/]
theorem mulEquiv_comp {B : Type*} [Group B] (hf : IsAbelianization f) (e : A ≃* B) :
    IsAbelianization ((e : A →* B).comp f) where
  surjective := (e.surjective.comp hf.surjective :)
  ker_eq := (f.ker_comp_of_injective _ e.injective).trans hf.ker_eq

/-- To show that a surjection onto an abelian group is an abelianization, it suffices to show
that its kernel is contained in the commutator subgroup. -/
@[to_additive
/-- To show that a surjection onto an additive abelian group is an additive abelianization, it
suffices to show that its kernel is contained in the additive commutator subgroup. -/]
theorem of_ker_le [IsMulCommutative A] (hs : Function.Surjective f)
    (h : f.ker ≤ commutator G) : IsAbelianization f :=
  ⟨hs, le_antisymm h (Abelianization.commutator_le_ker f)⟩

/-- If `H` is isomorphic to `G` and `A` is an abelianization of `G`, then `A` is an abelianization
of `H`. -/
@[to_additive
/-- If `H` is isomorphic to `G` and `A` is an additive abelianization of `G`, then `A` is an
additive abelianization of `H`. -/]
theorem comp_mulEquiv {H : Type*} [Group H] (hf : IsAbelianization f) (e : H ≃* G) :
    IsAbelianization (f.comp (e : H →* G)) where
  surjective := hf.surjective.comp e.surjective
  ker_eq := by
    rw [← MonoidHom.comap_ker, hf.ker_eq]
    sorry

/-- An abelianization of `G` induces an abelianization of `G ⧸ N`, given by the quotient of `A`
by the image `M` of `N`. -/
@[to_additive
/-- An additive abelianization of `G` induces an additive abelianization of `G ⧸ N`, given by the
quotient of `A` by the image `M` of `N`. -/]
theorem quotient (hf : IsAbelianization f) (N : Subgroup G) [N.Normal]
    (M : Subgroup A) [M.Normal] (h : N ≤ M.comap f) (h' : M ≤ N.map f) :
    IsAbelianization (QuotientGroup.map N M f h) :=
  sorry

@[to_additive]
theorem hom_ext (hf : IsAbelianization f) {M : Type*} [Monoid M] {φ ψ : A →* M}
    (h : φ.comp f = ψ.comp f) : φ = ψ :=
  MonoidHom.ext fun a ↦ by
    obtain ⟨x, rfl⟩ := hf.surjective a
    exact DFunLike.congr_fun h x

section lift

variable {B : Type w} [Group B] [IsMulCommutative B]

/-- If `f : G →* A` is an abelianization, homomorphisms from `G` to an abelian group `B`
correspond to homomorphisms from `A` to `B`. -/
@[to_additive
/-- If `f : G →+ A` is an additive abelianization, homomorphisms from `G` to an additive abelian
group `B` correspond to homomorphisms from `A` to `B`. -/]
noncomputable def lift (hf : IsAbelianization f) : (G →* B) ≃ (A →* B) where
  toFun φ := (Abelianization.lift φ).comp (hf.mulEquiv.symm : A →* Abelianization G)
  invFun ψ := ψ.comp f
  left_inv φ := by ext x; simp
  right_inv ψ := hf.hom_ext <| by ext x; simp

@[to_additive (attr := simp)]
theorem lift_apply_apply (hf : IsAbelianization f) (φ : G →* B) (x : G) :
    hf.lift φ (f x) = φ x := by
  simp [lift]

@[to_additive (attr := simp)]
theorem lift_comp (hf : IsAbelianization f) (φ : G →* B) : (hf.lift φ).comp f = φ :=
  hf.lift.symm_apply_apply φ

@[to_additive (attr := simp)]
theorem lift_symm_apply (hf : IsAbelianization f) (ψ : A →* B) :
    hf.lift.symm ψ = ψ.comp f :=
  rfl

end lift

section map

variable {H : Type*} [Group H] {B : Type*} [Group B] {g : H →* B}

/-- A homomorphism `G →* H` induces a homomorphism between abelianizations `A →* B`. -/
@[to_additive
/-- An additive homomorphism `G →+ H` induces an additive homomorphism between additive
abelianizations `A →+ B`. -/]
noncomputable def map (hf : IsAbelianization f) (hg : IsAbelianization g) (φ : G →* H) :
    A →* B :=
  (hg.mulEquiv : Abelianization H →* B).comp
    ((Abelianization.map φ).comp (hf.mulEquiv.symm : A →* Abelianization G))

@[to_additive (attr := simp)]
theorem map_apply_apply (hf : IsAbelianization f) (hg : IsAbelianization g) (φ : G →* H)
    (x : G) : hf.map hg φ (f x) = g (φ x) := by
  simp [map]

@[to_additive (attr := simp)]
theorem map_id (hf : IsAbelianization f) : hf.map hf (MonoidHom.id G) = MonoidHom.id A :=
  hf.hom_ext <| by ext; simp

@[to_additive (attr := simp)]
theorem map_map {I C : Type*} [Group I] [Group C] {k : I →* C}
    (hf : IsAbelianization f) (hg : IsAbelianization g) (hk : IsAbelianization k)
    (φ : G →* H) (ψ : H →* I) (x : A) :
    hg.map hk ψ (hf.map hg φ x) = hf.map hk (ψ.comp φ) x := by
  obtain ⟨x, rfl⟩ := hf.surjective x
  simp

end map

end IsAbelianization

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

section AdditiveMultiplicativeEquiv

/-- The abelianization of `Multiplicative A` is `Multiplicative` of the additive
abelianization of `A`. -/
def Group.Abelianization.abelianizationEquivMultiplicative (A : Type*) [AddGroup A] :
    Group.Abelianization (Multiplicative A) ≃* Multiplicative (AddGroup.Abelianization A) :=
  (lift AddGroup.Abelianization.of.toMultiplicative).toMulEquiv
    (AddGroup.Abelianization.lift of.toAdditiveRight).toMultiplicativeLeft
    (by ext; simp)
    (by ext; simp)

/-- The additive abelianization of `Additive G` is `Additive` of the abelianization of `G` -/
def AddGroup.Abelianization.abelianizationEquivAdditive (G : Type*) [Group G] :
    AddGroup.Abelianization (Additive G) ≃+ Additive (Group.Abelianization G) :=
  (lift Group.Abelianization.of.toAdditive).toAddEquiv
    (Group.Abelianization.lift of.toMultiplicativeRight).toAdditiveLeft
    (by ext; simp)
    (by ext; simp)

@[simp]
theorem Group.Abelianization.abelianizationEquivMultiplicative_of
    {A : Type*} [AddGroup A] (x : Multiplicative A) :
    abelianizationEquivMultiplicative A (of x) = .ofAdd (.of x.toAdd) :=
  rfl

@[simp]
theorem Group.Abelianization.abelianizationEquivMultiplicative_symm_ofAdd_of
    {A : Type*} [AddGroup A] (a : A) :
    (abelianizationEquivMultiplicative A).symm (.ofAdd (.of a)) = of (.ofAdd a) :=
  rfl

@[simp]
theorem AddGroup.Abelianization.abelianizationEquivAdditive_of
    {G : Type*} [Group G] (a : Additive G) :
    abelianizationEquivAdditive G (of a) = .ofMul (.of a.toMul) :=
  rfl

@[simp]
theorem AddGroup.Abelianization.abelianizationEquivAdditive_symm_ofMul_of
    {G : Type*} [Group G] (x : G) :
    (abelianizationEquivAdditive G).symm (.ofMul (.of x)) = of (.ofMul x) :=
  rfl

@[simp]
theorem isAbelianization_toMultiplicative_iff {A B : Type*} [AddGroup A] [AddGroup B]
    (f : A →+ B) :
    Group.IsAbelianization (AddMonoidHom.toMultiplicative f) ↔ AddGroup.IsAbelianization f := by
  sorry

theorem isAbelianization_toAdditive_iff {G H : Type*} [Group G] [Group H]
    (f : G →* H) :
    AddGroup.IsAbelianization (MonoidHom.toAdditive f) ↔ Group.IsAbelianization f := by
  sorry

end AdditiveMultiplicativeEquiv

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
