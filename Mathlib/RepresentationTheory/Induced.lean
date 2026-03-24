/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Induced representations

Given a commutative ring `k`, a group homomorphism `φ : G →* H`, and a `k`-linear
`G`-representation `A`, this file introduces the induced representation $Ind_G^H(A)$ of `A` as
an `H`-representation.

By `ind φ A` we mean the `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ`.
We define a representation of `H` on this submodule by sending `h : H` and `⟦h₁ ⊗ₜ a⟧` to
`⟦h₁h⁻¹ ⊗ₜ a⟧`.

We also prove that the restriction functor `Rep k H ⥤ Rep k G` along `φ` is right adjoint to the
induction functor and hence that the induction functor preserves colimits.

Additionally, we show that the functor `Rep k H ⥤ ModuleCat k` sending `B : Rep k H` to
`(Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B` to `(A ⊗ Res(φ)(B))_G`. This
is used to prove Shapiro's lemma in
`Mathlib/RepresentationTheory/Homological/GroupHomology/Shapiro.lean`.

## Main definitions

* `Representation.ind φ ρ` : given a group homomorphism `φ : G →* H`, this is the induction of a
  `G`-representation `(A, ρ)` along `φ`, defined as `(k[H] ⊗[k] A)_G` and with `H`-action given by
  `h • ⟦h₁ ⊗ₜ a⟧ := ⟦h₁h⁻¹ ⊗ₜ a⟧` for `h, h₁ : H`, `a : A`.
* `Rep.indResAdjunction k φ`: given a group homomorphism `φ : G →* H`, this is the adjunction
  between the induction functor along `φ` and the restriction functor `Rep k H ⥤ Rep k G`
  along `φ`.
* `Rep.coinvariantsTensorIndNatIso φ A` : given a group homomorphism `φ : G →* H` and
  `A : Rep k G`, this is a natural isomorphism between the functor sending `B : Rep k H` to
  `(Ind(φ)(A) ⊗ B))_H` and the one sending `B` to `(A ⊗ Res(φ)(B))_G`. Used to prove Shapiro's
  lemma.

-/

@[expose] public section

universe u

namespace Representation

open Finsupp TensorProduct

variable {k G H : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H) {A B : Type*}
  [AddCommGroup A] [Module k A] (ρ : Representation k G A)
  [AddCommGroup B] [Module k B] (τ : Representation k G B)

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this is the
`k`-module `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ`.
See `Representation.ind` for the induced `H`-representation on `IndV φ ρ`. -/
abbrev IndV := Coinvariants (V := TensorProduct k (H →₀ k) A)
  (Representation.tprod ((leftRegular k H).comp φ) ρ)

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this is the
`H → A →ₗ[k] (k[H] ⊗[k] A)_G` sending `h, a` to `⟦h ⊗ₜ a⟧`. -/
noncomputable abbrev IndV.mk (h : H) : A →ₗ[k] IndV φ ρ :=
  Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (single h 1)

@[ext]
lemma IndV.hom_ext {f g : IndV φ ρ →ₗ[k] B}
    (hfg : ∀ h : H, f ∘ₗ IndV.mk φ ρ h = g ∘ₗ IndV.mk φ ρ h) : f = g :=
  Coinvariants.hom_ext <| TensorProduct.ext <| Finsupp.lhom_ext' fun h =>
    LinearMap.ext_ring <| hfg h

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`. -/
@[simps]
noncomputable def ind : Representation k H (IndV φ ρ) where
  toFun h := Coinvariants.map _ _ ((lmapDomain k k fun x => x * h⁻¹).rTensor _)
    fun _ => by ext; simp [mul_assoc]
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [IndV, mul_assoc]

lemma ind_mk (h₁ h₂ : H) (a : A) :
    ind φ ρ h₁ (IndV.mk _ _ h₂ a) = IndV.mk _ _ (h₂ * h₁⁻¹) a := by
  simp

end Representation

namespace Rep

open CategoryTheory Finsupp

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H) (A : Rep k G)

section Ind

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`. -/
noncomputable abbrev ind : Rep k H := Rep.of (A.ρ.ind φ)

/-- Given a group homomorphism `φ : G →* H`, a morphism of `G`-representations `f : A ⟶ B` induces
a morphism of `H`-representations `(k[H] ⊗[k] A)_G ⟶ (k[H] ⊗[k] B)_G`. -/
@[simps]
noncomputable def indMap {A B : Rep k G} (f : A ⟶ B) : ind φ A ⟶ ind φ B where
  hom := ModuleCat.ofHom <| Representation.Coinvariants.map _ _
    (LinearMap.lTensor (H →₀ k) f.hom.hom) fun g => by ext; simp [hom_comm_apply]
  comm _ := by
    ext
    simp [ModuleCat.endRingEquiv]

variable (k) in
/-- Given a group homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the induced `H`-representation `ind φ A`, with action on maps induced by left tensoring. -/
@[simps obj map]
noncomputable def indFunctor : Rep k G ⥤ Rep k H where
  obj A := ind φ A
  map f := indMap φ f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

end Ind
section Adjunction

open Representation

variable (B : Rep k H)

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `φ : G →* H`, an `H`-representation `B`, and a `G`-representation
`A`, there is a `k`-linear equivalence between the `H`-representation morphisms `ind φ A ⟶ B` and
the `G`-representation morphisms `A ⟶ B`. -/
@[simps]
noncomputable def indResHomEquiv :
    (ind φ A ⟶ B) ≃ₗ[k] (A ⟶ (Action.res _ φ).obj B) where
  toFun f := {
    hom := ModuleCat.ofHom (f.hom.hom ∘ₗ IndV.mk φ A.ρ 1)
    comm g := by
      ext x
      have := (hom_comm_apply f (φ g) (IndV.mk φ A.ρ 1 x)).symm
      simp_all [← Coinvariants.mk_inv_tmul] }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := {
    hom := ModuleCat.ofHom <| Representation.Coinvariants.lift _ (TensorProduct.lift <|
      lift _ _ _ fun h => B.ρ h⁻¹ ∘ₗ f.hom.hom) fun _ => by ext; have := hom_comm_apply f; simp_all
    comm _ := by ext; simp [ModuleCat.endRingEquiv] }
  left_inv f := by
    ext h a
    simpa using (hom_comm_apply f h⁻¹ (IndV.mk φ A.ρ 1 a)).symm
  right_inv _ := by ext; simp

set_option backward.isDefEq.respectTransparency false in
variable (k) in
/-- Given a group homomorphism `φ : G →* H`, the induction functor `Rep k G ⥤ Rep k H` is left
adjoint to the restriction functor along `φ`. -/
@[simps! unit_app_hom_hom counit_app_hom_hom]
noncomputable def indResAdjunction : indFunctor k φ ⊣ Action.res _ φ :=
  Adjunction.mkOfHomEquiv {
    homEquiv A B := (indResHomEquiv φ A B).toEquiv
    homEquiv_naturality_left_symm _ _ :=
      Action.hom_ext _ _ <| ModuleCat.hom_ext <| IndV.hom_ext _ _ fun _ => by ext; simp
    homEquiv_naturality_right := by intros; rfl }

open Finsupp

noncomputable instance : (indFunctor k φ).IsLeftAdjoint :=
  (indResAdjunction k φ).isLeftAdjoint

noncomputable instance : (Action.res (ModuleCat.{u} k) φ).IsRightAdjoint :=
  (indResAdjunction k φ).isRightAdjoint

end Adjunction

section

variable (B : Rep k H)

open ModuleCat.MonoidalCategory Representation

set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear map
`(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to `⟦a ⊗ ρ(h)(b)⟧` for all
`h : H`, `a : A`, and `b : B`. -/
noncomputable def coinvariantsTensorIndHom :
    ((coinvariantsTensor k H).obj (ind φ A)).obj B ⟶
      ((coinvariantsTensor k G).obj A).obj ((Action.res _ φ).obj B) :=
  ModuleCat.ofHom <| Coinvariants.lift _ (TensorProduct.lift <|
    Coinvariants.lift _ (TensorProduct.lift <| Finsupp.lift _ _ _
      fun g => ((coinvariantsTensorMk A ((Action.res _ φ).obj B)).compl₂ (B.ρ g)))
      fun s => by ext; simpa [coinvariantsTensorMk, Coinvariants.mk_eq_iff]
        using Coinvariants.sub_mem_ker s _)
      fun _ => by
        simp only [MonoidalCategory.curriedTensor_obj_obj, Action.tensorObj_V, tensorObj_carrier]
        ext
        simp

set_option backward.isDefEq.respectTransparency false in
variable {A B} in
lemma coinvariantsTensorIndHom_mk_tmul_indVMk (h : H) (x : A) (y : B) :
    coinvariantsTensorIndHom φ A B (coinvariantsTensorMk _ _ (IndV.mk φ _ h x) y) =
      coinvariantsTensorMk _ _ x (B.ρ h y) := by
  simp [tensorObj_carrier, coinvariantsTensorIndHom, coinvariantsTensorMk]

set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear map
`(A ⊗ Res(φ)(B))_G ⟶ (Ind(φ)(A) ⊗ B))_H` sending `⟦a ⊗ₜ b⟧` to `⟦1 ⊗ₜ a⟧ ⊗ₜ b` for all
`a : A`, and `b : B`. -/
noncomputable def coinvariantsTensorIndInv :
    ((coinvariantsTensor k G).obj A).obj ((Action.res _ φ).obj B) ⟶
      ((coinvariantsTensor k H).obj (ind φ A)).obj B :=
  ModuleCat.ofHom <| Coinvariants.lift _ (TensorProduct.lift <|
      (coinvariantsTensorMk (ind φ A) B) ∘ₗ IndV.mk _ _ 1)
    fun s => by
      simp only [MonoidalCategory.curriedTensor_obj_obj, tensorObj_carrier, Action.tensorObj_V]
      ext x y
      simpa [Coinvariants.mk_eq_iff, coinvariantsTensorMk] using
        Coinvariants.mem_ker_of_eq (φ s) (IndV.mk φ A.ρ (1 : H) x ⊗ₜ[k] y) _
        (by simp [← Coinvariants.mk_inv_tmul])

set_option backward.isDefEq.respectTransparency false in
variable {A B} in
lemma coinvariantsTensorIndInv_mk_tmul_indMk (x : A) (y : B) :
    coinvariantsTensorIndInv φ A B (Coinvariants.mk
      (A.ρ.tprod (Rep.ρ ((Action.res _ φ).obj B))) <| x ⊗ₜ y) =
      coinvariantsTensorMk _ _ (IndV.mk φ _ 1 x) y := by
  simp [tensorObj_carrier, coinvariantsTensorIndInv, coinvariantsTensorMk]

set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear
isomorphism `(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to `⟦a ⊗ ρ(h)(b)⟧`
for all `h : H`, `a : A`, and `b : B`. -/
@[simps]
noncomputable def coinvariantsTensorIndIso :
    ((coinvariantsTensor k H).obj (ind φ A)).obj B ≅
      ((coinvariantsTensor k G).obj A).obj ((Action.res _ φ).obj B) where
  hom := coinvariantsTensorIndHom φ A B
  inv := coinvariantsTensorIndInv φ A B
  hom_inv_id := by
    ext h a b
    simpa [tensorObj_carrier, coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom, Coinvariants.mk_eq_iff] using
        Coinvariants.mem_ker_of_eq h (IndV.mk φ _ h a ⊗ₜ[k] b) _ <| by simp
  inv_hom_id := by
    ext
    simp [tensorObj_carrier, coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom]

set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H` and `A : Rep k G`, the functor `Rep k H ⥤ ModuleCat k` sending
`B ↦ (Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B ↦ (A ⊗ Res(φ)(B))_G`. -/
@[simps! hom_app inv_app]
noncomputable def coinvariantsTensorIndNatIso :
    (coinvariantsTensor k H).obj (ind φ A) ≅ Action.res _ φ ⋙ (coinvariantsTensor k G).obj A :=
  NatIso.ofComponents (fun B => coinvariantsTensorIndIso φ A B) fun {X Y} f => by
    ext
    simp [tensorObj_carrier, coinvariantsTensorIndHom, coinvariantsTensorMk,
      whiskerLeft_def, hom_comm_apply]

end
end Rep
