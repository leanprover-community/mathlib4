/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jiaxi Mo
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

open scoped MonoidAlgebra

universe t w w' u u' v v'

namespace Representation

open Finsupp

variable {k G H : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H) {A B : Type*}
  [AddCommGroup A] [Module k A] (ρ : Representation k G A)
  [AddCommGroup B] [Module k B] (τ : Representation k G B)

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this is the
`k`-module `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ`.
See `Representation.ind` for the induced `H`-representation on `IndV φ ρ`. -/
abbrev IndV := Coinvariants (V := TensorProduct k k[H] A)
  (Representation.tprod ((leftRegular k H).comp φ) ρ)

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this is the
`H → A →ₗ[k] (k[H] ⊗[k] A)_G` sending `h, a` to `⟦h ⊗ₜ a⟧`. -/
noncomputable def IndV.mk (h : H) : A →ₗ[k] IndV φ ρ :=
  Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (.single h 1)

@[ext 10000]
lemma IndV.hom_ext {f g : IndV φ ρ →ₗ[k] B}
    (hfg : ∀ h : H, f ∘ₗ IndV.mk φ ρ h = g ∘ₗ IndV.mk φ ρ h) : f = g :=
  Coinvariants.hom_ext <| TensorProduct.ext <| MonoidAlgebra.lhom_ext' fun h =>
    LinearMap.ext_ring <| hfg h

variable {φ ρ} in
@[elab_as_elim]
lemma IndV.induction_on {p : IndV φ ρ → Prop} (v : IndV φ ρ) (mk : ∀ h a, p (IndV.mk φ ρ h a))
    (add : ∀ x y : IndV φ ρ, p x → p y → p (x + y)) : p v := by
  refine Representation.Coinvariants.induction_on v ?_
  intro v
  induction v with
  | zero => simpa using mk 1 0
  | tmul m a =>
      refine MonoidAlgebra.induction_linear m ?_ ?_ ?_
      · simpa using mk 1 0
      · intro _ _ hx hy
        rw [TensorProduct.add_tmul, map_add]
        exact add _ _ hx hy
      · intro h r
        rw [← mul_one r, ← MonoidAlgebra.smul_single', TensorProduct.smul_tmul]
        exact mk h (r • a)
  | add _ _ hx hy => simpa [map_add] using add _ _ hx hy

@[simp]
lemma IndV.mk_map_mul (g : G) (h : H) (a : A) :
    IndV.mk φ ρ ((φ g) * h) a = IndV.mk φ ρ h (ρ g⁻¹ a) := by
  simp [IndV.mk]

@[simp]
lemma IndV.mk_map_inv_mul (g : G) (h : H) (a : A) :
    IndV.mk φ ρ ((φ g)⁻¹ * h) a = IndV.mk φ ρ h (ρ g a) := by
  simp [← map_inv]

@[simp]
lemma IndV.mk_map_eq (g : G) (a : A) :
    IndV.mk φ ρ (φ g) a = IndV.mk φ ρ 1 (ρ g⁻¹ a) := by
  simpa using IndV.mk_map_mul φ ρ g 1 a

@[simp]
lemma IndV.mk_map_inv_eq (g : G) (a : A) :
    IndV.mk φ ρ (φ g)⁻¹ a = IndV.mk φ ρ 1 (ρ g a) := by
  simp [← map_inv]

/-- Construct a linear map `IndV φ ρ →ₗ[k] B` from a compatible family of linear maps
`f : H → A →ₗ[k] B`, whose composition with `IndV.mk φ ρ h : A →ₗ[k] IndV φ ρ` is `f h`. -/
noncomputable def IndV.lift (f : H → A →ₗ[k] B)
    (hf : ∀ (g : G) (h : H) (a : A), f (φ g * h) a = f h (ρ g⁻¹ a)) :
    IndV φ ρ →ₗ[k] B :=
  Coinvariants.lift _ (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => f h) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun g => by ext; simp [hf]

@[simp]
lemma IndV.lift_apply_mk (f : H → A →ₗ[k] B) (h : H) (a : A)
    (hf : ∀ (g : G) (h : H) (a : A), f (φ g * h) a = f h (ρ g⁻¹ a)) :
    IndV.lift φ ρ f hf (IndV.mk φ ρ h a) = f h a := by
  simp [IndV.lift, IndV.mk]

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`. -/
noncomputable def ind : Representation k H (IndV φ ρ) where
  toFun h := IndV.lift φ ρ (fun x => IndV.mk φ ρ (x * h⁻¹)) (by simp [mul_assoc])
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

@[simp]
lemma ind_apply_mk (h₁ h₂ : H) (a : A) :
    ind φ ρ h₁ (IndV.mk _ _ h₂ a) = IndV.mk _ _ (h₂ * h₁⁻¹) a := by
  simp [ind]

lemma ind_conj_map_apply (g : G) (h : H) (a : A) :
    ind φ ρ (h⁻¹ * (φ g) * h) (IndV.mk _ _ h a) = IndV.mk _ _ h (ρ g a) := by
  simp

variable {ρ} in
/-- Construct an `IntertwiningMap` starting from an induced representation by lifting an
`IntertwiningMap` with a `res` representation as target. -/
noncomputable abbrev ind.lift {σ : Representation k H B} (f : IntertwiningMap ρ (σ.comp φ)) :
    (ind φ ρ).IntertwiningMap σ :=
  ⟨IndV.lift φ ρ (fun h => σ h⁻¹ ∘ₗ f.toLinearMap) fun _ _ _ => by
    simp [IntertwiningMap.isIntertwining], fun g => by ext; simp⟩

end Representation

namespace Rep

open CategoryTheory Finsupp Representation

variable {k : Type u} {G : Type v} {H : Type v'} [CommRing k] [Group G] [Group H] (φ : G →* H)
  (A : Rep.{w} k G)

section Ind

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`. -/
noncomputable abbrev ind : Rep k H := Rep.of (A.ρ.ind φ)

/-- Given a group homomorphism `φ : G →* H`, a morphism of `G`-representations `f : A ⟶ B` induces
a morphism of `H`-representations `(k[H] ⊗[k] A)_G ⟶ (k[H] ⊗[k] B)_G`. -/
noncomputable abbrev indMap {A B : Rep k G} (f : A ⟶ B) : ind φ A ⟶ ind φ B := Rep.ofHom <|
  ind.lift φ ⟨IndV.mk φ B.ρ 1 ∘ₗ f.hom, fun g => by ext; simp [IntertwiningMap.isIntertwining]⟩

variable (k) in
/-- Given a group homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the induced `H`-representation `ind φ A`, with action on maps induced by left tensoring. -/
@[implicit_reducible, simps obj map]
noncomputable def indFunctor : Rep.{w} k G ⥤ Rep k H where
  obj A := ind φ A
  map f := indMap φ f
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

end Ind
section Adjunction

open Representation

variable (B : Rep k H)

/-- Given a group homomorphism `φ : G →* H`, an `H`-representation `B`, and a `G`-representation
`A`, there is a `k`-linear equivalence between the `H`-representation morphisms `ind φ A ⟶ B` and
the `G`-representation morphisms `A ⟶ B`. -/
@[simps]
noncomputable def indResHomEquiv (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H) :
    (ind φ A ⟶ B) ≃ₗ[k] (A ⟶ res φ B) where
  toFun f := Rep.ofHom ⟨f.hom.toLinearMap ∘ₗ IndV.mk φ A.ρ 1, fun g ↦ by
    ext; simp [← IntertwiningMap.isIntertwining]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom (Representation.ind.lift φ f.hom)
  left_inv f := by ext; simp [← IntertwiningMap.isIntertwining]
  right_inv _ := by ext; simp

variable (k) in
/-- Given a group homomorphism `φ : G →* H`, the induction functor `Rep k G ⥤ Rep k H` is left
adjoint to the restriction functor along `φ`. -/
noncomputable def indResAdjunction : indFunctor k φ ⊣ resFunctor.{max w v' u} φ :=
  Adjunction.mkOfHomEquiv {
    homEquiv A B := (indResHomEquiv φ A B).toEquiv
    homEquiv_naturality_left_symm _ _ := by
      rw [Equiv.symm_apply_eq]
      ext; simp [indResHomEquiv]
    homEquiv_naturality_right _ _ := by ext; simp}

open Finsupp

noncomputable instance : (indFunctor.{max u v' w} k φ).IsLeftAdjoint :=
  (indResAdjunction k φ).isLeftAdjoint

noncomputable instance : (resFunctor.{max u v' w} (k := k) φ).IsRightAdjoint :=
  (indResAdjunction k φ).isRightAdjoint

end Adjunction

section

variable {G H : Type u} [Group G] [Group H] (φ : G →* H) (A : Rep k G) (B : Rep k H)

open Representation

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear map
`(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to `⟦a ⊗ ρ(h)(b)⟧` for all
`h : H`, `a : A`, and `b : B`. -/
noncomputable def coinvariantsTensorIndHom :
    ((coinvariantsTensor k H).obj (ind φ A)).obj B ⟶
      ((coinvariantsTensor k G).obj A).obj (res φ B) :=
  ModuleCat.ofHom <| Coinvariants.lift _ (TensorProduct.lift <| IndV.lift φ A.ρ
    (fun h => (coinvariantsTensorMk A (res φ B)).compl₂ (B.ρ h)) (fun g h a => by
      ext; simp [coinvariantsTensorMk])) (fun h => by
        simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V]
        ext; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {A B} in
lemma coinvariantsTensorIndHom_mk_tmul_indVMk (h : H) (x : A) (y : B) :
    coinvariantsTensorIndHom φ A B (coinvariantsTensorMk _ _ (IndV.mk φ _ h x) y) =
      coinvariantsTensorMk _ _ x (B.ρ h y) := by
  simp [coinvariantsTensorIndHom, coinvariantsTensorMk]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear map
`(A ⊗ Res(φ)(B))_G ⟶ (Ind(φ)(A) ⊗ B))_H` sending `⟦a ⊗ₜ b⟧` to `⟦1 ⊗ₜ a⟧ ⊗ₜ b` for all
`a : A`, and `b : B`. -/
noncomputable def coinvariantsTensorIndInv :
    ((coinvariantsTensor k G).obj A).obj (res φ B) ⟶
      ((coinvariantsTensor k H).obj (ind φ A)).obj B :=
  ModuleCat.ofHom <| Coinvariants.lift _ (TensorProduct.lift <|
    (coinvariantsTensorMk (ind (k := k) φ A) B) ∘ₗ IndV.mk _ _ 1) fun s ↦ by
      simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V]
      ext x y
      simpa [coinvariantsTensorMk, Coinvariants.mk_eq_iff] using Coinvariants.mem_ker_of_eq (φ s)
        ((IndV.mk φ A.ρ (1 : H) x) ⊗ₜ[k] y) _ (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {A B} in
lemma coinvariantsTensorIndInv_mk_tmul_indMk (x : A) (y : B) :
    coinvariantsTensorIndInv φ A B (Coinvariants.mk
      (A.ρ.tprod (Rep.ρ (res φ B))) <| x ⊗ₜ y) =
      coinvariantsTensorMk _ _ (IndV.mk φ _ 1 x) y := by
  simp [coinvariantsTensorIndInv, coinvariantsTensorMk]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear
isomorphism `(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to `⟦a ⊗ ρ(h)(b)⟧`
for all `h : H`, `a : A`, and `b : B`. -/
@[simps]
noncomputable def coinvariantsTensorIndIso :
    ((coinvariantsTensor k H).obj (ind φ A)).obj B ≅
      ((coinvariantsTensor k G).obj A).obj (res φ B) where
  hom := coinvariantsTensorIndHom φ A B
  inv := coinvariantsTensorIndInv φ A B
  hom_inv_id := by
    ext h a b
    simpa [coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom, Coinvariants.mk_eq_iff] using
        Coinvariants.mem_ker_of_eq h (IndV.mk φ _ h a ⊗ₜ[k] b) _ <| by simp
  inv_hom_id := by
    ext
    simp [coinvariantsTensorIndInv, coinvariantsTensorMk, coinvariantsTensorIndHom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H` and `A : Rep k G`, the functor `Rep k H ⥤ ModuleCat k` sending
`B ↦ (Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B ↦ (A ⊗ Res(φ)(B))_G`. -/
@[simps! hom_app inv_app]
noncomputable def coinvariantsTensorIndNatIso :
    (coinvariantsTensor k H).obj (ind φ A) ≅ resFunctor φ ⋙ (coinvariantsTensor k G).obj A :=
  NatIso.ofComponents (fun B => coinvariantsTensorIndIso φ A B) fun {X Y} f => by
    ext
    simp [coinvariantsTensorIndHom, coinvariantsTensorMk, hom_comm_apply]

end
end Rep
