/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Coinvariants

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

## Main definitions

* `Representation.ind φ ρ` : given a group homomorphism `φ : G →* H`, this is the induction of a
  `G`-representation `(A, ρ)` along `φ`, defined as `(k[H] ⊗[k] A)_G` and with `H`-action given by
  `h • ⟦h₁ ⊗ₜ a⟧ := ⟦h₁h⁻¹ ⊗ₜ a⟧` for `h, h₁ : H`, `a : A`.
* `Rep.indResAdjunction k φ`: given a group homomorphism `φ : G →* H`, this is the adjunction
  between the induction functor along `φ` and the restriction functor `Rep k H ⥤ Rep k G`
  along `φ`.

-/

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
  map_one' := by ext; simp [IndV, IndV.mk]
  map_mul' _ _ := by ext; simp [IndV, IndV.mk, mul_assoc]

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

noncomputable instance : Limits.PreservesColimits (indFunctor k φ) :=
  (indResAdjunction k φ).leftAdjoint_preservesColimits

noncomputable instance : Limits.PreservesLimits (Action.res (ModuleCat.{u} k) φ) :=
  (indResAdjunction k φ).rightAdjoint_preservesLimits

end Adjunction
end Rep
