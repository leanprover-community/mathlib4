/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Rep

/-!
# Coinvariants a group representation

Given a commutative ring `k` and a monoid `G`, this file introduces the coinvariants of a
`k`-linear `G`-representation `(V, ρ)`.

We first define `Representation.augmentationSubmodule`, the submodule of `V` generated by elements
of the form `ρ g x - x` for `x : V`, `g : G`. Then the coinvariants of `(V, ρ)` are the quotient of
`V` by this submodule.

## Main definitions

* `Representation.coinvariants ρ`: the coinvariants of a representation `ρ`.
* `Representation.coinvariantsFinsuppLEquiv ρ α`: given a type `α`, this is the `k`-linear
  equivalence between `(α →₀ V)_G` and `α →₀ V_G`.
* `Representation.coinvariantsTprodLeftRegularLEquiv ρ`: the `k`-linear equivalence between
  `(V ⊗ k[G])_G` and `V` sending `⟦v ⊗ single g r⟧ ↦ r • ρ(g⁻¹)(v)`.
* `Rep.coinvariantsAdjunction k G`: the adjunction between the functor sending a representation to
  its coinvariants and the functor equipping a module with the trivial representation.
* `Rep.coinvariantsTensor k G`: the functor sending representations `A, B` to `(A ⊗[k] B)_G`. This
  is naturally isomorphic to the functor sending `A, B` to `A ⊗[k[G]] B`, where we give `A` the
  `k[G]ᵐᵒᵖ`-module structure defined by `g • a := A.ρ g⁻¹ a`.
* `Rep.coinvariantsTensorFreeLEquiv A α`: given a representation `A` and a type `α`, this is the
  `k`-linear equivalence between `(A ⊗ (α →₀ k[G]))_G` and `α →₀ A` sending
  `⟦a ⊗ single x (single g r)⟧ ↦ single x (r • ρ(g⁻¹)(a))`. This is useful for group homology.

-/

universe u v

namespace Representation

section

variable {k G V W : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] (ρ : Representation k G V)

/-- The submodule of a representation generated by elements of the form `ρ g x - x`. -/
abbrev augmentationSubmodule : Submodule k V :=
  Submodule.span k (Set.range fun (x : G × V) => ρ x.1 x.2 - x.2)

variable {ρ}

lemma mem_augmentationSubmodule_of_eq (g : G) (x : V) (a : V) (h : ρ g x - x = a) :
    a ∈ augmentationSubmodule ρ :=
  Submodule.subset_span ⟨(g, x), h⟩

variable (ρ)

@[simp]
theorem augmentationSubmodule_eq_bot_of_isTrivial [ρ.IsTrivial] :
    augmentationSubmodule ρ = ⊥ := by
  rw [Submodule.span_eq_bot]
  rintro x ⟨⟨g, y⟩, rfl⟩
  simp

/-- The coinvariants of a representation, `V ⧸ ⟨{ρ g x - x | g ∈ G, x ∈ V}⟩`. -/
abbrev coinvariants := V ⧸ augmentationSubmodule ρ

/-- The quotient map from a representation to its coinvariants as a linear map. -/
abbrev coinvariantsMkQ := Submodule.mkQ (augmentationSubmodule ρ)

/-- A `G`-invariant linear map induces a linear map out of the coinvariants of a
`G`-representation. -/
def coinvariantsLift (f : V →ₗ[k] W) (h : ∀ (x : G), f ∘ₗ ρ x = f) :
    ρ.coinvariants →ₗ[k] W :=
  Submodule.liftQ _ f <| Submodule.span_le.2 fun x ⟨⟨g, y⟩, hy⟩ => by
    simpa only [← hy, SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, LinearMap.coe_comp,
      Function.comp_apply] using LinearMap.ext_iff.1 (h g) y

@[simp]
theorem coinvariantsLift_comp_mkQ (f : V →ₗ[k] W) (h : ∀ (x : G), f ∘ₗ ρ x = f) :
  coinvariantsLift ρ f h ∘ₗ (augmentationSubmodule ρ).mkQ = f := rfl

@[simp]
theorem coinvariantsLift_mk (f : V →ₗ[k] W) (h : ∀ (x : G), f ∘ₗ ρ x = f) (x : V) :
  coinvariantsLift ρ f h (Submodule.Quotient.mk x) = f x := rfl

end
section Finsupp

open Finsupp

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (α : Type*)

/-- Given a `G`-representation `(V, ρ)` and a type `α`, this is the map `(α →₀ V)_G →ₗ (α →₀ V_G)`
sending `⟦single a v⟧ ↦ single a ⟦v⟧`. -/
noncomputable def coinvariantsToFinsupp :
    coinvariants (ρ.finsupp α) →ₗ[k] α →₀ coinvariants ρ :=
  coinvariantsLift _ (mapRange.linearMap (Submodule.mkQ _)) <| fun g => lhom_ext fun _ x => by
    simp [mapRange.linearMap, ← (Submodule.Quotient.eq _).2
      (mem_augmentationSubmodule_of_eq g x _ rfl), finsupp]

@[simp]
lemma coinvariantsToFinsupp_mk_single (x : α) (a : V) :
    coinvariantsToFinsupp ρ α (Submodule.Quotient.mk (single x a)) =
      single x (Submodule.Quotient.mk a) := by simp [coinvariantsToFinsupp]

/-- Given a `G`-representation `(V, ρ)` and a type `α`, this is the map `(α →₀ V_G) →ₗ (α →₀ V)_G`
sending `single a ⟦v⟧ ↦ ⟦single a v⟧`. -/
noncomputable def finsuppToCoinvariants :
    (α →₀ coinvariants ρ) →ₗ[k] coinvariants (ρ.finsupp α) :=
  lsum (R := k) k fun a => coinvariantsLift _ (Submodule.mkQ _ ∘ₗ lsingle a) fun g =>
    LinearMap.ext fun x => (Submodule.Quotient.eq _).2 <|
    mem_augmentationSubmodule_of_eq g (single a x) _ <| by simp

@[simp]
lemma finsuppToCoinvariants_single_mk (a : α) (x : V) :
    finsuppToCoinvariants ρ α (single a <| Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (single a x) := by simp [finsuppToCoinvariants]

/-- Given a `G`-representation `(V, ρ)` and a type `α`, this is the linear equivalence
`(α →₀ V)_G ≃ₗ (α →₀ V_G)` sending `⟦single a v⟧ ↦ single a ⟦v⟧`. -/
noncomputable abbrev coinvariantsFinsuppLEquiv :
    coinvariants (ρ.finsupp α) ≃ₗ[k] α →₀ coinvariants ρ :=
  LinearEquiv.ofLinear (coinvariantsToFinsupp ρ α) (finsuppToCoinvariants ρ α)
    (lhom_ext fun _ x => Quotient.inductionOn' x fun _ => by
      simp [coinvariantsToFinsupp, finsuppToCoinvariants, Submodule.Quotient.mk''_eq_mk])
    (Submodule.linearMap_qext _ <| lhom_ext fun _ _ => by
      simp [finsuppToCoinvariants, coinvariantsToFinsupp])

end Finsupp

section TensorProduct

open TensorProduct

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] (ρ : Representation k G V)

@[simp]
lemma coinvariants_mk_inv_tmul (τ : Representation k G W) (x : V) (y : W) (g : G) :
    Submodule.Quotient.mk (p := (ρ.tprod τ).augmentationSubmodule) (ρ g⁻¹ x ⊗ₜ[k] y) =
      Submodule.Quotient.mk (p := (ρ.tprod τ).augmentationSubmodule) (x ⊗ₜ[k] τ g y) :=
  (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq g⁻¹ (x ⊗ₜ[k] τ g y) _ <| by simp

@[simp]
lemma coinvariants_mk_tmul_inv (τ : Representation k G W) (x : V) (y : W) (g : G) :
    Submodule.Quotient.mk (p := (ρ.tprod τ).augmentationSubmodule) (x ⊗ₜ[k] τ g⁻¹ y) =
      Submodule.Quotient.mk (p := (ρ.tprod τ).augmentationSubmodule) (ρ g x ⊗ₜ[k] y) :=
  (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq g⁻¹ (ρ g x ⊗ₜ[k] y) _ <| by simp

/-- Given a `k`-linear `G`-representation `V, ρ`, this is the map `(V ⊗ k[G])_G →ₗ[k] V` sending
`⟦v ⊗ single g r⟧ ↦ r • ρ(g⁻¹)(v)`. -/
noncomputable def ofCoinvariantsTprodLeftRegular :
    coinvariants (V := V ⊗[k] (G →₀ k)) (ρ.tprod (leftRegular k G)) →ₗ[k] V :=
  coinvariantsLift _ (TensorProduct.lift (Finsupp.linearCombination _ fun g => ρ g⁻¹) ∘ₗ
    (TensorProduct.comm _ _ _).toLinearMap) fun _ => TensorProduct.ext <|
      LinearMap.ext fun _ => Finsupp.lhom_ext fun _ _ => by simp

@[simp]
lemma ofCoinvariantsTprodLeftRegular_mk_tmul_single (x : V) (g : G) (r : k) :
    ofCoinvariantsTprodLeftRegular ρ (Submodule.Quotient.mk (x ⊗ₜ Finsupp.single g r)) =
      r • ρ g⁻¹ x :=
  congr($(Finsupp.linearCombination_single k (v := fun g => ρ g⁻¹) r g) x)

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the linear equivalence
`(V ⊗ k[G])_G ≃ₗ[k] V` sending `⟦v ⊗ single g r⟧ ↦ r • ρ(g⁻¹)(v)`. -/
noncomputable abbrev coinvariantsTprodLeftRegularLEquiv :
    coinvariants (V := V ⊗[k] (G →₀ k)) (ρ.tprod (leftRegular k G)) ≃ₗ[k] V :=
  LinearEquiv.ofLinear (ofCoinvariantsTprodLeftRegular ρ)
    (Submodule.mkQ _ ∘ₗ (mk k V (G →₀ k)).flip (Finsupp.single 1 1)) (by ext; simp) <|
    Submodule.linearMap_qext _ <| TensorProduct.ext <| LinearMap.ext fun a =>
      Finsupp.lhom_ext fun g r => (Submodule.Quotient.eq _).2 <| by
        apply mem_augmentationSubmodule_of_eq g⁻¹ (a ⊗ₜ Finsupp.single g r)
        simp_all [TensorProduct.smul_tmul', TensorProduct.smul_tmul]

end TensorProduct

end Representation

namespace Rep

open CategoryTheory

section

variable {k G : Type u} [CommRing k] [Monoid G] {A B C : Rep k G} {n : ℕ}

open Representation

/-- The linear map underlying a `G`-representation morphism `A ⟶ B`, where `B` has the trivial
representation, factors through `A_G`. -/
noncomputable abbrev coinvariantsLift [B.ρ.IsTrivial] (f : A ⟶ B) :
    coinvariants A.ρ →ₗ[k] B :=
  Representation.coinvariantsLift _ f.hom.hom fun _ => by
    ext
    have := hom_comm_apply f
    simp_all

/-- A `G`-representation morphism `A ⟶ B` induces a linear map `A_G →ₗ[k] B_G`. -/
noncomputable abbrev coinvariantsMap (f : A ⟶ B) :
    coinvariants A.ρ →ₗ[k] coinvariants B.ρ :=
  Representation.coinvariantsLift _ (Submodule.mkQ _ ∘ₗ f.hom.hom) fun g => LinearMap.ext fun x =>
    (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq g (f.hom x) _ <| by
      simpa using (hom_comm_apply f g x).symm

@[simp]
theorem coinvariantsMap_comp_mkQ (f : A ⟶ B) :
    coinvariantsMap f ∘ₗ coinvariantsMkQ A.ρ = coinvariantsMkQ B.ρ ∘ₗ f.hom.hom := rfl

@[simp]
theorem coinvariantsMap_mk (f : A ⟶ B) (x : A) :
    coinvariantsMap f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f.hom x) := rfl

@[simp]
theorem coinvariantsMap_id (A : Rep k G) :
    coinvariantsMap (𝟙 A) = LinearMap.id := by
  ext; rfl

@[simp]
theorem coinvariantsMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    coinvariantsMap (f ≫ g) = coinvariantsMap g ∘ₗ coinvariantsMap f := by
  ext; rfl

variable (k G)

/-- The functor sending a representation to its coinvariants. -/
@[simps]
noncomputable def coinvariantsFunctor : Rep k G ⥤ ModuleCat k where
  obj A := ModuleCat.of k (A.ρ.coinvariants)
  map f := ModuleCat.ofHom (coinvariantsMap f)

instance : (coinvariantsFunctor k G).Additive where
  map_add := ModuleCat.hom_ext <| LinearMap.ext fun x => Quotient.inductionOn' x (fun _ => rfl)

/-- The adjunction between the functor sending a representation to its coinvariants and the functor
equipping a module with the trivial representation. -/
noncomputable def coinvariantsAdjunction : coinvariantsFunctor k G ⊣ trivialFunctor G :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => {
        hom := ModuleCat.ofHom (f.hom ∘ₗ X.ρ.augmentationSubmodule.mkQ)
        comm := fun g => by
          ext x
          exact congr(f.hom $((Submodule.Quotient.eq <| X.ρ.augmentationSubmodule).2
            (X.ρ.mem_augmentationSubmodule_of_eq g x _ rfl))) }
      invFun := fun f => ModuleCat.ofHom (coinvariantsLift f)
      left_inv := fun _ => ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl
      right_inv := fun _ => Action.Hom.ext <| rfl }
    homEquiv_naturality_left_symm := fun _ _ => ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl
    homEquiv_naturality_right := by intros; rfl }

instance : (coinvariantsFunctor k G).PreservesZeroMorphisms where
  map_zero _ _ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl

instance : Limits.PreservesColimits (coinvariantsFunctor k G) :=
  (coinvariantsAdjunction k G).leftAdjoint_preservesColimits

open MonoidalCategory in
/-- The functor sending `A, B` to `(A ⊗[k] B)_G`. This is naturally isomorphic to the functor
sending `A, B` to `A ⊗[k[G]] B`, where we give `A` the `k[G]ᵐᵒᵖ`-module structure defined by
`g • a := A.ρ g⁻¹ a`. -/
@[simps]
noncomputable def coinvariantsTensor : Rep k G ⥤ Rep k G ⥤ ModuleCat k where
  obj A := MonoidalCategory.tensorLeft A ⋙ coinvariantsFunctor k G
  map f := {
    app := fun A => ModuleCat.ofHom (coinvariantsMap (f ⊗ 𝟙 A))
    naturality := fun _ _ _ => ModuleCat.hom_ext <| Submodule.linearMap_qext _ <|
      TensorProduct.ext' fun _ _ => by rfl }
  map_id _ := NatTrans.ext <| funext fun _ => by
    simpa only [tensorHom_id, id_whiskerRight] using (coinvariantsFunctor k G).map_id _
  map_comp _ _ := NatTrans.ext <| funext fun _ => by
    simpa only [tensorHom_id, comp_whiskerRight] using (coinvariantsFunctor k G).map_comp _ _

instance (A : Rep k G) : ((coinvariantsTensor k G).obj A).Additive := by
  unfold coinvariantsTensor
  infer_instance

end

section Finsupp

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (α : Type u) [DecidableEq α]

open MonoidalCategory Finsupp Representation

/-- Given a `k`-linear `G`-representation `(A, ρ)` and a type `α`, this is the map
`(A ⊗ (α →₀ k[G]))_G →ₗ[k] (α →₀ A)` sending
`⟦a ⊗ single x (single g r)⟧ ↦ single x (r • ρ(g⁻¹)(a)).` -/
noncomputable def coinvariantsTensorFreeToFinsupp :
    (A ⊗ free k G α).ρ.coinvariants →ₗ[k] (α →₀ A) :=
  (coinvariantsFinsuppLEquiv _ α ≪≫ₗ lcongr (Equiv.refl α)
    (coinvariantsTprodLeftRegularLEquiv A.ρ)).toLinearMap ∘ₗ coinvariantsMap (finsuppTensorRight A
      (leftRegular k G) α).hom

variable {A α}

lemma coinvariantsTensorFreeToFinsupp_mk_tmul_single (x : A) (i : α) (g : G) (r : k) :
    coinvariantsTensorFreeToFinsupp A α (Submodule.Quotient.mk (x ⊗ₜ single i (single g r))) =
      single i (r • A.ρ g⁻¹ x) := by
  simp [coinvariantsTensorFreeToFinsupp, coinvariantsMap, finsuppTensorRight,
    TensorProduct.finsuppRight, ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj]

variable (A α)

/-- Given a `k`-linear `G`-representation `(A, ρ)` and a type `α`, this is the map
`(α →₀ A) →ₗ[k] (A ⊗ (α →₀ k[G]))_G` sending `single x a ↦ ⟦a ⊗ₜ single x 1⟧.` -/
noncomputable def finsuppToCoinvariantsTensorFree :
    (α →₀ A) →ₗ[k] coinvariants (A ⊗ (free k G α)).ρ :=
  coinvariantsMap ((finsuppTensorRight A (leftRegular k G) α)).inv ∘ₗ
    (coinvariantsFinsuppLEquiv _ α ≪≫ₗ
    lcongr (Equiv.refl α) (coinvariantsTprodLeftRegularLEquiv A.ρ)).symm.toLinearMap

variable {A α}

lemma finsuppToCoinvariantsTensorFree_single (i : α) (x : A) :
    finsuppToCoinvariantsTensorFree A α (single i x) =
      Submodule.Quotient.mk (x ⊗ₜ single i (single (1 : G) (1 : k))) := by
  simp_all [finsuppToCoinvariantsTensorFree, coinvariantsMap, ModuleCat.MonoidalCategory.tensorObj,
    ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj]

variable (A α)

/-- Given a `k`-linear `G`-representation `(A, ρ)` and a type `α`, this is the linear equivalence
`(A ⊗ (α →₀ k[G]))_G ≃ₗ[k] (α →₀ A)` sending
`⟦a ⊗ single x (single g r)⟧ ↦ single x (r • ρ(g⁻¹)(a)).` -/
noncomputable abbrev coinvariantsTensorFreeLEquiv :
    coinvariants (A ⊗ free k G α).ρ ≃ₗ[k] (α →₀ A) :=
  LinearEquiv.ofLinear (coinvariantsTensorFreeToFinsupp A α) (finsuppToCoinvariantsTensorFree A α)
    (lhom_ext fun _ _ => by
      rw [LinearMap.comp_apply, finsuppToCoinvariantsTensorFree_single,
        coinvariantsTensorFreeToFinsupp_mk_tmul_single]
      simp) <|
    Submodule.linearMap_qext _ <| TensorProduct.ext <| LinearMap.ext fun a => lhom_ext' fun i =>
      lhom_ext fun g r => by
        have := coinvariantsTensorFreeToFinsupp_mk_tmul_single a i g r
        have := finsuppToCoinvariantsTensorFree_single (A := A) i
        simp_all [Submodule.Quotient.eq, TensorProduct.smul_tmul]

end Finsupp
end Rep
