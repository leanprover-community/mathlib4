/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Shapiro's lemma for group homology

Given a commutative ring `k` and a finite index subgroup `S ≤ G`, the file
`RepresentationTheory/FiniteIndex.lean` defines a natural isomorphism between the functors
`Ind_S^G` and `Coind_S^G : Rep k S ⥤ Rep k G`.

Using this isomorphism, we conclude that the `(Co)ind_S^G` and `Res(S) : Rep k G ⥤ Rep k S` are
both left and right adjoint to each other, and thus that `Res(S)` is an exact functor which
preserves projective objects. In particular, given a projective resolution `P` of `k` as a trivial
`k`-linear `G`-representation, `Res(S)(P)` is a projective resolution of `k` as a trivial
`k`-linear `S`-representation.

Given a `G`-representation `X`, we define a natural isomorphism between the functors
`Rep k S ⥤ ModuleCat k` sending `A` to `(Ind_S^G A ⊗ X)_G` and to `(A ⊗ Res(S)(X))_S`. Hence
a projective resolution `P` of `k` as a trivial `G`-representation induces an isomorphism of
complexes `(Ind_S^G A ⊗ P)_G ≅ (A ⊗ Res(S)(P))_S`, and since the homology of these complexes
calculate group homology, we conclude Shapiro's lemma: `Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A)` for all `n`.

## Main definitions

* `groupHomology.indIso A n`: Shapiro's lemma for group homology: an isomorphism
  `Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A)`, given a finite index subgroup `S ≤ G` and an
  `S`-representation `A`.

-/

universe u

namespace groupHomology

open CategoryTheory Finsupp TensorProduct Rep Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H)

section

variable (A : Rep k G) (B : Rep k H)

open ModuleCat.MonoidalCategory

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
        simp only [MonoidalCategory.curriedTensor_obj_obj, Action.tensorObj_V,
          tensorObj_def, tensorObj]
        ext
        simp

variable {A B} in
lemma coinvariantsTensorIndHom_mk_tmul_indVMk (h : H) (x : A) (y : B) :
    coinvariantsTensorIndHom φ A B (coinvariantsTensorMk _ _ (IndV.mk φ _ h x) y) =
      coinvariantsTensorMk _ _ x (B.ρ h y) := by
  simp [tensorObj_def, ModuleCat.MonoidalCategory.tensorObj, coinvariantsTensorIndHom,
    coinvariantsTensorMk]

/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear map
`(A ⊗ Res(φ)(B))_G ⟶ (Ind(φ)(A) ⊗ B))_H` sending `⟦a ⊗ₜ b⟧` to `⟦1 ⊗ₜ a⟧ ⊗ₜ b` for all
`a : A`, and `b : B`. -/
noncomputable def coinvariantsTensorIndInv :
    ((coinvariantsTensor k G).obj A).obj ((Action.res _ φ).obj B) ⟶
      ((coinvariantsTensor k H).obj (ind φ A)).obj B :=
  ModuleCat.ofHom <| Coinvariants.lift _ (TensorProduct.lift <|
      (coinvariantsTensorMk (ind φ A) B) ∘ₗ IndV.mk _ _ 1)
    fun s => by
      simp only [MonoidalCategory.curriedTensor_obj_obj, tensorObj_def,
        tensorObj, Action.tensorObj_V]
      ext x y
      simpa [Coinvariants.mk_eq_iff, coinvariantsTensorMk] using
        Coinvariants.mem_ker_of_eq (φ s) (IndV.mk φ A.ρ (1 : H) x ⊗ₜ[k] y) _
        (by simp [← Coinvariants.mk_inv_tmul])

variable {A B} in
lemma coinvariantsTensorIndInv_mk_tmul_indMk (x : A) (y : B) :
    coinvariantsTensorIndInv φ A B (Coinvariants.mk
      (A.ρ.tprod (Rep.ρ ((Action.res _ φ).obj B))) <| x ⊗ₜ y) =
      coinvariantsTensorMk _ _ (IndV.mk φ _ 1 x) y := by
  simp [tensorObj_def, tensorObj, coinvariantsTensorIndInv, coinvariantsTensorMk]

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
    simpa [tensorObj_def, tensorObj, coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom, Coinvariants.mk_eq_iff] using
        Coinvariants.mem_ker_of_eq h (IndV.mk φ _ h a ⊗ₜ[k] b) _ <| by simp
  inv_hom_id := by
    ext
    simp [tensorObj_def, tensorObj, coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom]

/-- Given a group hom `φ : G →* H` and `A : Rep k G`, the functor `Rep k H ⥤ ModuleCat k` sending
`B ↦ (Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B ↦ (A ⊗ Res(φ)(B))_G`. -/
@[simps! hom_app inv_app]
noncomputable def coinvariantsTensorIndNatIso :
    (coinvariantsTensor k H).obj (ind φ A) ≅ Action.res _ φ ⋙ (coinvariantsTensor k G).obj A :=
  NatIso.ofComponents (fun B => coinvariantsTensorIndIso φ A B) fun {X Y} f => by
    ext
    simp [tensorObj_def, tensorObj, coinvariantsTensorIndHom, coinvariantsTensorMk,
      whiskerLeft_def, ModuleCat.MonoidalCategory.whiskerLeft, hom_comm_apply]

end

variable (S : Subgroup G) [DecidableRel (QuotientGroup.rightRel S)] [S.FiniteIndex]
variable (A : Rep k S)

/-- Given a projective resolution `P` of `k` as a `k`-linear `G`-representation, a finite index
subgroup `S ≤ G`, and a `k`-linear `S`-representation `A`, this is an isomorphism of complexes
`(A ⊗ Res(S)(P))_S ≅ (Ind_S^G(A) ⊗ P)_G`. -/
noncomputable abbrev coinvariantsTensorResProjectiveResolutionIso
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    ((Action.res _ S.subtype).mapProjectiveResolution P).complex.coinvariantsTensorObj A ≅
      P.complex.coinvariantsTensorObj (ind S.subtype A) :=
  (NatIso.mapHomologicalComplex (coinvariantsTensorIndNatIso S.subtype A).symm _).app _

/-- Shapiro's lemma: given a finite index subgroup `S ≤ G` and an `S`-representation `A`, we have
`Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A).` -/
noncomputable def indIso [DecidableEq G] (A : Rep k S) (n : ℕ) :
    groupHomology (ind S.subtype A) n ≅ groupHomology A n :=
  (HomologicalComplex.homologyFunctor _ _ _).mapIso (inhomogeneousChainsIso (ind S.subtype A) ≪≫
    (coinvariantsTensorResProjectiveResolutionIso S A (barResolution k G)).symm) ≪≫
  (groupHomologyIso A n ((Action.res _ _).mapProjectiveResolution <| barResolution k G)).symm

end groupHomology
