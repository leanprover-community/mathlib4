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
`Ind_S^G, Coind_S^G : Rep k S ⥤ Rep k G`.

Using this isomorphism, we conclude that the `(Co)ind_S^G` and `Res(S) : Rep k G ⥤ Rep k S` are
both left and right adjoint to each other, and thus that `Res(S)` is an exact functor which
preserves projective objects. In particular, given a projective resolution `P` of `k` as a trivial
`k`-linear `G`-representation, `Res(S)(P)` is a projective resolution of `k` as a trivial
`k`-linear `S`-representation.

Given a `G`-representation `X`, we define a natural isomorphism between the functors
`Rep k S ⥤ ModuleCat k` sending `A` to `(X ⊗ Ind_S^G A)_G` and to `(Res(S)(X) ⊗ A)_S`. Hence
a projective resolution `P` of `k` as a trivial `G`-representation induces an isomorphism of
complexes `(P ⊗ Ind_S^G A)_G ≅ (Res(S)(P) ⊗ A)_S`, and since the homology of these complexes
are group homology, we conclude Shapiro's lemma: `Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A)` for all `n`.

## Main definitions

* `groupHomology.indIso A n`: Shapiro's lemma for group homology: an isomorphism
  `Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A)`, given a finite index subgroup `S ≤ G` and an
  `S`-representation `A`.

!-/

universe u

namespace groupHomology

open CategoryTheory Finsupp TensorProduct Rep Representation

variable {k G : Type u} [CommRing k] [Group G] {S : Subgroup G}
  [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)] (A : Rep k S)

variable (P : Rep k G) (A : Rep k S) (g : G)

#check (coinvariantsTensorMk A ((Action.res _ S.subtype).obj P)).compl₂ (P.ρ g)

#exit

open ModuleCat.MonoidalCategory
noncomputable def coinvariantsTensorIndHom (P : Rep k G) (A : Rep k S) :
    ((coinvariantsTensor k G).obj (ind S.subtype A)).obj P ⟶
      ((coinvariantsTensor k S).obj A).obj ((Action.res _ S.subtype).obj P) :=
  ModuleCat.ofHom <| Coinvariants.lift _ (TensorProduct.lift <|
    Coinvariants.lift _ (TensorProduct.lift <| Finsupp.lift _ _ _
      fun g => ((coinvariantsTensorMk A ((Action.res _ S.subtype).obj P)).compl₂ (P.ρ g)))
        fun s => by
          ext g x y
          simpa using (Coinvariants.mk_eq_iff _)).2
            (sub_mem_ker s (x ⊗ₜ[k] P.ρ g y)) fun g => by
          simp only [MonoidalCategory.tensorLeft_obj,
            ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
            ModuleCat.MonoidalCategory.tensorObj, Action.instMonoidalCategory_tensorObj_V]
          ext
          simp

omit [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)] in
lemma coinvariantsTensorIndHom_mk_tmul_indMk {P : Rep k G} {A : Rep k S}
    (g : G) (x : A) (y : P) :
    coinvariantsTensorIndHom P A (coinvariantsTensorMk _ _ (indMk S.subtype _ g x) y) =
      coinvariantsTensorMk _ _ x (P.ρ g y) := by
  simp [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj, coinvariantsTensorIndHom, coinvariantsTensorMk]

noncomputable def coinvariantsTensorIndInv (P : Rep k G) (A : Rep k S) :
    ((coinvariantsTensor k S).obj A).obj ((Action.res _ S.subtype).obj P) ⟶
      ((coinvariantsTensor k G).obj (ind S.subtype A)).obj P :=
  ModuleCat.ofHom <| Representation.coinvariantsLift _ (TensorProduct.lift <|
      (coinvariantsTensorMk (ind S.subtype A) P) ∘ₗ indMk _ _ 1)
    fun s => by
      simp only [MonoidalCategory.tensorLeft_obj,
        ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
        ModuleCat.MonoidalCategory.tensorObj, Action.instMonoidalCategory_tensorObj_V]
      ext x y
      simpa using (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq
        (ρ := ((A.ρ.ind S.subtype).tprod P.ρ)) s (indMk S.subtype A.ρ (1 : G) x ⊗ₜ[k] y) _
        (by simp [← coinvariantsMk_inv_tmul])

omit [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)] in
lemma coinvariantsTensorIndInv_mk_tmul_indMk {P : Rep k G} {A : Rep k S}
    (x : A) (y : P) :
    coinvariantsTensorIndInv P A (coinvariantsTensorMk _ _ x y) =
      coinvariantsTensorMk _ _ (indMk S.subtype _ 1 x) y := by
  simp [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj, coinvariantsTensorIndInv, coinvariantsTensorMk]

set_option maxHeartbeats 0 in
@[simps]
noncomputable def coinvariantsTensorIndIso (P : Rep k G) (A : Rep k S) :
    ((coinvariantsTensor k G).obj (ind S.subtype A)).obj P ≅
      ((coinvariantsTensor k S).obj A).obj ((Action.res _ S.subtype).obj P) where
  hom := coinvariantsTensorIndHom P A
  inv := coinvariantsTensorIndInv P A
  hom_inv_id := by
    ext g a p
    simpa [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
      ModuleCat.MonoidalCategory.tensorObj, coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom] using (coinvariantsMk_eq_iff ((A.ρ.ind S.subtype).tprod P.ρ)).2 <|
        mem_augmentationSubmodule_of_eq g (indMk S.subtype _ g a ⊗ₜ[k] p) _ <| by simp
  inv_hom_id := by
    ext
    simp [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
      ModuleCat.MonoidalCategory.tensorObj, coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom, coinvariantsTensorIndInv]

set_option maxHeartbeats 0 in
@[simps!]
noncomputable def indCompCoinvariantsTensorNatIso (P : Rep k G) :
    indFunctor k S.subtype ⋙ (coinvariantsTensor k G).flip.obj P ≅
      (coinvariantsTensor k S).flip.obj ((Action.res _ S.subtype).obj P) :=
  NatIso.ofComponents (fun A => coinvariantsTensorIndIso P A) fun {X Y} f => by
    simp only [Functor.comp_obj, Functor.flip_obj_obj]
    ext g x p
    simp [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj, coinvariantsTensorMk,
      ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_whiskerRight, coinvariantsTensorIndHom,
      ModuleCat.MonoidalCategory.tensorObj, ModuleCat.MonoidalCategory.whiskerRight,
      coinvariantsMap]

@[simps!]
noncomputable def coinvariantsTensorResMapProjectiveResolutionIso
    (P : ProjectiveResolution (trivial k G k)) (A : Rep k S) :
    (((coinvariantsTensor k S).obj A).mapHomologicalComplex _).obj
        (resMapProjectiveResolution S P).complex ≅
      (((coinvariantsTensor k G).obj (ind S.subtype A)).mapHomologicalComplex _).obj P.complex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coinvariantsTensorIndIso (P.complex.X n) A).symm) fun _ _ h =>
    coinvariantsTensor_hom_ext <| by
      ext a p
      simp [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj, coinvariantsTensorMk,
        ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_whiskerLeft, coinvariantsMap,
        ModuleCat.MonoidalCategory.tensorObj, ModuleCat.MonoidalCategory.whiskerLeft,
        coinvariantsTensorIndInv, h]

variable [DecidableEq G]

noncomputable def _root_.groupHomologyIso
    (P : ProjectiveResolution (trivial k G k)) (A : Rep k G) (n : ℕ) :
    groupHomology A n ≅ ((((coinvariantsTensor k G).obj A).mapHomologicalComplex _).obj
      P.complex).homology n :=
  groupHomologyIsoTor A n ≪≫ P.isoLeftDerivedObj ((coinvariantsTensor k G).obj A) n

noncomputable def shapiro2
    (P : ProjectiveResolution (trivial k G k) := barResolution k G) (A : Rep k S) (n : ℕ) :
    groupHomology A n ≅ groupHomology (ind S.subtype A) n :=
  groupHomologyIso (resMapProjectiveResolution S P) A n ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso
      (coinvariantsTensorResMapProjectiveResolutionIso P A) ≪≫
    (groupHomologyIso P (ind S.subtype A) n).symm

end groupHomology
