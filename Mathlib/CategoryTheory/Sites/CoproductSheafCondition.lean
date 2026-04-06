/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes

/-!
# The sheaf condition and universal coproducts

In this file we show that if `{ fᵢ : Yᵢ ⟶ X }` is a family of morphisms and `∐ᵢ Yᵢ` is a universal
coproduct, then any presheaf `F` that preserves products is a sheaf for the single object covering
`{ ∐ᵢ Yᵢ ⟶ X }` if and only if it is a sheaf for `{ fᵢ : Yᵢ ⟶ X }ᵢ`.

We provide both a version for a general coefficient category and one for type values presheafs.
-/

universe w

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C] {A : Type*} [Category* A] {S : C}

set_option backward.isDefEq.respectTransparency false in
/--
Let `E` be a pre-`0`-hypercover with pairwise pullbacks. If `∐ᵢ Eᵢ` is a universal coproduct
and the presheaf `F` preserves products, then the multifork associated to the single object
`0`-hypercover `{ ∐ᵢ Eᵢ ⟶ S }` is exact if and only if the multifork for `E` is exact.
-/
noncomputable
def PreZeroHypercover.isLimitSigmaOfIsColimitEquiv (E : PreZeroHypercover.{w} S)
    [E.HasPullbacks] {c : Cofan E.X} (hc : IsColimit c) (huniv : IsUniversalColimit c)
    [(E.sigmaOfIsColimit hc).HasPullbacks]
    [∀ i, HasPullback (E.f i) ((E.sigmaOfIsColimit hc).f PUnit.unit)]
    (F : Cᵒᵖ ⥤ A)
    [PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.X i)) F]
    [PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.Y' i)) F] :
    IsLimit ((E.sigmaOfIsColimit hc).toPreOneHypercover.multifork F) ≃
      IsLimit (E.toPreOneHypercover.multifork F) := by
  have : HasPullback (Cofan.IsColimit.desc hc E.f) (Cofan.IsColimit.desc hc E.f) :=
    inferInstanceAs <| HasPullback
      ((E.sigmaOfIsColimit hc).f ⟨⟩) ((E.sigmaOfIsColimit hc).f ⟨⟩)
  let c' : Cofan E.toPreOneHypercover.Y' :=
    Cofan.mk
      ((E.sigmaOfIsColimit hc).toPreOneHypercover.Y (i₁ := ⟨⟩) (i₂ := ⟨⟩) ⟨⟩)
      fun b ↦ pullback.map _ _ _ _ (c.inj _) (c.inj _) (𝟙 _) (by simp) (by simp)
  let equiv : E.toPreOneHypercover.I₁' ≃ E.I₀ × E.I₀ :=
    Equiv.sigmaPUnit (E.toPreOneHypercover.I₀ × E.toPreOneHypercover.I₀)
  have hc' : IsColimit c' := by
    refine (c'.isColimitEquivOfEquiv equiv.symm).symm (Nonempty.some ?_)
    exact IsUniversalColimit.nonempty_isColimit_prod_of_isPullback
      huniv huniv E.f E.f ((E.sigmaOfIsColimit hc).f ⟨⟩) ((E.sigmaOfIsColimit hc).f ⟨⟩)
      (fun i j ↦ .of_hasPullback _ _) (.of_hasPullback _ _) (.refl _) (by simp) (by simp)
      (by simp [c', equiv, Equiv.sigmaPUnit]) (by simp [c', equiv, Equiv.sigmaPUnit])
  refine .trans ?_ (E.toPreOneHypercover.isLimitSigmaOfIsColimitEquiv hc hc' F)
  apply PreOneHypercover.isLimitEquivOfIso
  refine PreOneHypercover.isoMk (.refl _) (fun _ ↦ .refl _) (fun _ _ ↦ .refl _)
      (fun _ _ _ ↦ Iso.refl _) (by cat_disch) ?_ ?_
  · intro ⟨⟩ ⟨⟩ k
    refine Cofan.IsColimit.hom_ext hc' _ _ fun k ↦ ?_
    congr 1
    exact Cofan.IsColimit.hom_ext hc' _ _ fun a ↦ by simp; simp [c']
  · intro ⟨⟩ ⟨⟩ k
    exact Cofan.IsColimit.hom_ext hc' _ _ fun a ↦ by simp; simp [c']

set_option backward.isDefEq.respectTransparency false in
open PreZeroHypercover in
/--
Let `{ fᵢ : Xᵢ ⟶ S }` be a family of morphisms. If `∐ᵢ Xᵢ` is a universal coproduct
and the presheaf `F` preserves products, then `F` is a sheaf for the single object covering
`{ ∐ᵢ Xᵢ ⟶ S }` if and only if it is a sheaf for `{ fᵢ : Xᵢ ⟶ S }ᵢ`.
-/
lemma Presieve.isSheafFor_sigmaDesc_iff {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ S)
    [(ofArrows X f).HasPairwisePullbacks] {c : Cofan X} (hc : IsColimit c)
    (hc' : IsUniversalColimit c)
    [HasPullback (Cofan.IsColimit.desc hc f) (Cofan.IsColimit.desc hc f)]
    [∀ i, HasPullback (f i) (Cofan.IsColimit.desc hc f)]
    (F : Cᵒᵖ ⥤ Type*)
    [PreservesLimit (Discrete.functor <| fun i ↦ op (X i)) F]
    [PreservesLimit (Discrete.functor fun (ij : ι × ι) ↦ op (pullback (f ij.1) (f ij.2))) F] :
    Presieve.IsSheafFor F (.singleton <| Cofan.IsColimit.desc hc f) ↔
      Presieve.IsSheafFor F (.ofArrows X f) := by
  let E := PreZeroHypercover.mk _ _ f
  have : (E.sigmaOfIsColimit hc).HasPullbacks :=
    fun i j ↦ by dsimp [sigmaOfIsColimit]; infer_instance
  have (i : E.I₀) : HasPullback (E.f i) ((E.sigmaOfIsColimit hc).f PUnit.unit) := by
    dsimp [sigmaOfIsColimit_f]; infer_instance
  have : PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.X i)) F := by
    dsimp [E]; infer_instance
  have : PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.Y' i)) F := by
    convert Functor.Initial.preservesLimit_of_comp (Discrete.equivalence <| .sigmaPUnit _).inverse
    assumption
  let equiv := (E.isLimitSigmaOfIsColimitEquiv hc hc' F).nonempty_congr
  rwa [isLimit_toPreOneHypercover_type_iff, isLimit_toPreOneHypercover_type_iff,
    presieve₀_sigmaOfIsColimit] at equiv

end CategoryTheory
