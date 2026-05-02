/-
Copyright (c) 2026 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Attaching a map to a subcomplex

For a subcomplex `A` of a simplicial set `X` and a morphism `σ : Y ⟶ X`,
this file builds the abstract attachment-as-pushout machinery underlying
the single-cell boundary and horn attachment results.

The image–preimage square in `X.Subcomplex` is bicartesian
(`Subcomplex.imagePreimageBicartSq`), hence a pushout in `SSet`
(`Subcomplex.imagePreimage_isPushout`). Choosing a preimage
`A.preimage σ = K` defines the **attaching map** `K ⟶ A`
(`Subcomplex.attachingMap`); the resulting square is again a pushout
whenever `σ` is injective on the complement of `K` at every dimension
(`Subcomplex.attachingMap_isPushout_of_injOn_compl`). The injectivity
hypothesis stops short of `Mono σ`, so the result applies to nondegenerate
single-simplex maps `Δ[n] ⟶ X`, which need not be monic.

See the files `Mathlib/AlgebraicTopology/SimplicialSet/BoundaryAttach.lean`
and `Mathlib/AlgebraicTopology/SimplicialSet/HornAttach.lean` for the
single-cell specializations.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet
namespace Subcomplex

variable {X Y : SSet.{u}}

/-- The image–preimage square of `σ : Y ⟶ X` at `A` is bicartesian in
`X.Subcomplex`. Its meet is `(A.preimage σ).image σ`, equivalently
`A ⊓ range σ`; its join is `A ⊔ range σ`. -/
lemma imagePreimageBicartSq (A : X.Subcomplex) (σ : Y ⟶ X) :
    BicartSq ((A.preimage σ).image σ) A (range σ) (A ⊔ range σ) where
  sup_eq := rfl
  inf_eq := by
    ext n x
    simp only [image_obj, preimage_obj, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨hxA, y, rfl⟩
      exact ⟨y, hxA, rfl⟩
    · rintro ⟨y, hyA, rfl⟩
      exact ⟨hyA, y, rfl⟩

/-- The bicartesian image–preimage square as a pushout in `SSet`. -/
lemma imagePreimage_isPushout (A : X.Subcomplex) (σ : Y ⟶ X) :
    IsPushout (homOfLE (imagePreimageBicartSq A σ).le₁₂)
      (homOfLE (imagePreimageBicartSq A σ).le₁₃)
      (homOfLE (show A ≤ A ⊔ range σ from le_sup_left))
      (homOfLE (show range σ ≤ A ⊔ range σ from le_sup_right)) :=
  (imagePreimageBicartSq A σ).isPushout

/-- The attaching map `K ⟶ A` induced by `σ : Y ⟶ X` together with an equation
`A.preimage σ = K`. Composing with `A.ι` recovers `K.ι ≫ σ`. -/
def attachingMap (A : X.Subcomplex) (σ : Y ⟶ X)
    {K : Y.Subcomplex} (hK : A.preimage σ = K) : (K : SSet) ⟶ A :=
  (Subcomplex.eqToIso hK.symm).hom ≫ A.fromPreimage σ

@[reassoc (attr := simp)]
lemma attachingMap_ι (A : X.Subcomplex) (σ : Y ⟶ X)
    {K : Y.Subcomplex} (hK : A.preimage σ = K) :
    attachingMap A σ hK ≫ A.ι = K.ι ≫ σ := by
  dsimp [attachingMap]
  rw [Category.assoc, fromPreimage_ι]
  rfl

@[reassoc (attr := simp)]
lemma attachingMap_comp_homOfLE (A : X.Subcomplex) (σ : Y ⟶ X)
    {K : Y.Subcomplex} (hK : A.preimage σ = K) :
    attachingMap A σ hK ≫
      homOfLE (show A ≤ A ⊔ range σ from le_sup_left) =
    K.ι ≫ lift σ (show range σ ≤ A ⊔ range σ from le_sup_right) := by
  rw [← cancel_mono (A ⊔ range σ).ι]
  simp [Category.assoc]

/-- Membership in `Set.range (K.ι.app d)` reduces to membership in `K.obj d`. -/
private lemma mem_range_ι_app (K : Y.Subcomplex) {d : SimplexCategoryᵒᵖ}
    (y : Y.obj d) :
    y ∈ Set.range (K.ι.app d) ↔ y ∈ K.obj d :=
  ⟨fun ⟨y', hy'⟩ ↦ hy' ▸ y'.2, fun hy ↦ ⟨⟨y, hy⟩, rfl⟩⟩

/-- The attaching square is a pullback in `Type` at every dimension. -/
private lemma attachingMap_isPullback_app (A : X.Subcomplex) (σ : Y ⟶ X)
    {K : Y.Subcomplex} (hK : A.preimage σ = K) (d : SimplexCategoryᵒᵖ) :
    IsPullback ((attachingMap A σ hK).app d) (K.ι.app d)
      ((homOfLE (show A ≤ A ⊔ range σ from le_sup_left)).app d)
      ((lift σ (show range σ ≤ A ⊔ range σ from le_sup_right)).app d) := by
  rw [Types.isPullback_iff]
  refine ⟨congr_app (attachingMap_comp_homOfLE A σ hK) d, ?_, ?_⟩
  · intro y₁ y₂ h
    exact Subtype.ext h.2
  · intro a y h
    have hval : a.val = σ.app d y := by
      simpa only [homOfLE_app_val, lift_app_coe] using congrArg Subtype.val h
    have hyA : σ.app d y ∈ A.obj d := by simp [← hval]
    refine ⟨⟨y, by simpa [← hK] using hyA⟩, ?_, rfl⟩
    exact Subtype.ext (by simpa [attachingMap] using hval.symm)

/-- The two structure maps into `A ⊔ range σ` are jointly surjective at every
dimension. -/
private lemma range_app_union_range_app (A : X.Subcomplex) (σ : Y ⟶ X)
    (d : SimplexCategoryᵒᵖ) :
    Set.range ((homOfLE (show A ≤ A ⊔ range σ from le_sup_left)).app d) ⊔
      Set.range ((lift σ (show range σ ≤ A ⊔ range σ from le_sup_right)).app d) =
    Set.univ := by
  ext x
  simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
  rcases x.2 with hxA | ⟨y, hy⟩
  · exact Or.inl ⟨⟨x.val, hxA⟩, Subtype.ext rfl⟩
  · exact Or.inr ⟨y, Subtype.ext (by simpa using hy)⟩

/-- Attachment along `K` is a pushout when `K` is the preimage of `A` and `σ`
is injective at every dimension on the complement of `K`.

We assume injectivity on the complement of `K` rather than `Mono σ` so the
lemma applies to the classifier of a single nondegenerate simplex, where
injectivity holds only off the boundary. -/
lemma attachingMap_isPushout_of_injOn_compl (A : X.Subcomplex)
    (σ : Y ⟶ X) {K : Y.Subcomplex} (hK : A.preimage σ = K)
    (hinj : ∀ d, Set.InjOn (σ.app d) (K.obj d)ᶜ) :
    IsPushout (attachingMap A σ hK) K.ι
      (homOfLE (show A ≤ A ⊔ range σ from le_sup_left))
      (lift σ (show range σ ≤ A ⊔ range σ from le_sup_right)) := by
  refine IsPushout.of_forall_isPushout_app fun d ↦ ?_
  refine Types.isPushout_of_isPullback_of_mono'
    (attachingMap_isPullback_app A σ hK d)
    (range_app_union_range_app A σ d) ?_
  intro y₁ y₂ hy₁ hy₂ h
  refine hinj d ?_ ?_ ?_
  · rwa [Set.mem_compl_iff, ← mem_range_ι_app K]
  · rwa [Set.mem_compl_iff, ← mem_range_ι_app K]
  · simpa only [Subtype.ext_iff, lift_app_coe] using congrArg Subtype.val h

end Subcomplex
end SSet
