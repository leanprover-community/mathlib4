/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.MorphismProperty.Local

/-!
# Covers in subcanonical topologies

In this file we provide API related to covers in subcanonical topologies.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace GrothendieckTopology.OneHypercover

variable {J : GrothendieckTopology C} [J.Subcanonical]

/-- Glue a family of morphisms along a `1`-hypercover for a subcanonical topology. -/
noncomputable def glueMorphisms {S T : C} (E : J.OneHypercover S) (f : ∀ i, E.X i ⟶ T)
    (h : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.p₁ k ≫ f i = E.p₂ k ≫ f j) :
    S ⟶ T :=
  E.amalgamate (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T)) f h

variable {S T : C} (E : J.OneHypercover S) (f : ∀ i, E.X i ⟶ T)
  (h : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.p₁ k ≫ f i = E.p₂ k ≫ f j)

@[reassoc (attr := simp)]
lemma f_glueMorphisms (i : E.I₀) : E.f i ≫ E.glueMorphisms f h = f i :=
  E.map_amalgamate (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T)) _ _ i

end GrothendieckTopology.OneHypercover

namespace Precoverage.ZeroHypercover

variable {J : Precoverage C} [J.toGrothendieck.Subcanonical]

lemma hom_ext {X Y : C} (𝒰 : J.ZeroHypercover X) {f g : X ⟶ Y}
    (h : ∀ i, 𝒰.f i ≫ f = 𝒰.f i ≫ g) : f = g := by
  have hs : 𝒰.presieve₀.IsSheafFor (yoneda.obj Y) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor_of_mem_precoverage
      𝒰.mem₀
  exact 𝒰.ext_of_isSeparatedFor hs.isSeparatedFor fun i ↦ by simp [h i]

/-- Glue morphisms along a `0`-hypercover. -/
noncomputable def glueMorphisms {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.HasPullbacks]
    (f : ∀ i, 𝒰.X i ⟶ T)
    (hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j) :
    S ⟶ T :=
  𝒰.toOneHypercover.glueMorphisms f fun i j _ ↦ hf i j

@[reassoc (attr := simp)]
lemma f_glueMorphisms {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.HasPullbacks]
    (f : ∀ i, 𝒰.X i ⟶ T)
    (hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j)
    (i : 𝒰.I₀) :
    𝒰.f i ≫ 𝒰.glueMorphisms f hf = f i :=
  𝒰.toOneHypercover.f_glueMorphisms _ _ _

open MorphismProperty

variable [Limits.HasPullbacks C] [J.IsStableUnderBaseChange]

/-- If `J` is a subcanonical precoverage, isomorphisms are local on the target for `J`. -/
instance : (isomorphisms C).IsLocalAtTarget J := by
  refine .mk_of_isStableUnderBaseChange fun {X Y} f 𝒰 (H : ∀ i, IsIso _) ↦ ⟨?_, ?_, ?_⟩
  · refine 𝒰.glueMorphisms (fun i ↦ inv (pullback.snd f (𝒰.f i)) ≫ pullback.fst _ _) fun i j ↦ ?_
    let f := pullback.map (pullback.fst f (𝒰.f i) ≫ f) (𝒰.f j) (𝒰.f i) (𝒰.f j) (pullback.snd _ _)
      (𝟙 _) (𝟙 _) (by simp [pullback.condition]) (by simp)
    rw [← cancel_epi ((pullbackRightPullbackFstIso _ _ _).hom ≫ f)]
    simp [pullback.condition, f]
  · exact (𝒰.pullback₁ f).hom_ext fun i ↦ by simp [pullback.condition_assoc]
  · exact 𝒰.hom_ext fun i ↦ by simp [pullback.condition]

/--
To show that
```
P ---> X
|      |
v      v
Y ---> Z
```
is a pullback square, it suffices to check that
```
P ×[X] Uᵢ ---> Uᵢ
   |           |
   v           v
   Y --------> Z
```
is a pullback square for all `Uᵢ` in a cover of `X` for some subcanonical topology.
-/
lemma isPullback_of_forall_isPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z)
    (g : Y ⟶ Z)
    -- TODO: after refactoring `MorphismProperty.IsLocalAtTarget` to allow covers
    -- in an arbitrary universe, replace `v` by an arbitrary universe
    (𝒰 : Precoverage.ZeroHypercover.{v} J X)
    (H : ∀ i, IsPullback (pullback.snd fst _) (pullback.fst fst (𝒰.f i) ≫ snd) (𝒰.f i ≫ f) g) :
    IsPullback fst snd f g := by
  have h : fst ≫ f = snd ≫ g := (𝒰.pullback₁ fst).hom_ext fun i ↦ by
    simpa [pullback.condition_assoc] using (H i).w
  suffices IsIso (pullback.lift fst snd h) from
    .of_iso_pullback ⟨h⟩ (asIso (pullback.lift _ _ h)) (by simp) (by simp)
  simp_rw [← isomorphisms.iff, IsLocalAtTarget.iff_of_zeroHypercover (P := isomorphisms C)
    (𝒰.pullbackCoverOfLeft f g), isomorphisms.iff]
  intro i
  let m := pullback.map (𝒰.f i ≫ f) g f g (𝒰.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)
  have : IsPullback (pullback.fst (𝒰.f i ≫ f) g) m (𝒰.f i) (pullback.fst _ _) := by
    simpa [← IsPullback.paste_vert_iff (.of_hasPullback _ _), m] using .of_hasPullback _ _
  have H' : IsPullback (pullback.fst fst (𝒰.f i))
      (pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ snd)
        (by simp [← h, pullback.condition_assoc]))
      (pullback.lift fst snd h) m := by
    rw [← IsPullback.paste_vert_iff this.flip (by ext <;> simp [m, pullback.condition])]
    simpa using .of_hasPullback _ _
  have heq : pullback.snd (pullback.lift fst snd h) ((𝒰.pullbackCoverOfLeft f g).f i) =
      H'.isoPullback.inv ≫ (H i).isoPullback.hom := by
    rw [Iso.eq_inv_comp]
    cat_disch
  rw [heq]
  infer_instance

end Precoverage.ZeroHypercover

end CategoryTheory
