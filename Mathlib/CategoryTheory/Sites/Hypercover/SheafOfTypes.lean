/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer

/-!

# `1`-hypercovers and (pre)sheaves of types

In this file we provide some API for working with `1`-hypercovers for sheaves of types.

## Main declarations

- `CategoryTheory.PreOneHypercover.IsStronglySheafFor`: A pre-`1`-hypercover `E`
  satisfies the strong sheaf condition for a presheaf of types `F` if
  `F` is a sheaf for the `0`-covering and separated for the `1`-coverings.
- `CategoryTheory.PreOneHypercover.IsStronglySheafFor.amalgamate`: Glue
  a family of compatible sections along `E` if `E` satisfies the strong sheaf condition.
- `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isLimitMultifork`: If `E`
  satisfies the strong sheaf condition for `F`, then the multiequalizer diagram
  for `E` is limiting.

-/

universe w

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C]

namespace PreOneHypercover

variable {X : C} {E : PreOneHypercover.{w} X} {F : Cᵒᵖ ⥤ Type*}

/-- A presheaf `F` of types is (strongly) separated for a pre-`1`-hypercover if `F` is separated for
both the `0` and the `1`-components. -/
structure IsStronglySeparatedFor {X : C} (E : PreOneHypercover X) (F : Cᵒᵖ ⥤ Type*) : Prop where
  isSeparatedFor_presieve₀ : E.presieve₀.IsSeparatedFor F
  isSeparatedFor_sieve₁ ⦃i j : E.I₀⦄ ⦃W : C⦄ (p₁ : W ⟶ E.X i) (p₂ : W ⟶ E.X j)
    (h : p₁ ≫ E.f i = p₂ ≫ E.f j) :
    (E.sieve₁ p₁ p₂).arrows.IsSeparatedFor F

/--
A presheaf `F` of types is (strongly) a sheaf for a pre-`1`-hypercover if `F` is a sheaf for
both the `0` and the `1`-components.
This implies that the multiequalizer diagram attached to `E` is exact
(see `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isLimitMultifork`).
-/
structure IsStronglySheafFor {X : C} (E : PreOneHypercover X) (F : Cᵒᵖ ⥤ Type*) : Prop where
  isSheafFor_presieve₀ : E.presieve₀.IsSheafFor F
  isSeparatedFor_sieve₁ ⦃i j : E.I₀⦄ ⦃W : C⦄ (p₁ : W ⟶ E.X i) (p₂ : W ⟶ E.X j)
    (h : p₁ ≫ E.f i = p₂ ≫ E.f j) :
    (E.sieve₁ p₁ p₂).arrows.IsSeparatedFor F

lemma IsStronglySheafFor.isStronglySeparatedFor (h : E.IsStronglySheafFor F) :
    E.IsStronglySeparatedFor F where
  isSeparatedFor_presieve₀ := h.isSheafFor_presieve₀.isSeparatedFor
  isSeparatedFor_sieve₁ _ _ _ p₁ p₂ w := h.isSeparatedFor_sieve₁ p₁ p₂ w

lemma IsStronglySeparatedFor.arrowsCompatible (h : E.IsStronglySeparatedFor F)
    (x : ∀ i, F.obj (op <| E.X i))
    (hc : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), F.map (E.p₁ k).op (x i) = F.map (E.p₂ k).op (x j)) :
    Presieve.Arrows.Compatible _ E.f x := by
  rintro i₁ i₂ Z g₁ g₂ heq
  refine (h.isSeparatedFor_sieve₁ g₁ g₂ heq).ext fun W f ⟨T, u, h₁, h₂⟩ ↦ ?_
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, h₁]
  conv_rhs => rw [← FunctorToTypes.map_comp_apply, ← op_comp, h₂]
  simp [hc]

/-- Glue sections of a `Type`-valued sheaf over a `1`-hypercover. -/
noncomputable def IsStronglySheafFor.amalgamate (h : E.IsStronglySheafFor F)
    (x : ∀ i, F.obj (op <| E.X i))
    (hc : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), F.map (E.p₁ k).op (x i) = F.map (E.p₂ k).op (x j)) :
    F.obj (op X) :=
  (h.isSheafFor_presieve₀).amalgamate _
    ((h.isStronglySeparatedFor.arrowsCompatible x hc).familyOfElements_compatible)

@[simp]
lemma IsStronglySheafFor.map_amalgamate (h : E.IsStronglySheafFor F)
    (x : ∀ i, F.obj (op <| E.X i))
    (hc : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), F.map (E.p₁ k).op (x i) = F.map (E.p₂ k).op (x j))
    (i : E.I₀) :
    F.map (E.f i).op (h.amalgamate x hc) = x i := by
  rw [amalgamate, Presieve.IsSheafFor.valid_glue _ _ _ ⟨i⟩]
  simp

/-- `F` satisfies the (strong) sheaf condition for the pre-`1`-hypercover `E`, then
the multiequalizer diagram attached to `E` is limiting. -/
noncomputable
def IsStronglySheafFor.isLimitMultifork (h : E.IsStronglySheafFor F) :
    IsLimit (E.multifork F) := by
  refine Nonempty.some ?_
  rw [Multifork.isLimit_types_iff]
  refine ⟨fun s t hst ↦ ?_, fun s ↦ ?_⟩
  · exact h.isSheafFor_presieve₀.isSeparatedFor.ext fun _ _ ⟨i⟩ ↦ congr($(hst).val i)
  · exact ⟨h.amalgamate s.val fun i j k ↦ s.property ⟨(i, j), k⟩, by ext; simp⟩

lemma IsStronglySheafFor.isSheafFor_sieve_of_pullback (h₁ : E.IsStronglySheafFor F)
    (h₂ : ∀ ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSeparatedFor F (E.sieve₀.pullback f).arrows)
    {S : Sieve X}
    (H : ∀ (i : E.I₀), Presieve.IsSheafFor F (S.pullback (E.f i)).arrows)
    (H' : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F (S.pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F S.arrows := by
  intro t ht
  choose s hs huniq using fun i ↦ H i (t.pullback (E.f i)) (ht.pullback (E.f i))
  have hr : Presieve.Arrows.Compatible _ E.f s := by
    intro i j Z gi gj hgij
    refine (h₁.isSeparatedFor_sieve₁ gi gj hgij).ext fun Y f ⟨k, h, hf₁, hf₂⟩ ↦ ?_
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp, hf₁, hf₂]
    simp only [op_comp, FunctorToTypes.map_comp_apply]
    congr! 1
    refine (H' k).ext fun W p hp ↦ ?_
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp, hs i (p ≫ E.p₁ k) (by simpa),
      hs j (p ≫ E.p₂ k) (by simpa [← E.w])]
    dsimp only [Presieve.FamilyOfElements.pullback]
    congr 1
    simp [E.w]
  obtain ⟨s', hs'⟩ := hr.exists_familyOfElements
  obtain ⟨t', ht', hunique⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp h₁.isSheafFor_presieve₀ _ hr
  refine ⟨t', fun T f hf ↦ (h₂ f).ext fun Z g hg ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨W, w, u, ⟨i⟩, heq⟩ := hg
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    have : t (g ≫ f) (by simp [hf]) = t (w ≫ E.f i) (by simp [heq, hf]) := by
      congr 1
      rw [heq]
    simpa [← heq, ht' i, ← t.comp_of_compatible _ ht, this] using hs i w _
  · refine hunique _ fun i ↦ huniq _ _ fun Z g hg ↦ ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

/--
Being a sheaf for a presieve `R` is local on the target in the following sense: If `E`
is a pre-`1`-hypercover for which `F` is separated and a sheaf for the `0`-components, then to
check that `F` is a sheaf for `R` it suffices to check:

- `F` is a sheaf for the pullbacks of `R` along the maps from the `0`-components.
- `F` is separated for the pullbacks of `R` along the maps from the `1`-components.
-/
lemma IsStronglySheafFor.isSheafFor_of_pullback (h₁ : E.IsStronglySheafFor F)
    (h₂ : ∀ ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSeparatedFor F (E.sieve₀.pullback f).arrows)
    {R : Presieve X}
    (H : ∀ (i : E.I₀), Presieve.IsSheafFor F ((Sieve.generate R).pullback (E.f i)).arrows)
    (H' : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F ((Sieve.generate R).pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F R := by
  rw [Presieve.isSheafFor_iff_generate]
  exact h₁.isSheafFor_sieve_of_pullback h₂ H H'

end PreOneHypercover

namespace GrothendieckTopology.OneHypercover

variable {J : GrothendieckTopology C} {X : C} {E : OneHypercover.{w} J X} {F : Cᵒᵖ ⥤ Type*}

lemma isStronglySeparatedFor (hf : Presieve.IsSeparated J F) : E.IsStronglySeparatedFor F where
  isSeparatedFor_presieve₀ := by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact hf _ E.mem₀
  isSeparatedFor_sieve₁ i j W p₁ p₂ h := hf _ (E.mem₁ _ _ _ _ h)

lemma isStronglySheafFor (hf : Presieve.IsSheaf J F) : E.IsStronglySheafFor F where
  isSheafFor_presieve₀ := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hf _ E.mem₀
  isSeparatedFor_sieve₁ i j W p₁ p₂ h := hf.isSeparated _ (E.mem₁ _ _ _ _ h)

variable (E) in
lemma isSheafFor_sieve_of_pullback (hF : Presieve.IsSheaf J F) {S : Sieve X}
    (h₁ : ∀ (i : E.I₀), Presieve.IsSheafFor F (S.pullback (E.f i)).arrows)
    (h₂ : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F (S.pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F S.arrows := by
  refine (E.isStronglySheafFor hF).isSheafFor_sieve_of_pullback ?_ h₁ h₂
  intro Y f
  exact (hF _ (J.pullback_stable _ E.mem₀)).isSeparatedFor

/-- If `F` is a `J`-sheaf, then being a sheaf for a presieve `R` is `J`-local on the target, i.e.
it can be checked on the pullbacks from a `1`-hypercover. -/
lemma isSheafFor_of_pullback (hF : Presieve.IsSheaf J F) {R : Presieve X}
    (h₁ : ∀ (i : E.I₀), Presieve.IsSheafFor F ((Sieve.generate R).pullback (E.f i)).arrows)
    (h₂ : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F ((Sieve.generate R).pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F R := by
  rw [Presieve.isSheafFor_iff_generate]
  exact E.isSheafFor_sieve_of_pullback hF h₁ h₂

end CategoryTheory.GrothendieckTopology.OneHypercover
