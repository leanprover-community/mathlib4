/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Pure subobjects

In this file, we define the notion of `κ`-pure morphism (`IsCardinalPure`)
in a category `C`. This class contains split monomorphisms and is stable
under `κ`-filtered colimits. When `C` is a `κ`-accessible category, we show
that `κ`-pure morphisms are monomorphisms.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

/-- Given a regular cardinal `κ`, we say that a morphism `f : X ⟶ Y`
if `κ`-pure for any commutative square:
```
      t
 X' -----> Y'
 |         |
l|         |r
 v         v
 X  -----> Y
      f
```
where `X'` and `Y'` are `κ`-presentable, there exists a morphism
`ρ : Y' ⟶ X` such that `t ≫ ρ = l`. -/
class IsCardinalPure (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {X Y : C} (f : X ⟶ Y) : Prop where
  exists_of_commSq {X' Y' : C} {t : X' ⟶ Y'} {l : X' ⟶ X} {r : Y' ⟶ Y}
    [IsCardinalPresentable X' κ] [IsCardinalPresentable Y' κ]
    (sq : CommSq t l r f) : ∃ (ρ : Y' ⟶ X), t ≫ ρ = l

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

variable (C) in
/-- `κ`-pure morphisms, as a property of morphisms in a category `C`. -/
abbrev isCardinalPure : MorphismProperty C := fun _ _ f ↦ IsCardinalPure κ f

instance {X Y : C} (f : X ⟶ Y) [IsSplitMono f] : IsCardinalPure κ f where
  exists_of_commSq {X' Y' t l r _ _} sq :=
    ⟨r ≫ retraction f, by simp [sq.w_assoc]⟩

instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsCardinalPure κ f] [IsCardinalPure κ g] :
    IsCardinalPure κ (f ≫ g) where
  exists_of_commSq {X' Y' t l r _ _} sq := by
    obtain ⟨ρ, hρ⟩ := IsCardinalPure.exists_of_commSq κ
      (show CommSq t (l ≫ f) r g from ⟨by simpa using sq.w⟩)
    exact IsCardinalPure.exists_of_commSq κ (CommSq.mk hρ)

instance : (isCardinalPure C κ).IsMultiplicative where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

instance : (isCardinalPure C κ).RespectsIso where
  precomp _ _ _ _ := inferInstance
  postcomp _ _ _ _ := inferInstance

lemma IsCardinalPure.of_postcomp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsCardinalPure κ (f ≫ g)] :
    IsCardinalPure κ f where
  exists_of_commSq {X' Y' t l r _ _} sq :=
    exists_of_commSq κ (show CommSq t l (r ≫ g) (f ≫ g) from ⟨by simp [sq.w_assoc]⟩)

instance : (isCardinalPure C κ).HasOfPostcompProperty (⊤ : MorphismProperty C) where
  of_postcomp f g _ _ := IsCardinalPure.of_postcomp κ f g

set_option backward.defeqAttrib.useBackward true in
lemma IsCardinalAccessibleCategory.mono_iff [IsCardinalAccessibleCategory C κ]
    {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ (T : C) [IsCardinalPresentable T κ] (g₁ g₂ : T ⟶ X),
      g₁ ≫ f = g₂ ≫ f → g₁ = g₂ :=
  ⟨fun _ _ _ _ _ _ ↦ by rwa [← cancel_mono f],
    fun hf ↦ ⟨fun {Z} g₁ g₂ h ↦ ((isCardinalPresentable C κ).ι.denseAt Z).hom_ext
      (by cat_disch)⟩⟩

set_option backward.defeqAttrib.useBackward true in
/-- In a `κ`-accessible category, `κ`-pure morphisms are monomorphisms.
(This proposition 2.29 in [Adamek_Rosicky_1994].) -/
lemma IsCardinalPure.mono [IsCardinalAccessibleCategory C κ]
    {X Y : C} (f : X ⟶ Y) [IsCardinalPure κ f] :
    Mono f := by
  rw [IsCardinalAccessibleCategory.mono_iff κ]
  intro K _ p q hpq
  obtain ⟨j, p', q', h₁, h₂⟩ := IsCardinalPresentable.exists_hom₂_of_isColimit κ
    ((isCardinalPresentable C κ).ι.denseAt X) p q
  obtain ⟨⟨X', (hX' : IsCardinalPresentable X' κ)⟩, u, rfl⟩ := j.mk_surjective
  dsimp at u h₁ h₂ p' q'
  obtain ⟨j', f', hf'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    ((isCardinalPresentable C κ).ι.denseAt Y) (u ≫ f)
  obtain ⟨j'', c, hc⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ
    ((isCardinalPresentable C κ).ι.denseAt Y) (p' ≫ f') (q' ≫ f') (by cat_disch)
  obtain ⟨⟨Y', _⟩, v', rfl⟩ := j'.mk_surjective
  obtain ⟨⟨Y'', _ : IsCardinalPresentable Y'' κ⟩, v, rfl⟩ := j''.mk_surjective
  obtain ⟨⟨h⟩, H, rfl⟩ := CostructuredArrow.homMk_surjective c
  dsimp at v' f' hf' v h H hc
  simp only [Category.assoc, Category.id_comp] at hf' h₁ h₂ hc
  obtain ⟨u', hu'⟩ :=
    IsCardinalPure.exists_of_commSq κ (show CommSq (f' ≫ h) u v f from { })
  simp only [Category.assoc] at hu'
  rw [← h₁, ← hu', reassoc_of% hc, hu', h₂]

variable (C) in
lemma isCardinalPure_le_monomorphisms [IsCardinalAccessibleCategory C κ] :
    isCardinalPure C κ ≤ .monomorphisms C :=
  fun _ _ f _ ↦ IsCardinalPure.mono κ f

set_option backward.defeqAttrib.useBackward true in
/-- `κ`-pure morphisms are stable under `κ`-filtered colimits.
(This proposition 2.30 (i) in [Adamek_Rosicky_1994].) -/
instance (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    (isCardinalPure C κ).IsStableUnderColimitsOfShape J := by
  have := isFiltered_of_isCardinalFiltered J κ
  rw [MorphismProperty.isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
  rintro _ _ f ⟨X, Y, c₁, c₂, hc₁, hc₂, f, hf⟩
  generalize hf' : hc₁.desc (Cocone.mk c₂.pt (f ≫ c₂.ι)) = f'
  have fac (j : J) : f.app j ≫ c₂.ι.app j = c₁.ι.app j ≫ f' := by simp [← hf']
  dsimp at f' hf' fac
  refine ⟨fun {X' Y' t l r _ _} sq ↦ ?_⟩
  dsimp at r
  obtain ⟨j', l', r', hl', hr', sq'⟩ :
      ∃ (j' : J) (l' : X' ⟶ X.obj j') (r' : Y' ⟶ Y.obj j'),
        l' ≫ c₁.ι.app j' = l ∧ r' ≫ c₂.ι.app j' = r ∧ CommSq t l' r' (f.app j') := by
    obtain ⟨j₁, l', hl'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc₁ l
    obtain ⟨j₂, r', hr'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc₂ r
    obtain ⟨j₃, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs j₁ j₂
    obtain ⟨j₄, c, hc⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ
      hc₂ (t ≫ r' ≫ Y.map b) (l' ≫ X.map a ≫ f.app j₃) (by
        simp [dsimp% hr', fac, reassoc_of% dsimp% hl', sq.w])
    exact ⟨j₄, l' ≫ X.map a ≫ X.map c, r' ≫ Y.map b ≫ Y.map c,
      by cat_disch, by cat_disch, { }⟩
  have := hf j'
  obtain ⟨ρ, hρ⟩ := IsCardinalPure.exists_of_commSq κ sq'
  exact ⟨ρ ≫ c₁.ι.app j', by cat_disch⟩

open MorphismProperty in
instance (J : Type*) [Category* J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    (isCardinalPure C κ).IsStableUnderColimitsOfShape J := by
  rw [isStableUnderColimitsOfShape_iff_colimitsOfShape_le,
    colimitsOfShape_eq_of_equivalence _ (equivSmallModel.{w} J),
    ← MorphismProperty.isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
  have : IsCardinalFiltered (SmallModel.{w} J) κ :=
    IsCardinalFiltered.of_equivalence _ (equivSmallModel.{w} J)
  infer_instance

end CategoryTheory
