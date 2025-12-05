/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Coequalizers arising from effective epimorphisms

Consider a pullback square where the right and bottom maps are the
same morphism `p : Y ⟶ X`:
```
    p₁
  Z ⟶ Y
p₂|   |p
  v   v
  Y ⟶ X
    p
```
If `p` is an effective epimorphism, we show that `X` identifies to the
coequalizer of `p₁` and `p₂`.

Moreover, if `q : W ⟶ Z` is an epimorphism, then `X` is also the coequalizer
of `q ≫ p₁` and `q ≫ p₂`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

/-- Let `p : Y ⟶ X` be an effective epimorphism, `p₁ : Z ⟶ Y` and `p₂ : Z ⟶ Y` two
morphisms which make `Z` the pullback of two copies of `Y` over `X`.
Then, `Y ⟶ X` is the coequalizer of `p₁` and `p₂`. -/
noncomputable def EffectiveEpiStruct.isColimitCoforkOfIsPullback
    {X Y Z : C} {p : Y ⟶ X} (hp : EffectiveEpiStruct p) {p₁ p₂ : Z ⟶ Y}
    (sq : IsPullback p₁ p₂ p p) :
    IsColimit (Cofork.ofπ  p sq.w) :=
  Cofork.IsColimit.mk _ (fun s ↦ hp.desc s.π (fun {T} g₁ g₂ h ↦ by
      obtain ⟨l, rfl, rfl⟩ := sq.exists_lift g₁ g₂ h
      simp [s.condition]))
    (fun s ↦ hp.fac _ _)
    (fun s m hm ↦ hp.uniq _ _ _ hm)

/-- Let `p : Y ⟶ X` be an effective epimorphism, `p₁ : Z ⟶ Y` and `p₂ : Z ⟶ Y` two
morphisms which make `Z` the pullback of two copies of `Y` over `X`, let `q : W ⟶ Z` be an
epimorphism. Then, `X` is the coequalizer of `q ≫ p₁` and `q ≫ p₂`. -/
noncomputable def EffectiveEpiStruct.isColimitCoforkOfEpiOfIsPullback
    {X Y Z : C} {p : Y ⟶ X} (hp : EffectiveEpiStruct p) {p₁ p₂ : Z ⟶ Y}
    (sq : IsPullback p₁ p₂ p p) {W : C} (q : W ⟶ Z) [Epi q] :
    IsColimit (Cofork.ofπ (f := q ≫ p₁) (g := q ≫ p₂) p
      (by simp only [Category.assoc, sq.w])) :=
  isCoequalizerEpiComp (hp.isColimitCoforkOfIsPullback sq) q

end CategoryTheory
