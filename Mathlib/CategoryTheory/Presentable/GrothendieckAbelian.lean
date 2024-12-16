/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory
import Mathlib.CategoryTheory.Limits.TypesFiltered

/-!
# Morphisms to a colimit in a Grothendieck abelian category

Let `C : Type u` be an abelian category `[Category.{v} C]` which
satisfies `IsGrothendieckAbelian.{w} C`. Then, we may expect
that all objects `X : C` are `κ`-presentable for some regular
cardinal `κ`. However, we prove only a weaker result (which
should be enough in order to obtain the existence of enough
injectives): there is a regular cardinal `κ` such that
if `Y : J ⥤ C` is a functor from a `κ`-filtered
category, and `c : Cocone Y` is a colimit cocone,
then the map from the colimit of `X ⟶ Y j` to `X ⟶ c.pt`
is injective, and bijective under the additional
assumption that for any map `f : j ⟶ j'` in `J`, `Y.map f`
is a monomorphism.

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

namespace IsCardinalFiltered

instance under (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] (j₀ : J) : IsCardinalFiltered (Under j₀) κ where
  nonempty_cocone {A _} F hA := ⟨by
    have := isFiltered_of_isCardinalDirected J κ
    let c := cocone (F ⋙ Under.forget j₀) hA
    let x (a : A) : j₀ ⟶ IsFiltered.max j₀ c.pt := (F.obj a).hom ≫ c.ι.app a ≫
      IsFiltered.rightToMax j₀ c.pt
    have hκ' : HasCardinalLT A κ := hasCardinalLT_of_hasCardinalLT_arrow hA
    exact
      { pt := Under.mk (toCoeq x hκ')
        ι :=
          { app a := Under.homMk (c.ι.app a ≫ IsFiltered.rightToMax j₀ c.pt ≫ coeqHom x hκ')
              (by simpa [x] using coeq_condition x hκ' a)
            naturality a b f := by
              ext
              have := c.w f
              dsimp at this ⊢
              simp only [reassoc_of% this, Category.assoc, Category.comp_id]} }⟩

end IsCardinalFiltered

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Limits

variable (J : Type u') [Category.{v'} J] (X : C)

@[simps]
def constCocone : Cocone ((Functor.const J).obj X) where
  pt := X
  ι := 𝟙 _

noncomputable def constCoconeIsColimit [IsFiltered J] :
    IsColimit (constCocone J X) := by
  have : Nonempty J := IsFiltered.nonempty
  let j₀ := Classical.arbitrary J
  exact
    { desc s := s.ι.app j₀
      fac s j := by
        have h₁ := s.w (IsFiltered.leftToMax j₀ j)
        have h₂ := s.w (IsFiltered.rightToMax j₀ j)
        dsimp at h₁ h₂ ⊢
        rw [← h₁, ← h₂, Category.id_comp]
      uniq s m hm := by simpa using hm j₀ }

end Limits

namespace HasExactColimitsOfShape

variable {J : Type u'} [Category.{v'} J]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    {S : ShortComplex (J ⥤ C)} (hS : S.Exact)
    {c₁ : Cocone S.X₁} (hc₁ : IsColimit c₁) {c₂ : Cocone S.X₂} (hc₂ : IsColimit c₂)
    {c₃ : Cocone S.X₃} (hc₃ : IsColimit c₃)
    (f : c₁.pt ⟶ c₂.pt) (g : c₂.pt ⟶ c₃.pt)
    (hf : ∀ j, c₁.ι.app j ≫ f = S.f.app j ≫ c₂.ι.app j)
    (hg : ∀ j, c₂.ι.app j ≫ g = S.g.app j ≫ c₃.ι.app j)

variable (S c₁ c₂ c₃) in
@[simps]
def mapShortComplex : ShortComplex C :=
  ShortComplex.mk f g (hc₁.hom_ext (fun j ↦ by
    dsimp
    rw [reassoc_of% (hf j), hg j, comp_zero, ← NatTrans.comp_app_assoc, S.zero,
      zero_app, zero_comp]))

include hc₂ hc₃ hS in
lemma mapShortComplex_exact : (mapShortComplex S c₁ hc₁ c₂ c₃ f g hf hg).Exact := by
  have := hc₂
  have := hc₃
  have := hS
  sorry

end HasExactColimitsOfShape

variable [IsGrothendieckAbelian.{w} C]

namespace IsGrothendieckAbelian

namespace IsPresentable

variable {X : C} {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
  (hXκ : HasCardinalLT (Subobject X) κ)
  {J : Type w} [SmallCategory J]
  [IsCardinalFiltered J κ] (Y : J ⥤ C)

section injectivity

variable {Y} {c : Cocone Y} (hc : IsColimit c) {j₀ : J}
  {y : X ⟶ Y.obj j₀} (hy : y ≫ c.ι.app j₀ = 0)

namespace injectivity₀

variable (y)

@[simps]
def γ : (Functor.const _).obj X ⟶ Under.forget j₀ ⋙ Y where
  app t := y ≫ Y.map t.hom
  naturality t₁ t₂ f := by
    dsimp
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp, Under.w]

@[simps]
noncomputable def S : ShortComplex (Under j₀ ⥤ C) :=
  ShortComplex.mk _ _ (kernel.condition (γ y))

instance : Mono (S y).f := by dsimp; infer_instance

omit [IsGrothendieckAbelian C] in
lemma S_exact : (S y).Exact :=
  (S y).exact_of_f_is_kernel (kernelIsKernel _)

end injectivity₀

include hXκ hc hy

open injectivity₀ in
lemma injectivity₀ : ∃ (j : J) (f : j₀ ⟶ j), y ≫ Y.map f = 0 := by
  have := isFiltered_of_isCardinalDirected J κ
  have := hc
  have := hXκ
  have := hy
  sorry

end injectivity

section surjectivity

variable {Y} {c : Cocone Y} (hc : IsColimit c)
  [∀ (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)] (z : X ⟶ c.pt)

include hXκ hc

lemma surjectivity : ∃ (j₀ : J) (y : X ⟶ Y.obj j₀), z = y ≫ c.ι.app j₀ := by
  have := hXκ
  have := hc
  sorry

end surjectivity

include hXκ in
lemma preservesColimit_of_mono [∀ (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)] :
    PreservesColimit Y ((coyoneda.obj (op X))) where
  preserves {c} hc := ⟨by
    have := isFiltered_of_isCardinalDirected J κ
    exact Types.FilteredColimit.isColimitOf' _ _
      (surjectivity hXκ hc) (fun j₀ y₁ y₂ hy ↦ by
        dsimp at y₁ y₂ hy ⊢
        rw [← sub_eq_zero, ← Preadditive.sub_comp] at hy
        obtain ⟨j, f, hf⟩ := injectivity₀ hXκ hc hy
        exact ⟨j, f, by simpa only [Preadditive.sub_comp, sub_eq_zero] using hf⟩)⟩

end IsPresentable

end IsGrothendieckAbelian

end CategoryTheory
