/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Morphisms to a colimit in a Grothendieck abelian category

Let `C : Type u` be an abelian category `[Category.{v} C]` which
satisfies `IsGrothendieckAbelian.{w} C`. Then, we may expect
that all objects `X : C` are `κ`-presentable for some regular
cardinal `κ`. However, we prove only a weaker result (which
is enough in order to obtain the existence of enough
injectives): let `κ` be a big enough regular cardinal `κ` such that
if `Y : J ⥤ C` is a functor from a `κ`-filtered
category, and `c : Cocone Y` is a colimit cocone,
then the map from the colimit of the types `X ⟶ Y j` to
`X ⟶ c.pt` is injective, and it is bijective under the
additional assumption that for any map `f : j ⟶ j'` in `J`,
`Y.map f` is a monomorphism.

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

attribute [local instance] IsFiltered.isConnected

namespace IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {X : C} {J : Type w} [SmallCategory J] (F : J ⥤ MonoOver X)

end IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C]

variable [IsGrothendieckAbelian.{w} C]

namespace IsGrothendieckAbelian

namespace IsPresentable

variable {X : C} {J : Type w} [SmallCategory J] (Y : J ⥤ C)

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

variable (c j₀) in
abbrev c₃ : Cocone (Under.forget j₀ ⋙ Y) := c.whisker _

@[simps]
noncomputable def F : Under j₀ ⥤ MonoOver X where
  obj j := MonoOver.mk' ((kernel.ι (γ y)).app j)
  map {j j'} f := MonoOver.homMk ((kernel (γ y)).map f)

noncomputable def f : colimit (kernel (γ y)) ⟶ X :=
  IsColimit.map (colimit.isColimit _) (constCocone _ X) (kernel.ι _)

lemma hf (j : Under j₀) :
    colimit.ι (kernel (γ y)) j ≫ f y = (kernel.ι (γ y)).app j :=
  (IsColimit.ι_map _ _ _ _).trans (by simp)

variable {y}

variable (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]

variable (j₀) in
noncomputable def hc₃ : IsColimit (c₃ c j₀) :=
  have := isFiltered_of_isCardinalDirected J κ
  (Functor.Final.isColimitWhiskerEquiv _ _).symm hc

include κ hκ hc hy in
lemma epi_f : Epi (f y) := by
  have := isFiltered_of_isCardinalDirected J κ
  exact (colim.exact_mapShortComplex (S_exact y)
    (colimit.isColimit _) (isColimitConstCocone _ _) (hc₃ hc j₀ κ) (f y) 0
    (fun j ↦ by simpa using hf y j) (fun _ ↦ by simpa using hy.symm)).epi_f rfl

end injectivity₀

variable {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hXκ : HasCardinalLT (Subobject X) κ)

include hXκ hc hy in
open injectivity₀ in
lemma injectivity₀ : ∃ (j : J) (φ : j₀ ⟶ j), y ≫ Y.map φ = 0 := by
  obtain ⟨j, h⟩ := exists_isIso_of_functor_from_monoOver (F y) hXκ _
      (colimit.isColimit (kernel (γ y))) (f y) (fun j ↦ by simpa using hf y j)
      (epi_f hc hy κ)
  dsimp at h
  refine ⟨j.right, j.hom, ?_⟩
  simpa only [← cancel_epi ((kernel.ι (γ y)).app j), comp_zero]
    using NatTrans.congr_app (kernel.condition (γ y)) j

end injectivity

section surjectivity

variable {Y} {c : Cocone Y} (hc : IsColimit c)

namespace surjectivity

variable (z : X ⟶ c.pt)

@[simps]
noncomputable def F [Mono c.ι] : J ⥤ MonoOver X where
  obj j := MonoOver.mk' ((pullback.snd c.ι ((Functor.const _).map z)).app j)
  map {j j'} f := MonoOver.homMk ((pullback c.ι ((Functor.const _).map z)).map f)

noncomputable def f : colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X :=
  colimit.desc _ (Cocone.mk X
    { app j := (pullback.snd c.ι ((Functor.const _).map z)).app j })

lemma hf (j : J) :
    colimit.ι (pullback c.ι ((Functor.const J).map z)) j ≫ f z =
      (pullback.snd c.ι ((Functor.const J).map z)).app j :=
  colimit.ι_desc _ _

variable (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]

include hc κ in
lemma epi_f : Epi (f z) := by
  have := isFiltered_of_isCardinalDirected J κ
  have isPullback := (IsPullback.of_hasPullback c.ι ((Functor.const _).map z)).map colim
  have : IsIso (f z) := by
    refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).1
      (MorphismProperty.of_isPullback isPullback ?_)
    · refine Arrow.isoMk (Iso.refl _)
        (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitConstCocone J X)) ?_
      dsimp
      ext j
      dsimp
      rw [Category.id_comp, ι_colimMap_assoc, colimit.comp_coconePointUniqueUpToIso_hom,
        constCocone_ι, NatTrans.id_app, Category.comp_id]
      apply hf
    · refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).2
        (inferInstanceAs (IsIso (𝟙 c.pt)))
      exact Arrow.isoMk (IsColimit.coconePointUniqueUpToIso (colimit.isColimit Y) hc)
        (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (isColimitConstCocone J c.pt))
  infer_instance

end surjectivity

variable [∀ (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)]
  {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hXκ : HasCardinalLT (Subobject X) κ) (z : X ⟶ c.pt)

include κ hXκ hc in
open surjectivity in
lemma surjectivity : ∃ (j₀ : J) (y : X ⟶ Y.obj j₀), z = y ≫ c.ι.app j₀ := by
  have := isFiltered_of_isCardinalDirected J κ
  have := hc.mono_ι_app_of_isFiltered
  have := NatTrans.mono_of_mono_app c.ι
  obtain ⟨j, _⟩ := exists_isIso_of_functor_from_monoOver (F z) hXκ _
    (colimit.isColimit _) (f z) (hf z) (epi_f hc z κ)
  refine ⟨j, inv ((F z).obj j).obj.hom ≫ (pullback.fst c.ι _).app j, ?_⟩
  dsimp
  rw [Category.assoc, IsIso.eq_inv_comp, ← NatTrans.comp_app, pullback.condition,
    NatTrans.comp_app, Functor.const_map_app]

end surjectivity

variable {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hXκ : HasCardinalLT (Subobject X) κ)

include hXκ in
lemma preservesColimit_of_mono [∀ (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)] :
    PreservesColimit Y ((coyoneda.obj (op X))) where
  preserves {c} hc := ⟨by
    have := isFiltered_of_isCardinalDirected J κ
    exact Types.FilteredColimit.isColimitOf' _ _
      (surjectivity hc hXκ) (fun j₀ y₁ y₂ hy ↦ by
        dsimp at y₁ y₂ hy ⊢
        rw [← sub_eq_zero, ← Preadditive.sub_comp] at hy
        obtain ⟨j, f, hf⟩ := injectivity₀ hc hy hXκ
        exact ⟨j, f, by simpa only [Preadditive.sub_comp, sub_eq_zero] using hf⟩)⟩

end IsPresentable

end IsGrothendieckAbelian

end CategoryTheory
