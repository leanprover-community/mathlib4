/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Morphisms to a colimit in a Grothendieck abelian category

Let `C : Type u` be an abelian category `[Category.{v} C]` which
satisfies `IsGrothendieckAbelian.{w} C`. We may expect
that all the objects `X : C` are `κ`-presentable for some regular
cardinal `κ`. However, we only prove a weaker result (which
is enough in order to obtain the existence of enough
injectives (TODO)): let `κ` be a big enough regular
cardinal such that if `Y : J ⥤ C` is a functor from
a `κ`-filtered category, and `c : Cocone Y` is a colimit cocone,
then the map from the colimit of the types `X ⟶ Y j` to
`X ⟶ c.pt` is injective, and it is bijective under the
additional assumption that for any map `f : j ⟶ j'` in `J`,
`Y.map f` is a monomorphism, see
`IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

attribute [local instance] IsFiltered.isConnected

namespace IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {X : C} {J : Type w} [SmallCategory J]

namespace IsPresentable

variable {Y : J ⥤ C} {c : Cocone Y} (hc : IsColimit c)

namespace injectivity₀

variable {j₀ : J} (y : X ⟶ Y.obj j₀) (hy : y ≫ c.ι.app j₀ = 0)

/-!
Given `y : X ⟶ Y.obj j₀`, we introduce a natural
transformation `g : X ⟶ Y.obj t.right` for `t : Under j₀`.
We consider the kernel of this morphism: we have a natural exact sequence
`kernel (g y) ⟶ X ⟶ Y.obj t.right` for all `t : Under j₀`. Under the
assumption that the composition `y ≫ c.ι.app j₀ : X ⟶ c.pt` is zero,
we get that after passing to the colimit, the right map `X ⟶ c.pt` is
zero, which implies that the left map `f : colimit (kernel (g y)) ⟶ X`
is an epimorphism (see `epi_f`). If `κ` is a regular cardinal that is
bigger than the cardinality of `Subobject X` and `J` is `κ`-filtered,
it follows that for some `φ : j₀ ⟶ j` in `Under j₀`,
the inclusion `(kernel.ι (g y)).app j` is an isomorphism,
which implies that `y ≫ Y.map φ = 0` (see the lemma `injectivity₀`).
-/

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `X ⟶ Y.obj t.right` for `t : Under j₀`
that is induced by `y : X ⟶ Y.obj j₀`. -/
@[simps]
def g : (Functor.const _).obj X ⟶ Under.forget j₀ ⋙ Y where
  app t := y ≫ Y.map t.hom
  naturality t₁ t₂ f := by
    dsimp
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp, Under.w]

/-- The obvious morphism `colimit (kernel (g y)) ⟶ X` (which is an epimorphism
if `J` is filtered, see `epi_f`). -/
noncomputable def f : colimit (kernel (g y)) ⟶ X :=
  IsColimit.map (colimit.isColimit _) (constCocone _ X) (kernel.ι _)

set_option backward.defeqAttrib.useBackward true in
lemma hf (j : Under j₀) :
    colimit.ι (kernel (g y)) j ≫ f y = (kernel.ι (g y)).app j :=
  (IsColimit.ι_map _ _ _ _).trans (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {y} in
include hc hy in
lemma epi_f [IsFiltered J] : Epi (f y) := by
  exact (colim.exact_mapShortComplex
    ((ShortComplex.mk _ _ (kernel.condition (g y))).exact_of_f_is_kernel
      (kernelIsKernel (g y)))
    (colimit.isColimit _) (isColimitConstCocone _ _)
    ((Functor.Final.isColimitWhiskerEquiv (Under.forget j₀) c).symm hc) (f y) 0
    (fun j ↦ by simpa using! hf y j)
    (fun _ ↦ by simpa using! hy.symm)).epi_f rfl

set_option backward.defeqAttrib.useBackward true in
/-- The kernel of `g y` gives a family of subobjects of `X` indexed by `Under j₀`, and
we consider it as a functor `Under j₀ ⥤ MonoOver X`. -/
@[simps]
noncomputable def F : Under j₀ ⥤ MonoOver X where
  obj j := MonoOver.mk ((kernel.ι (g y)).app j)
  map {j j'} f := MonoOver.homMk ((kernel (g y)).map f)

end injectivity₀

section

variable {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hXκ : HasCardinalLT (Subobject X) κ)

include hXκ hc

set_option backward.defeqAttrib.useBackward true in
open injectivity₀ in
lemma injectivity₀ {j₀ : J} (y : X ⟶ Y.obj j₀) (hy : y ≫ c.ι.app j₀ = 0) :
    ∃ (j : J) (φ : j₀ ⟶ j), y ≫ Y.map φ = 0 := by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨j, h⟩ := exists_isIso_of_functor_from_monoOver (F y) hXκ _
      (colimit.isColimit (kernel (g y))) (f y) (fun j ↦ by simpa using! hf y j)
      (epi_f hc hy)
  dsimp at h
  refine ⟨j.right, j.hom, ?_⟩
  simpa only [← cancel_epi ((kernel.ι (g y)).app j), comp_zero]
    using! NatTrans.congr_app (kernel.condition (g y)) j

lemma injectivity (j₀ : J) (y₁ y₂ : X ⟶ Y.obj j₀)
    (hy : y₁ ≫ c.ι.app j₀ = y₂ ≫ c.ι.app j₀) :
    ∃ (j : J) (φ : j₀ ⟶ j), y₁ ≫ Y.map φ = y₂ ≫ Y.map φ := by
  obtain ⟨j, φ, hφ⟩ := injectivity₀ hc hXκ (y₁ - y₂)
    (by rw [Preadditive.sub_comp, sub_eq_zero, hy])
  exact ⟨j, φ, by simpa only [Preadditive.sub_comp, sub_eq_zero] using hφ⟩

end

namespace surjectivity

variable (z : X ⟶ c.pt)

/-!
Let `z : X ⟶ c.pt` (where `c` is a colimit cocone for `Y : J ⥤ C`).
We consider the pullback of `c.ι` and of the constant
map `(Functor.const J).map z`. If we assume that `c.ι` is a monomorphism,
then this pullback evaluated at `j : J` can be identified to a subobject of `X`
(this is the inverse image by `z` of `Y.obj j` considered as a subobject of `c.pt`).
This corresponds to a functor `F z : J ⥤ MonoOver X`, and when taking the colimit
(computed in `C`), we obtain an epimorphism
`f z : colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X`
when `J` is filtered (see `epi_f`). If `κ` is a regular cardinal that is
bigger than the cardinality of `Subobject X` and `J` is `κ`-filtered,
we deduce that `z` factors as `X ⟶ Y.obj j ⟶ c.pt` for some `j`
(see the lemma `surjectivity`).
-/

set_option backward.defeqAttrib.useBackward true in
/-- The functor `J ⥤ MonoOver X` which sends `j : J` to the inverse image by `z : X ⟶ c.pt`
of the subobject `Y.obj j` of `c.pt`; it is defined here as the object in `MonoOver X`
corresponding to the monomorphism
`(pullback.snd c.ι ((Functor.const _).map z)).app j`. -/
@[simps]
noncomputable def F [Mono c.ι] : J ⥤ MonoOver X where
  obj j := MonoOver.mk ((pullback.snd c.ι ((Functor.const _).map z)).app j)
  map {j j'} f := MonoOver.homMk ((pullback c.ι ((Functor.const _).map z)).map f)

/-- The canonical map `colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X`,
which is an isomorphism when `J` is filtered, see `isIso_f`. -/
noncomputable def f : colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X :=
  colimit.desc _ (Cocone.mk X
    { app j := (pullback.snd c.ι ((Functor.const _).map z)).app j })

lemma hf (j : J) :
    colimit.ι (pullback c.ι ((Functor.const J).map z)) j ≫ f z =
      (pullback.snd c.ι ((Functor.const J).map z)).app j :=
  colimit.ι_desc _ _

include hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma isIso_f [IsFiltered J] : IsIso (f z) := by
  refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).1
    (MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback c.ι ((Functor.const _).map z)).map colim) ?_)
  · refine Arrow.isoMk (Iso.refl _)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitConstCocone J X)) ?_
    dsimp
    ext j
    rw [Category.id_comp, ι_colimMap_assoc, colimit.comp_coconePointUniqueUpToIso_hom,
      constCocone_ι, NatTrans.id_app, Category.comp_id]
    apply hf
  · refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).2
      ((inferInstance : IsIso (𝟙 c.pt)))
    exact Arrow.isoMk (IsColimit.coconePointUniqueUpToIso (colimit.isColimit Y) hc)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitConstCocone J c.pt))

lemma epi_f [IsFiltered J] : Epi (f z) := by
  have := isIso_f hc z
  infer_instance

end surjectivity

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
open surjectivity in
lemma surjectivity [∀ (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)]
    {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hXκ : HasCardinalLT (Subobject X) κ) (z : X ⟶ c.pt) :
    ∃ (j₀ : J) (y : X ⟶ Y.obj j₀), z = y ≫ c.ι.app j₀ := by
  have := isFiltered_of_isCardinalFiltered J κ
  have := hc.mono_ι_app_of_isFiltered
  have := NatTrans.mono_of_mono_app c.ι
  obtain ⟨j, _⟩ := exists_isIso_of_functor_from_monoOver (F z) hXκ _
    (colimit.isColimit _) (f z) (hf z) (epi_f hc z)
  refine ⟨j, inv ((F z).obj j).obj.hom ≫ (pullback.fst c.ι _).app j, ?_⟩
  dsimp
  rw [Category.assoc, IsIso.eq_inv_comp, ← NatTrans.comp_app, pullback.condition,
    NatTrans.comp_app, Functor.const_map_app]

end IsPresentable

open IsPresentable in
/-- If `X` is an object in a Grothendieck abelian category, then
the functor `coyoneda.obj (op X)` commutes with colimits corresponding
to diagrams of monomorphisms indexed by `κ`-filtered categories
for a big enough regular cardinal `κ`. -/
lemma preservesColimit_coyoneda_obj_of_mono
    (Y : J ⥤ C) {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
    [IsCardinalFiltered J κ] (hXκ : HasCardinalLT (Subobject X) κ)
    [∀ (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)] :
    PreservesColimit Y ((coyoneda.obj (op X))) where
  preserves {c} hc := ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    exact Types.FilteredColimit.isColimitOf' _ _
      (surjectivity hc hXκ) (injectivity hc hXκ)⟩

end IsGrothendieckAbelian

end CategoryTheory
