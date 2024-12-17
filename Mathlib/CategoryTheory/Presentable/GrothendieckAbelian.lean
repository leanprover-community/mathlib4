/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory
import Mathlib.CategoryTheory.Limits.TypesFiltered
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Filtered.Final

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

namespace Limits

variable {C : Type u} [Category.{v} C] (J : Type u') [Category.{v'} J] (X : C)

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

variable {C : Type u} [Category.{v} C] [Abelian C]
    {J : Type u'} [Category.{v'} J]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

section

variable
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
  refine (ShortComplex.exact_iff_of_iso ?_).2 (hS.map colim)
  refine ShortComplex.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₃ (colimit.isColimit _))
    (hc₁.hom_ext (fun j ↦ ?_)) (hc₂.hom_ext (fun j ↦ ?_))
  · dsimp
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
      colimit.cocone_ι, ι_colimMap, reassoc_of% (hf j),
      IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]
  · dsimp
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
      colimit.cocone_ι, ι_colimMap, reassoc_of% (hg j),
      IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]

end

section

variable {X₁ X₂ : J ⥤ C} (φ : X₁ ⟶ X₂) [∀ j, Mono (φ.app j)]
  {c₁ : Cocone X₁} (hc₁ : IsColimit c₁) {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
  (f : c₁.pt ⟶ c₂.pt) (hf : ∀ j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j)

include hf hc₁ hc₂ in
lemma map_mono : Mono f := by
  have : Mono φ := NatTrans.mono_of_mono_app φ
  have := hf
  have : Mono (colim.map φ) := inferInstance
  have e : Arrow.mk f ≅ Arrow.mk (colim.map φ) :=
    Arrow.isoMk
      (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
      (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
      (hc₁.hom_ext (fun j ↦ by
        dsimp
        rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
          colimit.cocone_ι, ι_colimMap, reassoc_of% (hf j),
          IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]))
  exact ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff e).2
    (inferInstanceAs (Mono (colim.map φ)))

end

end HasExactColimitsOfShape

namespace MonoOver

variable {C : Type u} [Category.{v} C] {X : C}

instance mono_obj_hom (S : MonoOver X) :
    Mono S.obj.hom := S.2

lemma subobject_mk_of_hom {S T : MonoOver X} (f : S ⟶ T) :
    Subobject.mk S.obj.hom ≤ Subobject.mk T.obj.hom :=
  Subobject.mk_le_mk_of_comm f.left (by simp)

end MonoOver

namespace Subobject

variable {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) [Mono f]

lemma epi_iff_mk_eq_top [Balanced C] :
    Epi f ↔ Subobject.mk f = ⊤ := by
  rw [← isIso_iff_mk_eq_top]
  exact ⟨fun _ ↦ isIso_of_mono_of_epi f, fun _ ↦ inferInstance⟩

end Subobject

namespace IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {X : C} {J : Type w} [SmallCategory J] (F : J ⥤ MonoOver X)

section

variable [IsFiltered J] {c : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _)}
  (hc : IsColimit c) (f : c.pt ⟶ X) (hf : ∀ (j : J), c.ι.app j ≫ f = (F.obj j).obj.hom)

include hc hf
lemma mono_of_isColimit_monoOver : Mono f := by
  let α : F ⋙ MonoOver.forget _ ⋙ Over.forget _ ⟶ (Functor.const _).obj X :=
    { app j := (F.obj j).obj.hom
      naturality _ _ f := (F.map f).w }
  exact HasExactColimitsOfShape.map_mono (φ := α) (hc₁ := hc)
    (hc₂ := constCoconeIsColimit J X) f (by simpa using hf)

lemma subobject_mk_of_isColimit_eq_iSup :
    haveI := mono_of_isColimit_monoOver F hc f hf
    Subobject.mk f = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
  haveI := mono_of_isColimit_monoOver F hc f hf
  apply le_antisymm
  · rw [le_iSup_iff]
    intro s H
    induction' s using Subobject.ind with Z g _
    let c' : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _) := Cocone.mk Z
      { app j := Subobject.ofMkLEMk _ _ (H j)
        naturality j j' f := by
          dsimp
          simpa only [← cancel_mono g, Category.assoc, Subobject.ofMkLEMk_comp,
            Category.comp_id] using MonoOver.w (F.map f) }
    exact Subobject.mk_le_mk_of_comm (hc.desc c')
      (hc.hom_ext (fun j ↦ by rw [hc.fac_assoc c' j, hf, Subobject.ofMkLEMk_comp]))
  · rw [iSup_le_iff]
    intro j
    exact Subobject.mk_le_mk_of_comm (c.ι.app j) (hf j)

end

section

variable
  {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hXκ : HasCardinalLT (Subobject X) κ)
  (c : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _)) (hc : IsColimit c)
  (f : c.pt ⟶ X) (hf : ∀ (j : J), c.ι.app j ≫ f = (F.obj j).obj.hom)

include hf hc hXκ in
lemma exists_isIso_of_functor_from_monoOver (h : Epi f) :
    ∃ (j : J), IsIso (F.obj j).obj.hom := by
  have := isFiltered_of_isCardinalDirected J κ
  simp only [Subobject.isIso_iff_mk_eq_top]
  have := mono_of_isColimit_monoOver F hc f hf
  rw [Subobject.epi_iff_mk_eq_top f,
    subobject_mk_of_isColimit_eq_iSup F hc f hf] at h
  have := hXκ
  let s (j : J) : Subobject X := Subobject.mk (F.obj j).obj.hom
  let S := Set.range s
  have h' : Function.Surjective (fun (j : J) ↦ (⟨s j, _, rfl⟩ : S)) := by
    rintro ⟨_, j, rfl⟩
    exact ⟨j, rfl⟩
  obtain ⟨σ, hσ⟩ := h'.hasRightInverse
  have hS : HasCardinalLT S κ :=
    hXκ.of_injective (f := Subtype.val) Subtype.val_injective
  refine ⟨IsCardinalFiltered.max σ hS, ?_⟩
  rw [← top_le_iff, ← h, iSup_le_iff]
  intro j
  let t : S := ⟨_, j, rfl⟩
  trans Subobject.mk (F.obj (σ t)).obj.hom
  · have := le_of_eq (hσ t).symm
    exact this
  · exact MonoOver.subobject_mk_of_hom
      (F.map (IsCardinalFiltered.toMax σ hS t))

end

end IsGrothendieckAbelian

namespace IsFiltered

instance (J : Type u) [Category.{v} J] [IsFilteredOrEmpty J] (j₀ : J) :
    IsFiltered (Under j₀) where
  nonempty := ⟨Under.mk (𝟙 j₀)⟩
  cocone_objs X Y := by
    let f := coeqHom (X.hom ≫ leftToMax _ _) (Y.hom ≫ rightToMax _ _)
    exact ⟨Under.mk (X.hom ≫ leftToMax _ _ ≫ f),
      Under.homMk (leftToMax _ _ ≫ f), Under.homMk (rightToMax _ _ ≫ f)
      (by simpa [Category.assoc] using
        (coeq_condition (X.hom ≫ leftToMax _ _) (Y.hom ≫ rightToMax _ _)).symm), ⟨⟩⟩
  cocone_maps X Y f g :=
    ⟨Under.mk (Y.hom ≫ coeqHom f.right g.right),
      Under.homMk (coeqHom f.right g.right), by ext; apply coeq_condition⟩

instance (J : Type u) [Category.{v} J] [IsFiltered J] (j₀ : J) :
    (Under.forget j₀).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun j ↦ ⟨Under.mk (leftToMax j₀ j), ⟨rightToMax _ _⟩⟩)
    (fun {j k} s s' ↦ ⟨Under.mk (k.hom ≫ coeqHom s s'),
        Under.homMk (coeqHom s s'), coeq_condition s s'⟩)

end IsFiltered

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

variable (c j₀) in
abbrev c₃ : Cocone (Under.forget j₀ ⋙ Y) := c.whisker _

instance (j : Under j₀) : Mono ((kernel.ι (γ y)).app j) := by
  -- this should already be an instance
  change Mono (((evaluation _ _).obj j).map (kernel.ι (γ y)))
  infer_instance

@[simps]
noncomputable def F : Under j₀ ⥤ MonoOver X where
  obj j := MonoOver.mk' ((kernel.ι (γ y)).app j)
  map {j j'} f := MonoOver.homMk ((kernel (γ y)).map f)

variable (κ j₀) in
noncomputable def hc₃ : IsColimit (c₃ c j₀) :=
  have := isFiltered_of_isCardinalDirected J κ
  (Functor.Final.isColimitWhiskerEquiv _ _).symm hc

noncomputable def f : colimit (kernel (γ y)) ⟶ X :=
  IsColimit.map (colimit.isColimit _) (constCocone _ X) (kernel.ι _)

lemma hf (j : Under j₀) :
    colimit.ι (kernel (γ y)) j ≫ f y = (kernel.ι (γ y)).app j :=
  (IsColimit.ι_map _ _ _ _).trans (by simp)

variable {y} (κ)

include κ hc hy in
lemma epi_f : Epi (f y) := by
  have := isFiltered_of_isCardinalDirected J κ
  exact (HasExactColimitsOfShape.mapShortComplex_exact (S_exact y)
    (colimit.isColimit _) (constCoconeIsColimit _ _) (hc₃ κ hc j₀) (f y) 0
    (fun j ↦ by simpa using hf y j) (fun _ ↦ by simpa using hy.symm)).epi_f rfl

end injectivity₀

include hXκ hc hy

open injectivity₀ in
lemma injectivity₀ : ∃ (j : J) (φ : j₀ ⟶ j), y ≫ Y.map φ = 0 := by
  have := isFiltered_of_isCardinalDirected J κ
  have := epi_f κ hc hy
  obtain ⟨j, h⟩ := exists_isIso_of_functor_from_monoOver (F y) hXκ _
      (colimit.isColimit (kernel (γ y))) (f y) (fun j ↦ by simpa using hf y j)
      (epi_f κ hc hy)
  dsimp at h
  refine ⟨j.right, j.hom, ?_⟩
  simpa only [← cancel_epi ((kernel.ι (γ y)).app j), comp_zero]
    using NatTrans.congr_app (kernel.condition (γ y)) j

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
